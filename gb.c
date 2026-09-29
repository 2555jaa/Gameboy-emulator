/*
 * Game Boy (DMG) emulator - faili moja, Windows (GDI)
 *
 * Compile (MinGW):  gcc gb.c -o gb.exe -O2 -lgdi32 -luser32
 * Compile (MSVC):   cl /O2 gb.c user32.lib gdi32.lib
 * Run:              gb.exe [rom.gb]     (default: tetris.gb)
 *
 * Keys: Arrows = D-pad, Z/J = A, X/K = B, Space/RShift = Select, Enter = Start
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>

#define FLAG_Z 0x80
#define FLAG_N 0x40
#define FLAG_H 0x20
#define FLAG_C 0x10

#define GB_WIDTH   160
#define GB_HEIGHT  144
#define SCALE      3
#define CYCLES_PER_FRAME 70224
#define CPU_HZ     4194304.0

typedef struct {
    union { struct { uint8_t f; uint8_t a; }; uint16_t af; };
    union { struct { uint8_t c; uint8_t b; }; uint16_t bc; };
    union { struct { uint8_t e; uint8_t d; }; uint16_t de; };
    union { struct { uint8_t l; uint8_t h; }; uint16_t hl; };
    uint16_t sp;
    uint16_t pc;
} Registers;

/* ---------- state ---------- */
static Registers cpu;
static uint8_t memory[65536];
static uint8_t *rom = NULL;
static size_t rom_size = 0;
static uint8_t ext_ram[0x20000];
static size_t ext_ram_size = 0;

static int mbc_type = 0;              /* 0 none, 1 MBC1, 3 MBC3, 5 MBC5 */
static unsigned rom_bank = 1, ram_bank = 0;
static int ram_enable = 0, mbc1_mode = 0, mbc1_hi = 0, mbc1_lo = 1;

static int ime = 0, ei_pending = 0, halted = 0, halt_bug = 0;
static uint64_t sysclk = 0xABCC;

static int ppu_cycles = 0, ly = 0, ppu_mode = 1, stat_line = 0, win_line = 0, frame_ready = 0;
static uint32_t screen_buffer[GB_WIDTH * GB_HEIGHT];
static uint8_t bg_idx[GB_WIDTH];

static uint8_t joypad_buttons = 0x0F;
static uint8_t joypad_dpad    = 0x0F;

static HWND hwnd;
static BITMAPINFO bmi;
static char rom_path[MAX_PATH] = "tetris.gb";
static int running = 1;

static const uint32_t colors[4] = { 0x00E0F8D0, 0x0088C070, 0x00346856, 0x00081820 };

static const uint8_t cyc[256] = { /* M-cycles */
    1,3,2,2,1,1,2,1, 5,2,2,2,1,1,2,1,
    1,3,2,2,1,1,2,1, 3,2,2,2,1,1,2,1,
    2,3,2,2,1,1,2,1, 2,2,2,2,1,1,2,1,
    2,3,2,2,3,3,3,1, 2,2,2,2,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    2,2,2,2,2,2,1,2, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    1,1,1,1,1,1,2,1, 1,1,1,1,1,1,2,1,
    2,3,3,4,3,4,2,4, 2,4,3,1,3,6,2,4,
    2,3,3,1,3,4,2,4, 2,4,3,1,3,1,2,4,
    3,3,2,1,1,4,2,4, 4,1,4,1,1,1,2,4,
    3,3,2,1,1,4,2,4, 3,2,4,1,1,1,2,4
};

/* ---------- memory / MBC ---------- */
static void mbc_write(uint16_t a, uint8_t v) {
    switch (mbc_type) {
    case 1:
        if (a < 0x2000) ram_enable = ((v & 0x0F) == 0x0A);
        else if (a < 0x4000) { mbc1_lo = v & 0x1F; if (!mbc1_lo) mbc1_lo = 1; rom_bank = (mbc1_hi << 5) | mbc1_lo; }
        else if (a < 0x6000) { mbc1_hi = v & 3; rom_bank = (mbc1_hi << 5) | mbc1_lo; ram_bank = mbc1_mode ? mbc1_hi : 0; }
        else { mbc1_mode = v & 1; ram_bank = mbc1_mode ? mbc1_hi : 0; }
        break;
    case 3:
        if (a < 0x2000) ram_enable = ((v & 0x0F) == 0x0A);
        else if (a < 0x4000) { rom_bank = v & 0x7F; if (!rom_bank) rom_bank = 1; }
        else if (a < 0x6000) ram_bank = v;
        break;
    case 5:
        if (a < 0x2000) ram_enable = ((v & 0x0F) == 0x0A);
        else if (a < 0x3000) rom_bank = (rom_bank & 0x100) | v;
        else if (a < 0x4000) rom_bank = (rom_bank & 0xFF) | ((v & 1) << 8);
        else if (a < 0x6000) ram_bank = v & 0x0F;
        break;
    default: break;
    }
}

static uint8_t read_io(uint16_t a) {
    switch (a) {
    case 0xFF00: {
        uint8_t sel = memory[0xFF00] & 0x30, res = 0x0F;
        if (!(sel & 0x10)) res &= joypad_dpad;
        if (!(sel & 0x20)) res &= joypad_buttons;
        return 0xC0 | sel | res;
    }
    case 0xFF04: return (uint8_t)(sysclk >> 8);
    case 0xFF0F: return memory[0xFF0F] | 0xE0;
    case 0xFF41: {
        uint8_t v = (memory[0xFF41] & 0x78) | 0x80 | (uint8_t)ppu_mode;
        if (memory[0xFF40] & 0x80) { if (ly == memory[0xFF45]) v |= 4; }
        else v &= ~3;
        return v;
    }
    case 0xFF44: return (uint8_t)ly;
    default: return memory[a];
    }
}

static uint8_t read_byte(uint16_t a) {
    if (a < 0x4000) return rom[a % rom_size];
    if (a < 0x8000) return rom[((size_t)rom_bank * 0x4000 + (a - 0x4000)) % rom_size];
    if (a >= 0xA000 && a < 0xC000) {
        if (!ram_enable || !ext_ram_size) return 0xFF;
        if (mbc_type == 3 && ram_bank > 3) return 0xFF;
        return ext_ram[((size_t)ram_bank * 0x2000 + (a - 0xA000)) % ext_ram_size];
    }
    if (a >= 0xE000 && a < 0xFE00) return memory[a - 0x2000];
    if (a >= 0xFEA0 && a < 0xFF00) return 0xFF;
    if (a >= 0xFF00) return read_io(a);
    return memory[a];
}

static void write_io(uint16_t a, uint8_t v) {
    switch (a) {
    case 0xFF00: memory[0xFF00] = v & 0x30; break;
    case 0xFF04: sysclk = 0; break;
    case 0xFF0F: memory[0xFF0F] = v & 0x1F; break;
    case 0xFF40: {
        uint8_t old = memory[0xFF40];
        if ((old & 0x80) && !(v & 0x80)) {
            ly = 0; ppu_cycles = 0; ppu_mode = 0; stat_line = 0;
            for (int i = 0; i < GB_WIDTH * GB_HEIGHT; i++) screen_buffer[i] = colors[0];
        }
        if (!(old & 0x80) && (v & 0x80)) { ly = 0; ppu_cycles = 0; win_line = 0; ppu_mode = 0; }
        memory[0xFF40] = v;
        break;
    }
    case 0xFF41: memory[0xFF41] = v & 0x78; break;
    case 0xFF44: break;
    case 0xFF46: {
        uint16_t src = (uint16_t)v << 8;
        for (int i = 0; i < 160; i++) memory[0xFE00 + i] = read_byte(src + i);
        memory[0xFF46] = v;
        break;
    }
    default: memory[a] = v; break;
    }
}

static void write_byte(uint16_t a, uint8_t v) {
    if (a < 0x8000) { mbc_write(a, v); return; }
    if (a >= 0xA000 && a < 0xC000) {
        if (ram_enable && ext_ram_size && !(mbc_type == 3 && ram_bank > 3))
            ext_ram[((size_t)ram_bank * 0x2000 + (a - 0xA000)) % ext_ram_size] = v;
        return;
    }
    if (a >= 0xE000 && a < 0xFE00) { memory[a - 0x2000] = v; return; }
    if (a >= 0xFEA0 && a < 0xFF00) return;
    if (a >= 0xFF00) { write_io(a, v); return; }
    memory[a] = v;
}

static uint8_t fetch8(void)  { return read_byte(cpu.pc++); }
static uint16_t fetch16(void) { uint8_t lo = fetch8(); uint8_t hi = fetch8(); return (uint16_t)((hi << 8) | lo); }
static void push_word(uint16_t v) { write_byte(--cpu.sp, v >> 8); write_byte(--cpu.sp, v & 0xFF); }
static uint16_t pop_word(void) { uint8_t lo = read_byte(cpu.sp++); uint8_t hi = read_byte(cpu.sp++); return (uint16_t)((hi << 8) | lo); }

/* ---------- PPU ---------- */
static void render_scanline(int y) {
    uint8_t lcdc = memory[0xFF40];
    uint8_t bgp = memory[0xFF47];
    uint32_t pal[4];
    for (int i = 0; i < 4; i++) pal[i] = colors[(bgp >> (i * 2)) & 3];
    uint32_t *line = &screen_buffer[y * GB_WIDTH];
    memset(bg_idx, 0, sizeof bg_idx);

    if (lcdc & 1) {
        uint8_t scy = memory[0xFF42], scx = memory[0xFF43];
        uint8_t wy = memory[0xFF4A], wx = memory[0xFF4B];
        int win = (lcdc & 0x20) && y >= wy && wx <= 166;
        int win_drawn = 0;
        uint16_t bg_map  = (lcdc & 0x08) ? 0x9C00 : 0x9800;
        uint16_t win_map = (lcdc & 0x40) ? 0x9C00 : 0x9800;
        for (int x = 0; x < GB_WIDTH; x++) {
            uint16_t map; int px, py;
            if (win && x >= (int)wx - 7) {
                map = win_map; px = x - ((int)wx - 7); py = win_line; win_drawn = 1;
            } else {
                map = bg_map; px = (x + scx) & 0xFF; py = (y + scy) & 0xFF;
            }
            uint8_t tile = memory[map + (py >> 3) * 32 + (px >> 3)];
            uint16_t addr = (lcdc & 0x10) ? (uint16_t)(0x8000 + tile * 16)
                                          : (uint16_t)(0x9000 + (int8_t)tile * 16);
            addr += (py & 7) * 2;
            int bit = 7 - (px & 7);
            int idx = (((memory[addr + 1] >> bit) & 1) << 1) | ((memory[addr] >> bit) & 1);
            bg_idx[x] = (uint8_t)idx;
            line[x] = pal[idx];
        }
        if (win_drawn) win_line++;
    } else {
        for (int x = 0; x < GB_WIDTH; x++) line[x] = colors[0];
    }

    if (lcdc & 2) {
        int h = (lcdc & 4) ? 16 : 8;
        int list[10], n = 0;
        for (int i = 0; i < 40 && n < 10; i++) {
            int sy = memory[0xFE00 + i * 4] - 16;
            if (y >= sy && y < sy + h) list[n++] = i;
        }
        if (n) {
            uint8_t obp0 = memory[0xFF48], obp1 = memory[0xFF49];
            for (int x = 0; x < GB_WIDTH; x++) {
                int best = -1, best_x = 1000, best_col = 0, best_flags = 0;
                for (int k = 0; k < n; k++) {
                    int i = list[k];
                    int sy = memory[0xFE00 + i * 4] - 16;
                    int sx = memory[0xFE00 + i * 4 + 1] - 8;
                    if (x < sx || x >= sx + 8) continue;
                    if (best != -1 && sx >= best_x) continue;
                    int tile = memory[0xFE00 + i * 4 + 2];
                    uint8_t flags = memory[0xFE00 + i * 4 + 3];
                    int row = y - sy;
                    if (flags & 0x40) row = h - 1 - row;
                    if (h == 16) { tile = (tile & 0xFE) + (row >= 8); row &= 7; }
                    int col = x - sx;
                    if (flags & 0x20) col = 7 - col;
                    int bit = 7 - col;
                    uint16_t addr = (uint16_t)(0x8000 + tile * 16 + row * 2);
                    int idx = (((memory[addr + 1] >> bit) & 1) << 1) | ((memory[addr] >> bit) & 1);
                    if (idx == 0) continue;
                    best = i; best_x = sx; best_col = idx; best_flags = flags;
                }
                if (best >= 0) {
                    if ((best_flags & 0x80) && bg_idx[x]) continue;
                    uint8_t p = (best_flags & 0x10) ? obp1 : obp0;
                    line[x] = colors[(p >> (best_col * 2)) & 3];
                }
            }
        }
    }
}

static void ppu_step(int c) {
    if (!(memory[0xFF40] & 0x80)) return;
    ppu_cycles += c;
    if (ppu_cycles >= 456) {
        ppu_cycles -= 456;
        ly++;
        if (ly == 144) { memory[0xFF0F] |= 0x01; frame_ready = 1; }
        else if (ly > 153) { ly = 0; win_line = 0; }
    }
    int mode;
    if (ly >= 144) mode = 1;
    else if (ppu_cycles < 80) mode = 2;
    else if (ppu_cycles < 252) mode = 3;
    else mode = 0;
    if (ppu_mode == 3 && mode == 0 && ly < 144) render_scanline(ly);
    ppu_mode = mode;

    uint8_t stat = memory[0xFF41];
    int lyc = (ly == memory[0xFF45]);
    int line = (lyc && (stat & 0x40)) || (mode == 0 && (stat & 0x08)) ||
               (mode == 1 && (stat & 0x10)) || (mode == 2 && (stat & 0x20));
    if (line && !stat_line) memory[0xFF0F] |= 0x02;
    stat_line = line;
}

/* ---------- timer ---------- */
static void timer_step(int c) {
    static const int shift[4] = { 10, 4, 6, 8 };
    uint64_t old = sysclk;
    sysclk += c;
    uint8_t tac = memory[0xFF07];
    if (tac & 4) {
        int sh = shift[tac & 3];
        uint64_t inc = (sysclk >> sh) - (old >> sh);
        while (inc--) {
            if (++memory[0xFF05] == 0) {
                memory[0xFF05] = memory[0xFF06];
                memory[0xFF0F] |= 0x04;
            }
        }
    }
}

/* ---------- CPU ---------- */
static uint8_t get_r(int i) {
    switch (i) {
    case 0: return cpu.b; case 1: return cpu.c; case 2: return cpu.d; case 3: return cpu.e;
    case 4: return cpu.h; case 5: return cpu.l; case 6: return read_byte(cpu.hl);
    default: return cpu.a;
    }
}
static void set_r(int i, uint8_t v) {
    switch (i) {
    case 0: cpu.b = v; break; case 1: cpu.c = v; break; case 2: cpu.d = v; break; case 3: cpu.e = v; break;
    case 4: cpu.h = v; break; case 5: cpu.l = v; break; case 6: write_byte(cpu.hl, v); break;
    default: cpu.a = v; break;
    }
}
static uint16_t get_rp(int i) {
    switch (i) { case 0: return cpu.bc; case 1: return cpu.de; case 2: return cpu.hl; default: return cpu.sp; }
}
static void set_rp(int i, uint16_t v) {
    switch (i) { case 0: cpu.bc = v; break; case 1: cpu.de = v; break; case 2: cpu.hl = v; break; default: cpu.sp = v; break; }
}
static uint16_t get_rp2(int i) {
    switch (i) { case 0: return cpu.bc; case 1: return cpu.de; case 2: return cpu.hl; default: return cpu.af; }
}
static void set_rp2(int i, uint16_t v) {
    switch (i) { case 0: cpu.bc = v; break; case 1: cpu.de = v; break; case 2: cpu.hl = v; break; default: cpu.af = v & 0xFFF0; break; }
}
static int cond(int cc) {
    switch (cc) {
    case 0: return !(cpu.f & FLAG_Z);
    case 1: return  (cpu.f & FLAG_Z);
    case 2: return !(cpu.f & FLAG_C);
    default: return (cpu.f & FLAG_C);
    }
}

static void alu(int op, uint8_t v) {
    uint8_t a = cpu.a;
    int c = (cpu.f & FLAG_C) ? 1 : 0;
    switch (op) {
    case 0: case 1: {
        int cy = (op == 1) ? c : 0;
        int r = a + v + cy;
        cpu.f = 0;
        if ((r & 0xFF) == 0) cpu.f |= FLAG_Z;
        if (((a & 0x0F) + (v & 0x0F) + cy) > 0x0F) cpu.f |= FLAG_H;
        if (r > 0xFF) cpu.f |= FLAG_C;
        cpu.a = (uint8_t)r;
        break;
    }
    case 2: case 3: case 7: {
        int cy = (op == 3) ? c : 0;
        int r = a - v - cy;
        cpu.f = FLAG_N;
        if ((r & 0xFF) == 0) cpu.f |= FLAG_Z;
        if ((a & 0x0F) < ((v & 0x0F) + cy)) cpu.f |= FLAG_H;
        if (r < 0) cpu.f |= FLAG_C;
        if (op != 7) cpu.a = (uint8_t)r;
        break;
    }
    case 4: cpu.a &= v; cpu.f = cpu.a ? FLAG_H : (FLAG_Z | FLAG_H); break;
    case 5: cpu.a ^= v; cpu.f = cpu.a ? 0 : FLAG_Z; break;
    case 6: cpu.a |= v; cpu.f = cpu.a ? 0 : FLAG_Z; break;
    }
}

static uint8_t inc8(uint8_t v) {
    uint8_t r = v + 1;
    cpu.f = (cpu.f & FLAG_C) | (r == 0 ? FLAG_Z : 0) | ((v & 0x0F) == 0x0F ? FLAG_H : 0);
    return r;
}
static uint8_t dec8(uint8_t v) {
    uint8_t r = v - 1;
    cpu.f = (cpu.f & FLAG_C) | FLAG_N | (r == 0 ? FLAG_Z : 0) | ((v & 0x0F) == 0 ? FLAG_H : 0);
    return r;
}

static void cb_step(int *cycles) {
    uint8_t op = fetch8();
    int r = op & 7, y = (op >> 3) & 7;
    *cycles = (r == 6) ? 16 : 8;
    uint8_t v = get_r(r);
    switch (op >> 6) {
    case 0: {
        int c; uint8_t res; int oc = (cpu.f & FLAG_C) ? 1 : 0;
        switch (y) {
        case 0: c = v >> 7; res = (v << 1) | c; break;
        case 1: c = v & 1;  res = (v >> 1) | (c << 7); break;
        case 2: c = v >> 7; res = (v << 1) | oc; break;
        case 3: c = v & 1;  res = (v >> 1) | (oc << 7); break;
        case 4: c = v >> 7; res = v << 1; break;
        case 5: c = v & 1;  res = (v >> 1) | (v & 0x80); break;
        case 6: c = 0;      res = (v >> 4) | (v << 4); break;
        default: c = v & 1; res = v >> 1; break;
        }
        cpu.f = (res == 0 ? FLAG_Z : 0) | (c ? FLAG_C : 0);
        set_r(r, res);
        break;
    }
    case 1:
        cpu.f = (cpu.f & FLAG_C) | FLAG_H | ((v & (1 << y)) ? 0 : FLAG_Z);
        if (r == 6) *cycles = 12;
        break;
    case 2: set_r(r, v & ~(1 << y)); break;
    default: set_r(r, v | (1 << y)); break;
    }
}

static int cpu_step(void) {
    uint8_t pending = memory[0xFF0F] & memory[0xFFFF] & 0x1F;
    if (pending) {
        halted = 0;
        if (ime) {
            ime = 0; ei_pending = 0;
            for (int i = 0; i < 5; i++) {
                if (pending & (1 << i)) {
                    memory[0xFF0F] &= ~(1 << i);
                    push_word(cpu.pc);
                    cpu.pc = 0x40 + i * 8;
                    break;
                }
            }
            return 20;
        }
    }
    if (halted) return 4;

    int was_ei = ei_pending;
    uint8_t op = read_byte(cpu.pc);
    if (halt_bug) halt_bug = 0; else cpu.pc++;
    int cycles = cyc[op] * 4;

    if ((op & 0xC0) == 0x40) {
        if (op == 0x76) {
            if (!ime && (memory[0xFF0F] & memory[0xFFFF] & 0x1F)) halt_bug = 1;
            else halted = 1;
        } else set_r((op >> 3) & 7, get_r(op & 7));
    }
    else if ((op & 0xC0) == 0x80) alu((op >> 3) & 7, get_r(op & 7));
    else if ((op & 0xC7) == 0x04) { int r = (op >> 3) & 7; set_r(r, inc8(get_r(r))); }
    else if ((op & 0xC7) == 0x05) { int r = (op >> 3) & 7; set_r(r, dec8(get_r(r))); }
    else if ((op & 0xC7) == 0x06) { int r = (op >> 3) & 7; set_r(r, fetch8()); }
    else if ((op & 0xCF) == 0x01) set_rp((op >> 4) & 3, fetch16());
    else if ((op & 0xCF) == 0x03) { int r = (op >> 4) & 3; set_rp(r, get_rp(r) + 1); }
    else if ((op & 0xCF) == 0x0B) { int r = (op >> 4) & 3; set_rp(r, get_rp(r) - 1); }
    else if ((op & 0xCF) == 0x09) {
        uint16_t v = get_rp((op >> 4) & 3);
        uint32_t r = cpu.hl + v;
        cpu.f = (cpu.f & FLAG_Z) | ((((cpu.hl & 0x0FFF) + (v & 0x0FFF)) > 0x0FFF) ? FLAG_H : 0) | (r > 0xFFFF ? FLAG_C : 0);
        cpu.hl = (uint16_t)r;
    }
    else if ((op & 0xCF) == 0xC1) set_rp2((op >> 4) & 3, pop_word());
    else if ((op & 0xCF) == 0xC5) push_word(get_rp2((op >> 4) & 3));
    else if ((op & 0xE7) == 0xC0) { if (cond((op >> 3) & 3)) { cpu.pc = pop_word(); cycles += 12; } }
    else if ((op & 0xE7) == 0xC2) { uint16_t a = fetch16(); if (cond((op >> 3) & 3)) { cpu.pc = a; cycles += 4; } }
    else if ((op & 0xE7) == 0xC4) { uint16_t a = fetch16(); if (cond((op >> 3) & 3)) { push_word(cpu.pc); cpu.pc = a; cycles += 12; } }
    else if ((op & 0xE7) == 0x20) { int8_t o = (int8_t)fetch8(); if (cond((op >> 3) & 3)) { cpu.pc += o; cycles += 4; } }
    else if ((op & 0xC7) == 0xC7) { push_word(cpu.pc); cpu.pc = op & 0x38; }
    else if ((op & 0xC7) == 0xC6) alu((op >> 3) & 7, fetch8());
    else switch (op) {
    case 0x00: break;
    case 0x10: fetch8(); break;                                   /* STOP */
    case 0x02: write_byte(cpu.bc, cpu.a); break;
    case 0x12: write_byte(cpu.de, cpu.a); break;
    case 0x22: write_byte(cpu.hl++, cpu.a); break;
    case 0x32: write_byte(cpu.hl--, cpu.a); break;
    case 0x0A: cpu.a = read_byte(cpu.bc); break;
    case 0x1A: cpu.a = read_byte(cpu.de); break;
    case 0x2A: cpu.a = read_byte(cpu.hl++); break;
    case 0x3A: cpu.a = read_byte(cpu.hl--); break;
    case 0x07: { int c = cpu.a >> 7; cpu.a = (cpu.a << 1) | c; cpu.f = c ? FLAG_C : 0; break; }
    case 0x0F: { int c = cpu.a & 1;  cpu.a = (cpu.a >> 1) | (c << 7); cpu.f = c ? FLAG_C : 0; break; }
    case 0x17: { int oc = (cpu.f & FLAG_C) ? 1 : 0; int c = cpu.a >> 7; cpu.a = (cpu.a << 1) | oc; cpu.f = c ? FLAG_C : 0; break; }
    case 0x1F: { int oc = (cpu.f & FLAG_C) ? 1 : 0; int c = cpu.a & 1;  cpu.a = (cpu.a >> 1) | (oc << 7); cpu.f = c ? FLAG_C : 0; break; }
    case 0x08: { uint16_t a = fetch16(); write_byte(a, cpu.sp & 0xFF); write_byte(a + 1, cpu.sp >> 8); break; }
    case 0x18: { int8_t o = (int8_t)fetch8(); cpu.pc += o; break; }
    case 0x27: {
        uint8_t a = cpu.a; int n = cpu.f & FLAG_N, h = cpu.f & FLAG_H, c = cpu.f & FLAG_C;
        if (!n) {
            if (c || a > 0x99) { a += 0x60; c = FLAG_C; }
            if (h || (a & 0x0F) > 9) a += 0x06;
        } else {
            if (c) a -= 0x60;
            if (h) a -= 0x06;
        }
        cpu.a = a;
        cpu.f = (a == 0 ? FLAG_Z : 0) | n | (c ? FLAG_C : 0);
        break;
    }
    case 0x2F: cpu.a = ~cpu.a; cpu.f |= FLAG_N | FLAG_H; break;
    case 0x37: cpu.f = (cpu.f & FLAG_Z) | FLAG_C; break;
    case 0x3F: cpu.f = (cpu.f & FLAG_Z) | ((cpu.f & FLAG_C) ? 0 : FLAG_C); break;
    case 0xC3: cpu.pc = fetch16(); break;
    case 0xC9: cpu.pc = pop_word(); break;
    case 0xD9: cpu.pc = pop_word(); ime = 1; break;
    case 0xCD: { uint16_t a = fetch16(); push_word(cpu.pc); cpu.pc = a; break; }
    case 0xCB: cb_step(&cycles); break;
    case 0xE0: write_byte(0xFF00 + fetch8(), cpu.a); break;
    case 0xF0: cpu.a = read_byte(0xFF00 + fetch8()); break;
    case 0xE2: write_byte(0xFF00 + cpu.c, cpu.a); break;
    case 0xF2: cpu.a = read_byte(0xFF00 + cpu.c); break;
    case 0xEA: write_byte(fetch16(), cpu.a); break;
    case 0xFA: cpu.a = read_byte(fetch16()); break;
    case 0xE9: cpu.pc = cpu.hl; break;
    case 0xF9: cpu.sp = cpu.hl; break;
    case 0xE8: case 0xF8: {
        int8_t e = (int8_t)fetch8();
        uint16_t r = cpu.sp + e;
        cpu.f = 0;
        if (((cpu.sp & 0x0F) + (e & 0x0F)) > 0x0F) cpu.f |= FLAG_H;
        if (((cpu.sp & 0xFF) + (e & 0xFF)) > 0xFF) cpu.f |= FLAG_C;
        if (op == 0xE8) cpu.sp = r; else cpu.hl = r;
        break;
    }
    case 0xF3: ime = 0; ei_pending = 0; break;
    case 0xFB: ei_pending = 1; break;
    default: break;                                               /* illegal opcodes */
    }

    if (was_ei) { ime = 1; if (op != 0xFB) ei_pending = 0; }
    return cycles;
}

/* ---------- init / ROM / save ---------- */
static void init_hw(void) {
    memset(memory, 0, sizeof memory);
    cpu.af = 0x01B0; cpu.bc = 0x0013; cpu.de = 0x00D8; cpu.hl = 0x014D;
    cpu.sp = 0xFFFE; cpu.pc = 0x0100;
    memory[0xFF00] = 0xCF; memory[0xFF0F] = 0x01;
    memory[0xFF40] = 0x91; memory[0xFF41] = 0x00;
    memory[0xFF47] = 0xFC; memory[0xFF48] = 0xFF; memory[0xFF49] = 0xFF;
    memory[0xFFFF] = 0x00;
    ppu_mode = 1;
    for (int i = 0; i < GB_WIDTH * GB_HEIGHT; i++) screen_buffer[i] = colors[0];
}

static int load_rom(const char *filename) {
    FILE *f = fopen(filename, "rb");
    if (!f) { printf("Error: sijaona faili la ROM (%s)\n", filename); return 0; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz < 0x150) { printf("Error: ROM ni ndogo mno\n"); fclose(f); return 0; }
    rom_size = (size_t)sz < 0x8000 ? 0x8000 : (size_t)sz;
    rom = (uint8_t *)calloc(rom_size, 1);
    if (fread(rom, 1, (size_t)sz, f) != (size_t)sz) { printf("Error: imeshindwa kusoma ROM\n"); fclose(f); return 0; }
    fclose(f);

    uint8_t t = rom[0x147];
    if (t >= 1 && t <= 6) mbc_type = 1;
    else if (t >= 0x0F && t <= 0x13) mbc_type = 3;
    else if (t >= 0x19 && t <= 0x1E) mbc_type = 5;
    else mbc_type = 0;

    static const size_t ram_sizes[6] = { 0, 0x800, 0x2000, 0x8000, 0x20000, 0x10000 };
    uint8_t rs = rom[0x149];
    ext_ram_size = (rs < 6) ? ram_sizes[rs] : 0;
    return 1;
}

static void sav_path(char *out, size_t n) { snprintf(out, n, "%s.sav", rom_path); }

static void load_save(void) {
    if (!ext_ram_size) return;
    char p[MAX_PATH + 8]; sav_path(p, sizeof p);
    FILE *f = fopen(p, "rb");
    if (f) { if (fread(ext_ram, 1, ext_ram_size, f)) {} fclose(f); }
}
static void write_save(void) {
    if (!ext_ram_size || mbc_type == 0) return;
    char p[MAX_PATH + 8]; sav_path(p, sizeof p);
    FILE *f = fopen(p, "wb");
    if (f) { fwrite(ext_ram, 1, ext_ram_size, f); fclose(f); }
}

/* ---------- window / input ---------- */
static void draw(HDC hdc) {
    StretchDIBits(hdc, 0, 0, GB_WIDTH * SCALE, GB_HEIGHT * SCALE,
                  0, 0, GB_WIDTH, GB_HEIGHT, screen_buffer, &bmi, DIB_RGB_COLORS, SRCCOPY);
}

static void set_key(WPARAM wp, int down) {
    uint8_t *reg = NULL; int bit = -1;
    switch (wp) {
    case VK_RIGHT:  reg = &joypad_dpad;    bit = 0; break;
    case VK_LEFT:   reg = &joypad_dpad;    bit = 1; break;
    case VK_UP:     reg = &joypad_dpad;    bit = 2; break;
    case VK_DOWN:   reg = &joypad_dpad;    bit = 3; break;
    case 'Z': case 'J': reg = &joypad_buttons; bit = 0; break;
    case 'X': case 'K': reg = &joypad_buttons; bit = 1; break;
    case VK_SPACE: case VK_RSHIFT: reg = &joypad_buttons; bit = 2; break;
    case VK_RETURN: reg = &joypad_buttons; bit = 3; break;
    default: return;
    }
    if (down) {
        if (*reg & (1 << bit)) { *reg &= ~(1 << bit); memory[0xFF0F] |= 0x10; }
    } else *reg |= (1 << bit);
}

LRESULT CALLBACK WndProc(HWND h, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
    case WM_ERASEBKGND: return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; HDC hdc = BeginPaint(h, &ps);
        draw(hdc);
        EndPaint(h, &ps);
        return 0;
    }
    case WM_KEYDOWN: if (!(lp & (1 << 30))) set_key(wp, 1); return 0;
    case WM_KEYUP:   set_key(wp, 0); return 0;
    case WM_KILLFOCUS: joypad_dpad = 0x0F; joypad_buttons = 0x0F; return 0;
    case WM_DESTROY: PostQuitMessage(0); return 0;
    }
    return DefWindowProc(h, msg, wp, lp);
}

int main(int argc, char **argv) {
    if (argc > 1) snprintf(rom_path, sizeof rom_path, "%s", argv[1]);
    if (!load_rom(rom_path)) return 1;
    init_hw();
    load_save();

    memset(&bmi, 0, sizeof bmi);
    bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth = GB_WIDTH;
    bmi.bmiHeader.biHeight = -GB_HEIGHT;
    bmi.bmiHeader.biPlanes = 1;
    bmi.bmiHeader.biBitCount = 32;
    bmi.bmiHeader.biCompression = BI_RGB;

    WNDCLASS wc = {0};
    wc.lpfnWndProc = WndProc;
    wc.hInstance = GetModuleHandle(NULL);
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.lpszClassName = "GBEmuWindow";
    RegisterClass(&wc);

    char title[64] = "Game Boy";
    {
        char t[17]; memcpy(t, &rom[0x134], 16); t[16] = 0;
        for (int i = 0; i < 16; i++) if ((unsigned char)t[i] < 32 || (unsigned char)t[i] > 126) t[i] = 0;
        if (t[0]) snprintf(title, sizeof title, "Game Boy - %s", t);
    }

    DWORD style = (WS_OVERLAPPEDWINDOW & ~WS_THICKFRAME & ~WS_MAXIMIZEBOX) | WS_VISIBLE;
    RECT r = {0, 0, GB_WIDTH * SCALE, GB_HEIGHT * SCALE};
    AdjustWindowRect(&r, style, FALSE);
    hwnd = CreateWindow("GBEmuWindow", title, style, CW_USEDEFAULT, CW_USEDEFAULT,
                        r.right - r.left, r.bottom - r.top, NULL, NULL, wc.hInstance, NULL);

    /* timer resolution ya 1ms bila kulink winmm */
    HMODULE winmm = LoadLibraryA("winmm.dll");
    if (winmm) {
        typedef UINT (WINAPI *TBP)(UINT);
        TBP tbp = (TBP)GetProcAddress(winmm, "timeBeginPeriod");
        if (tbp) tbp(1);
    }

    LARGE_INTEGER freq, now;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&now);
    double frame_ticks = (double)freq.QuadPart * (CYCLES_PER_FRAME / CPU_HZ);
    double next = (double)now.QuadPart + frame_ticks;
    int frame_acc = 0;
    MSG msg;

    while (running) {
        int c = cpu_step();
        timer_step(c);
        ppu_step(c);
        frame_acc += c;

        int lcd_on = memory[0xFF40] & 0x80;
        if (frame_ready || (!lcd_on && frame_acc >= CYCLES_PER_FRAME)) {
            frame_ready = 0; frame_acc = 0;

            while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE)) {
                if (msg.message == WM_QUIT) running = 0;
                TranslateMessage(&msg);
                DispatchMessage(&msg);
            }
            HDC hdc = GetDC(hwnd);
            draw(hdc);
            ReleaseDC(hwnd, hdc);

            for (;;) {
                QueryPerformanceCounter(&now);
                double remaining = next - (double)now.QuadPart;
                if (remaining <= 0) break;
                if (remaining > freq.QuadPart / 500.0) Sleep(1);
            }
            next += frame_ticks;
            QueryPerformanceCounter(&now);
            if ((double)now.QuadPart > next + frame_ticks * 5) next = (double)now.QuadPart + frame_ticks;
        }
    }

    write_save();
    free(rom);
    return 0;
}
