// Stack VM for make.fun's tiny stack ISA; follows the reference VM exactly (traps, limits, exit codes).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode tables: immediate bytes (-1 = not an opcode), popped, pushed.
const IM = new Int8Array(256).fill(-1);
const PO = new Int8Array(256);
const PU = new Int8Array(256);
function def(op: number, imm: number, pops: number, pushes: number): void {
  IM[op] = imm;
  PO[op] = pops;
  PU[op] = pushes;
}
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
for (let o = 0x10; o <= 0x22; o++) {
  if (o !== 0x17 && o !== 0x1b && o !== 0x1f) def(o, 0, 2, 1); // the binary operators
}
def(0x17, 0, 1, 1); // NEG
def(0x1b, 0, 1, 1); // NOT
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

const enc = new TextEncoder();

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ip = 0;
  let pc = 0;
  let steps = 0;
  const done = (code: number): { out: Uint8Array; code: number } => ({ out: out.slice(0, olen), code });
  for (;;) {
    // One step, in the reference's order: step limit, pc bounds, opcode, immediate fit, stack needs, effect.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    const imm = IM[op];
    if (imm < 0) return done(5);
    if (pc + imm >= n) return done(9);
    steps++;
    if (sp < PO[op]) return done(2);
    if (sp - PO[op] + PU[op] > 256) return done(3);
    const next = pc + 1 + imm;
    pc = next;
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = D[sp - 1];
      const a = D[sp - 2];
      let r: number;
      switch (op) {
        case 0x10: r = (a + b) | 0; break;
        case 0x11: r = (a - b) | 0; break;
        case 0x12: r = Math.imul(a, b); break;
        case 0x13:
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
          break;
        case 0x14:
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0;
          break;
        case 0x15:
          if (b === 0) return done(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
          break;
        case 0x16:
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
          break;
        case 0x18: r = a & b; break;
        case 0x19: r = a | b; break;
        case 0x1a: r = a ^ b; break;
        case 0x1c: r = a << (b & 31); break;
        case 0x1d: r = a >> (b & 31); break;
        case 0x1e: r = (a >>> (b & 31)) | 0; break;
        case 0x20: r = a === b ? 1 : 0; break;
        case 0x21: r = a < b ? 1 : 0; break;
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // 0x22 LTU
      }
      sp -= 2;
      D[sp++] = r;
      continue;
    }
    switch (op) {
      case 0x00: // HALT
        return done(0);
      case 0x01: // PUSH8, sign-extended
        D[sp++] = (p[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian
        D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24);
        break;
      case 0x03: // POP
        sp--;
        break;
      case 0x04: // DUP
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT ( a b c -- b c a )
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 0x17: // NEG
        D[sp - 1] = (-D[sp - 1]) | 0;
        break;
      case 0x1b: // NOT
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x30: // JMP
      case 0x31: // JZ
      case 0x32: { // JNZ
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, to the unsigned immediate
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE ( v addr -- )
        const addr = D[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        sp -= 2;
        M[addr] = D[sp];
        break;
      }
      case 0x50: { // PRINT, decimal ASCII; a write past the limit traps and writes nothing
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > 65536) return done(11);
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN, -1 once the input is used up
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53: // EXIT, low byte of the value
        return done(D[sp - 1] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let inp: Uint8Array;
  try {
    inp = new Uint8Array(readFileSync(join(I, id, 'input.bin')));
  } catch {
    inp = new Uint8Array(0);
  }
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
