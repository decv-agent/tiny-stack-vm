// A tiny stack virtual machine for make.fun's tiny stack ISA v1 (ISA.md in
// the bounty kit). For every /input/<id>/{program.bin,input.bin} it writes
// /output/<id>/{stdout.bin,exit.txt}: the bytes the program wrote and the
// code it ended with, a trap's code when it traps.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode facts, indexed by opcode byte: immediate length, values popped,
// values pushed, and whether the byte is an opcode at all (else trap 5).
// 00-07 HALT PUSH8 PUSH32 POP DUP SWAP OVER ROT; 10-1E arithmetic and logic
// (17 NEG, 1B NOT unary); 20-22 EQ LT LTU; 30-34 JMP JZ JNZ CALL RET;
// 40-41 LOAD STORE; 50-53 PRINT PUTC IN EXIT.
const IMM = new Int8Array(0x54), POPN = new Int8Array(0x54), PUSHN = new Int8Array(0x54), KNOWN = new Uint8Array(0x54);
IMM[1] = 1; IMM[2] = 4;
for (let o = 0x30; o <= 0x33; o++) IMM[o] = 2;
for (const o of [3, 4, 0x17, 0x1b, 0x31, 0x32, 0x40, 0x50, 0x51, 0x53]) POPN[o] = 1;
for (const o of [5, 6, 0x41]) POPN[o] = 2;
POPN[7] = 3;
for (let o = 0x10; o <= 0x1e; o++) { KNOWN[o] = 1; PUSHN[o] = 1; if (o !== 0x17 && o !== 0x1b) POPN[o] = 2; }
for (const o of [0x20, 0x21, 0x22]) { KNOWN[o] = 1; POPN[o] = 2; PUSHN[o] = 1; }
for (let o = 0; o <= 7; o++) KNOWN[o] = 1;
for (let o = 0x30; o <= 0x34; o++) KNOWN[o] = 1;
KNOWN[0x40] = KNOWN[0x41] = 1;
for (let o = 0x50; o <= 0x53; o++) KNOWN[o] = 1;
PUSHN[1] = PUSHN[2] = PUSHN[0x52] = PUSHN[0x40] = 1;
PUSHN[4] = PUSHN[5] = 2; PUSHN[6] = PUSHN[7] = 3;

// Runs one program to its end; a trap is thrown as its code and caught here,
// so the exit code is the trap's and the output before the trap is kept.
function run(prog, input) {
  const S = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const n = prog.length;
  try {
    for (;;) {
      if (steps === 1000000) throw 10;
      if (pc < 0 || pc >= n) throw 9;
      const op = prog[pc], imm = IMM[op];
      if (op > 0x53 || !KNOWN[op]) throw 5;
      if (imm > 0 && pc + imm >= n) throw 9;
      steps++;
      const next = pc + 1 + imm;
      if (sp < POPN[op]) throw 2;
      if (sp - POPN[op] + PUSHN[op] > 256) throw 3;
      pc = next;
      switch (op) {
        case 0x00: return { out: out.slice(0, olen), code: 0 };
        case 0x01: S[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
        case 0x02: S[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
        case 0x03: sp--; break;
        case 0x04: S[sp] = S[sp - 1]; sp++; break;
        case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
        case 0x06: S[sp] = S[sp - 2]; sp++; break;
        case 0x07: { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
        case 0x17: S[sp - 1] = -S[sp - 1] | 0; break;
        case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
        case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: signed offset from next
          const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
          let take = true;
          if (op !== 0x30) { const v = S[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
          if (take) pc = next + rel;
          break;
        }
        case 0x33: // CALL: unsigned absolute address in the immediate
          if (csp === 64) throw 7;
          C[csp++] = next; pc = prog[next - 2] | (prog[next - 1] << 8); break;
        case 0x34: if (csp === 0) throw 8; pc = C[--csp]; break;
        case 0x40: { const a = S[sp - 1]; if (a < 0 || a > 255) throw 6; S[sp - 1] = M[a]; break; }
        case 0x41: { const a = S[sp - 1]; if (a < 0 || a > 255) throw 6; M[a] = S[sp - 2]; sp -= 2; break; } // STORE ( v addr -- )
        case 0x50: { // PRINT: decimal ASCII; a print past the limit writes nothing
          const s = String(S[sp - 1]);
          if (olen + s.length > 65536) throw 11;
          sp--;
          for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
          break;
        }
        case 0x51: if (olen + 1 > 65536) throw 11; out[olen++] = S[--sp] & 255; break;
        case 0x52: S[sp++] = ip < input.length ? input[ip++] : -1; break; // IN: -1 at/past end
        case 0x53: return { out: out.slice(0, olen), code: S[--sp] & 255 }; // EXIT: low byte
        default: { // binary operators and comparisons
          const b = S[sp - 1], a = S[sp - 2];
          let r;
          switch (op) {
            case 0x10: r = (a + b) | 0; break;
            case 0x11: r = (a - b) | 0; break;
            case 0x12: r = Math.imul(a, b); break;
            case 0x13: if (b === 0) throw 4; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break; // DIV
            case 0x14: if (b === 0) throw 4; r = b === -1 ? 0 : (a % b) | 0; break; // MOD
            case 0x15: if (b === 0) throw 4; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
            case 0x16: if (b === 0) throw 4; r = ((a >>> 0) % (b >>> 0)) | 0; break; // MODU
            case 0x18: r = a & b; break;
            case 0x19: r = a | b; break;
            case 0x1a: r = a ^ b; break;
            case 0x1c: r = a << (b & 31); break;
            case 0x1d: r = a >> (b & 31); break;
            case 0x1e: r = (a >>> (b & 31)) | 0; break;
            case 0x20: r = a === b ? 1 : 0; break;
            case 0x21: r = a < b ? 1 : 0; break;
            default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU
          }
          sp -= 2; S[sp++] = r;
        }
      }
    }
  } catch (e) {
    if (typeof e === 'number') return { out: out.slice(0, olen), code: e };
    throw e;
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(join(I, id, 'program.bin'));
  let input;
  try { input = readFileSync(join(I, id, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
