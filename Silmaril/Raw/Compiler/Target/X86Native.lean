module

public import Silmaril.Machine.X86.Lir.Defs
public import Silmaril.X86.Float.Encoding

/-! # Native floating point on x86-64: Lir with `fop` to scalar SSE2

The verified backend `X86.Backend.compile` rejects Lir's floating-point instruction
`fop` (`X86.Backend.Error.floatOp`): its target model `X86.Ext` has no XMM state. This
emitter is that backend with one more case. Every other instruction, the prologues,
terminators, frames and the stack-limit check are `X86.Backend`'s own chunks
(`instrChunk`, `termChunk`, `prologue`), and its checks (`progErrors` without
`floatOp`) apply unchanged. A `fop op d x y` becomes a short scalar SSE sequence
through `xmm0` and `xmm1`, which no other code uses (`selFop`):

| `op` | code |
| --- | --- |
| `add sub mul div` | `movq xmm0, x; movq xmm1, y; addsd xmm0, xmm1; movq d, xmm0` (`movd`/`addss` for binary32) |
| `cmp f c` | `movq xmm0, x; movq xmm1, y; cmpsd xmm0, xmm1, pred; movq d, xmm0; and d, 1` |
| `ofInt` | `cvtsi2sd xmm0, x` (64-bit source); `movq d, xmm0` |
| `toInt f wide` | `movq xmm0, x; cvttsd2si d, xmm0` (`r64` if `wide`, else `r32`, which zero-extends) |
| `widen` / `narrow` | `movd xmm0, x; cvtss2sd xmm0, xmm0; movq d, xmm0` / `movq …; cvtsd2ss …; movd d, xmm0` |

The predicates are `eq` (EQ_OQ), `neq` (NEQ_UQ), `lt` (LT_OS) and `le` (LE_OS), whose
mask is all ones exactly when `Lir.FCond.predicate` holds. MOVD/MOVQ from an XMM register
zero-extends into the 64-bit register, which is the zero-extended binary32 convention of
`Lir.FFmt.put`.

`codeX86` (`Compile/Target/Backends.lean`) uses this emitter only for a program that
contains a `fop`; every other program is compiled by the verified backend.

## Trusted base

This file is unverified. Its intended theorem is `X86.Backend.compile_correct` for
`compile`, on the machine `X86.Float.Machine` (the integer subset of `X86.Ext` with the
XMM state and the SSE subset of `X86.Float`): the non-`fop` cases are the existing proof
(the chunks and their machine steps are the same), and each `fop` case is the statement
that its sequence leaves `FOp.eval op x y` in `d`, keeps the other allocatable registers,
the stack and the memory, and falls through. The SSE semantics of `X86.Float.Semantics`
computes with the same profile `Lir.floatProfile` (`Profile.x86SSE` under the default
MXCSR), so each case reduces to a lane computation. The default MXCSR is the process's
initial one (crt0 does not change it).
-/

@[expose] public section

namespace Silmaril.Compile.Target.X86Native

open Silmaril.Machine
open Silmaril.X86 (Reg XReg Byte)
open Silmaril.X86.Backend (Assign AInstr Layout Error nslots)

/-- An instruction of the emitter: one of the verified backend's, or a scalar SSE one. -/
inductive NInstr where
  | int (i : AInstr)
  | sse (i : X86.Float.Instr)

/-- The encoded length, independent of the resolved targets. -/
def NInstr.len : NInstr → Nat
  | .int i => i.len
  | .sse i => (X86.Float.encode i).length

def NInstr.encode (L : Layout) (addr : Nat) : NInstr → List Byte
  | .int i => X86.Ext.encode (i.resolve L addr)
  | .sse i => X86.Float.encode i

def lenOf (l : List NInstr) : Nat := (l.map NInstr.len).sum

/-! ## Selection -/

def prec : Lir.FFmt → X86.Float.Precision
  | .f32 => .single
  | .f64 => .double

/-- MOVD for binary32, MOVQ for binary64. -/
def movWidth : Lir.FFmt → X86.Float.IntWidth
  | .f32 => .w32
  | .f64 => .w64

def toX (f : Lir.FFmt) (x : XReg) (r : Reg) : NInstr := .sse (.movToX (movWidth f) x r)

def fromX (f : Lir.FFmt) (r : Reg) (x : XReg) : NInstr := .sse (.movFromX (movWidth f) r x)

def cmpPred : Lir.FCond → X86.Float.CmpPred
  | .eq => .eq
  | .ne => .neq
  | .lt => .lt
  | .le => .le

def selArith (o : X86.Float.ArithOp) (f : Lir.FFmt) (d x y : Reg) : List NInstr :=
  [toX f .xmm0 x, toX f .xmm1 y, .sse (.arith o (prec f) .xmm0 (.reg .xmm1)), fromX f d .xmm0]

/-- The code of `fop op d x y`. -/
def selFop (op : Lir.FOp) (d x y : Reg) : List NInstr :=
  match op with
  | .add f => selArith .add f d x y
  | .sub f => selArith .sub f d x y
  | .mul f => selArith .mul f d x y
  | .div f => selArith .div f d x y
  | .cmp f c =>
    [toX f .xmm0 x, toX f .xmm1 y, .sse (.cmp (prec f) (cmpPred c) .xmm0 (.reg .xmm1)),
      fromX f d .xmm0, .int (.plain (.aluI .q .and (.reg d) 1))]
  | .ofInt f => [.sse (.cvtFromInt (prec f) .w64 .xmm0 (.reg x)), fromX f d .xmm0]
  | .toInt f wide =>
    [toX f .xmm0 x, .sse (.cvtToIntTrunc (prec f) (if wide then .w64 else .w32) d (.reg .xmm0))]
  | .widen => [toX .f32 .xmm0 x, .sse (.cvtPrec .single .xmm0 (.reg .xmm0)), fromX .f64 d .xmm0]
  | .narrow => [toX .f64 .xmm0 x, .sse (.cvtPrec .double .xmm0 (.reg .xmm0)), fromX .f32 d .xmm0]

/-! ## Code generation -/

section Gen

variable {P : Type} (A : Assign P)

def instrChunk (ns : Nat) : Lir.Instr P → List NInstr
  | .fop op d x y => selFop op (A.reg d) (A.reg x) (A.reg y)
  | i => (X86.Backend.instrChunk A ns i).map .int

def blockCode (f : Lir.FuncId) (ns : Nat) (b : Lir.Block P) : List NInstr :=
  b.instrs.flatMap (instrChunk A ns) ++ (X86.Backend.termChunk A f ns b.term).map .int

def funcCode (f : Lir.FuncId) (fn : Lir.Func P) : List NInstr :=
  (X86.Backend.prologue A f fn).map .int ++ (fn.blocks.map (blockCode A f (nslots fn))).flatten

/-- The code of every function, the offset of every function and of every block (from
the start of its function), computed once. -/
def gen (p : Lir.Prog P) : Array (List NInstr) × Array Nat × Array (Array Nat) :=
  let (codes, fo, bo, _) := p.funcs.zipIdx.foldl
    (fun (codes, fo, bo, off) (fn, f) =>
      let pro := (X86.Backend.prologue A f fn).map .int
      let (blocks, offs, end_) := fn.blocks.foldl
        (fun (bs, os, o) b =>
          let c := blockCode A f (nslots fn) b
          (bs.push c, os.push o, o + lenOf c)) ((#[] : Array (List NInstr)), (#[] : Array Nat), lenOf pro)
      (codes.push (pro ++ blocks.toList.flatten), fo.push off, bo.push offs, off + end_))
    ((#[] : Array (List NInstr)), (#[] : Array Nat), (#[] : Array (Array Nat)), 0)
  (codes, fo, bo)

def layoutOf (codeBase : Nat) (fo : Array Nat) (bo : Array (Array Nat)) : Layout where
  func g := codeBase + fo.getD g 0
  block f l := codeBase + fo.getD f 0 + (bo.getD f #[]).getD l 0

/-- Append the encoding of the instructions placed from `addr`. -/
def encodeAll (L : Layout) (out : ByteArray) (addr : Nat) (is : List NInstr) : ByteArray × Nat :=
  is.foldl (fun (out, a) i =>
    ((i.encode L a).foldl (fun out b => out.push b.toNat.toUInt8) out, a + i.len)) (out, addr)

/-- Whether a program contains a floating-point instruction. -/
def hasFop (p : Lir.Prog P) : Bool :=
  p.funcs.any fun fn => fn.blocks.any fun b => b.instrs.any fun
    | .fop .. => true
    | _ => false

/-- Compile a Lir program placed at `codeBase`: its bytes and the offset of each
function. The checks are `X86.Backend.progErrors` except `floatOp`, and the size
limit on the code actually emitted. -/
def compile (p : Lir.Prog P) (codeBase : Nat) :
    Except (List Error) (ByteArray × Array Nat) :=
  let errs := (X86.Backend.progErrors A p).filter fun
    | .floatOp _ | .codeTooLarge => false
    | _ => true
  let (codes, fo, bo) := gen A p
  let size := codes.foldl (fun n c => n + lenOf c) 0
  let errs := errs ++ (if size < 2 ^ 31 then [] else [.codeTooLarge])
  match errs with
  | [] =>
    let L := layoutOf codeBase fo bo
    .ok ((codes.foldl (fun (out, a) c => encodeAll L out a c) (ByteArray.empty, codeBase)).1, fo)
  | errs => .error errs

end Gen

end Silmaril.Compile.Target.X86Native
