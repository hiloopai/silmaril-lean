module

public import Silmaril.Wasm.Instructions
public import Silmaril.Wasm.Numerics.Integer

/-!
# A frame machine for the i32 fragment of Core 3.0 used by the asyncify tool

The verified asyncify pass (`Silmaril.Wasm.FX.Asyncify.Tool`) reads and writes silmaril-lean's Core
3.0 module AST (`Silmaril.Wasm.Module`). Its source and its output are executed here by one small
frame machine over **unchanged Core instructions** (`Silmaril.Wasm.Instr`) on 32-bit words; it is a
reading of the Core reduction rules on the fragment below, not silmaril-lean's `Step` (that the two
agree on the fragment is an open target, see `docs/projects/wasm-binaryen-tooling.md`).

The fragment:

* pure instructions (`pexec`): `nop`, `drop`, `local.get/set/tee`, and the `i32` instructions
  `const`, unary, binary (division traps as in `Numerics.intBinOp`), test and comparison;
* `global.get/set` on a list of `i32` globals;
* `i32.load` and `i32.store` (no packing, memory 0) on a word memory `Nat → W` indexed by the
  effective address `addr + offset` (the memory is unbounded and word-granular: a store writes one
  word at its address; the pass only uses aligned, disjoint word addresses);
* `if` with the empty block type, executed by splicing the chosen arm in front of the remaining code
  (the fragment has no branches, so no label is needed);
* `return` (the top `nres` operands) and falling off the end of a body (the whole operand stack);
* `call f`: for an import (`f < E.imps.length`) the machine stops with `ask f args`; a defined
  function gets a new frame whose locals are the arguments followed by zeros.

Operand stacks are lists, top first. Everything else traps.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

/-- Machine words. -/
abbrev W := BitVec 32

/-- One pure instruction on locals and operands (top first); `none` is a trap. -/
def pexec : Instr → List W → List W → Option (List W × List W)
  | .nop, ls, ops => some (ls, ops)
  | .drop, ls, _ :: ops => some (ls, ops)
  | .localGet i, ls, ops => (ls[i.value.val]?).map fun v => (ls, v :: ops)
  | .localSet i, ls, v :: ops =>
    if i.value.val < ls.length then some (ls.set i.value.val v, ops) else none
  | .localTee i, ls, v :: ops =>
    if i.value.val < ls.length then some (ls.set i.value.val v, v :: ops) else none
  | .intConst .i32 b, ls, ops => some (ls, b :: ops)
  | .intUnOp .i32 op, ls, x :: ops => some (ls, Numerics.intUnOp .i32 op x :: ops)
  | .intBinOp .i32 op, ls, y :: x :: ops =>
    match Numerics.intBinOp .i32 op x y with
    | .ok r => some (ls, r :: ops)
    | .error _ => none
  | .intTestOp .i32 op, ls, x :: ops => some (ls, Numerics.intTestOp .i32 op x :: ops)
  | .intRelOp .i32 op, ls, y :: x :: ops => some (ls, Numerics.intRelOp .i32 op x y :: ops)
  | _, _, _ => none

/-- A defined function: parameter, local and result counts (all `i32`) and its body. -/
structure FnDef where
  nparams : Nat
  nlocals : Nat
  nres : Nat
  body : List Instr

/-- A program: the imports (arity, result count), then the defined functions. The function index
space is that of Core: imports first. -/
structure Env where
  imps : List (Nat × Nat)
  fns : List FnDef

/-- An activation frame. -/
structure Frame where
  /-- The function index (bookkeeping only; `step` does not read it). -/
  fid : Nat
  locals : List W
  ops : List W
  code : List Instr
  nres : Nat

/-- A machine configuration: frames (top first), globals and memory. -/
structure Cfg where
  frames : List Frame
  globals : List W
  mem : Nat → W

/-- The result of one machine step. -/
inductive Res where
  | next (c : Cfg)
  /-- The bottom frame returned these operands (top first). -/
  | done (vs : List W) (c : Cfg)
  | trap
  /-- An import call with its arguments (in parameter order); `c` is the configuration with the
  call consumed, waiting for the results to be pushed on its top frame. -/
  | ask (f : Nat) (args : List W) (c : Cfg)

/-- Replace the top frame. -/
def Cfg.setTop (c : Cfg) (fr : Frame) (rest : List Frame) : Cfg := { c with frames := fr :: rest }

/-- Return `vs` (top first) from the top frame to the frames `rest` below it. -/
def ret (c : Cfg) (vs : List W) : List Frame → Res
  | [] => .done vs { c with frames := [] }
  | caller :: rest => .next { c with frames := { caller with ops := vs ++ caller.ops } :: rest }

/-- The entry frame of defined function `fid` with arguments `args` (parameter order). -/
def entry (fid : Nat) (fn : FnDef) (args : List W) : Frame :=
  ⟨fid, args ++ List.replicate fn.nlocals 0, [], fn.body, fn.nres⟩

/-- Store a word. -/
def upd (m : Nat → W) (a : Nat) (w : W) : Nat → W := fun x => if x = a then w else m x

/-- The state a straight-line instruction acts on. -/
structure LS where
  locals : List W
  ops : List W
  globals : List W
  mem : Nat → W

/-- The control instructions of the fragment. -/
inductive Ctl where
  | call (f : Nat)
  | ret
  | ifE (bt : BlockType) (t e : List Instr)

/-- Classify an instruction as a control instruction. -/
def ctlOf : Instr → Option Ctl
  | .call f => some (.call f.value.val)
  | .return_ => some .ret
  | .if_ bt t e => some (.ifE bt t e)
  | _ => none

/-- One straight-line instruction (globals, memory, pure instructions); `none` is a trap. -/
def segCore (i : Instr) (s : LS) : Option LS :=
  match i with
  | .globalGet g =>
    match s.globals[g.value.val]? with
    | some v => some { s with ops := v :: s.ops }
    | none => none
  | .globalSet g =>
    match s.ops with
    | v :: ops =>
      if g.value.val < s.globals.length then
        some { s with ops := ops, globals := s.globals.set g.value.val v }
      else none
    | [] => none
  | .intLoad .i32 none m arg =>
    match s.ops with
    | a :: ops =>
      if m.value.val = 0 then some { s with ops := s.mem (a.toNat + arg.offset.val) :: ops }
      else none
    | [] => none
  | .intStore .i32 none m arg =>
    match s.ops with
    | v :: a :: ops =>
      if m.value.val = 0 then
        some { s with ops := ops, mem := upd s.mem (a.toNat + arg.offset.val) v }
      else none
    | _ => none
  | i =>
    match pexec i s.locals s.ops with
    | some (ls, ops) => some { s with locals := ls, ops := ops }
    | none => none

/-- A straight-line instruction: `none` for control instructions and traps. -/
def segStep (i : Instr) (s : LS) : Option LS :=
  match ctlOf i with
  | some _ => none
  | none => segCore i s

/-- The straight-line state of the top frame. -/
def Frame.ls (fr : Frame) (c : Cfg) : LS := ⟨fr.locals, fr.ops, c.globals, c.mem⟩

/-- Execute instruction `i` of the top frame `fr` (whose remaining code after `i` is `code`). -/
def exec (E : Env) (c : Cfg) (fr : Frame) (i : Instr) (code : List Instr) (rest : List Frame) :
    Res :=
  match ctlOf i with
  | some (.call f) =>
    if h : f < E.imps.length then
      let n := (E.imps[f]'h).1
      if n ≤ fr.ops.length then
        .ask f (fr.ops.take n).reverse (c.setTop { fr with ops := fr.ops.drop n, code := code } rest)
      else .trap
    else
      match E.fns[f - E.imps.length]? with
      | none => .trap
      | some fn =>
        if fn.nparams ≤ fr.ops.length then
          .next (c.setTop (entry f fn (fr.ops.take fn.nparams).reverse)
            ({ fr with ops := fr.ops.drop fn.nparams, code := code } :: rest))
        else .trap
  | some .ret => ret c (fr.ops.take fr.nres) rest
  | some (.ifE bt t e) =>
    match bt, fr.ops with
    | .empty, x :: ops =>
      .next (c.setTop { fr with ops := ops, code := (if x = 0 then e else t) ++ code } rest)
    | _, _ => .trap
  | none =>
    match segCore i (fr.ls c) with
    | some s => .next ⟨{ fr with locals := s.locals, ops := s.ops, code := code } :: rest,
        s.globals, s.mem⟩
    | none => .trap

/-- One machine step. -/
def step (E : Env) (c : Cfg) : Res :=
  match c.frames with
  | [] => .trap
  | fr :: rest =>
    match fr.code with
    | [] => ret c fr.ops rest
    | i :: code => exec E c fr i code rest

/-- `n` machine steps, each a `next`. -/
inductive Steps (E : Env) : Nat → Cfg → Cfg → Prop where
  | refl (c : Cfg) : Steps E 0 c c
  | cons {n : Nat} {c c₁ c₂ : Cfg} : step E c = .next c₁ → Steps E n c₁ c₂ → Steps E (n + 1) c c₂

end Silmaril.Wasm.FX.Asyncify.Tool
