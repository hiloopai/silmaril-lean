module

public import Silmaril.Wasm.Det.Core.Defs

/-!
# Stateless code modulo traps and imports: definitions

A **syntactic subset** of Wasm 3.0 (a predicate on Core 3.0 code, so it embeds into full Wasm
3.0 by definition) whose functions are stateless and deterministic modulo traps and imports at
**every** profile (`Silmaril.Wasm.Det.Stateless.Thms`), and the run-time invariant behind it.

## The subset

`slInstr A R W m i` (`slInstrs` on sequences) accepts, for a function of the module instance
`m`:

* integer constants and integer `unop`/`binop`/`testop`/`relop` (`binop` may trap);
* `nop`, `unreachable`, `drop`, `select`, locals (`local.get`/`set`/`tee`);
* structured control (`block`, `loop`, `if`), `br`, `br_if`, `br_table`, `return`;
* `call x` when the callee address `m.funcs[x]` is in the set `A` (closed by `GoodFuns`; host
  functions, that is imports, may be in `A`);
* `global.get x` when the global's address is in the read set `R`, `global.set x` when it is in
  the write set `W` and in `R` (a written global counts as read: two stores must agree on it for
  the write to be possible in both).

Everything else is rejected: memories, tables, floats and vectors (including their constants),
references, GC aggregates, exceptions (`throw`, `try_table`), `call_ref`, `call_indirect` and
tail calls. With `W` empty and `R` the globals the code reads, steps of such code never change
the store, read only the functions and the globals of `R`, and are the same at every profile.
The **obvious stateless subset** (no memory, no floats, no globals) is `R`, `W` empty.

`slFunc A R W fi`: a host function, or Wasm code in the subset for its own module instance.
`GoodFuns A R W funcs`: every address of `A` holds such a function. This is a closed set of
functions: callers and callees together.

## The run-time invariant

Import answers are arbitrary Core results (`Silmaril.Wasm.Det.Core.Runs`), so the operand stack can
hold any reference after an import call. The only rule that could use one to call a function
outside `A` is `call_ref`, and the `CALL_REF` administrative instruction only ever follows the
`ref.func a` produced by `call x` for `a ∈ A`, or a trap or `throw_ref` that bubbles over it.
`PairedFrom A p code` records exactly this (`Blk A p`: `p` is such a predecessor). `okA`/`okL`
say that the code is in the subset, up to the administrative forms that steps create (values,
`throw_ref`, `CALL_REF dt`, labels, frames, traps), with the source instructions of every frame
body checked against the frame's module. `Inv A R W c` packages the three with `GoodFuns` for
the configuration's store.

## Stores and effects

* `Agree R t s`: the stores have the same functions and the same globals at the addresses of
  `R`.
* `Eff`: the store effect of one step of subset code: none, or `global.set a v`.

## Checkers

`closure s roots` collects the functions reachable by `call` (a bounded fixpoint); `readsOf`
and `writesOf` the global addresses read and written by a list of functions; `checkSet s A R W`
checks `GoodFuns` on a concrete store; `allAddrs s` lists the function addresses. The
Boolean checks of the tactics (`statelessCheck`, `crCheck`, `moduleCheck`, `detCheck`) are
built from these. Soundness only relies on `checkSet`.

New definitions (no source file).
-/

@[expose] public section

namespace Silmaril.Wasm.Det.Stateless

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## The subset -/

mutual
/-- **The stateless subset**: an instruction of a function of the module instance `m`, calling
only functions of `A`, reading only globals of `R`, writing only globals of `W`. -/
def slInstr (A R W : Nat → Bool) (m : ModuleInst) : Instr → Bool
  | .block _ body | .loop _ body => slInstrs A R W m body
  | .if_ _ b₁ b₂ => slInstrs A R W m b₁ && slInstrs A R W m b₂
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .return_
  | .localGet _ | .localSet _ | .localTee _ | .intConst _ _ | .intUnOp _ _ | .intBinOp _ _
  | .intTestOp _ _ | .intRelOp _ _ => true
  | .call x => match m.funcs[x.toNat]? with
    | some a => A a
    | none => false
  | .globalGet x => match m.globals[x.toNat]? with
    | some a => R a
    | none => false
  | .globalSet x => match m.globals[x.toNat]? with
    | some a => W a && R a
    | none => false
  | _ => false

/-- `slInstr` on a sequence. -/
def slInstrs (A R W : Nat → Bool) (m : ModuleInst) : List Instr → Bool
  | [] => true
  | i :: is => slInstr A R W m i && slInstrs A R W m is
end

/-- A function in the subset: a host function (an import), or Wasm code in the subset for its
own module instance. -/
def slFunc {H : Type} (A R W : Nat → Bool) (fi : FuncInst H) : Bool :=
  match fi.code with
  | .wasm fn => slInstrs A R W fi.module fn.body
  | .host _ => true

/-- Every address of `A` holds a function of the subset: a closed set of functions. -/
def GoodFuns {H : Type} (A R W : Nat → Bool) (funcs : List (FuncInst H)) : Prop :=
  ∀ a, A a = true → ∃ fi, funcs[a]? = some fi ∧ slFunc A R W fi = true

/-! ## The run-time invariant -/

/-- Source instructions that only appear in run-time code: non-integer constants (values read
from locals or received from imports) and `throw_ref` (an exception answer). -/
def rtPlain : Instr → Bool
  | .floatConst _ _ | .vecConst _ | .throwRef => true
  | _ => false

/-- The `CALL_REF dt` administrative instruction. -/
def isCRT : Admin → Bool
  | .callRefType _ => true
  | _ => false

/-- A permitted predecessor of a `CALL_REF dt`: the reference of a function of `A`, a trap or a
`throw_ref` (both bubble over it). -/
def Blk (A : Nat → Bool) : Option Admin → Prop
  | some (.ref (.func a)) => A a = true
  | some .trap => True
  | some (.plain .throwRef) => True
  | _ => False

/-- Every `CALL_REF dt` of the sequence has a permitted predecessor; `p` is the element before
the sequence. -/
def PairedFrom (A : Nat → Bool) : Option Admin → List Admin → Prop
  | _, [] => True
  | p, x :: l => (isCRT x = true → Blk A p) ∧ PairedFrom A (some x) l

/-- The last element of `l`, or `p` for the empty sequence. -/
def lastOr (p : Option Admin) (l : List Admin) : Option Admin := l.getLast?.or p

mutual
/-- Run-time code of the subset, for the module instance `m` of its frame. -/
def okA (A R W : Nat → Bool) (m : ModuleInst) : Admin → Prop
  | .plain i => slInstr A R W m i = true ∨ rtPlain i = true
  | .ref _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => False
  | .label _ cont body => slInstrs A R W m cont = true ∧ okL A R W m body ∧ PairedFrom A none body
  | .handler _ _ _ => False
  | .frame _ fr body => okL A R W fr.module body ∧ PairedFrom A none body
  | .trap => True

/-- `okA` on a sequence. -/
def okL (A R W : Nat → Bool) (m : ModuleInst) : List Admin → Prop
  | [] => True
  | x :: l => okA A R W m x ∧ okL A R W m l
end

/-- **The invariant** of a configuration running subset code. -/
def Inv {H : Type} (A R W : Nat → Bool) (c : Config H) : Prop :=
  GoodFuns A R W c.store.funcs ∧ okL A R W c.frame.module c.code ∧ PairedFrom A none c.code

/-! ## Stores and effects -/

/-- Two stores agree for code reading the globals of `R`: the same functions and the same globals
at the addresses of `R`. -/
def Agree {H : Type} (R : Nat → Bool) (t s : Store H) : Prop :=
  t.funcs = s.funcs ∧ ∀ a : Nat, R a = true → t.globals[a]? = s.globals[a]?

/-- The store effect of a step of subset code. -/
inductive Eff where
  /-- The store is unchanged. -/
  | keep
  /-- `global.set` of the value `v` at address `a`. -/
  | set (a : Nat) (v : Val)

/-- Apply an effect to a store. -/
def Eff.app {H : Type} : Eff → Store H → Store H
  | .keep, s => s
  | .set a v, s => s.setGlobal a v

/-- The effect writes only globals of `W`. -/
def Eff.Ok (W : Nat → Bool) : Eff → Prop
  | .keep => True
  | .set a _ => W a = true

/-- The globals outside `W` and the functions of `t` are those of `s`: what runs of code writing
only the globals of `W` keep. -/
def Outside {H : Type} (W : Nat → Bool) (t s : Store H) : Prop :=
  Agree (fun a => !W a) t s

/-! ## Checkers -/

mutual
/-- The function addresses named by `call` in an instruction of a function of `m`. -/
def callsI (m : ModuleInst) : Instr → List Nat
  | .block _ body | .loop _ body => callsL m body
  | .if_ _ b₁ b₂ => callsL m b₁ ++ callsL m b₂
  | .call x => m.funcs[x.toNat]?.toList
  | _ => []

/-- `callsI` on a sequence. -/
def callsL (m : ModuleInst) : List Instr → List Nat
  | [] => []
  | i :: is => callsI m i ++ callsL m is
end

mutual
/-- The global addresses named by `global.get` (`set = false`) or `global.set` (`set = true`) in
an instruction of a function of `m`. -/
def globalsI (set : Bool) (m : ModuleInst) : Instr → List Nat
  | .block _ body | .loop _ body => globalsL set m body
  | .if_ _ b₁ b₂ => globalsL set m b₁ ++ globalsL set m b₂
  | .globalGet x => if set then [] else m.globals[x.toNat]?.toList
  | .globalSet x => if set then m.globals[x.toNat]?.toList else []
  | _ => []

/-- `globalsI` on a sequence. -/
def globalsL (set : Bool) (m : ModuleInst) : List Instr → List Nat
  | [] => []
  | i :: is => globalsI set m i ++ globalsL set m is
end

/-- The callees of the function at `a`. -/
def calleesAt {H : Type} (s : Store H) (a : Nat) : List Nat :=
  match s.funcs[a]? with
  | some fi => match fi.code with
    | .wasm fn => callsL fi.module fn.body
    | .host _ => []
  | none => []

/-- The global addresses read (`set = false`) or written (`set = true`) by the function at `a`. -/
def globalsAt {H : Type} (set : Bool) (s : Store H) (a : Nat) : List Nat :=
  match s.funcs[a]? with
  | some fi => match fi.code with
    | .wasm fn => globalsL set fi.module fn.body
    | .host _ => []
  | none => []

/-- One round of the call closure. -/
def closeStep {H : Type} (s : Store H) (l : List Nat) : List Nat :=
  (l ++ l.flatMap (calleesAt s)).eraseDups

/-- The functions reachable by `call` from `roots` (`|funcs| + 1` rounds). -/
def closure {H : Type} (s : Store H) (roots : List Nat) : List Nat :=
  (closeStep s)^[s.funcs.length + 1] roots

/-- The globals read by the functions of `A`. -/
def readsOf {H : Type} (s : Store H) (A : List Nat) : List Nat := A.flatMap (globalsAt false s)

/-- The globals written by the functions of `A`. -/
def writesOf {H : Type} (s : Store H) (A : List Nat) : List Nat := A.flatMap (globalsAt true s)

/-- Every function address of the store. -/
def allAddrs {H : Type} (s : Store H) : List Nat := List.range s.funcs.length

/-- **The executable check of `GoodFuns`**: every address of `A` holds a function of the subset
for the call set `A`. -/
def checkSet {H : Type} (s : Store H) (A : List Nat) (R W : Nat → Bool) : Bool :=
  A.all fun a => match s.funcs[a]? with
    | some fi => slFunc A.contains R W fi
    | none => false

/-- **Stateless check** of the function at `a`: its call closure is in the subset without global
writes, reading only the globals it names. -/
def statelessCheck {H : Type} (s : Store H) (a : Nat) : Bool :=
  let A := closure s [a]
  A.contains a && checkSet s A (readsOf s A).contains fun _ => false

/-- **Module check**: every function of the store is in the subset (any global reads), writing
only the globals named by `global.set`. -/
def moduleCheck {H : Type} (s : Store H) : Bool :=
  checkSet s (allAddrs s) (fun _ => true) (writesOf s (allAddrs s)).contains

/-- **Stateless check over the call states of a module**: `statelessCheck`, and either the
function reads no global, or every function of the store passes `moduleCheck` and no global the
function reads is written. -/
def crCheck {H : Type} (s : Store H) (a : Nat) : Bool :=
  let A := closure s [a]
  statelessCheck s a && ((readsOf s A).isEmpty || (moduleCheck s &&
    (readsOf s A).all fun g => !(writesOf s (allAddrs s)).contains g))

/-- **Stateless module check**: every function of the store is in the subset, without global
writes. -/
def moduleStatelessCheck {H : Type} (s : Store H) : Bool :=
  checkSet s (allAddrs s) (fun _ => true) fun _ => false

/-- **Determinism check** of the function at `a`: its call closure is in the subset, with any
global reads and writes. -/
def detCheck {H : Type} (s : Store H) (a : Nat) : Bool :=
  let A := closure s [a]
  A.contains a && checkSet s A (fun _ => true) fun _ => true

end Silmaril.Wasm.Det.Stateless
