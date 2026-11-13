module

public import Silmaril.Wasm.Det.Core.Defs
public import Silmaril.Wasm.Verify.Guard.Defs

/-!
# Subset 2: no floats, memory allowed, allocation failure always traps

A syntactic subset of Wasm 3.0 on which Core 3.0 is **deterministic modulo traps and imports**
(`Silmaril.Wasm.Det.Core.DetCfg`) at **every** profile `P`, although `P` may let every
`memory.grow` fail (`Profile.spec`: `grow := .nondet`).

## The source subset

* `flatOk`: the flat instructions of the subset: integer numerics (`intConst`, `intUnOp`,
  `intBinOp`, `intTestOp`, `intRelOp`), locals, globals, `nop`/`unreachable`/`drop`/`select`,
  branches, direct `call`, `return`, `throw_ref`, the integer memory instructions (`intLoad`,
  `intStore`, `memory.size`, `memory.grow`, `memory.fill`, `memory.copy`, `memory.init`,
  `data.drop`), and constants of every numeric and vector type (values are inert). Excluded:
  every float and vector **operation** (including float/vector loads and stores and
  conversions), tables (and `table.grow`), references, GC aggregates, exceptions handlers
  (`try_table`), `throw`, tail calls and `call_ref`/`call_indirect`;
* `instrOk`, `seqOk` (structural, kernel-reducible): every instruction is in the subset,
  recursively through `block`/`loop`/`if`, and **every `memory.grow` is immediately followed,
  in its instruction sequence, by a trap-on-failure guard** (`guardB`):

  ```wat
  memory.grow x  (local.tee k)?  t.const -1  t.eq  if bt  unreachable … else … end
  ```

  i.e. an optional `local.tee`, then `t.const c` with `c` all ones, `t.eq` at the same integer
  type `t`, and an `if` whose `then` branch starts with `unreachable`.

A failing `memory.grow` pushes `-1` (all ones at the operand's address type). If that type is
`t`, the guard compares `-1` with `-1`, takes the `then` branch and traps; if it is not `t`, the
comparison is stuck. Either way the run never reaches a non-trapping stop.

## Runtime invariant

* `GrowSeq code K`: every `memory.grow` of `code` is followed, in `code ++ K`, by a guard
  (`guardA`); `K` is the rest of the enclosing sequence;
* `PairSeq G p code`: every `CALL_REF dt` administrative instruction of `code` (left by a direct
  `call`) is preceded by `REF.FUNC_ADDR a` with `G a`, or by a trap or `throw_ref` (`EndOk`);
* `GA G fs`/`GAs G fs`: administrative instructions in the subset, every `call` resolving
  through `fs` (the function addresses of the current frame's module) into `G`, label bodies and
  frame bodies with the two sequence conditions (frames switch `fs` to their own module);
* `FuncsOk G F`: every Wasm function of `F` in `G` has a `seqOk` body whose calls resolve into
  `G` (host functions are imports: anything);
* `Inv G c`: the four together for a configuration.

## Executable check

`funcOkB`, `checkG F G` (every function of the list `G` passes), `reachOf F a` (the functions
reachable from `a` by direct calls, `|F| + 1` rounds) and `check s a` (the function `a` with
its reachable set passes). Soundness depends only on `checkG`.

New definitions; the call-index function `Silmaril.Wasm.Verify.instrCalls` is reused.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.GrowTrap

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Verify (instrCalls exprCalls)

/-! ## Source level -/

/-- The flat instructions of the subset (`memory.grow` included; its guard is checked by
`seqOk`). -/
def flatOk : Instr → Bool
  | .nop | .unreachable | .drop | .select _ | .br _ | .brIf _ | .brTable _ _ | .call _
  | .return_ | .throwRef | .localGet _ | .localSet _ | .localTee _ | .globalGet _
  | .globalSet _ | .intConst _ _ | .floatConst _ _ | .vecConst _ | .intUnOp _ _
  | .intBinOp _ _ | .intTestOp _ _ | .intRelOp _ _ | .intLoad _ _ _ _ | .intStore _ _ _ _
  | .memorySize _ | .memoryGrow _ | .memoryFill _ | .memoryCopy _ _ | .memoryInit _ _
  | .dataDrop _ => true
  | _ => false

/-- `memory.grow`. -/
def isGrow : Instr → Bool
  | .memoryGrow _ => true
  | _ => false

/-- The guard after the optional `local.tee`: `t.const -1; t.eq; if bt (unreachable …) …`. -/
def guardRestB : List Instr → Bool
  | .intConst t c :: .intRelOp t' .eq :: .if_ _ (.unreachable :: _) _ :: _ =>
    t == t' && c == BitVec.allOnes _
  | _ => false

/-- A `local.tee` followed by the guard. -/
def teeGuardB : List Instr → Bool
  | .localTee _ :: l => guardRestB l
  | _ => false

/-- **The trap-on-failure guard** that must follow every `memory.grow`. -/
def guardB (l : List Instr) : Bool := guardRestB l || teeGuardB l

mutual
/-- An instruction of the subset, recursively. -/
def instrOk : Instr → Bool
  | .block _ b | .loop _ b => seqOk b
  | .if_ _ b₁ b₂ => seqOk b₁ && seqOk b₂
  | i => flatOk i

/-- A sequence of the subset: every instruction is in the subset, and every `memory.grow` is
immediately followed by a guard. -/
def seqOk : List Instr → Bool
  | [] => true
  | i :: is => instrOk i && (!isGrow i || guardB is) && seqOk is
end

/-- Every function index named by `i` (`call`, recursively) resolves through `fs` into `G`. -/
def CallsIn (G : Nat → Prop) (fs : List Nat) (i : Instr) : Prop :=
  ∀ x ∈ instrCalls i, ∀ a, fs[x]? = some a → G a

/-! ## Runtime level -/

/-- `memory.grow` in administrative code. -/
def isGrowA : Admin → Bool
  | .plain (.memoryGrow _) => true
  | _ => false

/-- `CALL_REF dt` with a runtime type (what a direct `call` leaves). -/
def isCRT : Admin → Bool
  | .callRefType _ => true
  | _ => false

/-- The guard after the optional `local.tee`, in administrative code. -/
def guardRestA : List Admin → Bool
  | .plain (.intConst t c) :: .plain (.intRelOp t' .eq) :: .plain (.if_ _ (.unreachable :: _) _)
      :: _ => t == t' && c == BitVec.allOnes _
  | _ => false

/-- A `local.tee` followed by the guard, in administrative code. -/
def teeGuardA : List Admin → Bool
  | .plain (.localTee _) :: l => guardRestA l
  | _ => false

/-- The trap-on-failure guard, in administrative code. -/
def guardA (l : List Admin) : Bool := guardRestA l || teeGuardA l

/-- Every `memory.grow` of the sequence is followed, in `code ++ K`, by a guard. -/
def GrowSeq : List Admin → List Admin → Prop
  | [], _ => True
  | x :: l, K => (isGrowA x = true → guardA (l ++ K) = true) ∧ GrowSeq l K

/-- What may precede `CALL_REF dt`: a function reference into `G`, a trap or `throw_ref`. -/
def EndOk (G : Nat → Prop) : Admin → Prop
  | .ref (.func a) => G a
  | .trap => True
  | .plain .throwRef => True
  | _ => False

/-- Every `CALL_REF dt` of the sequence is preceded (the first element by `p`) by an `EndOk`
element. -/
def PairSeq (G : Nat → Prop) : Option Admin → List Admin → Prop
  | _, [] => True
  | p, x :: l => (isCRT x = true → ∃ y, p = some y ∧ EndOk G y) ∧ PairSeq G (some x) l

mutual
/-- Administrative instructions of the subset; `fs` is the function list of the current frame's
module. -/
def GA (G : Nat → Prop) (fs : List Nat) : Admin → Prop
  | .plain i => instrOk i = true ∧ CallsIn G fs i
  | .label _ cont body => seqOk cont = true ∧ (∀ i ∈ cont, CallsIn G fs i) ∧ GAs G fs body ∧
      GrowSeq body [] ∧ PairSeq G none body
  | .frame _ fr body => GAs G fr.module.funcs body ∧ GrowSeq body [] ∧ PairSeq G none body
  | .handler _ _ _ => False
  | .returnCallRefType _ => False
  | .ref _ | .callRefType _ | .trap => True

/-- `GA` on a sequence. -/
def GAs (G : Nat → Prop) (fs : List Nat) : List Admin → Prop
  | [] => True
  | a :: as => GA G fs a ∧ GAs G fs as
end

/-- Every Wasm function of `F` in `G` has a body of the subset whose calls resolve into `G`. -/
def FuncsOk (G : Nat → Prop) (F : List (FuncInst Nat)) : Prop :=
  ∀ a fi fn, G a → F[a]? = some fi → fi.code = .wasm fn →
    seqOk fn.body = true ∧ ∀ i ∈ fn.body, CallsIn G fi.module.funcs i

/-- **The runtime invariant** of the subset. -/
def Inv (G : Nat → Prop) (c : Config Nat) : Prop :=
  GAs G c.frame.module.funcs c.code ∧ GrowSeq c.code [] ∧ PairSeq G none c.code ∧
    FuncsOk G c.store.funcs

/-! ## The executable check -/

/-- The function at `b` passes: a host function, or a Wasm function with a `seqOk` body whose
calls resolve into the list `G`. -/
def funcOkB (F : List (FuncInst Nat)) (G : List Nat) (b : Nat) : Bool :=
  match F[b]? with
  | some fi =>
    match fi.code with
    | .wasm fn => seqOk fn.body && (exprCalls fn.body).all fun x =>
        match fi.module.funcs[x]? with
        | some a => G.contains a
        | none => true
    | .host _ => true
  | none => true

/-- Every function of the list `G` passes. -/
def checkG (F : List (FuncInst Nat)) (G : List Nat) : Bool := G.all (funcOkB F G)

/-- The direct callees of the function at `b`. -/
def callees (F : List (FuncInst Nat)) (b : Nat) : List Nat :=
  match F[b]? with
  | some fi =>
    match fi.code with
    | .wasm fn => (exprCalls fn.body).filterMap fun x => fi.module.funcs[x]?
    | .host _ => []
  | none => []

/-- One round of the reachability closure. -/
def reachStep (F : List (FuncInst Nat)) (G : List Nat) : List Nat :=
  G ++ ((G.flatMap (callees F)).filter fun b => !G.contains b).eraseDups

/-- The functions reachable from `a` by direct calls (`|F| + 1` rounds). -/
def reachOf (F : List (FuncInst Nat)) (a : Nat) : List Nat :=
  (reachStep F)^[F.length + 1] [a]

/-- **The check** of the function at `a` in `s`: it and the functions it reaches pass. -/
def check (s : Store Nat) (a : Nat) : Bool := checkG s.funcs (reachOf s.funcs a)

end Silmaril.Wasm.Det.GrowTrap
