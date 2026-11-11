module

public import Silmaril.Wasm.Binaryen.Interp
public import Silmaril.Wasm.Binaryen.NativeProfileBridge
public import Silmaril.Wasm.Logic.Core.Defs

@[expose] public section

/-!
# The native Binaryen interpreter against Core 3.0: fragments

silmaril-lean's native interpreter (`Silmaril.Wasm.Binaryen.run`, its big-step relation
`Eval`, `invokeRun`, `nbeh`) evaluates folded trees on a top-first value stack. Its adequacy
for Core 3.0 small-step execution is open upstream: `Silmaril/Wasm/Binaryen/AdequacyReduce.lean`
reduces it to `FwdSim`, `BwdSim` and `NoDivOfTerm`, none of which is proved there.

**What the interpreter assumes.** It implements integer instructions by silmaril's
`Numerics.intUnOp`/`intBinOp`/`intTestOp`/`intRelOp` (profile-independent), locals, globals,
structured control, `br`/`br_if`/`br_table`/`return`, `select` (ignoring its type annotation),
and direct calls; it does not implement floats, memory, tables, references or `memory.grow`.
Nothing in it depends
on a numeric profile, so adequacy is to be stated for **every** profile `P` and host. It does
not check typing: blocks truncate stacks with `take`, `local.set` out of range is a no-op, so
adequacy needs a typing invariant beyond the straight-line fragment below.

This topic proves adequacy on fragments, as plain Core 3.0 code reduced by unchanged
`Execution.Core.Step P host`:

* `Instr.straight`, `BExpr.straight`, `BExpr.straightList`: **straight-line integer code** —
  trees of `nop`, `drop`, integer constants and unary/test/binary/comparison operators,
  `local.get/set/tee`, `global.get/set` (no control flow, no calls, no `select`);
* `BExpr.setsBelow n`: every `local.set`/`local.tee` index is below `n` (the frame's number of
  locals; validated code satisfies it);
* `NAdmins`: **Core configurations of the native profile** — administrative code built from
  silmaril-lean's native-profile instructions (`Binaryen.instrInNativeProfile`: integer
  numerics, locals, globals, `select`, structured control, branches, direct calls, `return`),
  constants of any value type, references and traps, recursively through labels, handlers and
  frames. Together with `Binaryen.NativeFuncsOk` on the store it is closed under Core steps,
  and on it Core reduction does not depend on the profile;
* `chk`, `StoreChk`: **an arity check** for native trees with structured control, branches,
  `return` and direct calls (`Instr.straight` operators plus `select`, `unreachable`, `br`,
  `br_if`, `br_table`, `return`, `call`), against the functions of a store and a module
  instance: every pop finds enough values, every branch target (every target of a `br_table`,
  `tableOk`) exists and finds its label's arity on the stack, and every block, loop, `if` arm and
  function body falls through with exactly its result arity. It stands in for Core validation,
  which the interpreter does not perform (it truncates with `take`);
* `storeChkB`, `nativeFuncsB` (with `instrNative`): executable forms of `StoreChk` and of
  silmaril-lean's `Binaryen.NativeFuncsOk`, decided by kernel evaluation on concrete stores;
* `FlowMatch`, `Match`: a native outcome and a Core outcome (`Silmaril.Wasm.Logic.Core.Outcome`)
  agree: equal normal results (Core bottom-first, native top-first), the same branch label or
  `return` with the native values on top of the Core ones, or both trap.

Results in `Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Binaryen

/-- The straight-line integer instructions. -/
def Instr.straight : Instr → Bool
  | .nop | .drop | .intConst .. | .intUnOp .. | .intTestOp .. | .intBinOp .. | .intRelOp ..
  | .localGet _ | .localSet _ | .localTee _ | .globalGet _ | .globalSet _ => true
  | _ => false

/-- The index of a local written by an instruction, if any. -/
def Instr.setIdx? : Instr → Option LocalIdx
  | .localSet x | .localTee x => some x
  | _ => none

/-- Every written local of an instruction is below `n`. -/
def Instr.setsBelow (n : Nat) (i : Instr) : Bool :=
  match Instr.setIdx? i with
  | some x => decide (x.toNat < n)
  | none => true

mutual
/-- A straight-line tree. -/
def BExpr.straight (n : Nat) : BExpr → Bool
  | .op i args => Instr.straight i && Instr.setsBelow n i && BExpr.straightList n args
  | _ => false

/-- Straight-line trees. -/
def BExpr.straightList (n : Nat) : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.straight n e && BExpr.straightList n es
end

/-- Plain instructions of native-profile configurations: profile instructions and constants of
every value type (arguments and results need not be integers). -/
def NInstr (i : Instr) : Prop :=
  Binaryen.instrInNativeProfile i ∨ (∃ t b, i = .floatConst t b) ∨ (∃ b, i = .vecConst b)

mutual
/-- Administrative instructions of native-profile configurations. -/
def NAdmin : Execution.Core.Admin → Prop
  | .plain i => NInstr i
  | .label _ cont body => (∀ i ∈ cont, Binaryen.instrInNativeProfile i) ∧ NAdmins body
  | .handler _ _ body => NAdmins body
  | .frame _ _ body => NAdmins body
  | .ref _ | .callRefType _ | .returnCallRefType _ | .trap => True
/-- `NAdmin` on a sequence. -/
def NAdmins : List Execution.Core.Admin → Prop
  | [] => True
  | a :: as => NAdmin a ∧ NAdmins as
end

/-! ## The arity check -/

section Chk

variable {H : Type}

/-- Parameter and result counts of a block type in a module instance (the native `arity`). -/
def blockArity (mi : Execution.Core.ModuleInst) (bt : BlockType) : Option (Nat × Nat) :=
  Binaryen.arity { module := mi } bt

/-- Parameter and result counts of the function `x` of a module instance in a store. -/
def callArity (F : List (Execution.Core.FuncInst H)) (mi : Execution.Core.ModuleInst) (x : FuncIdx) :
    Option (Nat × Nat) :=
  match mi.funcs[x.toNat]? >>= (F[·]?) with
  | some fi => (Validation.DefType.funcType? fi.type).map fun p => (p.1.length, p.2.length)
  | none => none

/-- Pops and pushes of a flat instruction that falls through (`nl` locals). -/
def flatEff (F : List (Execution.Core.FuncInst H)) (mi : Execution.Core.ModuleInst) (nl : Nat) :
    Instr → Option (Nat × Nat)
  | .nop => some (0, 0)
  | .drop => some (1, 0)
  | .intConst .. | .localGet _ | .globalGet _ => some (0, 1)
  | .intUnOp .. | .intTestOp .. => some (1, 1)
  | .intBinOp .. | .intRelOp .. => some (2, 1)
  | .localSet x => if x.toNat < nl then some (1, 0) else none
  | .localTee x => if x.toNat < nl then some (1, 1) else none
  | .globalSet _ => some (1, 0)
  | .select _ => some (3, 1)
  | .call x => callArity F mi x
  | _ => none

/-- Every target of a `br_table` exists and finds its label's arity at height `h` (the height
after popping the index). -/
def tableOk (labels : List Nat) (h : Nat) (ls : List LabelIdx) : Bool :=
  ls.all fun l => match labels[l.toNat]? with
    | some n => decide (n ≤ h)
    | none => false

/-- The arity check of a flat instruction at stack height `h`, under labels of arities
`labels` and a function result arity `ret`: `some (some h')` falls through at height `h'`,
`some none` never falls through, `none` fails. -/
def flatChk (F : List (Execution.Core.FuncInst H)) (mi : Execution.Core.ModuleInst) (nl ret : Nat)
    (labels : List Nat) (h : Nat) : Instr → Option (Option Nat)
  | .unreachable => some none
  | .br l => match labels[l.toNat]? with
    | some n => if n ≤ h then some none else none
    | none => none
  | .brIf l => match labels[l.toNat]? with
    | some n => if n + 1 ≤ h then some (some (h - 1)) else none
    | none => none
  | .brTable ls d => if decide (1 ≤ h) && tableOk labels (h - 1) (d :: ls) then some none else none
  | .return_ => if ret ≤ h then some none else none
  | i => match flatEff F mi nl i with
    | some (p, q) => if p ≤ h then some (some (h - p + q)) else none
    | none => none

/-- A body check result ends at arity `n` (or never falls through). -/
def endsAt : Option (Option Nat) → Nat → Bool
  | some none, _ => true
  | some (some k), n => k == n
  | none, _ => false

mutual
/-- **The arity check** of a sequence of trees from height `h` (`none`: unreachable code,
accepted). -/
def chk (F : List (Execution.Core.FuncInst H)) (mi : Execution.Core.ModuleInst) (nl ret : Nat) (labels : List Nat) :
    Option Nat → List Binaryen.BExpr → Option (Option Nat)
  | none, _ => some none
  | some h, [] => some (some h)
  | some h, e :: es => (chk1 F mi nl ret labels h e).bind fun o => chk F mi nl ret labels o es

/-- The arity check of one tree from height `h`. -/
def chk1 (F : List (Execution.Core.FuncInst H)) (mi : Execution.Core.ModuleInst) (nl ret : Nat) (labels : List Nat)
    (h : Nat) : Binaryen.BExpr → Option (Option Nat)
  | .op i args => (chk F mi nl ret labels (some h) args).bind fun
    | none => some none
    | some h₁ => flatChk F mi nl ret labels h₁ i
  | .block bt body => match blockArity mi bt with
    | some (np, nr) =>
      if decide (np ≤ h) && endsAt (chk F mi nl ret (nr :: labels) (some np) body) nr then
        some (some (h - np + nr))
      else none
    | none => none
  | .loop bt body => match blockArity mi bt with
    | some (np, nr) =>
      if decide (np ≤ h) && endsAt (chk F mi nl ret (np :: labels) (some np) body) nr then
        some (some (h - np + nr))
      else none
    | none => none
  | .if_ bt c t e => (chk F mi nl ret labels (some h) c).bind fun
    | none => some none
    | some h₁ => match blockArity mi bt with
      | some (np, nr) =>
        if decide (np + 1 ≤ h₁) && endsAt (chk F mi nl ret (nr :: labels) (some np) t) nr &&
            endsAt (chk F mi nl ret (nr :: labels) (some np) e) nr then
          some (some (h₁ - 1 - np + nr))
        else none
      | none => none
  | .tryTable .. => none
end

/-- **Every function of the store passes the arity check** in its own module: from the empty
stack, with its parameters and declared locals, its body falls through (or branches to its
own label, or returns) with exactly its results. -/
def StoreChk (F : List (Execution.Core.FuncInst H)) : Prop :=
  ∀ (a : Nat) (fi : Execution.Core.FuncInst H) (fn : Func) (ps rs : List Validation.CValType),
    F[a]? = some fi → fi.code = .wasm fn → Validation.DefType.funcType? fi.type = some (ps, rs) →
    endsAt (chk F fi.module (ps.length + fn.locals.length) rs.length [rs.length] (some 0)
      (Binaryen.liftInstrs fn.body)) rs.length = true

/-- An executable `StoreChk` for one function (host functions and functions without a function
type pass vacuously). -/
def funcChkB (F : List (Execution.Core.FuncInst H)) (fi : Execution.Core.FuncInst H) : Bool :=
  match fi.code, Validation.DefType.funcType? fi.type with
  | .wasm fn, some (ps, rs) =>
    endsAt (chk F fi.module (ps.length + fn.locals.length) rs.length [rs.length] (some 0)
      (Binaryen.liftInstrs fn.body)) rs.length
  | _, _ => true

/-- **An executable `StoreChk`** (`storeChk_of_storeChkB`). -/
def storeChkB (F : List (Execution.Core.FuncInst H)) : Bool := F.all (funcChkB F)

end Chk

/-! ## An executable native-profile check -/

mutual
/-- An executable `Binaryen.instrInNativeProfile`. -/
def instrNative : Instr → Bool
  | .block bt body | .loop bt body => Binaryen.nativeBlockType bt && instrsNative body
  | .if_ bt b₁ b₂ => Binaryen.nativeBlockType bt && instrsNative b₁ && instrsNative b₂
  | i => Binaryen.nativeInstr i

/-- `instrNative` on a sequence. -/
def instrsNative : List Instr → Bool
  | [] => true
  | i :: is => instrNative i && instrsNative is
end

/-- **An executable `Binaryen.NativeFuncsOk`** (`nativeFuncsOk_of_nativeFuncsB`). -/
def nativeFuncsB {H : Type} (F : List (Execution.Core.FuncInst H)) : Bool :=
  F.all fun fi => match fi.code with
    | .wasm fn => instrsNative fn.body
    | .host _ => false

/-! ## Matching outcomes -/

/-- A native flow and a Core outcome agree (Core stacks bottom-first, native top-first; a branch
or `return` may carry extra Core values below the native ones). -/
def FlowMatch : Binaryen.Flow → Logic.Core.Outcome → Prop
  | .normal vs, .normal ws => ws = vs.reverse
  | .brk l vs, .br l' ws => l' = l ∧ ∃ junk, ws = junk ++ vs.reverse
  | .ret vs, .ret ws => ∃ junk, ws = junk ++ vs.reverse
  | .trap, .trap => True
  | _, _ => False

/-- The Core postcondition of a native result. -/
def Match {H : Type} (r : Execution.Core.Store H × Execution.Core.Frame × Binaryen.Flow) :
    Logic.Core.Post H :=
  fun s f o => s = r.1 ∧ f = r.2.1 ∧ FlowMatch r.2.2 o

end Silmaril.Wasm.Interp
