module

public import Silmaril.Wasm.Jco.Resource.Handle.Defs

/-!
# Full handles: destructors, imported resources, borrow scopes and lends

The fragment of `Silmaril.Wasm.Jco.Resource.Basic` has only `own` entries: every resource type is
defined by the component, none has a destructor, and there are no imports. This module models
the remaining parts of a handle in `definitions.py` (`a25fc0b`; REF line numbers as in
`Silmaril.Raw.Wasm.Component.Canon.Handles`) inside the jco memory-based model:

* `FEntry`: REF `ResourceHandle` (L689): `rt`, `rep`, `own`, and `num_lends` (`lends`). A borrow
  entry's `borrow_scope` is always the current task: calls are synchronous and not reentrant,
  so only one task is live.
* `FSt`: the instance's handle table (`tab`, unbounded, with fresh indices `next`; the
  reference free list is not modelled, see `Silmaril.Wasm.Jco.Resource.Basic` for that) and the
  current task's REF `num_borrows` (`borrows`).
* `RTypes σ`: for each resource type, whether this instance implements it (REF
  `t.rt.impl is cx.inst`; otherwise it is **imported**) and its destructor (REF `rt.dtor`), a
  computation on the rep.
* Built-ins (`fullB R`): `resource.new` (`fNew`), `resource.rep` (`fRep`), and
  `resource.drop` (`fDrop`, REF `canon_resource_drop` L2246-2263). `fDrop` removes the entry,
  traps on another type or on `num_lends ≠ 0`. For an `own` entry it then runs the destructor,
  if any, on the rep. For a borrow entry it decrements `num_borrows`.
* `canon lift` (`canonCallF`): `lower_own` adds an `own` entry. `lower_borrow` (L1740-1746)
  passes the rep for a resource type the instance implements. For an imported one it adds a
  borrow entry and increments `num_borrows`. After the callee, `lift_own` (L1425-1431) removes
  the entry and traps on another type, on `num_lends ≠ 0` or on a borrow entry. Then the
  task's exit check `trap_if(num_borrows > 0)` runs.
* `canon lower` of an imported function (`canonLowerF`). Parameters: `lift_borrow` (L1433-1439)
  reads the handle, checks its type, increments `num_lends` and records the lender. Memory-free
  values are lifted flat. The host function runs on the boundary values, then the lenders are
  released (`num_lends -= 1` each, REF `Subtask.deliver_resolve`). A memory-free or `own` result
  is lowered (an `own` result by `lower_own`). Not covered: `own` parameters of imports, and
  results or parameters in memory.

`Silmaril.Wasm.Jco.Resource.Scope.Thms` proves the borrow-scope theorem, the lend theorem and the
destructor equations.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.Res.Scope

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Res
open Silmaril.Wasm.Component (Flat ValTy Val)

/-! ## Handles and the table -/

/-- REF `ResourceHandle` without the borrow scope (always the current task). -/
structure FEntry where
  rt : RtId
  rep : BitVec 32
  own : Bool
  lends : Nat := 0
  deriving Repr, Inhabited, DecidableEq

/-- The instance's resource state. -/
structure FSt where
  tab : Nat → Option FEntry
  next : Nat
  borrows : Nat

namespace FSt

/-- Add an entry at the next fresh index. -/
def add (s : FSt) (e : FEntry) : Nat × FSt :=
  (s.next, { s with tab := fun j => if j = s.next then some e else s.tab j, next := s.next + 1 })

/-- The table without entry `i`. -/
def removed (s : FSt) (i : Nat) : FSt := { s with tab := fun j => if j = i then none else s.tab j }

/-- Remove a live entry. -/
def remove? (s : FSt) (i : Nat) : Option (FEntry × FSt) :=
  match s.tab i with
  | some e => some (e, s.removed i)
  | none => none

/-- Change the lend count of entry `i` (nothing if it is not live). -/
def modLends (s : FSt) (i : Nat) (f : Nat → Nat) : FSt :=
  { s with tab := fun j => if j = i then (s.tab j).map (fun e => { e with lends := f e.lends })
      else s.tab j }

/-- The number of live borrow entries below `n`. -/
def countB (t : Nat → Option FEntry) : Nat → Nat
  | 0 => 0
  | n + 1 => countB t n + (match t n with | some e => if e.own then 0 else 1 | none => 0)

/-- **The invariant**: no entry at or above `next`, and `num_borrows` counts the live borrow
entries. -/
def Inv (s : FSt) : Prop := (∀ j, s.next ≤ j → s.tab j = none) ∧ s.borrows = countB s.tab s.next

end FSt

/-- The resource types: implemented here or imported, and their destructors. -/
structure RTypes (σ : Type) where
  impl : RtId → Bool
  dtor : RtId → Option (BitVec 32 → RM (σ × FSt) Unit) := fun _ => none

variable {σ : Type} (R : RTypes σ)

/-! ## Table operations and built-ins -/

/-- `lower_own`/`resource.new`: add an `own` entry; the handle (trap beyond `2^32`). -/
def fNew (r : RtId) (rep : BitVec 32) : RM (σ × FSt) (BitVec 32) :=
  RM.ofTab fun s => let p := s.add ⟨r, rep, true, 0⟩
    if p.1 < 2 ^ 32 then some (BitVec.ofNat 32 p.1, p.2) else none

/-- `lower_borrow` of an imported resource: add a borrow entry, `num_borrows += 1`. -/
def fBorrow (r : RtId) (rep : BitVec 32) : RM (σ × FSt) (BitVec 32) :=
  RM.ofTab fun s => let p := s.add ⟨r, rep, false, 0⟩
    if p.1 < 2 ^ 32 then some (BitVec.ofNat 32 p.1, { p.2 with borrows := p.2.borrows + 1 })
    else none

/-- `resource.rep`: read a live entry of type `r`. -/
def fRep (r : RtId) (h : BitVec 32) : RM (σ × FSt) (BitVec 32) :=
  RM.ofTab fun s => match s.tab h.toNat with
    | some e => if e.rt == r then some (e.rep, s) else none
    | none => none

/-- `resource.drop`: remove, check the type and `num_lends == 0`; then the destructor of an `own`
entry, or `num_borrows -= 1` for a borrow entry. -/
def fDrop (r : RtId) (h : BitVec 32) : RM (σ × FSt) Unit := do
  let e ← RM.ofTab fun s => s.remove? h.toNat
  RM.check (e.rt == r)
  RM.check (e.lends == 0)
  if e.own then
    match R.dtor r with
    | some d => d e.rep
    | none => pure ()
  else RM.ofTab fun s => some ((), { s with borrows := s.borrows - 1 })

/-- `lift_own`: remove, check the type, `num_lends == 0` and ownership; the rep. -/
def fTake (r : RtId) (h : BitVec 32) : RM (σ × FSt) (BitVec 32) := do
  let e ← RM.ofTab fun s => s.remove? h.toNat
  RM.check (e.rt == r)
  RM.check (e.lends == 0)
  RM.check e.own
  pure e.rep

/-- `lift_borrow` with the lender recorded: read, check the type, `num_lends += 1`. -/
def fLend (r : RtId) (h : BitVec 32) : RM (σ × FSt) (BitVec 32) := do
  let rep ← fRep r h
  RM.ofTab fun s => some ((), s.modLends h.toNat (· + 1))
  pure rep

/-- Release the lenders: `num_lends -= 1` for each. -/
def fRelease (hs : List Nat) : RM (σ × FSt) Unit :=
  RM.ofTab fun s => some ((), hs.foldl (fun s i => s.modLends i (· - 1)) s)

/-- A built-in on its one `i32` argument. -/
def unary (f : BitVec 32 → RM (σ × FSt) (List Flat)) : List Flat → RM (σ × FSt) (List Flat)
  | [⟨.int .i32, x⟩] => f x
  | _ => RM.fail

/-- **The built-ins** with destructors. -/
def fullB : RBuiltins (σ × FSt) where
  new r := unary fun x => do let h ← fNew r x; pure [Flat.i32 h]
  rep r := unary fun h => do let x ← fRep r h; pure [Flat.i32 x]
  drop r := unary fun h => do fDrop R r h; pure []

/-! ## `canon lift` -/

variable (M : CoreInst)

/-- Lower one parameter into the instance. -/
def lowerParamF (realloc : List Flat → RM (withTab M FSt).St (List Flat)) :
    RTy → RVal → RM (withTab M FSt).St (List Flat)
  | .base t, .base v => lowerParam (withTab M FSt) realloc t v
  | .own r, .res x => do
    let h ← fNew r x
    pure [Flat.i32 h]
  | .borrow r, .res x =>
    if R.impl r then pure [Flat.i32 x] else do
      let h ← fBorrow r x
      pure [Flat.i32 h]
  | _, _ => RM.fail

/-- Lower a parameter list. -/
def lowerParamsF (realloc : List Flat → RM (withTab M FSt).St (List Flat)) :
    List RTy → List RVal → RM (withTab M FSt).St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← lowerParamF R M realloc t v
    let b ← lowerParamsF realloc ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- Lift the result. -/
def liftResultF : Option RTy → List Flat → RM (withTab M FSt).St (Option RVal)
  | none, xs => do
    let r ← liftResult (withTab M FSt) none xs
    pure (r.map .base)
  | some (.base t), xs => do
    let r ← liftResult (withTab M FSt) (some t) xs
    pure (r.map .base)
  | some (.own r), [x] => do
    let h ← RM.ofOption (asI32? x)
    let rep ← fTake r h
    pure (some (.res rep))
  | _, _ => RM.fail

/-- The task's exit check: `trap_if(num_borrows > 0)`. -/
def exitCheck : RM (withTab M FSt).St Unit := fun st o =>
  o = if st.2.borrows = 0 then .ok () st else .trap

/-- **`canon lift` with full handles**: lower, call, lift, exit. -/
def canonCallF (realloc callee : List Flat → RM (withTab M FSt).St (List Flat)) (sig : RSig)
    (vs : List RVal) : RM (withTab M FSt).St (Option RVal) := do
  let xs ← lowerParamsF R M realloc sig.params vs
  let rs ← callee xs
  let r ← liftResultF M sig.result rs
  exitCheck M
  pure r

/-! ## `canon lower` of an imported function -/

/-- Lift the flat arguments of an imported function: memory-free values and borrowed handles
(lent); the lenders. -/
def liftArgsF : List RTy → List Flat → RM (withTab M FSt).St (List RVal × List Nat)
  | [], [] => pure ([], [])
  | .base (.val t) :: ts, xs =>
    match t.lift xs with
    | some (v, rest) => do
      let (vs, ls) ← liftArgsF ts rest
      pure (.base (.val v) :: vs, ls)
    | none => RM.fail
  | .borrow r :: ts, x :: rest => do
    let h ← RM.ofOption (asI32? x)
    let rep ← fLend r h
    let (vs, ls) ← liftArgsF ts rest
    pure (.res rep :: vs, h.toNat :: ls)
  | _, _ => RM.fail

/-- Lower the host's result into the instance: a memory-free value, or an `own` handle. -/
def lowerResF : Option RTy → Option RVal → RM (withTab M FSt).St (List Flat)
  | none, none => pure []
  | some (.base (.val t)), some (.base (.val v)) => do
    RM.check (t.check v)
    pure (t.lower v)
  | some (.own r), some (.res x) => do
    let h ← fNew r x
    pure [Flat.i32 h]
  | _, _ => RM.fail

/-- **`canon lower` with full handles** of the host function `host` at `sig`: lift (lending
borrowed handles), call, release the lenders, lower the result. The host does not reach the
instance's table. -/
def canonLowerF (host : List RVal → RM M.St (Option RVal)) (sig : RSig) (xs : List Flat) :
    RM (withTab M FSt).St (List Flat) := do
  let (vs, ls) ← liftArgsF M sig.params xs
  let r ← (host vs).onFst
  fRelease ls
  lowerResF M sig.result r

end Silmaril.Wasm.Jco.Res.Scope
