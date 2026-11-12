module

public import Silmaril.Wasm.Jco.Canon.Defs
public import Silmaril.Wasm.Resource.Table.Defs

/-!
# Resources in the jco toolchain: handle types, handle tables, the canonical ABI

Part (d) of `docs/projects/wasm-components.md`, in the memory-based model of `Silmaril.Wasm.Jco.Basic`.

* `RTy`/`RVal`/`RSig`: the fragment of `Silmaril.Wasm.Jco.Basic` (`PTy`) extended with handle types
  `own<r>` and `borrow<r>` of resource types numbered `r`. The value of a handle type **at the
  component boundary is its representation** `rep : i32`, as in `definitions.py` (`a25fc0b`):
  `lift_own`/`lift_borrow` return `h.rep`, and the caller's `lower_own` makes a handle of its own
  from it. Handle indices never cross the boundary.
* `HEntry`: a handle-table entry (`ResourceHandle` without `own`, `borrow_scope`, `num_lends`:
  in this fragment every entry is an `own` handle with no lends, see below).
* `HTab`: a **handle-table implementation**: the operations `add?`, `get?`, `remove?` (`none` is
  a trap), the state after a successful `get` (`touch`, to record uses), a capacity (`none`:
  unbounded) and a representation invariant. `HTab.Lawful` lists
  the laws the theorems use. `refTab` is the reference machine's table
  (`Silmaril.Wasm.Component.Runtime.Table`, the transcription of `definitions.py` class
  `Table`) with capacity `MAX_LENGTH` and invariant `FreeOK` (of `Silmaril.Wasm.Resource.Table`)
  plus the size bound.
* `RM.onFst`, `RM.ofTab`, `CoreInst.withTab`: a component instance's state is the core instance's
  state together with its handle table; core code only touches the first component.
* `tabNew`, `tabGet`, `tabRemove`; the built-ins `resource.new r`, `resource.rep r`,
  `resource.drop r` on flat values (`builtinNew`, `builtinRep`, `builtinDrop`);
* `canonCallR`: `canon lift` of a function with handle types. `lower_own` adds an entry to the
  instance's table and passes the new handle; `lower_borrow` of a resource type the instance
  implements passes the rep (`cx.inst is t.rt.impl`); `lift_own` of a result removes the handle
  and checks its resource type.

Every resource type of the fragment is **defined by the component itself** (exported
resources; world imports are not in the fragment) and has **no destructor**. So `resource.drop`
of an `own` handle only removes the entry, no handle is ever lent out (no imports), and borrow
handles never enter the table (lowering a borrow into its implementing instance passes the rep).
-/

@[expose] public section

namespace Silmaril.Wasm.Jco.RM

variable {σ τ α : Type}

/-- A computation of the core instance, run in a state with a handle table it does not touch. -/
def onFst (m : RM σ α) : RM (σ × τ) α := fun st o =>
  match o with
  | .ok a st' => m st.1 (.ok a st'.1) ∧ st'.2 = st.2
  | .trap => m st.1 .trap

/-- A deterministic operation on the handle table (`none` traps). -/
def ofTab (f : τ → Option (α × τ)) : RM (σ × τ) α := fun st o =>
  o = match f st.2 with
    | some (a, t') => .ok a (st.1, t')
    | none => .trap

end Silmaril.Wasm.Jco.RM

namespace Silmaril.Wasm.Jco.Res

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy Val)

/-! ## Types and values -/

/-- Resource types are numbered. -/
abbrev RtId := Nat

/-- Parameter and result types: the first fragment plus handle types. -/
inductive RTy where
  | base (t : PTy)
  | own (r : RtId)
  | borrow (r : RtId)
  deriving Repr, Inhabited, DecidableEq

/-- Values at the component boundary: a value of the first fragment, or the rep of a handle. -/
inductive RVal where
  | base (v : PVal)
  | res (rep : BitVec 32)
  deriving Repr, Inhabited

/-- A world function with handle types. -/
structure RSig where
  name : String
  params : List RTy
  result : Option RTy := none
  deriving Repr, Inhabited, DecidableEq

/-- The number of flat core values of a type. -/
def RTy.flatLen : RTy → Nat
  | .base t => t.flat.length
  | .own _ | .borrow _ => 1

/-- The number of `own` parameters. -/
def ownCount : List RTy → Nat
  | [] => 0
  | .own _ :: ts => ownCount ts + 1
  | _ :: ts => ownCount ts

/-- `1` for an `own` result, `0` otherwise. -/
def ownRes : Option RTy → Nat
  | some (.own _) => 1
  | _ => 0

/-! ## Handle tables -/

/-- A handle-table entry: the resource type and the representation. -/
structure HEntry where
  rt : RtId
  rep : BitVec 32
  deriving Repr, Inhabited, DecidableEq

/-- A handle-table implementation. -/
structure HTab where
  /-- Silmaril.Wasm.Component.Runtime.Table states. -/
  T : Type
  /-- `add(e)`: a new index, or a trap. -/
  add? : T → HEntry → Option (Nat × T)
  /-- `get(i)`. -/
  get? : T → Nat → Option HEntry
  /-- The state after a successful `get(i)` (the identity, unless the implementation records
  uses). -/
  touch : T → Nat → T := fun t _ => t
  /-- `remove(i)`: the removed entry, or a trap. -/
  remove? : T → Nat → Option (HEntry × T)
  /-- How many more entries the table can take (`none`: unbounded). -/
  cap : T → Option Nat
  /-- The representation invariant. -/
  Inv : T → Prop

/-- The laws of a handle-table implementation. -/
structure HTab.Lawful (H : HTab) : Prop where
  /-- `add` succeeds while there is room. -/
  add_some : ∀ t e, H.Inv t → H.cap t ≠ some 0 → (H.add? t e).isSome
  /-- `add` returns a fresh index below `2^32`, stores the entry there and nothing else, and uses
  one unit of capacity. -/
  add_spec : ∀ t e i t', H.Inv t → H.add? t e = some (i, t') →
    i < 2 ^ 32 ∧ H.get? t i = none ∧ H.get? t' i = some e ∧
      (∀ j, j ≠ i → H.get? t' j = H.get? t j) ∧ H.Inv t' ∧ H.cap t' = (H.cap t).map (· - 1)
  /-- `remove` succeeds on a live index. -/
  remove_some : ∀ t i e, H.get? t i = some e → ∃ t', H.remove? t i = some (e, t')
  /-- A recorded use changes no entry and no capacity, and keeps the invariant. -/
  touch_spec : ∀ t i e, H.Inv t → H.get? t i = some e →
    (∀ j, H.get? (H.touch t i) j = H.get? t j) ∧ H.cap (H.touch t i) = H.cap t ∧
      H.Inv (H.touch t i)
  /-- `remove` empties a live index and nothing else, and frees one unit of capacity. -/
  remove_spec : ∀ t i e t', H.Inv t → H.remove? t i = some (e, t') →
    H.get? t i = some e ∧ H.get? t' i = none ∧ (∀ j, j ≠ i → H.get? t' j = H.get? t j) ∧
      H.Inv t' ∧ H.cap t' = (H.cap t).map (· + 1)

/-- The table has room for `n` more entries. -/
def HTab.Room (H : HTab) (t : H.T) (n : Nat) : Prop := ∀ c, H.cap t = some c → n ≤ c

/-- Two table states are interchangeable for later calls: same entries, same capacity, and the
second satisfies the invariant. -/
def HTab.Same (H : HTab) (t t' : H.T) : Prop :=
  H.Inv t' ∧ (∀ j, H.get? t' j = H.get? t j) ∧ H.cap t' = H.cap t

open Silmaril.Wasm.Component.Runtime (Table) in
/-- **The canonical handle tables**: the reference machine's `Table` of `definitions.py`. -/
def refTab : HTab where
  T := Silmaril.Wasm.Component.Runtime.Table HEntry
  add? := Table.add?
  get? := Table.get?
  remove? := Table.remove?
  cap t := some (t.free.length + (Table.maxLength + 1 - t.array.size))
  Inv t := Silmaril.Wasm.Resource.FreeOK t ∧ t.array.size ≤ Table.maxLength + 1

/-! ## Component-instance states -/


/-- The core instance `M` inside a component instance with handle tables `T`. -/
abbrev withTab (M : CoreInst) (T : Type) : CoreInst where
  St := M.St × T
  mem s := M.mem s.1
  setMem s m := (M.setMem s.1 m, s.2)
  call n xs := (M.call n xs).onFst

variable (M : CoreInst) (H : HTab)

/-- `resource.new`'s table operation: add an entry; the handle as an `i32`. -/
def tabNew (e : HEntry) : RM (withTab M H.T).St (BitVec 32) :=
  RM.ofTab fun t => (H.add? t e).map fun p => (BitVec.ofNat 32 p.1, p.2)

/-- Read the entry of a handle. -/
def tabGet (h : BitVec 32) : RM (withTab M H.T).St HEntry :=
  RM.ofTab fun t => (H.get? t h.toNat).map fun e => (e, H.touch t h.toNat)

/-- Remove the entry of a handle. -/
def tabRemove (h : BitVec 32) : RM (withTab M H.T).St HEntry :=
  RM.ofTab fun t => H.remove? t h.toNat

/-- `canon resource.new r`: `(rep: i32) -> i32`. -/
def builtinNew (r : RtId) : List Flat → RM (withTab M H.T).St (List Flat)
  | [⟨.int .i32, x⟩] => do
    let h ← tabNew M H ⟨r, x⟩
    pure [Flat.i32 h]
  | _ => RM.fail

/-- `canon resource.rep r`: `(handle: i32) -> i32`; traps on a dead handle or another type. -/
def builtinRep (r : RtId) : List Flat → RM (withTab M H.T).St (List Flat)
  | [⟨.int .i32, h⟩] => do
    let e ← tabGet M H h
    RM.check (e.rt == r)
    pure [Flat.i32 e.rep]
  | _ => RM.fail

/-- `canon resource.drop r`: `(handle: i32) -> ()`; no destructor. -/
def builtinDrop (r : RtId) : List Flat → RM (withTab M H.T).St (List Flat)
  | [⟨.int .i32, h⟩] => do
    let e ← tabRemove M H h
    RM.check (e.rt == r)
    pure []
  | _ => RM.fail

/-! ## The canonical ABI with handle types -/

/-- Canonical lowering of one parameter into the instance. -/
def lowerParamR (realloc : List Flat → RM (withTab M H.T).St (List Flat)) :
    RTy → RVal → RM (withTab M H.T).St (List Flat)
  | .base t, .base v => lowerParam (withTab M H.T) realloc t v
  | .own r, .res x => do
    let h ← tabNew M H ⟨r, x⟩
    pure [Flat.i32 h]
  | .borrow _, .res x => pure [Flat.i32 x]
  | _, _ => RM.fail

/-- Canonical lowering of a parameter list. -/
def lowerParamsR (realloc : List Flat → RM (withTab M H.T).St (List Flat)) :
    List RTy → List RVal → RM (withTab M H.T).St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← lowerParamR M H realloc t v
    let b ← lowerParamsR realloc ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- Canonical lifting of a result (a `borrow` result is invalid and traps). -/
def liftResultR : Option RTy → List Flat → RM (withTab M H.T).St (Option RVal)
  | none, xs => do
    let r ← liftResult (withTab M H.T) none xs
    pure (r.map .base)
  | some (.base t), xs => do
    let r ← liftResult (withTab M H.T) (some t) xs
    pure (r.map .base)
  | some (.own r), [x] => do
    let h ← RM.ofOption (asI32? x)
    let e ← tabRemove M H h
    RM.check (e.rt == r)
    pure (some (.res e.rep))
  | _, _ => RM.fail

/-- `canon lift` with handle types: lower, call, lift. -/
def canonCallR (realloc callee : List Flat → RM (withTab M H.T).St (List Flat)) (sig : RSig)
    (vs : List RVal) : RM (withTab M H.T).St (Option RVal) := do
  let xs ← lowerParamsR M H realloc sig.params vs
  let rs ← callee xs
  liftResultR M H sig.result rs

/-! ## Simulation up to the handle table -/

/-- `m`, run from table `t`, has the outcomes of `n` on the core state, with values and final
tables related by `R`. -/
structure Sim {σ τ α β : Type} (m : RM (σ × τ) α) (n : RM σ β) (t : τ)
    (R : α → β → τ → Prop) : Prop where
  fwd : ∀ s a s' t', m (s, t) (.ok a (s', t')) → ∃ b, n s (.ok b s') ∧ R a b t'
  bwd : ∀ s b s', n s (.ok b s') → ∃ a t', m (s, t) (.ok a (s', t')) ∧ R a b t'
  trap : ∀ s, m (s, t) .trap ↔ n s .trap

end Silmaril.Wasm.Jco.Res
