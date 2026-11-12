module

public import Silmaril.Wasm.Resource.Table.Defs
public import Silmaril.Wasm.Resource.Component.Defs
public import Silmaril.Wasm.Spec.Component.Ref.Defs

@[expose] public section

/-!
# The resource built-ins of the reference machine and their handle tables

`Silmaril.Wasm.Resource.Table` reads successful histories of a component handle table
(`Table.Steps`) as handle events. This file connects them to the **programs** of the reference
machine that operate on the tables: the table-manipulating cores of the canonical built-ins
(`Canon.resourceNewCore`, `Canon.resourceRepCore`, `Canon.resourceDropCore`, REF
`canon_resource_new/rep/drop` after the `may_leave` check and before the destructor call).

* `StoreH`: the store-only handler of the specification programs `Canon.P E σ`: `get` answers
  the current store, `modify f` applies `f`; every other operation (traps, calls, choices,
  threads, host state) has no successful answer. `Prog.Eval StoreH p s a s'` is a successful
  run of `p` from store `s` returning `a` in store `s'`, exactly as the machine rules `Step.get`
  and `Step.modify` execute it (`Silmaril.Proofs.Wasm.Resource.CompTable.Machine`).
  `StoreProg p`: every operation `p` can issue is `get`, `modify` or `trap` (the three cores
  are such programs).
* `handles? s j`: the handle table of component instance `j` in store `s`.
* `TabSteps s s' j evs`: the handle table of instance `j` goes from its value in `s` to its value
  in `s'` through the successful table history `evs` (or `j` is not an instance of `s`).
* `ResCall`: a call of one of the three cores on a given instance; `ResCall.prog` runs it
  (`resource.drop`'s destructor request is discarded: the destructor call itself is a
  cross-component call, outside the store-only fragment); `resScript` runs a list of calls in
  order.
* `ResCall.hev c n`: the handle event of a call `c` with result `n` (the index returned by
  `resource.new`, the index operated on by `rep`/`drop`): `alloc n`, `use i`, `free i`.
* `instEvs j cs ns`: the handle events of the calls on instance `j`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-- The store-only handler: `get` and `modify` act on the component store; no other operation
succeeds. -/
def StoreH : (o : (Eff E σ).Op) → CStore E → (Eff E σ).Resp o → CStore E → Prop :=
  fun o => match (o : Op E σ) with
  | .get => fun s r s' => r = s ∧ s' = s
  | .modify f => fun s _ s' => s' = f s
  | _ => fun _ _ _ => False

/-- The operations of the store-only fragment: `get`, `modify` and `trap`. -/
def IsStoreOp : (Eff E σ).Op → Prop :=
  fun o => match (o : Op E σ) with
  | .get | .modify _ | .trap _ => True
  | _ => False

/-- A program of the store-only fragment: every operation it can issue is `get`, `modify` or
`trap`. -/
abbrev StoreProg {α : Type} (p : P E σ α) : Prop := Prog.Every (S := Eff E σ) IsStoreOp p

/-- A successful store-only run of a specification program. -/
abbrev SRun {α : Type} (p : P E σ α) (s : CStore E) (a : α) (s' : CStore E) : Prop :=
  Prog.Eval (S := Eff E σ) StoreH p s a s'

/-- The handle table of instance `j`. -/
def handles? (s : CStore E) (j : InstId) : Option (Silmaril.Wasm.Component.Runtime.Table HandleEntry) :=
  (s.inst? j).map (·.handles)

/-- The table of instance `j` evolves from `s` to `s'` through the successful history `evs`. -/
def TabSteps (s s' : CStore E) (j : InstId) (evs : List (Silmaril.Wasm.Component.Runtime.Table.Event HandleEntry)) : Prop :=
  ∀ t, handles? s j = some t → ∃ t', handles? s' j = some t' ∧ Silmaril.Wasm.Component.Runtime.Table.Steps t evs t'

/-- A call of a resource built-in core on instance `inst` at resource type `rt`. -/
inductive ResCall where
  /-- `resource.new rt rep`. -/
  | new (inst : InstId) (rt : RtId) (rep : ℕ)
  /-- `resource.rep rt i`. -/
  | rep (inst : InstId) (rt : RtId) (i : ℕ)
  /-- `resource.drop rt i`, up to the destructor call. -/
  | drop (inst : InstId) (rt : RtId) (i : ℕ)

/-- The instance a call operates on. -/
def ResCall.inst : ResCall → InstId
  | .new inst _ _ | .rep inst _ _ | .drop inst _ _ => inst

/-- The program of a call: the core of the built-in. `new` returns the new index, `rep` the
representation, `drop` returns `0` (its destructor request is discarded). -/
def ResCall.prog (lim : Silmaril.Wasm.Component.Limits) : ResCall → P E σ ℕ
  | .new inst rt v => resourceNewCore lim inst rt v
  | .rep inst rt i => resourceRepCore lim inst rt i
  | .drop inst rt i => do let _ ← resourceDropCore lim inst rt i; pure 0

/-- Run calls in order, collecting their results. -/
def resScript (lim : Silmaril.Wasm.Component.Limits) (cs : List ResCall) : P E σ (List ℕ) :=
  Prog.mapM (ResCall.prog lim) cs

/-- The handle event of call `c` with result `n`. -/
def ResCall.hev : ResCall → ℕ → HEv ℕ
  | .new _ _ _, n => .alloc n
  | .rep _ _ i, _ => .use i
  | .drop _ _ i, _ => .free i

/-- The handle events of the calls on instance `j`, with their results. -/
def instEvs (j : InstId) (cs : List ResCall) (ns : List ℕ) : List (HEv ℕ) :=
  ((cs.zip ns).filter fun p => decide (p.1.inst = j)).map fun p => p.1.hev p.2

end Silmaril.Wasm.Resource
