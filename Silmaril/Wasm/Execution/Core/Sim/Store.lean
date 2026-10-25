module

public import Silmaril.Wasm.Execution.Core.Store

@[expose] public section

/-! # Stores that differ only in function code, and code-parametric hosts

`StoreRel F s t`: two stores agreeing everywhere except in their function
instances, which are related pointwise by `F` and have equal types. This is the
store half of a code-relation simulation (`Sim/Closure.lean`): a transformation
of function bodies leaves every other store component untouched.

A host call receives the whole store, so the host must be *parametric* in
function code: `HostRespects F host` says that every interaction on a store is
matched, with the same result, on any `F`-related store, the returned stores
being `F`-related again. The outcome relation is the shared
`Silmaril.Wasm.Execution.Host.Outcome.Sim (StoreRel F) id`.

`HostParametric host` quantifies over every reflexive `F`. The Binaryen adapter
`Silmaril/Wasm/Binaryen/HostCode.lean` aliases this API;
`CodeStoreRel` is `StoreRel`.

`HostParametric` is satisfiable (a host returning its input store, for instance)
but excludes every host whose result depends on function code, such as a host
that calls back into Wasm. This is a scope limit of the DCE results built on it.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Execution

variable {H : Type}

/-- Stores differing only in related function implementations of equal types. -/
structure StoreRel (F : FuncInst H → FuncInst H → Prop) (s t : Store H) : Prop where
  types : s.funcs.map (FuncInst.type (H := H)) = t.funcs.map (FuncInst.type (H := H))
  other : ({ s with funcs := [] } : Store H) = ({ t with funcs := [] } : Store H)
  funcs : List.Forall₂ F s.funcs t.funcs

/-- A reflexive function relation relates every store to itself. -/
theorem StoreRel.refl {F : FuncInst H → FuncInst H → Prop} (hF : ∀ f, F f f) (s : Store H) :
    StoreRel F s s := by
  refine ⟨rfl, rfl, ?_⟩
  induction s.funcs with
  | nil => exact .nil
  | cons f fs ih => exact .cons (hF f) ih

/-- `StoreRel` is monotone in the function relation. -/
theorem StoreRel.mono {F G : FuncInst H → FuncInst H → Prop} (hFG : ∀ f g, F f g → G f g)
    {s t : Store H} (h : StoreRel F s t) : StoreRel G s t :=
  ⟨h.types, h.other, h.funcs.imp hFG⟩

/-- `StoreRel` of the converse relation is the converse. -/
theorem StoreRel.symm {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : StoreRel F s t) : StoreRel (fun g f => F f g) t s :=
  ⟨h.types.symm, h.other.symm, List.Forall₂.flip (R := fun g f => F f g) h.funcs⟩

/-- Allocating the same exception preserves `StoreRel`. -/
theorem StoreRel.addExn {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : StoreRel F s t) (e : ExnInst) : StoreRel F (s.addExn e) (t.addExn e) := by
  refine ⟨h.types, ?_, h.funcs⟩
  have := congrArg Store.exns h.other
  simp only at this
  have ho := h.other
  cases s; cases t
  simp_all [Store.addExn]

/-- Related stores have the same exceptions. -/
theorem StoreRel.exns_eq {F : FuncInst H → FuncInst H → Prop} {s t : Store H}
    (h : StoreRel F s t) : s.exns = t.exns := by
  simpa using congrArg Store.exns h.other

/-- Host outcomes related by `F`: the same result, with `F`-related returned
stores; divergence matches divergence. -/
abbrev OutcomeRel (F : FuncInst H → FuncInst H → Prop) : HostOutcome H → HostOutcome H → Prop :=
  Host.Outcome.Sim (StoreRel F) id

/-- A host respects the function relation `F`: every interaction on a store is
matched, with an `OutcomeRel F`-related outcome, on any `F`-related store. -/
def HostRespects (F : FuncInst H → FuncInst H → Prop) (host : HostSemantics H) : Prop :=
  ∀ h s t vs out, StoreRel F s t → host h s vs out →
    ∃ out', host h t vs out' ∧ OutcomeRel F out out'

/-- A host is parametric in function implementations: it respects every reflexive
function relation. (The sketch's `HostCodeParametric`.) -/
def HostParametric (host : HostSemantics H) : Prop :=
  ∀ F : FuncInst H → FuncInst H → Prop, (∀ f, F f f) → HostRespects F host

theorem HostParametric.respects {host : HostSemantics H} (hh : HostParametric host)
    {F : FuncInst H → FuncInst H → Prop} (hF : ∀ f, F f f) : HostRespects F host :=
  hh F hF

/-- `StoreRel` for equality is equality. -/
theorem StoreRel.eq {s t : Store H} (h : StoreRel (· = ·) s t) : s = t := by
  have hf : s.funcs = t.funcs := List.forall₂_eq_eq_eq ▸ h.funcs
  have ho := h.other
  cases s; cases t
  simp_all

/-- Every host respects equality of function instances: related stores are equal. -/
theorem hostRespects_eq (host : HostSemantics H) : HostRespects (· = ·) host := by
  intro h s t vs out hst hout
  obtain rfl := hst.eq
  refine ⟨out, hout, ?_⟩
  cases out with
  | diverged => trivial
  | returned s r => exact ⟨StoreRel.refl (fun _ => rfl) s, rfl⟩

end Silmaril.Wasm.Execution.Core.Sim
