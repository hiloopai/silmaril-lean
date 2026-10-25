module

public import Silmaril.Wasm.Binaryen.Equiv
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Store

@[expose] public section

/-! # Code-parametric hosts with related returned stores

`HostRespectsCode` transports an identical outcome, including its store, across
code replacement. Combining that contract with `HostOk` excludes returning
hosts in stores containing Wasm functions. Here the returned stores instead
remain related by the same function relation as the input stores. This is the
host obligation for a future open-code simulation; it does not assert that
local joinability has already been lifted to contextual equivalence.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Validation

-- FLAG(statement-change): `CodeStoreRel`, `CodeOutcomeRel` and `HostCodeParametric` were
-- separate copies of the code-simulation tooling's `Sim.StoreRel`, `Sim.OutcomeRel` and
-- `Sim.HostParametric` (operational simulation development, item 4). They are now aliases: the store relation has the same
-- three fields; the outcome relation lists the store before the (equal) result.
/-- Stores differing only in related function implementations of equal types.
The relation may include identity pairs for functions allocated by a host.
An alias of the tooling's `Sim.StoreRel`. -/
abbrev CodeStoreRel {H : Type} (F : FuncInst H → FuncInst H → Prop) (s t : Store H) : Prop :=
  Sim.StoreRel F s t

/-- Identical stores are related whenever unchanged function implementations
are allowed. This also covers arbitrary stores returned by a code-respecting
host, without assuming that the host preserves typing. -/
theorem CodeStoreRel.refl {H : Type} {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ f, F f f) (s : Store H) : CodeStoreRel F s s :=
  Sim.StoreRel.refl hF s

/-- A host interaction keeps the same result (including reference addresses)
and transports its returned store along the function relation. An alias of
`Sim.OutcomeRel`. -/
abbrev CodeOutcomeRel {H : Type} (F : FuncInst H → FuncInst H → Prop) :
    HostOutcome H → HostOutcome H → Prop :=
  Sim.OutcomeRel F

/-- A host is parametric in function implementations: it must match each
interaction when the store's implementations change. Unlike
`HostRespectsCode`, this does not require the two returned stores to be equal.
An alias of the tooling's `Sim.HostParametric`. -/
abbrev HostCodeParametric {H : Type} (host : HostSemantics H) : Prop :=
  Sim.HostParametric host

/-- The existing identical-interaction contract supplies returned-store
parametricity by choosing the very same outcome. After a return, the stores
coincide and the function relation is reflexive. This is useful for DCE's
untyped structural simulation; Joinable additionally needs host typing. -/
theorem HostRespectsCode.codeParametric {H : Type} {host : HostSemantics H}
    (hh : HostRespectsCode host) : HostCodeParametric host := by
  intro F hF h s t vs out hst hout
  refine ⟨out, hh h s t vs out ⟨hst.types, hst.other⟩ hout, ?_⟩
  cases out with
  | diverged => trivial
  | returned s r => exact ⟨CodeStoreRel.refl hF s, rfl⟩

/-- Typing and code-parametric interaction are separate host obligations. -/
def HostCodeOk {H : Type} (host : HostSemantics H) : Prop :=
  HostOk host ∧ HostCodeParametric host

/-- A returning host which leaves the store intact and reports a trap. It is
well behaved for every function signature, including nonempty result types. -/
def returningTrapHost {H : Type} : HostSemantics H :=
  fun _ s _ out => out = .returned s .trap

theorem returningTrapHost_typed {H : Type} : HostOk (returningTrapHost (H := H)) := by
  intro s fi h vs ps rs hs _ _ _ _
  refine ⟨⟨_, rfl⟩, ?_⟩
  intro out hout
  cases hout
  exact ⟨hs, Extend.refl hs, trivial⟩

theorem returningTrapHost_parametric {H : Type} :
    HostCodeParametric (returningTrapHost (H := H)) := by
  intro F _ h s t vs out hst hout
  cases hout
  exact ⟨.returned t .trap, rfl, hst, rfl⟩

/-- The combined contract admits host returns in arbitrary valid stores,
including stores containing Wasm code. -/
theorem returningTrapHost_ok {H : Type} : HostCodeOk (returningTrapHost (H := H)) :=
  ⟨returningTrapHost_typed, returningTrapHost_parametric⟩

theorem returningTrapHost_returns {H : Type} (h : H) (s : Store H) (vs : List Val) :
    returningTrapHost h s vs (.returned s .trap) := rfl

theorem closedHost_codeParametric {H : Type} :
    HostCodeParametric (closedHost (H := H)) := by
  intro F hF h s t vs out hst hout
  exact hout.elim

/-! ## Typed hosts without progress

`HostOk` also demands progress (some outcome exists), which `closedHost` fails
whenever the store holds a host function. Refinement does not need progress, only
that every returned outcome is typed. -/

/-- The safety half of `HostOk`: every returned store is valid, extends the input
store, and carries a result of the function's result type. -/
def HostSafe {H : Type} (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (fi : FuncInst H) (h : H) (vs : List Val) (ps rs : Ty (.list .val)),
    StoreOk s → fi ∈ s.funcs → fi.code = .host h → Expand fi.type (.func ps rs) →
    List.Forall₂ (ValOk s) vs ps.toList →
      ∀ out, host h s vs out → match out with
        | .diverged => True
        | .returned s' r => StoreOk s' ∧ Extend s s' ∧ ResultTyped s' r rs.toList

theorem HostOk.safe {H : Type} {host : HostSemantics H} (hh : HostOk host) : HostSafe host :=
  fun s fi h vs ps rs hs hfi hc he hv => (hh s fi h vs ps rs hs hfi hc he hv).2

/-- **Typed, code-parametric hosts**: the host class of the typed contextual
equivalences (`SeqEquivH HostCodeSafe`). It excludes the store-corrupting host of
`JoinableHostCex` and includes `closedHost` at every `H`. -/
def HostCodeSafe {H : Type} (host : HostSemantics H) : Prop :=
  HostSafe host ∧ HostCodeParametric host

theorem HostCodeOk.codeSafe {H : Type} {host : HostSemantics H} (hh : HostCodeOk host) :
    HostCodeSafe host :=
  ⟨HostOk.safe hh.1, hh.2⟩

theorem closedHost_codeSafe {H : Type} : HostCodeSafe (closedHost (H := H)) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ hout => hout.elim, closedHost_codeParametric⟩

/-- `HostRespectsCode` hosts are code-parametric in the tooling's sense. -/
theorem HostRespectsCode.hostParametric {H : Type} {host : HostSemantics H}
    (hh : HostRespectsCode host) : Sim.HostParametric host :=
  hh.codeParametric

end Silmaril.Wasm.Binaryen
