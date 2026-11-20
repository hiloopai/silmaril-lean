module

public import Silmaril.Wasm.Component.Reference.LinkedGImp.Defs

/-!
# A session round of a linked component with an abstract exporter: definitions

**Scope.** The reference machine over `core3P P`, the exporter interface `ExpSpec.RefAdeqB` of
`LinkedGImp` (R1–R6).

## The read-back of R3 passes only through returns

R3 (`RefData.Bwd`) classifies every run of the exporter's core activation without host events:
still running, or passed through an end of R2 (`RefData.Ends`) for some step of the
specification (with the control chain non-empty there), or trapped. `Ends` has two branches: a
return to the caller's continuation, and a trapped configuration (locked down). R3's middle case
may therefore be witnessed by a **locked-down configuration whose control chain is not empty**,
and it says nothing about the run after it.

Such a configuration is not stuck: of the machine's rules only the host events require the store
not to be locked down; program steps (`Step.modify`, `Step.call`, …) and core steps
(`Step.coreInternal`) do not. From a locked-down configuration with a `modify` in focus the
machine unlocks the store, and with a running core activation in focus it changes the core
store (`Thms`: `locked_modify_step`, `locked_core_step`). So the read-back of the importer
cannot conclude, from such a witness, that the run ends trapped at a core store related to the
exporter's state: the run may continue, unlock, and change the store.

**The correction** (`RefData.EndsT`, `RefData.BwdT`): in R3's middle case the end of R2 is
required to have an empty control chain when it is locked down. Together with the middle case's
non-empty control chain this means that the middle case passes only through R2's **returns**;
trapped runs are R3's third case. A locked-down configuration with an empty control chain takes
no step (`steps_of_locked`), so nothing is lost. `BwdT` implies `Bwd`, and a simple exporter
meets `BwdT` (`Thms`), its middle case being a return.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **An end of R2 that is a trapped configuration only with an empty control chain.** -/
def EndsT {σ : Type} (pl : d.Pl) (x : Export) (S : RefStore (core3P P)) (F : CoreFoot)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P))) (segs : List (Seg (core3P P) σ))
    (rest : List (Activation (core3P P) σ)) (R : Option Payload) (s' : e.St)
    (m : Machine.Config (core3P P) σ) : Prop :=
  d.Ends pl x S F M th K segs rest R s' m ∧ (m.store.lockdown = true → m.ctl = [])

/-- **R3, corrected**: `Bwd` with the middle case passing through an `EndsT`. -/
def BwdT : Prop :=
  ∀ (pl : d.Pl) (s : e.St) (w : Nat) (vs : List IVal) (x : Export),
    e.comp.exports[w]? = some x → ValTy.checkList x.ty.params vs = true →
    ∀ (S : RefStore (core3P P)) (F : CoreFoot), d.Hold pl s S F →
    ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
      (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
      (K : List FlatValue → Canon.P (core3P P) σ (Ret (core3P P)))
      (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
      M.ref = S → S.lockdown = false → instOfThread? S.toCStore th = some ⟨d.inst pl w⟩ →
      ∀ (tr : List (Label (core3P P) σ)) (m' : Machine.Config (core3P P) σ),
        Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
          (d.startCfg pl w x vs M th K segs rest) tr m' → (∀ ev, Label.host ev ∉ tr) →
        (m'.ctl ≠ [] ∧ m'.store.lockdown = false) ∨
        (∃ (tr₁ tr₂ : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ)
            (R : Option Payload) (s' : e.St),
          tr = tr₁ ++ tr₂ ∧
          Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch
            (d.startCfg pl w x vs M th K segs rest) tr₁ m ∧
          Machine.Steps prof (linkHost impl).hr (linkHost impl).dispatch m tr₂ m' ∧
          e.Step P s ⟨(w, .vals vs), R⟩ s' ∧ d.EndsT pl x S F M th K segs rest R s' m ∧
          m.ctl ≠ []) ∨
        (m'.store.lockdown = true ∧ ((∀ msg, Label.trap (.internal msg) ∉ tr) →
          ∃ (s' : e.St) (S' : RefStore (core3P P)) (F' : CoreFoot),
            e.Step P s ⟨(w, .vals vs), none⟩ s' ∧
            S'.core = m'.core ∧ S'.funcs = S.funcs ∧ d.Hold pl s' S' F'))

end ExpSpec.RefData

/-- **The reference interface of an exporter, with allocated footprints and R3 through returns
only** (R1, R2, the corrected R3, R4, R5, R6). -/
def ExpSpec.RefAdeqT (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdT ∧ d.Init ∧ d.Resume ∧ d.Bounded

end Silmaril.Wasm.Component.Reference
