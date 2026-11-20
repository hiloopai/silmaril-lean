module

public import Silmaril.Wasm.Component.Reference.LinkedGInit.Defs

/-!
# The read-back of a linked call through an abstract exporter: definitions

**Scope.** The reference machine over `core3P P`, the exporter interface `ExpSpec.RefAdeqS` of
`LinkedGInit` (R1, R2, the corrected R3 `RefData.BwdT` of `LinkedGRound`, `InitS`, R5, R6).

## What R3's trapped case does not say

The read-back of the importer's side of a linked call reads every nested call of the importer
back through R3 (`RefData.BwdT`). R3's third case says of a run of the exporter's core
activation that ends locked down only that some trapped step of the specification holds at a
store with the trapped core store. It says nothing about:

* **the importer's part of the trapped core store.** The importer's invariant after the trap
  (`TrapAtG`, then `LReadyG` at `resumeCfg`) relates the importer's store to the trapped core
  store. Before the nested call it is related to the core store at the callout, disjointly from
  the exporter's footprint `F`; it survives the exporter's run exactly when that run changes the
  core store only inside `F` and by allocation (`CoreFoot.Within`), with its footprint grown by
  fresh addresses (`CoreFoot.Grows`). R2's trapped end (`RefData.Ends`) carries both; R3's third
  case carries neither, so an exporter whose trapping runs overwrite an importer global or
  struct is not excluded by R1–R6, and the importer's store read back after such a trap is not
  related to the machine's;
* **the control chain.** A locked-down configuration with a non-empty control chain still steps
  and may unlock (`locked_modify_step` of `LinkedGRound`); R3's third case may end at one, so the
  read-back cannot conclude that the call ended there.

**The correction** (`RefData.BwdF`): R3's third case ends with an empty control chain, and
the trapped step comes with the footprint discipline of R2's trapped end (`Within`, `Grows`).
`BwdF` implies `BwdT`, and a simple exporter meets it (`Thms`): its trapped runs end in
`trapCfg` of its core activation, which changes the core store only inside its part.
`ExpSpec.RefAdeqF` is `RefAdeqS` with `BwdF` for R3.

Note that the third case may also be the reading of a run that passed through a return of the
exporter and then trapped in the importer: the read-back then answers the nested call with the
exporter's trap. Both readings are consistent with the machine, because the trapped core store
relates to the importer's store at the callout (`Within`) and to the exporter's state after the
trapped step (`Hold`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **R3, corrected for the read-back**: `BwdT` whose trapped case ends with an empty control
chain and whose trapped step changes the core store only inside the footprint `F` and by
allocation, `F` growing by fresh addresses. -/
def BwdF : Prop :=
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
        (m'.store.lockdown = true ∧ m'.ctl = [] ∧ ((∀ msg, Label.trap (.internal msg) ∉ tr) →
          ∃ (s' : e.St) (S' : RefStore (core3P P)) (F' : CoreFoot),
            e.Step P s ⟨(w, .vals vs), none⟩ s' ∧
            S'.core = m'.core ∧ S'.funcs = S.funcs ∧ d.Hold pl s' S' F' ∧
            F.Within (S.core : Store (CanonHost (core3P P))) m'.core ∧
            F.Grows F' (S.core : Store (CanonHost (core3P P)))))

end ExpSpec.RefData

/-- **The reference interface of an exporter, for the read-back** (R1, R2, R3 with the
corrected trapped case `BwdF`, `InitS`, R5, R6). -/
def ExpSpec.RefAdeqF (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdF ∧ d.InitS ∧ d.Resume ∧ d.Bounded

end Silmaril.Wasm.Component.Reference
