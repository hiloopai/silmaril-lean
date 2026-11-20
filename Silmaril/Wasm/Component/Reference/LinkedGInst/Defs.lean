module

public import Silmaril.Wasm.Component.Reference.LinkedGInv.Defs

/-!
# The instantiation of a linked component read back: definitions

**Scope.** The reference machine over `core3P P` under `linkHost impl`, the exporter given by
reference data `d` (`ExpSpec.RefData`), as in `LinkedGInit` and `LinkedGInv`.

## What `InitS` does not say

`LinkedG.sessObs` quantifies over **every** instantiation behaviour of `lg.toRef`. R4 as the
parent reads it (`RefData.InitS`) gives **one** run of the exporter's nested instantiation
reaching an `InitAt` end; it says nothing of the other runs (a run that stops elsewhere, traps,
diverges or reaches another end), and nothing of the store's waiting threads, which the
read-back of calls (`sessL_invB` of `LinkedGInv`) needs to be empty between calls.

**The read-back law** (`RefData.InitU`): R4's run is a **live deterministic run** (`LiveDet`:
every configuration it leaves has a running activation, is not locked down and has exactly one
step, the one taken), and the configuration it reaches keeps the waiting threads. Every machine
run from the start of a live deterministic run stops inside it at a live configuration or
extends it, and a divergence of its start is a divergence of its end; so the parent's
instantiation result is unique. `InitU` implies `InitS` (`Thms`), and a simple exporter meets it:
its nested instantiation is a big-step run of a program without choices.

`ExpSpec.RefAdeqU` is `RefAdeqF` of `LinkedGInv` with `InitU` for R4.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Machine Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Numerics (Profile)

/-- **A live deterministic run**: every configuration the run leaves has a running activation,
is not locked down, and has exactly one step, the one the run takes. -/
inductive LiveDet {E : CoreEngine} {σ : Type} (prof : ProfileKind) (hr : HostReady σ)
    (D : Call E → Canon.P E σ (Ret E)) :
    Machine.Config E σ → List (Label E σ) → Machine.Config E σ → Prop where
  | refl (m : Machine.Config E σ) : LiveDet prof hr D m [] m
  | cons {m m₁ m₂ : Machine.Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
      m.ctl ≠ [] → m.store.lockdown = false → Machine.Step prof hr D m l m₁ →
      (∀ l' m', Machine.Step prof hr D m l' m' → l' = l ∧ m' = m₁) →
      LiveDet prof hr D m₁ tr m₂ → LiveDet prof hr D m (l :: tr) m₂

namespace ExpSpec.RefData

variable {P : Profile} {e : ExpSpec} (d : e.RefData P)

/-- **R4 with a read-back**: `InitS` whose run is a live deterministic run (`LiveDet`), its end
keeping the store's waiting threads. -/
def InitU : Prop :=
  ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (outer : List (Instantiate.Frame (core3P P)))
    (k : Ret (core3P P) → Canon.P (core3P P) σ (Ret (core3P P)))
    (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
    M.core = (core3P P).empty (CanonHost (core3P P)) → M.store.lockdown = false →
    ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × Instantiate.ItemVal (core3P P))),
      LiveDet prof (linkHost impl).hr (linkHost impl).dispatch
        { M with ctl := ⟨th, .prog (callRet (.instantiate ⟨e.ref, outer⟩ []) >>= k), segs⟩ ::
          rest } tr m ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ traceObs tr = [] ∧
      m.ctl = ⟨th, .prog (k (.items es)), segs⟩ :: rest ∧ d.InitAt pl F es M m ∧
      m.store.waiting = M.store.waiting

/-- **`InitU` with any host code in the exporter's core store** (`InitAtX` for `InitAt`). -/
def InitUX : Prop :=
  ∀ {σ : Type} (prof : ProfileKind) (impl : HostImpl (core3P P) σ)
    (M : Machine.Config (core3P P) σ) (th : Option ThreadId)
    (outer : List (Instantiate.Frame (core3P P)))
    (k : Ret (core3P P) → Canon.P (core3P P) σ (Ret (core3P P)))
    (segs : List (Seg (core3P P) σ)) (rest : List (Activation (core3P P) σ)),
    M.core = (core3P P).empty (CanonHost (core3P P)) → M.store.lockdown = false →
    ∃ (tr : List (Label (core3P P) σ)) (m : Machine.Config (core3P P) σ) (pl : d.Pl)
      (F : CoreFoot) (es : List (String × Instantiate.ItemVal (core3P P))),
      LiveDet prof (linkHost impl).hr (linkHost impl).dispatch
        { M with ctl := ⟨th, .prog (callRet (.instantiate ⟨e.ref, outer⟩ []) >>= k), segs⟩ ::
          rest } tr m ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ traceObs tr = [] ∧
      m.ctl = ⟨th, .prog (k (.items es)), segs⟩ :: rest ∧ d.InitAtX pl F es M m ∧
      m.store.waiting = M.store.waiting

end ExpSpec.RefData

/-- **The reference interface of an exporter, for the read-back from instantiation** (R1, R2,
R3 as `BwdF`, R4 as `InitU`, R5, R6). -/
def ExpSpec.RefAdeqU (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdF ∧ d.InitU ∧ d.Resume ∧ d.Bounded

/-- **`RefAdeqU` with any host code in the exporter's core store** (R4 as `InitUX`). -/
def ExpSpec.RefAdeqUX (P : Profile) (e : ExpSpec) : Prop :=
  ∃ d : e.RefData P, d.Frame ∧ d.Fwd ∧ d.BwdF ∧ d.InitUX ∧ d.Resume ∧ d.Bounded

end Silmaril.Wasm.Component.Reference
