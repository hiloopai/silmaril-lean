module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.TransferD
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MemSimd.StoreD

/-!
# Round 7, memory SIMD: `Round7.Task.wholeStepValidRM` from its open leaves

Round 6 assembles its target from a transfer lemma, a cast leaf and the proved declarative
halves (`Round6.Target.wholeStepValidR_of_open`). This file does the same for the round-7 target
at `configVD`, with every proved piece plugged in:

* the backend transfer away from cast redexes is proved (`sstepB_iff_of_not_castRedexD`, this
  pass);
* the backward recursion is proved (`backward_upToD`, pass 5), with the memory SIMD loads
  discharged at every configuration (`readMSD`, this pass; pass 5 needed a store
  without memory SIMD code), and the memory SIMD stores `Step` 22–25 too (`stepMSD`, this pass).

What is left is collected in `OpenRM`, at the target's builtins
`withVBytes (Prims.builtins P hn host)`:

* `forward`: the declarative forward half at `configVD`, away from cast redexes (round 6's
  `Target.forwardR'` with its context lifting, at `configVD`);
* `closed`, `entry`: the parameter `V` is a predicate closed under SpecTec's context decompositions that holds at
  every valid `BoundedSelM` configuration without a cast redex (round 6 uses `NoCastV`);
* `typed`: valid `BoundedSelM` configurations have typed `configVD` images (round 5's
  `typed_of_configOk_sel`, at `configVD`);
* `rest`: the per-rule backward obligations of the rules without memory SIMD
  (`BackwardUpToDRestS`; the memory SIMD loads and stores are `readMSD` and `stepMSD`);
* `casts`: the cast leaf at `configVD` (round 6's `Target.Casts`).

`wholeStepValidRM_of_open` proves the frozen target from `OpenRM` at every injective encoding,
finite `HostOk` host and spec profile. It is a reduction: no field of `OpenRM` is proved here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round6.Target (CastRedex CtxClosedVals)

variable {H : Type}

/-- The round-7 target's builtins. -/
noncomputable abbrev BM (P : Profile) (hn : H → String) (host : HostSemantics H) : Builtins :=
  withVBytes (Prims.builtins P hn host)

/-- **The open leaves of `Round7.Task.wholeStepValidRM`** at one encoding, profile and host (see
the module docstring). -/
structure OpenRM (V : Config H → Prop) (hn : H → String) (P : Profile) (host : HostSemantics H) :
    Prop where
  /-- The declarative forward half at `configVD`, away from cast redexes, up to Core's choice of
  successor. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BM P hn host)) (configVD hn c) (configVD hn d')
  /-- The predicate `V` the backward recursion runs under is closed under SpecTec's context decompositions. -/
  closed : CtxClosedVals V
  /-- It holds at the sources of the backward half that are not cast redexes. -/
  entry : ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    ¬ CastRedex c.code → V c
  /-- Valid `BoundedSelM` configurations have typed `configVD` images. -/
  typed : ∀ (c : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    TypedD (simEnv (BM P hn host)) hn c
  /-- The per-rule backward obligations of the rules without memory SIMD. -/
  rest : BackwardUpToDRestS V (simEnv (BM P hn host)) hn P host
  /-- The cast leaf, forward: Core's cast steps are deterministic, so it is exact. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BM P hn host) (configVD hn c) (configVD hn d')
  /-- The cast leaf, backward. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code →
    Round6.Int.backend.step (BM P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

variable {V : Config H → Prop} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-- **The forward half of the round-7 target, from `OpenRM`.** -/
theorem fwdRM_of_open (O : OpenRM V hn P host) (c c' : Config H) (ts : List CValType)
    (hc : ConfigOk c ts) (hb : BoundedSelM c) (hsucc : ∀ c₁, Step P host c c₁ → BoundedSelM c₁)
    (hs : Step P host c c') :
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        Round6.Int.backend.step (BM P hn host) (configVD hn c) (configVD hn d') := by
  by_cases hx : CastRedex c.code
  · obtain ⟨d', hd', hst⟩ := O.castsFwd c c' ts hc hb hsucc hx hs
    exact ⟨c', hs, fun _ => rfl, d', hd', hst⟩
  · obtain ⟨c'', hs'', hu, d', hd', hst⟩ := O.forward c c' ts hc hb hsucc hx hs
    exact ⟨c'', hs'', hu, d', hd', (transferD_backend _ hn hx _).2 hst⟩

/-- **The backward half of the round-7 target, from `OpenRM`.** -/
theorem bwdRM_of_open (O : OpenRM V hn P host) (c : Config H) (ts : List CValType) (w : Value)
    (hc : ConfigOk c ts) (hb : BoundedSelM c)
    (hs : Round6.Int.backend.step (BM P hn host) (configVD hn c) w) :
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c' := by
  by_cases hx : CastRedex c.code
  · exact O.castsBwd c ts w hc hb hx hs
  · exact backward_upToD_restS O.closed O.rest c w (O.entry c ts hc hb hx) (O.typed c ts hc hb)
      ((transferD_backend _ hn hx w).1 hs)

/-- **`Round7.Task.wholeStepValidRM` from its open leaves**: the frozen round-7 target holds as
soon as `OpenRM` does at every injective encoding, finite `HostOk` host and spec profile, with
`B := withVBytes (Prims.builtins …)`. -/
theorem wholeStepValidRM_of_open
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), ∃ V, OpenRM V hn (Profile.spec nd r) host) :
    Task.wholeStepValidRM := fun H hn hinj host hfin hok nd r =>
  have O := (h H hn hinj host hfin hok nd r).choose_spec
  ⟨BM (Profile.spec nd r) hn host,
    fun c c' ts hc hb hsucc hs => fwdRM_of_open O c c' ts hc hb hsucc hs,
    fun c ts w hc hb hs => bwdRM_of_open O c ts w hc hb hs⟩

end Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd
