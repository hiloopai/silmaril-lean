module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.BMHost.Core
public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD.Thms

/-!
# Round 7, memory SIMD: `ForwardBM` fails for `msAddHost`

At round 5's `srcCfg` (`ref.func 0; call_ref dt0` on `store0`, no memory SIMD code) Core steps,
under `msAddHost`, only to `msDst`, whose store holds memory SIMD code. Suppose a SpecTec step at
`BM` from `configVD srcCfg` to `configVD d'` with `d' ≈ msDst`.

* The source has no memory SIMD code, so `configVD srcCfg = configV srcCfg`, and its image has no
  memory SIMD atom (`noAtoms_srcCfg`, by a Boolean check `noAtomsB` and `noAtomsB_sound`). So the
  step is a step at round 6's builtins `BI` (`VInv.sstep_withVBytes_iff_of_noAtoms`).
* Round 6's backward simulation (`Round6.Target.backwardNC`) makes its target a `configV`
  image: `configVD d' = configV d₂`. Then `storeVD (addMS store0) = storeV d₂.store`, which
  `MSPres.storeVD_ne_storeV` forbids.

So `not_forwardBM`: **`ForwardBM hnU (Profile.spec nd r) msAddHost` is false** at every spec
profile, for an injective encoding, a finite host and a `HostOk` host. Consequences:
`not_openRMRest`, `not_openRM`, `not_openRMRestMS` (each field `forward` is `ForwardBM`), and
`not_openRMRest_all` etc.: the hypotheses of round 7's `MemSimd.wholeStepValidRM_of_rest`,
`MemSimd.wholeStepValidRM_of_open` and `VInv.wholeStepValidRM_of_restMS` are unsatisfiable.
`not_forwardBM_backend`: the forward half of `Round7.Task.wholeStepValidRM` itself fails at the
witness `B := BM`. The target is not refuted: it is `∃ B`, and `RMD.wholeStepValidRM_of_restD`
takes `B := HostD.BD`, whose `$hostcall` encodes the returned store by `storeVD`; there the same
Core step is simulated (`bd_step_srcCfg`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.BMHost

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Round5.Pos (srcCfg srcCfg_eq hnU hnU_injective configOk_srcCfg)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD storeVD)
open Round7.VInv (NoAtoms NoAtomsL NoAtomsF msAtoms)

/-! ## A Boolean check for `NoAtoms` -/

mutual
/-- `NoAtoms A v`, as a Boolean. -/
def noAtomsB (A : List MixopS) : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => noAtomsLB A vs
  | .case a w => !A.contains a && noAtomsB A w
  | .struct gs => noAtomsFB A gs
  | .list vs => noAtomsLB A vs
  | .opt none => true
  | .opt (some w) => noAtomsB A w

/-- `noAtomsB` on a list of values. -/
def noAtomsLB (A : List MixopS) : List Value → Bool
  | [] => true
  | v :: vs => noAtomsB A v && noAtomsLB A vs

/-- `noAtomsB` on the fields of a record. -/
def noAtomsFB (A : List MixopS) : List (AtomS × Value) → Bool
  | [] => true
  | (_, v) :: gs => noAtomsB A v && noAtomsFB A gs
end

mutual
theorem noAtomsB_sound (A : List MixopS) : ∀ v : Value, noAtomsB A v = true → NoAtoms A v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => by
      simp only [NoAtoms]
      exact noAtomsLB_sound A vs (by simpa only [noAtomsB] using h)
  | .case a w, h => by
      simp only [noAtomsB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      simp only [NoAtoms]
      exact ⟨h.1, noAtomsB_sound A w h.2⟩
  | .struct gs, h => by
      simp only [NoAtoms]
      exact noAtomsFB_sound A gs (by simpa only [noAtomsB] using h)
  | .list vs, h => by
      simp only [NoAtoms]
      exact noAtomsLB_sound A vs (by simpa only [noAtomsB] using h)
  | .opt none, _ => by simp only [NoAtoms]
  | .opt (some w), h => by
      simp only [NoAtoms]
      exact noAtomsB_sound A w (by simpa only [noAtomsB] using h)

theorem noAtomsLB_sound (A : List MixopS) : ∀ vs : List Value, noAtomsLB A vs = true →
    NoAtomsL A vs
  | [], _ => trivial
  | v :: vs, h => by
      simp only [noAtomsLB, Bool.and_eq_true] at h
      exact ⟨noAtomsB_sound A v h.1, noAtomsLB_sound A vs h.2⟩

theorem noAtomsFB_sound (A : List MixopS) : ∀ gs : List (AtomS × Value), noAtomsFB A gs = true →
    NoAtomsF A gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
      simp only [noAtomsFB, Bool.and_eq_true] at h
      exact ⟨noAtomsB_sound A v h.1, noAtomsFB_sound A gs h.2⟩
end

/-- The image of `srcCfg` has no memory SIMD atom. -/
theorem noAtoms_srcCfg : NoAtoms msAtoms (configV hnU srcCfg) :=
  noAtomsB_sound msAtoms (configV hnU srcCfg) (by decide +kernel)

/-! ## The refutation -/

theorem noMemSimd_srcCfg : Round6.MemSimd.NoMemSimd srcCfg :=
  Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.noMemSimd_srcCfg

/-- **Every `BM` step from `configVD srcCfg` under `msAddHost` reaches a `configV` image.** -/
theorem bm_step_srcCfg (nd : Bool) (r : RelaxedChoice) {w : Value}
    (hs : SStep (simEnv (Round7.MemSimd.BM (Profile.spec nd r) hnU msAddHost))
      (configVD hnU srcCfg) w) :
    ∃ d₂ : Config Unit, w = configV hnU d₂ := by
  rw [Round7.MemSimd.configVD_eq_of_noMemSimd hnU noMemSimd_srcCfg] at hs
  have hs' := (VInv.sstep_withVBytes_iff_of_noAtoms _ noAtoms_srcCfg).1 hs
  have hb := boundedSelM_srcCfg
  have hx := not_castRedex_srcCfg
  obtain ⟨-, d₂, -, hw, -⟩ := Round6.Target.backwardNC hnU_injective msAddHost_finite
    (Round5.BwdStep.growMaySucceed_spec nd r) (fun _ _ _ _ => trivial) srcCfg w
    (Round7.MemSimd.noCastV_of_noCastVM
      (Round7.MemSimd.noCastVM_entry srcCfg [] configOk_srcCfg hb hx) noMemSimd_srcCfg.code)
    (VInv.typed_of_typedD noMemSimd_srcCfg
      (Round7.MemSimd.typedD_of_configOk_selM _ hnU configOk_srcCfg hb))
    hs'
  exact ⟨d₂, hw⟩

/-- **`ForwardBM` fails for `msAddHost`**, at every spec profile. -/
theorem not_forwardBM (nd : Bool) (r : RelaxedChoice) :
    ¬ ForwardBM hnU (Profile.spec nd r) msAddHost := by
  intro hF
  obtain ⟨c'', hs'', -, d', hd', hst⟩ := hF srcCfg msDst [] configOk_srcCfg boundedSelM_srcCfg
    (fun _ h => step_msSrc_inv h ▸ boundedSelM_msDst) not_castRedex_srcCfg (step_msSrc _)
  obtain rfl := step_msSrc_inv hs''
  obtain ⟨d₂, hw⟩ := bm_step_srcCfg nd r hst
  have hst : storeVD hnU d'.store = storeV hnU d₂.store := by
    simp only [configVD, configV, Round7.MemSimd.stateVD, stateV] at hw
    injection hw with _ hw
    injection hw with hw
    injection hw with hw _
    injection hw with _ hw
    injection hw with hw
    injection hw with hw _
  exact Round7.MSPres.storeVD_ne_storeV hnU (hd'.1 ▸ not_storeMS_msDst) _ hst

/-! ## Consequences for round 7's reductions -/

/-- `OpenRMRest` fails for `msAddHost`. -/
theorem not_openRMRest (nd : Bool) (r : RelaxedChoice) :
    ¬ Round7.MemSimd.OpenRMRest hnU (Profile.spec nd r) msAddHost :=
  fun O => not_forwardBM nd r O.forward

/-- `OpenRM V` fails for `msAddHost`, at every `V`. -/
theorem not_openRM (V : Config Unit → Prop) (nd : Bool) (r : RelaxedChoice) :
    ¬ Round7.MemSimd.OpenRM V hnU (Profile.spec nd r) msAddHost :=
  fun O => not_forwardBM nd r O.forward

/-- `OpenRMRestMS` fails for `msAddHost`. -/
theorem not_openRMRestMS (nd : Bool) (r : RelaxedChoice) :
    ¬ VInv.OpenRMRestMS hnU (Profile.spec nd r) msAddHost :=
  fun O => not_forwardBM nd r O.forward

/-- **The hypothesis of `MemSimd.wholeStepValidRM_of_rest` is unsatisfiable.** -/
theorem not_openRMRest_all :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), Round7.MemSimd.OpenRMRest hn (Profile.spec nd r) host :=
  fun h => not_openRMRest false .det
    (h Unit hnU hnU_injective msAddHost msAddHost_finite msAddHost_ok false .det)

/-- **The hypothesis of `VInv.wholeStepValidRM_of_restMS` is unsatisfiable.** -/
theorem not_openRMRestMS_all :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : RelaxedChoice), VInv.OpenRMRestMS hn (Profile.spec nd r) host :=
  fun h => not_openRMRestMS false .det
    (h Unit hnU hnU_injective msAddHost msAddHost_finite msAddHost_ok false .det)

/-- **The forward half of `Round7.Task.wholeStepValidRM` fails at the witness `B := BM`** for
`msAddHost`, at every spec profile. -/
theorem not_forwardBM_backend (nd : Bool) (r : RelaxedChoice) :
    ¬ ∀ (c c' : Config Unit) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
        (∀ c₁, Step (Profile.spec nd r) msAddHost c c₁ → BoundedSelM c₁) →
        Step (Profile.spec nd r) msAddHost c c' →
        ∃ c'', Step (Profile.spec nd r) msAddHost c c'' ∧
          ((∀ c₃, Step (Profile.spec nd r) msAddHost c c₃ → c₃ = c') → c'' = c') ∧
          ∃ d', Bwd.ConfigEq c'' d' ∧
            Round6.Int.backend.step (Round7.MemSimd.BM (Profile.spec nd r) hnU msAddHost)
              (configVD hnU c) (configVD hnU d') := by
  intro h
  refine not_forwardBM nd r fun c c' ts hc hb hsucc hx hs => ?_
  obtain ⟨c'', hs'', hu, d', hd', hst⟩ := h c c' ts hc hb hsucc hs
  exact ⟨c'', hs'', hu, d', hd', (Round7.MemSimd.transferD_backend _ hnU hx _).1 hst⟩

/-! ## At `BD` the same step is simulated -/

theorem configOk_msDst : ConfigOk msDst [] :=
  (Step.preservation msAddHost_ok configOk_srcCfg (step_msSrc (Profile.spec false .det))).1

/-- **At `BD` the image of `srcCfg` steps to the image of `msDst`** (`HostRulesD.fwd_callRefHostD`):
the counterexample to `ForwardBM` is not one to `RMD.OpenRMRestD.forward`. -/
theorem bd_step_srcCfg (P : Profile) :
    SStep (simEnv (Round7.HostD.BD P hnU msAddHost)) (configVD hnU srcCfg) (configVD hnU msDst) := by
  rw [srcCfg_eq]
  exact HostRulesD.fwd_callRefHostD (vs := []) (a := 0) (fi := Round5.Pos.hostFn) (ps := .nil)
    (rs := .nil) (h := ()) (r := .trap) hnU_injective msAddHost_finite trivial rfl
    Round5.Pos.expand_dt0 rfl rfl rfl Round5.Pos.tyBnd_dt0
    (Round7.MemSimd.typedD_of_configOk_selM _ hnU configOk_srcCfg boundedSelM_srcCfg)
    (Round7.MemSimd.typedD_of_configOk_selM _ hnU configOk_msDst boundedSelM_msDst)

end Silmaril.Wasm.SpecTec.Sim.Round7.BMHost
