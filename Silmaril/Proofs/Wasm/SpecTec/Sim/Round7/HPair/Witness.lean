module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HPair.Forward
public import Silmaril.Wasm.SpecTec.Sim.Round7.MSPres.Thms

/-!
# Round 7, `BD`: `EasyP` is strictly larger than `RMRed.Easy`

`cfgP` is round 5's source configuration (`Round5.Pos.srcCfg`, a host function in the store) with
the code `nop; CALL_REF dt0`: a `CALL_REF` that does not follow a function reference.

* `noPairB`, `noPairB_sound`: a Boolean check for `NoPair`.
* `easyP_cfgP`: `cfgP` is `EasyP` (at any profile, for the host with no outcome).
* `not_easy_cfgP`: `cfgP` is not `RMRed.Easy` (its image has `CALL_REF`, `MSAtoms` bridge).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round5.Pos (dt0 store0 srcCfg hnU)
open Round6.MemSimd (NoMemSimd)

/-! ## A Boolean check -/

/-- `PairFreeL`, as a Boolean. -/
def pairFreeB : List Value → Bool
  | a :: b :: rest => !pairAt a b && pairFreeB (b :: rest)
  | _ => true

mutual
/-- `NoPair`, as a Boolean. -/
def noPairB : Value → Bool
  | .tuple vs => noPairLB vs
  | .case _ w => noPairB w
  | .struct gs => noPairFB gs
  | .list vs => pairFreeB vs && noPairLB vs
  | .opt (some w) => noPairB w
  | _ => true

/-- `noPairB` on every element. -/
def noPairLB : List Value → Bool
  | [] => true
  | v :: vs => noPairB v && noPairLB vs

/-- `noPairB` on every field. -/
def noPairFB : List (AtomS × Value) → Bool
  | [] => true
  | (_, v) :: gs => noPairB v && noPairFB gs
end

theorem pairFreeB_sound : ∀ {vs : List Value}, pairFreeB vs = true → PairFreeL vs
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: b :: rest, h => by
    simp only [pairFreeB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨h.1, pairFreeB_sound (vs := b :: rest) h.2⟩

mutual
theorem noPairB_sound : ∀ v : Value, noPairB v = true → NoPair v
  | .bool _, _ => trivial
  | .num _, _ => trivial
  | .text _, _ => trivial
  | .tuple vs, h => noPairLB_sound vs (by simpa only [noPairB] using h)
  | .case _ w, h => noPairB_sound w (by simpa only [noPairB] using h)
  | .struct gs, h => noPairFB_sound gs (by simpa only [noPairB] using h)
  | .list vs, h => by
    simp only [noPairB, Bool.and_eq_true] at h
    exact ⟨pairFreeB_sound h.1, noPairLB_sound vs h.2⟩
  | .opt none, _ => trivial
  | .opt (some w), h => noPairB_sound w (by simpa only [noPairB] using h)

theorem noPairLB_sound : ∀ vs : List Value, noPairLB vs = true → NoPairL vs
  | [], _ => trivial
  | v :: vs, h => by
    simp only [noPairLB, Bool.and_eq_true] at h
    exact ⟨noPairB_sound v h.1, noPairLB_sound vs h.2⟩

theorem noPairFB_sound : ∀ gs : List (AtomS × Value), noPairFB gs = true → NoPairF gs
  | [], _ => trivial
  | (_, v) :: gs, h => by
    simp only [noPairFB, Bool.and_eq_true] at h
    exact ⟨noPairB_sound v h.1, noPairFB_sound gs h.2⟩
end

/-! ## The witness -/

/-- **`nop; CALL_REF dt0`** over round 5's store with one host function. -/
def cfgP : Config Unit := ⟨store0, {}, [.plain .nop, .callRefType dt0]⟩

theorem noMemSimd_cfgP : NoMemSimd cfgP :=
  ⟨Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.MSPres.noMemSimd_srcCfg.store, by
    simp [cfgP, Round6.MemSimd.AdminsMS, Round6.MemSimd.AdminMS, Round6.MemSimd.instrMS,
      Round6.MemSimd.memSimd]⟩

theorem noPair_cfgP : NoPair (configV hnU cfgP) :=
  noPairB_sound _ (by decide +kernel)

/-- **`cfgP` is `EasyP`**, for the host with no outcome, at every profile. -/
theorem easyP_cfgP (P : Profile) : EasyP hnU P NullHost.nullHost cfgP :=
  ⟨noMemSimd_cfgP,
    fun _ h => Round7.MSPres.step_noMemSimd NullHost.nullHost_keepsMS h noMemSimd_cfgP,
    noPair_cfgP⟩

/-- **`cfgP` is not `RMRed.Easy`.** -/
theorem not_easy_cfgP (P : Profile) : ¬ RMRed.Easy hnU P NullHost.nullHost cfgP := by
  intro h
  have hc : MSAtoms.NoCallRef cfgP := (MSAtoms.noAtoms_h_configV_iff hnU noMemSimd_cfgP).1 h.2.2
  have hcode : MSAtoms.AdminsOk false cfgP.code := hc.2
  simp [cfgP, MSAtoms.AdminsOk, MSAtoms.AdminOk] at hcode

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
