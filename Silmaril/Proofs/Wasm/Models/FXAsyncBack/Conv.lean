module

public import Silmaril.Proofs.Wasm.Models.FXAsyncBack.UResume

/-!
# The converse of `kernel_in_fx` on the calm fragment

* `CalmSupported`: the fragment `Supported` along the kernel run, and no `suspend` is ever
  executed;
* `umatched_rel`: from related configurations in the fragment, `UMatched` (the converse of
  `sim_step`);
* **`fx_in_kernel`**: every `StepFX'` behaviour of the related WasmFX configuration is `obsB` of
  a kernel behaviour; with `kernel_in_fx`, **`beh_eq`**: the `StepFX'` behaviours are exactly the
  images of the kernel's.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncBack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync
  Silmaril.Wasm.Models.FXAsyncFX
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (SX Top cfgOf fine_cons supported_next
  fine_of_supported runN_succ_next)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} (S : Setup H) {W : Prog (Ins Val)}

/-- The next instruction of a configuration is not `suspend`. -/
def calmCfg (x : SCfg Val) : Bool :=
  match x.stack with
  | fr :: _ => CalmTop fr
  | [] => true

/-- **The calm fragment along a run**: `Supported`, and no `suspend` is executed. -/
def CalmSupported (W : Prog (Ins Val)) (x : SCfg Val) : Prop :=
  Supported W x ∧ ∀ n y, runN (sstep W i32Test) n x = .next y → calmCfg y = true

theorem calmSupported_next {x x' : SCfg Val} (h : CalmSupported W x)
    (hs : sstep W i32Test x = .next x') : CalmSupported W x' :=
  ⟨supported_next h.1 hs, fun n y hy => h.2 (n + 1) y (by rw [runN_succ_next hs]; exact hy)⟩

/-- **The backward simulation step**: the converse of `sim_step`. -/
theorem umatched_rel (hS : SX S = SD o S.fx) (hP : S.P = Profile.deterministic o)
    (hH : S.host = noHost) (hok : Ok S W) {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c)
    (hsup : CalmSupported W x) : UMatched S W c (sstep W i32Test x) := by
  obtain ⟨hs, hf₀, hK, st, hstk, hmain, hcode⟩ := hR
  have hc : c = ⟨S.s, c.conts, S.f0, (stkCtx S st).plug []⟩ := by
    rw [← hs, ← hf₀, ← hcode]
  have hf := fine_of_supported hsup.1
  have hcalm := hsup.2 0 x rfl
  match st, hmain, hstk with
  | [], hm, _ =>
    obtain ⟨init, last, heq, -⟩ := hm.2.2
    exact absurd heq.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | (fr, a) :: rs, hm, hstk =>
    have hx : x = ⟨x.conts, fr :: rs.map Prod.fst⟩ := by
      rw [← List.map_cons (f := Prod.fst) (a := (fr, a)), ← hstk]
    have hf' : fine W ⟨x.conts, fr :: rs.map Prod.fst⟩ = true := hx ▸ hf
    have hcalm' : CalmTop fr = true := by
      rw [hx] at hcalm
      simpa [calmCfg] using hcalm
    obtain ⟨hnt, htop⟩ := fine_cons hf'
    rw [hc, hx]
    exact umatched_top S hS hP hH hok ⟨hm, hK, hnt, htop⟩ hcalm'

theorem sx_eq (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) :
    SX S = SD o S.fx := by
  simp only [SX, SD, hP, hH]

/-- The hypotheses of the backward argument, on the calm fragment. -/
theorem backHyp (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) (hok : Ok S W) :
    BackHyp S W (CalmSupported W) where
  next _ _ h hs := calmSupported_next h hs
  matched _ _ hR hsup := umatched_rel S (sx_eq S hP hH) hP hH hok hR hsup
  stuck c d ws hc h := by
    rw [sx_eq S hP hH] at h
    exact Silmaril.Proofs.Wasm.Models.FXVRuns.no_step_fvals' h (liftV ws)
      (by rw [hc, liftV_fvals])

/-- **Every `StepFX'` behaviour is a kernel behaviour** (calm fragment, deterministic profile,
no host calls). -/
theorem fx_in_kernel (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) (hok : Ok S W)
    {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c) (hsup : CalmSupported W x) :
    ∀ b ∈ behavioursFX' S.P S.host S.fx c, ∃ ob ∈ beh (sstep W i32Test) x, obsB ob = b :=
  fx_sub_kernel (backHyp S hP hH hok) hR hsup

/-- **The `StepFX'` behaviours are exactly the images of the kernel's** (calm fragment). -/
theorem beh_eq (hP : S.P = Profile.deterministic o) (hH : S.host = noHost) (hok : Ok S W)
    {x : SCfg Val} {c : ConfigFX H} (hR : Rel S W x c) (hsup : CalmSupported W x) :
    behavioursFX' S.P S.host S.fx c = obsB '' beh (sstep W i32Test) x := by
  ext b
  constructor
  · intro hb
    obtain ⟨ob, hob, rfl⟩ := fx_in_kernel S hP hH hok hR hsup b hb
    exact ⟨ob, hob, rfl⟩
  · rintro ⟨ob, hob, rfl⟩
    exact Silmaril.Proofs.Wasm.Models.FXAsyncFX.beh_in_fx S hok hR hsup.1 ob hob

end Silmaril.Proofs.Wasm.Models.FXAsyncBack
