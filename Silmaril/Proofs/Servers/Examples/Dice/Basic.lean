module

public import Silmaril.Servers.Examples.Dice.Defs
public import Silmaril.Servers.Core.Thms
public import Silmaril.Servers.Hosts.Thms
public import Silmaril.Servers.Observe.Thms
import Mathlib.Tactic.IntervalCases

/-!
# Proofs: the dice server

A machine each of whose steps satisfies a relation has a server satisfying the atomic sentence
of the relation; the dice machine with six faces meets `Ok`; the sequential trace of one request
is a trace of a server exactly when the machine can answer it.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Examples.Dice

open Silmaril.Servers Silmaril.Servers.Hosts Silmaril.Servers.Observe
open Silmaril.Servers.Examples.Dice
open Silmaril.Net.Http (Request Response)

variable {A : Sig}

theorem run_pointwise {σ : Type} {M : Machine A σ} {R : A.Req → A.Resp → Prop}
    (hR : ∀ q r s q', M q r s q' → R r s) {q q' : σ} {h : History A} (hr : M.Run q h q') :
    SeqSpec.pointwise R h := by
  induction hr with
  | nil => exact fun _ h => absurd h List.not_mem_nil
  | cons hm _ ih =>
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hR _ _ _ _ hm
    · exact ih p hp

/-- **A server whose every handler step satisfies `R` satisfies the atomic sentence of `R`.** -/
theorem server_sat_atomic {σ : Type} (M : Machine A σ) (q₀ : σ) {R : A.Req → A.Resp → Prop}
    (hR : ∀ q r s q', M q r s q' → R r s) : (M.server q₀).Sat (Sen.atomic R) := by
  intro t ht
  have hl := Sen.lin_mono (fun h ⟨_, hr⟩ => run_pointwise hR hr) t (M.server_sat_lin q₀ t ht)
  exact (Sen.lin_pointwise_iff R (Sen.wf_of_lin hl)).1 hl

theorem face_six (x : UInt64) : 1 ≤ face 6 x ∧ face 6 x ≤ 6 := by
  unfold face; have := Nat.mod_lt x.toNat (by decide : 0 < 6); omega

theorem rollPath_ne_pairPath : rollPath ≠ pairPath := by decide

/-- The dice machine meets `Ok` when every face the host can produce is in `1..6`. -/
theorem machine_ok_of_faces (k : Nat) {σ : Type} (h : Stateful σ Unit UInt64)
    (hf : ∀ q, 1 ≤ face k (h.step q ()).1 ∧ face k (h.step q ()).1 ≤ 6) {q q' : σ} {r : Request}
    {s : Response} (hm : machine k h q r s q') : Ok r s := by
  unfold machine at hm
  refine ⟨fun hp => ?_, fun hp => ?_, fun h1 h2 => ?_⟩
  · rw [ite_eq_left hp] at hm
    exact ⟨_, (hf q).1, (hf q).2, hm.1⟩
  · rw [ite_eq_right (hp ▸ rollPath_ne_pairPath.symm), ite_eq_left hp] at hm
    exact ⟨_, _, (hf q).1, (hf q).2, (hf _).1, (hf _).2, hm.1⟩
  · rw [ite_eq_right h1, ite_eq_right h2] at hm
    exact hm.1

theorem machine_ok {σ : Type} (h : Stateful σ Unit UInt64) {q q' : σ} {r : Request}
    {s : Response} (hm : machine 6 h q r s q') : Ok r s :=
  machine_ok_of_faces 6 h (fun _ => face_six _) hm

theorem machine_zero_roll {k : Nat} {q q' : Unit} {r : Request} {s : Response}
    (hm : machine k zeroHost q r s q') (hp : r.target.pathWithQuery = rollPath) :
    s = rollResp (face k 0) := by
  unfold machine at hm
  rw [ite_eq_left hp] at hm
  exact hm.1

/-- The sequential trace of one exchange. -/
def one (r : Request) (s : Response) : Trace Http.sig :=
  Trace.seq (A := Http.sig) [(⟨0, 0⟩, r, s)]

theorem one_mem {σ : Type} {M : Machine Http.sig σ} {q₀ q₁ : σ} {r : Request} {s : Response}
    (hm : M q₀ r s q₁) : (M.server q₀).Tr (one r s) := by
  rw [Machine.server_tr_iff, one, Sen.lin_seq_iff _ (by simp)]
  exact ⟨q₁, .cons hm (.nil _)⟩

theorem rollResp_seven_ne {n : Nat} (h1 : 1 ≤ n) (h6 : n ≤ 6) : rollResp 7 ≠ rollResp n := by
  interval_cases n <;> decide

theorem perRequest_roll {σ : Type} (h : Stateful σ Unit UInt64) {r : Request} {s : Response}
    (hp : r.target.pathWithQuery = rollPath) (hs : ∃ q', machine 6 h h.init r s q') :
    s = rollResp (face 6 (h.step h.init ()).1) := by
  obtain ⟨_, hm⟩ := hs
  unfold machine at hm
  rw [ite_eq_left hp] at hm
  exact hm.1

section Hosts

open Silmaril.Servers.Hosts

/-- **Under the zero host, no run answers `/roll` with `6`.** -/
theorem zero_not_maySix : ¬ (openDice 6 Unit zeroHost).May rollsSix := by
  rintro ⟨_, ⟨t, rfl, ht⟩, i, hr, hs⟩
  have := server_sat_atomic (machine 6 zeroHost) () (R := fun (r : Request) (s : Response) =>
    r.target.pathWithQuery = rollPath → s = rollResp (face 6 0))
    (fun _ _ _ _ hm hp => machine_zero_roll hm hp) t ht i _ _ hr hs rfl
  exact absurd this (by decide)

/-- **The seven-faced variant fails the must property** under the host drawing `6`. -/
theorem buggy_not_mustAll : ¬ MustAll Set.univ (openDice 7 Unit) (Obs.sen spec) := by
  refine not_mustAll_of_witness (η := constHost 6)
    (o := .run (one (getReq rollPath) (rollResp (face 7 6)))) trivial
    ⟨_, rfl, one_mem (M := machine 7 (constHost 6)) (q₁ := ()) ⟨rfl, rfl⟩⟩ fun hφ => ?_
  obtain ⟨n, h1, h6, he⟩ := (hφ ⟨0, 0⟩ (getReq rollPath) (rollResp (face 7 6))
    (by simp [one, Trace.seq]) (by simp [one, Trace.seq])).1 rfl
  exact rollResp_seven_ne h1 h6 he

/-- **Yet it passes under the zero host.** -/
theorem buggy_mustAll_zero : MustAll {zeroHost} (openDice 7 Unit) (Obs.sen spec) := by
  rintro _ rfl
  refine (Beh.must_ofModel_iff _ _).2 (server_sat_atomic _ _ fun _ _ _ _ hm => ?_)
  exact machine_ok_of_faces 7 zeroHost
    (fun _ => show 1 ≤ face 7 0 ∧ face 7 0 ≤ 6 from ⟨by decide, by decide⟩) hm

end Hosts

end Silmaril.Proofs.Servers.Examples.Dice
