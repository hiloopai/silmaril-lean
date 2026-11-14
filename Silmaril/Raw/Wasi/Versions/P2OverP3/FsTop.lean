module

public import Silmaril.Raw.Wasi.Versions.P2OverP3.FsMain

/-!
# Proofs (unrefined): the methods of file streams, every export call, the invariant method

* `wp_fsStream`: the methods of a file-stream handle;
* `wp_progF`: every export call establishes `PostF`;
* `wpInvF`, `p2OverP3Fs_sat`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Versions.P2OverP3

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3
open Silmaril.Wasi.Versions.P2
open Silmaril.Wasi.Versions.P3OverP2 (fsReadTh3w fsRead2 rd2Step)

variable {F : BitVec 32 → List (BitVec 8)}

/-- The neutral answer of a stream method of a file stream is good. -/
theorem good_neutral {s : StF} {f : FnName} {a : List Val} {q2 q3 : RdSt} {e : FEnt}
    (hI : RdInv s q2 q3) (he : s.fs (selfOf a) = some e) (hst : (ioOp f).isStream = true)
    (hmem : f ∈ exp2)
    (hrd : ioOp f = .read ∨ ioOp f = .bread →
      s.io.closed (selfOf a) = true ∨ e.live = false ∨ u32Head a = false) :
    Good F s f a q2 (neutral s.io (ioOp f) a) where
  ans := neutral_ans s.io a hst
  p2 := by
    have : ioOp f ≠ .other := fun h => by rw [h] at hst; exact absurd hst (by decide)
    simp [p2Ok, this]
  fs := fsOk_of_mem hmem a _
  rd := by
    have hfr := ne_fdReadStream_of_mem hmem
    by_cases hr : ioOp f = .read ∨ ioOp f = .bread
    · have hf : f = isRead ∨ f = isBread := hr.imp ioOp_read ioOp_bread
      have hneu : neutral s.io (ioOp f) a =
          if s.io.closed (selfOf a) then errAns else okBytes [] := by
        rcases hr with h | h <;> rw [h] <;> rfl
      rcases hrd hr with hc | hl | hu
      · rw [hneu, ite_eq_left hc]
        refine ⟨q2, rd2_err q2 a hfr ?_, fun _ => rfl⟩
        cases hq : rest q2 (selfOf a).toNat with
        | none => exact .inl rfl
        | some bs =>
          refine .inr ?_
          cases bs with
          | nil => rfl
          | cons b bs =>
            have := (hI.rel _ e _ he hq).1 (by simp)
            rw [hc] at this; exact absurd this (by decide)
      · by_cases hu : u32Head a = true
        · obtain ⟨h, t, ha⟩ : ∃ h t, a = .u32 h :: t := by
            match a, hu with
            | .u32 h :: t, _ => exact ⟨h, t, rfl⟩
          cases hc : s.io.closed (selfOf a)
          · rw [hneu, hc]
            cases hq : rest q2 (selfOf a).toNat with
            | none => exact ⟨q2, rd2_untracked q2 a _ hfr hq, fun _ => rfl⟩
            | some bs =>
              refine ⟨setRest q2 (selfOf a).toNat (bs.drop ([] : List (BitVec 8)).length), ?_,
                fun n => ?_⟩
              · rw [ha] at hq ⊢
                exact rd2_bytes q2 hfr hf hq (by simp)
              · rw [rest_setRest]
                split
                · next hn => rw [hn, hq]; rfl
                · rfl
          · rw [hneu, hc]
            refine ⟨q2, rd2_err q2 a hfr ?_, fun _ => rfl⟩
            cases hq : rest q2 (selfOf a).toNat with
            | none => exact .inl rfl
            | some bs =>
              refine .inr ?_
              cases bs with
              | nil => rfl
              | cons b bs =>
                have := (hI.rel _ e _ he hq).1 (by simp)
                rw [hc] at this; exact absurd this (by decide)
        · exact ⟨q2, rd2_nohead q2 _ hfr (by simpa using hu), fun _ => rfl⟩
      · exact ⟨q2, rd2_nohead q2 _ hfr hu, fun _ => rfl⟩
    · exact ⟨q2, rd2_other q2 a _ hfr (fun h => hr (.inl (h ▸ by decide)))
        (fun h => hr (.inr (h ▸ by decide))), fun _ => rfl⟩
  closed := fun h hx => by
    rcases ioUpd_closed hx with hx | ⟨rfl, -, herr⟩
    · exact .inl hx
    · exact .inl (neutral_err herr)

theorem good_drop {s : StF} {f : FnName} {a : List Val} {q2 : RdSt} (hf : f = osDrop ∨ f = isDrop) :
    Good F s f a q2 (some []) := by
  rcases hf with rfl | rfl
  · exact good_other (by decide) (by decide) cliOk_osDrop (fsOk_of_mem (by simp [exp2, ioImports_eq]) a _)
  · exact good_other (by decide) (by decide) (cliOk_isDrop _)
      (fsOk_of_mem (by simp [exp2, ioImports_eq]) a _)

/-- **The methods of a file-stream handle.** -/
theorem wp_fsStream {s : StF} {f : FnName} {a : List Val} {g : Option (BitVec 64)} {q2 : RdSt}
    {qT : ClockSt × RdSt} {e : FEnt} (hJ : JF s qT ((s.io, g, (), ()), q2))
    (he : s.fs (selfOf a) = some e) (hm : fsMethod f = true) (hmem : f ∈ exp2) :
    Wp (t3F F) (fsStreamP s f a e) (PostF F s f a g q2) qT := by
  have hn : f ≠ clockNow := fun h => by subst h; exact absurd hm (by decide)
  have hI := hJ.2.2
  unfold fsStreamP
  dsimp only
  split
  · next hop =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact wp_fsRead false hJ he hc.1.2 hc.1.1 hc.2 (.inl (ioOp_read hop))
    · next hc =>
      refine wp_noread hn hJ (p := .pure _) ⟨shrinks_refl _, ?_⟩
      have := good_neutral (F := F) (q2 := q2) hI he (by rw [hop]; rfl) hmem (fun _ => by
        cases h1 : s.io.closed (selfOf a) <;> cases h2 : e.live <;> cases h3 : u32Head a <;>
          simp_all)
      rw [hop] at this
      exact this
  · next hop =>
    split
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact wp_fsRead true hJ he hc.1.2 hc.1.1 hc.2 (.inr (ioOp_bread hop))
    · next hc =>
      refine wp_noread hn hJ (p := .pure _) ⟨shrinks_refl _, ?_⟩
      have := good_neutral (F := F) (q2 := q2) hI he (by rw [hop]; rfl) hmem (fun _ => by
        cases h1 : s.io.closed (selfOf a) <;> cases h2 : e.live <;> cases h3 : u32Head a <;>
          simp_all)
      rw [hop] at this
      exact this
  · next hop =>
    have hdrop := fsMethod_other hm hop
    split
    · next hfd =>
      unfold fsDropP
      split
      · next hl =>
        refine wp_noread hn hJ ⟨⟨(by decide : cStreamDropR ≠ readVia3),
          (by decide : cStreamDropR ≠ cStreamRead)⟩, fun _ => ⟨⟨(by decide : cFutureDropR ≠ readVia3),
          (by decide : cFutureDropR ≠ cStreamRead)⟩, fun _ => ⟨shrinks_kill _ he, good_drop hdrop⟩⟩⟩
      · exact wp_noread hn hJ (p := .pure _) ⟨shrinks_refl _, good_drop hdrop⟩
    · exact wp_noread hn hJ (p := .pure _) ⟨shrinks_refl _, good_drop hdrop⟩
  · next o hr hb ho =>
    have hst : (ioOp f).isStream = true := by
      unfold fsMethod at hm
      rcases Bool.or_eq_true_iff.1 hm with h | h
      · rcases Bool.or_eq_true_iff.1 h with h | h
        · exact h
        · have : f = osDrop := of_decide_eq_true h
          subst this; exact absurd (by decide) ho
      · have : f = isDrop := of_decide_eq_true h
        subst this; exact absurd (by decide) ho
    exact wp_noread hn hJ (p := .pure _) ⟨shrinks_refl _,
      good_neutral hI he hst hmem (fun h => h.elim (absurd · hr) (absurd · hb))⟩

end Silmaril.Wasi.Versions.P2OverP3
