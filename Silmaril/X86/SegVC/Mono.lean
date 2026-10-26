module

public import Silmaril.X86.SegVC

/-! # The path budget of `SegVC.wpN` is monotone

`SegVC.vc` takes one budget `K` for the entry and every cut point. A VC proved with a
smaller budget (a cut point whose paths are short) holds at every larger one: `wpN_mono`.
VERIFIED (no `sorry`, no new axiom). -/

@[expose] public section

namespace Silmaril.X86.SegVC

open Silmaril.X86 (State Word Byte)
open Silmaril.Process (Memory)

variable {σ : Type} {I : Isa σ} {code : List Byte} {L : Listing I}
  {cuts : List (Nat × Cut (σ := σ))} {stops : List (Nat × (σ → Prop))}
  {calls : List (Nat × Nat × Call I)} {subs : List (Nat × Nat × Call I)} {base : Word}

theorem nextAt_mono {μ : Option Nat} {cont cont' : Nat → σ → Prop}
    (h : ∀ o s, cont o s → cont' o s) {o : Nat} {s : σ} :
    nextAt cuts stops μ cont o s → nextAt cuts stops μ cont' o s := by
  unfold nextAt
  split
  · exact id
  · split
    · exact id
    · exact h _ _

theorem wpN_mono {μ : Option Nat} :
    ∀ {k k' : Nat}, k ≤ k' → ∀ {o : Nat} {s : σ},
      wpN I code L cuts stops calls subs base μ k o s →
        wpN I code L cuts stops calls subs base μ k' o s := by
  intro k
  induction k with
  | zero => intro _ _ _ _ h; exact h.elim
  | succ k ih =>
    intro k' hk o s h
    obtain ⟨k'', rfl⟩ : ∃ k'', k' = k'' + 1 := ⟨k' - 1, by omega⟩
    have ih' : ∀ o s, wpN I code L cuts stops calls subs base μ k o s →
        wpN I code L cuts stops calls subs base μ k'' o s :=
      fun _ _ => ih (by omega)
    simp only [wpN] at h ⊢
    cases hsb : subs.lookup o with
    | some osb =>
      obtain ⟨o', sb⟩ := osb
      rw [hsb] at h
      exact ⟨h.1, fun t ht => let ⟨a, b, c⟩ := h.2 t ht; ⟨a, b, nextAt_mono ih' c⟩⟩
    | none =>
      rw [hsb] at h
      simp only at h ⊢
      cases hl : L.lookup o with
      | none => rw [hl] at h; exact h.elim
      | some il =>
        rw [hl] at h
        obtain ⟨i, l⟩ := il
        simp only [wpI] at h ⊢
        revert h
        cases I.exec i (I.core s) (I.mem s) l with
        | ok c m =>
          simp only [onOk, after]
          rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, ?_⟩
          cases hcl : calls.lookup o with
          | some ocl =>
            obtain ⟨o', cl⟩ := ocl
            rw [hcl] at h3
            exact ⟨h3.1, fun t ht => let ⟨a, b, c⟩ := h3.2 t ht; ⟨a, b, nextAt_mono ih' c⟩⟩
          | none =>
            rw [hcl] at h3
            exact nextAt_mono ih' h3
        | _ => simp [onOk]

end Silmaril.X86.SegVC
