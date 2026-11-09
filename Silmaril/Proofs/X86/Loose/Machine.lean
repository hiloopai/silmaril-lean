module

public import Silmaril.X86.Loose.Defs
public import Silmaril.X86.RelIsa.Thms

/-!
# Proofs: the loose machine

The header is `Silmaril/X86/Loose/Thms.lean`: antitonicity in the table and the form
specifications, the exact stop condition, the shape of a step from a specified state, the
one-instruction `Must` rule, non-vacuity, and the footprint (`fsBase` and the extension are
kept).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Loose

open Silmaril.X86 (State Word Byte Reg RelIsa)
open Silmaril.Process (Memory)
open Silmaril.X86.RelIsa (Views Res Must Le ExtFrame)
open Silmaril.X86.Loose

variable {Φ σ : Type}

theorem regAfter_of_not_mem {e : Effect} {c : State} {r : Reg}
    (h : r ∉ e.regs.map (·.1)) : e.regAfter c r = c.read r := by
  unfold Effect.regAfter
  cases hf : e.regs.reverse.find? (fun p => decide (p.1 = r)) with
  | none => rfl
  | some p =>
    exfalso
    have hm := List.mem_of_find?_eq_some hf
    have hp : p.1 = r := by simpa using List.find?_some hf
    rw [List.mem_reverse] at hm
    exact h (List.mem_map.2 ⟨p, hm, hp⟩)

theorem antitone_S {D : DTable Φ} {S S' : Sigma Φ} {V : Views σ}
    (hS : ∀ i F, S i = some F → ∃ F', S' i = some F' ∧ F.Tightens F') :
    Le (X86Loose.rel D S' V) (X86Loose.rel D S V) where
  views := rfl
  step {_ _} _ h := by
    refine ⟨fun e hm hat F hF => ?_, h.2⟩
    obtain ⟨F', hF', hsub⟩ := hS e.form F hF
    obtain ⟨res, hsem, hmr⟩ := h.1 e hm hat F' hF'
    exact ⟨res, hsub _ _ _ _ hsem, hmr⟩

theorem step_stop_iff {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s : σ} :
    X86Loose.step D S V s .stop ↔ ∀ e ∈ D, AtEntry e (V.core s) (V.mem s) → ∀ F,
      S e.form = some F → F.unspecified (V.core s) (V.mem s) e.bytes.length := by
  constructor
  · intro h e hm hat F hF
    obtain ⟨res, hsem, hmr⟩ := h.1 e hm hat F hF
    rcases hsem with hu | ⟨c', m', rfl, _⟩
    · exact hu
    · cases hmr c' m' rfl
  · intro h
    refine ⟨fun e hm hat F hF => ⟨.trap, Or.inl (h e hm hat F hF), fun _ _ e => by cases e⟩,
      fun _ e => by cases e⟩

theorem step_ok_of_spec {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s t : σ}
    {e : DEntry Φ} {F : FormSpec} (hm : e ∈ D) (hat : AtEntry e (V.core s) (V.mem s))
    (hF : S e.form = some F) (hu : ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length)
    (h : X86Loose.step D S V s (.ok t)) :
    ∃ c' m', t = V.upd s c' m' ∧ F.allows (V.core s) (V.mem s) e.bytes.length c' m' := by
  obtain ⟨res, hsem, hmr⟩ := h.1 e hm hat F hF
  obtain ⟨c', m', rfl, ha⟩ := hsem.resolve_left hu
  cases hmr c' m' rfl
  exact ⟨c', m', rfl, ha⟩

theorem exists_step {D : DTable Φ} {S : Sigma Φ} {V : Views σ} {s : σ}
    {e : DEntry Φ} {F : FormSpec} (hlive : ∀ t, V.live t) (hF : S e.form = some F)
    (hu : ¬ F.unspecified (V.core s) (V.mem s) e.bytes.length)
    (huniq : ∀ e' ∈ D, AtEntry e' (V.core s) (V.mem s) →
      e'.form = e.form ∧ e'.bytes.length = e.bytes.length) :
    ∃ t, X86Loose.step D S V s (.ok t) := by
  obtain ⟨c', m', ha⟩ := F.nonempty hu
  refine ⟨V.upd s c' m', fun e' hm' hat' F' hF' => ?_, fun t _ => hlive t⟩
  obtain ⟨hf, hl⟩ := huniq e' hm' hat'
  rw [hf, hF] at hF'
  cases hF'
  refine ⟨.ok c' m', by rw [hl]; exact Or.inr ⟨c', m', rfl, ha⟩, fun c m he => ?_⟩
  cases he
  rfl

theorem must_keeps_of_step {A : RelIsa σ} {α : Type} (f : σ → α) {R R' Q : σ → Prop}
    (hf : ∀ s t, R' s → A.step s (.ok t) → f t = f s) {s : σ}
    (h : Must A (fun x => R x ∧ R' x) Q s) : Must A R (fun t => Q t ∧ f t = f s) s := by
  suffices H : ∀ x, Must A (fun x => R x ∧ R' x) Q x → ∀ v, f x = v →
      Must A R (fun t => Q t ∧ f t = v) x from H s h _ rfl
  intro x hx
  induction hx with
  | done hq => exact fun v hv => .done ⟨hq, hv⟩
  | step hR hns _ ih =>
    rename_i y _
    intro v hv
    exact .step hR.1 hns fun t ht => ih t ht v (by rw [hf y t hR.2 ht, hv])

end Silmaril.Proofs.X86.Loose
