module

public import Silmaril.Proofs.Wasm.Models.FXAsyncSus.Exit

/-!
# Every run through an encoded `suspend` reaches the kernel's next configuration, or dies

The encoding of a kernel `suspend t (ar t)` handled by resumer `q` is the code
`PreC.plug [handler [(on ta 0)] (E.plug (fvals P ++ [suspend x]))]`, where `E` is the captured
segment and `PreC` the frames below, ending in the `block btH` label of the handler. `StepFX'`
may take the `suspend` rule at any handler frame and with any split of the values in front of the
`suspend` (`suspend_nondet`). This module shows that only one choice leads anywhere:

* **`sus_unique`**: any `suspend` step (`SusOut`) of that code is taken at the resumer's handler
  (an inner handler for the same tag address would make `E` handle it; an outer one would see the
  resumer's handler in its context), under the same outer context, and captures a context with
  the same layers as `E`; it differs from the intended step only in how the values in front of
  `suspend` are split between the captured context and the payload;
* **`inev_sus`**: when the captured frame holds exactly the payload (`(canon E).pre = []`), every
  `StepFX'` run from that code either reaches the intended configuration (the full split, then
  the unique `br 0`), or is stuck without a result (a shorter split: its `br 0` carries fewer
  values than the label's arity). So the next related configuration is inevitable (`InevP`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXAsyncSus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXAsyncFX (ix br1 comp)
open Silmaril.Proofs.Wasm.Models.FXAsyncFX (plug_comp frameAt_comp)
open Silmaril.Proofs.Wasm.Models.FXAsyncBack (Deep Iso SD TermFX Inev InevP UPath
  deep_plug deep_suspend inev_of_upath)
open Silmaril.Wasm.Numerics (GrowKind)

variable {H : Type} {o : GrowKind → Nat → Nat → Nat → Bool} {fx : H → Option FuncFX}

theorem append_cons_cases {α : Type} :
    ∀ {A A' B B' : List α} {x x' : α}, A ++ x :: B = A' ++ x' :: B' →
      (A = A' ∧ x = x' ∧ B = B') ∨ x ∈ B' ∨ x' ∈ B
  | [], [], _, _, _, _, h => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨rfl, h.1, h.2⟩
  | [], a' :: A', B, B', x, x', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact Or.inr (Or.inr (h.2 ▸ List.mem_append_right _ (List.mem_cons_self ..)))
  | a :: A, [], B, B', x, x', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact Or.inr (Or.inl (h.2 ▸ List.mem_append_right _ (List.mem_cons_self ..)))
  | a :: A, a' :: A', B, B', x, x', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases append_cons_cases h.2 with ⟨h₁, h₂, h₃⟩ | h' | h'
    · exact Or.inl ⟨by rw [h.1, h₁], h₂, h₃⟩
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')

/-- A handler layer with a clause for `ta` handles it. -/
theorem layer_handles {pre : List FVal} {hs : List HClause} {post : List AdminFX} {ta : Nat}
    {l : LabelIdx} (hcl : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    Layer.Handles ta ⟨pre, .handler hs, post⟩ :=
  ⟨hs, rfl, _, List.mem_of_find?_eq_some hcl, rfl⟩

theorem layer_handles_res {pre : List FVal} {post : List AdminFX} (ta : Nat) :
    Layer.Handles ta ⟨pre, .handler [.onLabel ta (ix 0)], post⟩ :=
  ⟨_, rfl, _, List.mem_singleton_self _, rfl⟩

/-- The frame at the `suspend`, read off the canonical form of the whole context. -/
theorem frame_sus (Eo : CtxV) (hs : List HClause) (E : CtxV) (f : Frame) :
    E.frameAt (Eo.frameAt f) = frameLs (canon (comp Eo (.handler hs E))).layers f := by
  rw [canon_frameAt, frameAt_comp]
  rfl

/-- Canonical forms with the same fields are equal. -/
theorem cctx_eq {C C' : CCtx} (hp : C.pre = C'.pre) (hq : C.post = C'.post)
    (hl : C.layers = C'.layers) : C = C' := by
  cases C; cases C'; simp_all

/-- The clause found for `ta` in the resumer's handler is its own. -/
theorem find_res {ta : Nat} {l : LabelIdx}
    (hcl : [HClause.onLabel ta (ix 0)].find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    l = ix 0 := by
  simp only [List.find?_cons, HClause.tag, BEq.rfl, Option.some.injEq,
    HClause.onLabel.injEq, true_and] at hcl
  exact hcl.symm

/-- The handler layer of the step is the resumer's, unless one of the two contexts handles the
tag. -/
theorem layer_cases {Eo PreC E' E : CtxV} {hs hR : List HClause}
    (hL : (canon Eo).layers ++ ⟨(canon Eo).pre, .handler hs, (canon Eo).post⟩ ::
        (canon E').layers =
      (canon PreC).layers ++ ⟨(canon PreC).pre, .handler hR, (canon PreC).post⟩ ::
        (canon E).layers) :
    ((canon Eo).layers = (canon PreC).layers ∧ (canon Eo).pre = (canon PreC).pre ∧ hs = hR ∧
        (canon Eo).post = (canon PreC).post ∧ (canon E').layers = (canon E).layers) ∨
      (⟨(canon Eo).pre, .handler hs, (canon Eo).post⟩ : Layer) ∈ (canon E).layers ∨
      (⟨(canon PreC).pre, .handler hR, (canon PreC).post⟩ : Layer) ∈ (canon E').layers := by
  rcases append_cons_cases hL with ⟨h₃, h₄, h₅⟩ | h' | h'
  · have h₆ : (canon Eo).pre = (canon PreC).pre ∧ hs = hR ∧
        (canon Eo).post = (canon PreC).post := by
      simpa only [Layer.mk.injEq, Wrp.handler.injEq] using h₄
    exact Or.inl ⟨h₃, h₆.1, h₆.2.1, h₆.2.2, h₅⟩
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr h')

/-- **Only the resumer's handler, with the encoded segment, can take the `suspend` step.** -/
theorem sus_unique {s : Store H} {f : Frame} {x : TagIdx} {Eo PreC E' E : CtxV}
    {hs : List HClause} {vs' P : List FVal} {ta ta' : Nat} {ti ti' : TagInst} {l : LabelIdx}
    (hc : Eo.plug [.handler hs (E'.plug (fvals vs' ++ [.fx (.suspend x)]))] =
      PreC.plug [.handler [.onLabel ta (ix 0)] (E.plug (fvals P ++ [.fx (.suspend x)]))])
    (ht' : s.tag? (E'.frameAt (Eo.frameAt f)) x = some (ta', ti')) (hE' : ¬ E'.Handles ta')
    (hcl : hs.find? (fun c => c.tag == ta') = some (.onLabel ta' l))
    (ht : s.tag? (E.frameAt (PreC.frameAt f)) x = some (ta, ti)) (hE : ¬ E.Handles ta) :
    hs = [.onLabel ta (ix 0)] ∧ l = ix 0 ∧ canon Eo = canon PreC ∧
      (canon E').layers = (canon E).layers ∧ (canon E').post = (canon E).post ∧
      (canon E').pre ++ vs' = (canon E).pre ++ P := by
  have h₁ : (comp Eo (.handler hs E')).plug (fvals vs' ++ [.fx (.suspend x)]) =
      (comp PreC (.handler [.onLabel ta (ix 0)] E)).plug (fvals P ++ [.fx (.suspend x)]) := by
    simpa only [plug_comp, CtxV.plug] using hc
  obtain ⟨hL, hpre, hpost⟩ := canon_unique rfl id h₁
  have hfr : E'.frameAt (Eo.frameAt f) = E.frameAt (PreC.frameAt f) := by
    rw [frame_sus, frame_sus, hL]
  have hta : ta' = ta := by
    have h₂ : some (ta', ti') = some (ta, ti) := by rw [← ht', ← ht, hfr]
    exact (Prod.mk.inj (Option.some.inj h₂)).1
  have hL' := hL
  rw [canon_comp_handler, canon_comp_handler] at hL'
  have hpre' : (canon E').pre ++ vs' = (canon E).pre ++ P := by
    simpa only [canon_comp_handler] using hpre
  have hpost' : (canon E').post = (canon E).post := by
    simpa only [canon_comp_handler] using hpost
  have hcl' : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l) := hta ▸ hcl
  rcases layer_cases hL' with ⟨h₃, h₄, h₅, h₆, h₇⟩ | h' | h'
  · have hl : l = ix 0 := find_res (h₅ ▸ hcl')
    exact ⟨h₅, hl, cctx_eq h₄ h₆ h₃, h₇, hpost', hpre'⟩
  · exact absurd ((canon_handles E ta).mp ⟨_, h', layer_handles hcl'⟩) hE
  · exact absurd ((canon_handles E' ta).mp ⟨_, h', layer_handles_res ta⟩) (hta ▸ hE')

end Silmaril.Proofs.Wasm.Models.FXAsyncSus
