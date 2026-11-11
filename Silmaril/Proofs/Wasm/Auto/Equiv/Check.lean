module

public import Silmaril.Proofs.Wasm.Auto.Equiv.Sexec

/-!
# Soundness of the equivalence checker

* `segEquiv_of_final`: two segments whose symbolic runs end in states with equal
  values in every environment are equivalent (`SegEquiv`);
* `segEquiv_of_check`: **the checker is sound**;
* `segEquiv_of_residuals`: equal shapes plus proofs of the residual bitvector goals
  give equivalence;
* `not_segEquiv_of_cex`: an environment in which the final states differ refutes
  equivalence (through the every-run logic's adequacy, `HWP.sound_vals`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare

variable {ρ : Env}

theorem den_eq_of_slotEq {p q : IntType × Term} (h : slotEq p q = true) : den ρ p = den ρ q := by
  rcases p with ⟨t, a⟩
  rcases q with ⟨t', b⟩
  simp only [slotEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨rfl, h₂⟩ := h
  simp only [den]
  rw [← ev_norm t a, h₂, ev_norm]

theorem map_den_of_slotsEq : ∀ {ps qs : List (IntType × Term)}, slotsEq ps qs = true →
    ps.map (den ρ) = qs.map (den ρ)
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
    simp only [slotsEq, Bool.and_eq_true] at h
    simp [den_eq_of_slotEq h.1, map_den_of_slotsEq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [slotsEq] at h

theorem den_eq_of_goal (t : IntType) {a b : Term}
    (hg : Goal.Holds (t, norm t a, norm t b)) : den ρ (t, a) = den ρ (t, b) := by
  have := hg ρ
  simp only [ev_norm] at this
  simp [den, this]

theorem map_den_of_slotsGoals : ∀ {ps qs : List (IntType × Term)} {gs : List Goal},
    slotsGoals ps qs = some gs → (∀ g ∈ gs, g.Holds) → ps.map (den ρ) = qs.map (den ρ)
  | [], [], _, _, _ => rfl
  | p :: ps, q :: qs, gs, h, hg => by
    rcases p with ⟨t, a⟩
    rcases q with ⟨t', b⟩
    simp only [slotsGoals] at h
    split at h
    · rename_i ht
      subst ht
      obtain ⟨gs', hgs', rfl⟩ := Option.map_eq_some_iff.mp h
      by_cases hn : norm t a = norm t b
      · simp only [hn, ite_true] at hg
        have hab : den ρ (t, a) = den ρ (t, b) := by
          simp only [den]
          rw [← ev_norm t a, hn, ev_norm]
        simp [hab, map_den_of_slotsGoals hgs' hg]
      · simp only [hn, ite_false] at hg
        have hab := den_eq_of_goal (ρ := ρ) (a := a) (b := b) t (hg _ List.mem_cons_self)
        have hrest := map_den_of_slotsGoals hgs' (fun g hm => hg g (by simp [hm]))
        simp [hab, hrest]
    · cases h
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [slotsGoals] at h

theorem frameAt_eq {A B : SState} (h : A.locals.map (den ρ) = B.locals.map (den ρ)) (f : Frame) :
    frameAt f ρ A = frameAt f ρ B := by
  have h' := congrArg (List.map some) h
  simp only [List.map_map] at h'
  simp only [frameAt]
  rw [show (fun p => some (den ρ p)) = some ∘ den ρ from rfl, h']

/-- **Equal final states give equivalence.** -/
theorem segEquiv_of_final {lt st : List IntType} {a b : List Instr} {A B : SState}
    (ha : sexec (initState lt st) a = some A) (hb : sexec (initState lt st) b = some B)
    (hl : ∀ ρ : Env, A.locals.map (den ρ) = B.locals.map (den ρ))
    (hs : ∀ ρ : Env, stackAt ρ A = stackAt ρ B) : SegEquiv lt st a b := by
  intro m P H host s f ρ us rest Q
  rw [wp_sexec_iff ha, wp_sexec_iff hb, frameAt_eq (hl ρ) f, hs ρ]

/-- **The equivalence checker is sound.** -/
theorem segEquiv_of_check {lt st : List IntType} {a b : List Instr}
    (h : check lt st a b = true) : SegEquiv lt st a b := by
  unfold check at h
  split at h
  · rename_i A B ha hb
    simp only [stateEq, Bool.and_eq_true] at h
    exact segEquiv_of_final ha hb (fun _ => map_den_of_slotsEq h.1)
      (fun _ => map_den_of_slotsEq h.2)
  · cases h

/-- **Residual goals.** Two segments with the same shape and types are equivalent once
the residual bitvector goals are proved. -/
theorem segEquiv_of_residuals {lt st : List IntType} {a b : List Instr} {gs : List Goal}
    (h : residuals lt st a b = some gs) (hg : ∀ g ∈ gs, g.Holds) : SegEquiv lt st a b := by
  unfold residuals at h
  split at h
  · rename_i A B ha hb
    unfold stateGoals at h
    split at h
    · rename_i g₁ g₂ h₁ h₂
      cases h
      exact segEquiv_of_final ha hb
        (fun _ => map_den_of_slotsGoals h₁ (fun g hm => hg g (List.mem_append_left _ hm)))
        (fun _ => map_den_of_slotsGoals h₂ (fun g hm => hg g (List.mem_append_right _ hm)))
    · cases h
  · cases h

theorem wp_vals_iff {m : Corr} {P : Profile} {H : Type} {host : HostSemantics H}
    {Q : Silmaril.Wasm.Logic.Core.Post H} (s : Store H) (F : Frame) (vs : List Val) :
    Wp m P host s F (vals vs) Q ↔ Q s F (.normal vs) := by
  cases m
  · exact ⟨fun h => HWP.sound_vals h Relation.ReflTransGen.refl, HWP.of_vals⟩
  · refine ⟨fun h => ?_, fun hq => TSafe.exit (.normal vs) rfl hq⟩
    obtain ⟨o, he, hq⟩ := TSafe.exit_of_stuck h (fun _ => not_step_vals)
    exact exits_vals_inv he ▸ hq

/-- **Equal final stacks give equivalence of results.** -/
theorem outEquiv_of_final {lt st : List IntType} {a b : List Instr} {A B : SState}
    (ha : sexec (initState lt st) a = some A) (hb : sexec (initState lt st) b = some B)
    (hs : ∀ ρ : Env, stackAt ρ A = stackAt ρ B) : OutEquiv lt st a b := by
  intro m P H host s f ρ us Q hQ
  rw [wp_sexec_iff ha, wp_sexec_iff hb, List.append_nil, List.append_nil, wp_vals_iff,
    wp_vals_iff, hs ρ]
  exact hQ _ _ _ _ rfl

/-- **The result check is sound.** -/
theorem outEquiv_of_checkOut {lt st : List IntType} {a b : List Instr}
    (h : checkOut lt st a b = true) : OutEquiv lt st a b := by
  unfold checkOut at h
  split at h
  · rename_i A B ha hb
    exact outEquiv_of_final ha hb (fun _ => map_den_of_slotsEq h)
  · cases h

/-- Residual goals for the result check. -/
theorem outEquiv_of_residualsOut {lt st : List IntType} {a b : List Instr} {gs : List Goal}
    (h : residualsOut lt st a b = some gs) (hg : ∀ g ∈ gs, g.Holds) : OutEquiv lt st a b := by
  unfold residualsOut at h
  split at h
  · rename_i A B ha hb
    exact outEquiv_of_final ha hb (fun _ => map_den_of_slotsGoals h hg)
  · cases h

theorem resultPost_blind (mi : ModuleInst) (vs : List Val) : LocalsBlind (resultPost mi vs) := by
  intro s F F' o hm
  simp only [resultPost, hm]

theorem cexAt_spec {lt st : List IntType} {a b : List Instr} {ρ : Env}
    (h : cexAt lt st a b ρ = true) :
    ∃ A B, sexec (initState lt st) a = some A ∧ sexec (initState lt st) b = some B ∧
      differ ρ A B = true := by
  unfold cexAt at h
  split at h
  · exact ⟨_, _, by assumption, by assumption, h⟩
  · cases h

theorem cexAtOut_spec {lt st : List IntType} {a b : List Instr} {ρ : Env}
    (h : cexAtOut lt st a b ρ = true) :
    ∃ A B, sexec (initState lt st) a = some A ∧ sexec (initState lt st) b = some B ∧
      differOut ρ A B = true := by
  unfold cexAtOut at h
  split at h
  · exact ⟨_, _, by assumption, by assumption, h⟩
  · cases h

theorem locals_of_frameAt_eq {A B : SState} {F : Frame} (h : frameAt F ρ B = frameAt F ρ A) :
    B.locals.map (den ρ) = A.locals.map (den ρ) := by
  have h₁ : B.locals.map (fun p => some (den ρ p)) = A.locals.map (fun p => some (den ρ p)) :=
    congrArg Frame.locals h
  have h₂ : (B.locals.map fun p => some (den ρ p)).map (fun o => o.getD (Val.i32 0)) =
      (A.locals.map fun p => some (den ρ p)).map (fun o => o.getD (Val.i32 0)) := by rw [h₁]
  simpa [List.map_map, Function.comp_def] using h₂

/-- What `SegEquiv` says about two final states: from the first, the second segment must
reach the same frame and values (the every-run logic's adequacy, `HWP.sound_vals`). -/
theorem final_eq_of_segEquiv {lt st : List IntType} {a b : List Instr} {A B : SState}
    (heq : SegEquiv lt st a b) (ha : sexec (initState lt st) a = some A)
    (hb : sexec (initState lt st) b = some B) (ρ : Env) :
    frameAt {} ρ B = frameAt {} ρ A ∧ stackAt ρ B = stackAt ρ A := by
  let I := initState lt st
  let Q := exactPost (frameAt {} ρ A) (stackAt ρ A).reverse
  have hwa : Wp .part detP noHost ({} : Store Unit) (frameAt {} ρ I) (codeAt ρ I [] a []) Q := by
    rw [wp_sexec_iff ha]
    simpa using HWP.of_vals (P := detP) (host := noHost) (s := ({} : Store Unit))
      (f := frameAt {} ρ A) (Q := Q) ⟨rfl, rfl⟩
  have hwb : Wp .part detP noHost ({} : Store Unit) (frameAt {} ρ I) (codeAt ρ I [] b []) Q :=
    (heq .part detP noHost {} {} ρ [] [] Q).mp hwa
  have hwb' : HWP detP noHost ({} : Store Unit) (frameAt {} ρ B) (vals (stackAt ρ B).reverse) Q := by
    simpa using (wp_sexec_iff hb {} {} [] []).mp hwb
  have hq : Q {} (frameAt {} ρ B) (.normal (stackAt ρ B).reverse) :=
    HWP.sound_vals hwb' Relation.ReflTransGen.refl
  have hs : stackAt ρ B = stackAt ρ A := by simpa [Q, exactPost] using hq.2
  exact ⟨hq.1, hs⟩

/-- What `OutEquiv` says about two final stacks. -/
theorem stack_eq_of_outEquiv {lt st : List IntType} {a b : List Instr} {A B : SState}
    (heq : OutEquiv lt st a b) (ha : sexec (initState lt st) a = some A)
    (hb : sexec (initState lt st) b = some B) (ρ : Env) : stackAt ρ B = stackAt ρ A := by
  let I := initState lt st
  let Q := resultPost ({} : Frame).module (stackAt ρ A).reverse
  have hwa : Wp .part detP noHost ({} : Store Unit) (frameAt {} ρ I) (codeAt ρ I [] a []) Q := by
    rw [wp_sexec_iff ha]
    simpa using HWP.of_vals (P := detP) (host := noHost) (s := ({} : Store Unit))
      (f := frameAt {} ρ A) (Q := Q) ⟨rfl, rfl⟩
  have hwb : Wp .part detP noHost ({} : Store Unit) (frameAt {} ρ I) (codeAt ρ I [] b []) Q :=
    (heq .part detP noHost {} {} ρ [] Q (resultPost_blind _ _)).mp hwa
  have hwb' : HWP detP noHost ({} : Store Unit) (frameAt {} ρ B) (vals (stackAt ρ B).reverse) Q := by
    simpa using (wp_sexec_iff hb {} {} [] []).mp hwb
  have hq : Q {} (frameAt {} ρ B) (.normal (stackAt ρ B).reverse) :=
    HWP.sound_vals hwb' Relation.ReflTransGen.refl
  simpa [Q, resultPost] using hq.2

/-- **Refutation by a counterexample.** An environment in which the two final states
differ refutes `SegEquiv`. -/
theorem not_segEquiv_of_cex {lt st : List IntType} {a b : List Instr} (ρ : Env)
    (h : cexAt lt st a b ρ = true) : ¬ SegEquiv lt st a b := by
  intro heq
  obtain ⟨A, B, ha, hb, hd⟩ := cexAt_spec h
  obtain ⟨hF, hs⟩ := final_eq_of_segEquiv heq ha hb ρ
  have hl : B.locals.map (den ρ) = A.locals.map (den ρ) := locals_of_frameAt_eq hF
  have hnd : differ ρ A B = false := by simp [differ, hl, hs]
  simp [hnd] at hd

/-- **Refutation of results by a counterexample.** -/
theorem not_outEquiv_of_cex {lt st : List IntType} {a b : List Instr} (ρ : Env)
    (h : cexAtOut lt st a b ρ = true) : ¬ OutEquiv lt st a b := by
  intro heq
  obtain ⟨A, B, ha, hb, hd⟩ := cexAtOut_spec h
  have hs : stackAt ρ B = stackAt ρ A := stack_eq_of_outEquiv heq ha hb ρ
  have hnd : differOut ρ A B = false := by simp [differOut, hs]
  simp [hnd] at hd

end Silmaril.Proofs.Wasm.Auto.Equiv