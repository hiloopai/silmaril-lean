module

public import Silmaril.Logic.ACL2.Recursive.Institution.Defs
public import Silmaril.Logic.ACL2.Recursive.Thms
import Silmaril.Logic.ACL2.Books.Thms

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Recursive.Institution

open CategoryTheory Silmaril.Logic.ACL2 Silmaril.Logic.ACL2.Recursive

variable {P : Presentation} {W : World} {B : Block W.signature}
  {fresh : B.TheoremNamesFresh W}

theorem equation_mem (B : Block P.signature) {k : Nat} (f : B.members.Symbol k) :
    B.equation f ∈ (B.extendPresentation P).equations :=
  ⟨k, B.symbol f, (B.body f).toTerm B, by simp [Block.extendPresentation, Block.symbol, f.property],
    rfl⟩

theorem equations (B : Block P.signature) :
    (B.extendPresentation P).equations =
      Sentence.map B.inclusion '' P.equations ∪
        {p | ∃ (k : Nat) (f : B.members.Symbol k), p = B.equation f} := by
  ext p
  constructor
  · rintro ⟨k, f, t, ht, rfl⟩
    by_cases hm : B.members.arity f.val = some k
    · let member : B.members.Symbol k := ⟨f.val, hm⟩
      have hf : f = B.symbol member := Subtype.ext rfl
      have ht' : t = (B.body member).toTerm B := Option.some.inj (by
        simpa only [Block.extendPresentation, dite_eq_left hm] using ht.symm)
      exact Or.inr ⟨k, member, by rw [hf, ht']; rfl⟩
    · have oldArity : P.signature.arity f.val = some k := by
        have hf := f.property
        cases he : B.members.arity f.val <;> simp_all [Block.extendPresentation, Block.signature]
      let old : P.signature.Symbol k := ⟨f.val, oldArity⟩
      have ht' : (P.body old).map (Term.map B.inclusion) = some t := by
        simpa only [Block.extendPresentation, dite_eq_right hm] using ht
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp ht'
      have hf : B.inclusion.symbol old = f := Subtype.ext rfl
      exact Or.inl ⟨definitionEquation old u, ⟨k, old, u, hu, rfl⟩,
        by
          rw [definitionEquation_map, hf]
          rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨k, f, rfl⟩)
    · exact Presentation.equations_map (B.presentationHom P) hq
    · exact equation_mem B f

theorem extendWorld_checked (hW : W.Checked) : (B.extendWorld W fresh).Checked := by
  rintro p ⟨name, hp⟩
  change (W.theoremAt name).map (Sentence.map B.inclusion) = some p at hp
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
  exact ((hW q ⟨name, hq⟩).map B.inclusion).weaken
    (Set.image_subset_iff.mpr (Presentation.equations_map (B.presentationHom W.presentation)))

theorem modelBy_models {M : Model W.signature}
    {lt : Call B.members M.primitives.Value → Call B.members M.primitives.Value → Prop}
    (wf : WellFounded lt) (h : B.TerminatesBy M lt) (hM : W.Models M) :
    (B.extendWorld W fresh).Models (B.modelBy M wf h) := by
  have mapped (q : Sentence W.signature) (hq : q ∈ W.theory) :
      (q.map B.inclusion).Holds (B.modelBy M wf h) := by
    apply (q.holds_map B.inclusion _).mpr
    rw [B.modelBy_reduct wf h]
    exact hM q hq
  rintro p (hp | ⟨name, hp⟩)
  · change p ∈ (B.extendPresentation W.presentation).equations at hp
    rw [equations B] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨_, f, rfl⟩
    · exact mapped q (Or.inl hq)
    · exact B.equation_holdsBy wf h f
  · change (W.theoremAt name).map (Sentence.map B.inclusion) = some p at hp
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact mapped q (Or.inr ⟨name, hq⟩)

theorem entails_iff
    (terminates : ∀ M : Model W.signature, W.Models M →
      ∃ lt : Call B.members M.primitives.Value → Call B.members M.primitives.Value → Prop,
        WellFounded lt ∧ B.TerminatesBy M lt)
    (p : Sentence W.signature) :
    (B.extendWorld W fresh).Entails (p.map B.inclusion) ↔ W.Entails p := by
  constructor
  · intro extended M hM
    obtain ⟨lt, wf, h⟩ := terminates M hM
    have holds := (p.holds_map B.inclusion _).mp (extended _ (modelBy_models (fresh := fresh) wf h hM))
    rwa [B.modelBy_reduct wf h] at holds
  · intro old N hN
    exact (p.holds_map B.inclusion N).mpr (old _ ((B.worldExtension W fresh).models_reduct hN))

end Silmaril.Proofs.Logic.ACL2.Recursive.Institution
