module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.CoHom
public import Silmaril.Wasm.SpecTec.Institution.Juxt.Defs

/-!
# The full grammar comorphism into whole SpecTec specifications

`fullCoHom f` followed by `Institution.grammarInclusion` (grammars as a sub-institution of whole
scripts, `juxt (inst backend) G`) is a comorphism from the grammar institution over `A`,
productions included, into whole specifications whose grammar part is `instIn B f.toFun D`
(`wholeCoHom`). Its satisfaction condition is the composite of the two. `grammarInclusion` is
model-expansive (a grammar model extends by the empty relational model), so consequence is
preserved and reflected (`wholeCoHom_entails_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open CategoryTheory
open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec.Grammar

variable {α β : Type} {A : Attr α} {B : Attr β}

/-- The relational model of the empty signature: nothing is declared and nothing holds. -/
def emptyRelModel : Institution.Model Institution.Sig.empty where
  env := Silmaril.SpecTec.Sem.Env.empty
  D := fun _ _ _ _ => False
  typs_def _ hx := hx.elim
  funs_def _ hf := hf.elim
  vanish _ _ _ _ h := h.elim

/-- **Grammars embed model-expansively into whole specifications.** -/
theorem grammarInclusion_modelExpansive (G : Inst.{1, 0, 0, 0, 0}) :
    (Institution.grammarInclusion G).ModelExpansive := by
  intro S M
  exact ⟨(Discrete.mk emptyRelModel, M), rfl⟩

/-- **The full comorphism into whole SpecTec specifications.** -/
def wholeCoHom (f : AttrHom A B) (D : Type) :
    Inst.CoHom (inst A D) (Institution.withGrammars (instIn B f.toFun D)) :=
  (fullCoHom f D).comp (Institution.grammarInclusion _)

/-- **Borrowing along the whole comorphism**: an `A`-grammar theory entails a sentence iff its
translation entails the translated sentence in whole SpecTec specifications (at the empty
relational signature, with grammar models supported on the image of `f`). -/
theorem wholeCoHom_entails_iff (f : AttrHom A B) (D : Type) (S : Sig D) (Γ : Set (Sen S.N α))
    (φ : Sen S.N α) :
    (room A S.N).Entails Γ φ ↔
      ((Institution.withGrammars (instIn B f.toFun D)).I.obj (Institution.Sig.empty, S)).Entails
        (Sum.inr '' (mapSen f '' Γ)) (Sum.inr (mapSen f φ)) := by
  rw [fullCoHom_entails_iff f Γ φ]
  exact (Institution.grammarInclusion (instIn B f.toFun D)).entails_iff
    (grammarInclusion_modelExpansive _) S _ _

/-- The instance at `lebHom`: `lebAlg` grammars into whole SpecTec specifications. -/
noncomputable def lebWholeCoHom (D : Type) :
    Inst.CoHom (inst lebAlg D)
      (Institution.withGrammars (instIn Silmaril.SpecTec.Sem.actAlg lebHom.toFun D)) :=
  wholeCoHom lebHom D

end Silmaril.Wasm.SpecTec.GrammarInst
