module

public import Silmaril.Wasm.Binaryen.InlUnwrapRecursiveValues

@[expose] public section

/-! # Escape-free fixed regions preserve free branch targets

Removing a fixed region's wrapper does not expose new branch targets when that
region has none. This guard is essential: original block typing alone does not
suffice, as the typed exit counterexample demonstrates.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {R : List Instr}

private theorem labels_append (x y : List Instr) :
    instrsLabels (x ++ y) = instrsLabels x ++ instrsLabels y := by
  simp only [instrsLabels, List.flatMap_append]

mutual
/-- Structured instruction pairs retain their exact free-label list. -/
theorem UI.labels_eq (regionLabels : instrsLabels R = []) :
    ∀ {i j : Instr}, UI R i j → instrLabels i = instrLabels j
  | _, _, .flat _ => rfl
  | _, _, .block h => by
    simp only [instrLabels_block, UIL.labels_eq regionLabels h]
  | _, _, .loop h => by
    simp only [instrLabels_loop, UIL.labels_eq regionLabels h]
  | _, _, .if_ ht he => by
    simp only [instrLabels_if, UIL.labels_eq regionLabels ht, UIL.labels_eq regionLabels he]
  | _, _, .tryTable h => by
    simp only [instrLabels_tryTable, UIL.labels_eq regionLabels h]
/-- Source unwrapping/folding does not change free targets for an escape-free
fixed region; folding's common tails already have their own `FoldOk` guard. -/
theorem UIL.labels_eq (regionLabels : instrsLabels R = []) :
    ∀ {x y : List Instr}, UIL R x y → instrsLabels x = instrsLabels y
  | _, _, .nil => rfl
  | _, _, .cons h t => by
    simp only [instrsLabels_cons, UI.labels_eq regionLabels h, UIL.labels_eq regionLabels t]
  | _, _, .site bt tail => by
    simp only [instrsLabels_cons, instrLabels_block, labels_append, regionLabels,
      show unbind [] = [] from rfl, List.nil_append, UIL.labels_eq regionLabels tail]
  | _, _, @UIL.fold _ bt T T' E E' X is is' ht he hT hE tail => by
    have hT0 : instrsLabels T = [] ∧ instrsLabels X = [] := by
      apply List.append_eq_nil_iff.mp
      simpa only [labels_append] using hT.2
    have hEpair : instrsLabels E ++ instrsLabels X = [] := by
      simpa only [labels_append] using hE.2
    have hE0 : instrsLabels E = [] := (List.append_eq_nil_iff.mp hEpair).1
    have hT' : instrsLabels T' = [] := (UIL.labels_eq regionLabels ht).symm.trans hT0.1
    have hE' : instrsLabels E' = [] := (UIL.labels_eq regionLabels he).symm.trans hE0
    simp only [instrsLabels_cons, instrLabels_if]
    simpa only [labels_append, hT0.1, hT0.2, hE0, hT', hE',
      List.nil_append, show unbind [] = [] from rfl] using UIL.labels_eq regionLabels tail
end

mutual
/-- Monotonicity of free-target predicates, including runtime contexts. -/
theorem _root_.Silmaril.Wasm.Binaryen.AdmLab.mono {S T : Nat → Prop}
    (imp : ∀ n, S n → T n) : ∀ {a : Admin}, AdmLab S a → AdmLab T a
  | .plain _, h => fun n hn => imp n (h n hn)
  | .label _ _ _, h => ⟨fun n hn => imp n (h.1 n hn),
      AdmsLab.mono (fun n hn => by
        cases n with
        | zero => trivial
        | succ n => exact imp n hn) h.2⟩
  | .handler _ _ _, h => ⟨fun c hc => imp _ (h.1 c hc), AdmsLab.mono imp h.2⟩
  | .ref _, _ => trivial
  | .callRefType _, _ => trivial
  | .returnCallRefType _, _ => trivial
  | .frame _ _ _, _ => trivial
  | .trap, _ => trivial
/-- Sequence form of free-target predicate monotonicity. -/
theorem _root_.Silmaril.Wasm.Binaryen.AdmsLab.mono {S T : Nat → Prop}
    (imp : ∀ n, S n → T n) : ∀ {code : List Admin}, AdmsLab S code → AdmsLab T code
  | [], _ => trivial
  | _ :: _, h => ⟨AdmLab.mono imp h.1, AdmsLab.mono imp h.2⟩
end

private theorem fold_labels_parts {T X : List Instr} (safe : FoldOk (T ++ X)) :
    instrsLabels T = [] ∧ instrsLabels X = [] := by
  apply List.append_eq_nil_iff.mp
  simpa only [labels_append] using safe.2

mutual
/-- Runtime instruction pairs preserve every permitted free-target predicate. -/
theorem UA.admsLab (regionLabels : instrsLabels R = []) :
    ∀ {a b : Admin}, UA R a b → ∀ {S : Nat → Prop}, AdmLab S a → AdmLab S b
  | _, _, .plain related, _, h => by
    simpa only [AdmLab_plain, ← UI.labels_eq regionLabels related] using h
  | _, _, .ref _, _, _ => trivial
  | _, _, .callRef _, _, _ => trivial
  | _, _, .retCallRef _, _, _ => trivial
  | _, _, .label cont body, _, h =>
      ⟨by simpa only [← UIL.labels_eq regionLabels cont] using h.1,
        UL.admsLab regionLabels body h.2⟩
  | _, _, .handler body, _, h => ⟨h.1, UL.admsLab regionLabels body h.2⟩
  | _, _, .frame _, _, _ => trivial
  | _, _, .trap, _, _ => trivial
/-- Removing guarded wrappers cannot expose a new free branch target, including
through running phases and the already guarded folding constructors. -/
theorem UL.admsLab (regionLabels : instrsLabels R = []) :
    ∀ {x y : List Admin}, UL R x y → ∀ {S : Nat → Prop}, AdmsLab S x → AdmsLab S y
  | _, _, .nil, _, _ => trivial
  | _, _, .cons head tail, _, h =>
      ⟨UA.admsLab regionLabels head h.1, UL.admsLab regionLabels tail h.2⟩
  | _, _, .site _ tail, S, h => by
    refine (AdmsLab_append S _ _).mpr ⟨?_, UL.admsLab regionLabels tail h.2⟩
    simp only [AdmsLab_expression, regionLabels, List.not_mem_nil, IsEmpty.forall_iff, forall_const]
  | _, _, .run body safe tail, S, h =>
      (AdmsLab_append S _ _).mpr
        ⟨AdmsLab.mono (fun _ impossible => impossible.elim)
          (UL.admsLab regionLabels body safe.2), UL.admsLab regionLabels tail h.2⟩
  | _, _, @UL.foldIf _ bt T T' E E' X os ns ht he hT hE tail, S, h => by
    have tp : instrsLabels T' = [] := (UIL.labels_eq regionLabels ht).symm.trans (fold_labels_parts hT).1
    have ep : instrsLabels E' = [] := (UIL.labels_eq regionLabels he).symm.trans (fold_labels_parts hE).1
    refine ⟨?_, (AdmsLab_append S _ _).mpr ⟨?_, UL.admsLab regionLabels tail h.2⟩⟩
    · simp only [AdmLab_plain, instrLabels_if, tp, ep, List.nil_append,
        show unbind [] = [] from rfl, List.not_mem_nil, IsEmpty.forall_iff, forall_const]
    · simp only [AdmsLab_expression, (fold_labels_parts hT).2,
        List.not_mem_nil, IsEmpty.forall_iff, forall_const]
  | _, _, @UL.foldBlock _ bt T T' X os ns ht hT tail, S, h => by
    have tp : instrsLabels T' = [] := (UIL.labels_eq regionLabels ht).symm.trans (fold_labels_parts hT).1
    refine ⟨?_, (AdmsLab_append S _ _).mpr ⟨?_, UL.admsLab regionLabels tail h.2⟩⟩
    · simp only [AdmLab_plain, instrLabels_block, tp,
        show unbind [] = [] from rfl, List.not_mem_nil, IsEmpty.forall_iff, forall_const]
    · simp only [AdmsLab_expression, (fold_labels_parts hT).2,
        List.not_mem_nil, IsEmpty.forall_iff, forall_const]
  | _, _, .foldLabel body safe _ tail, S, h => by
    obtain ⟨c, xa⟩ := (AdmsLab_append _ _ _).mp safe.2
    refine ⟨⟨by simp, ?_⟩, (AdmsLab_append S _ _).mpr ⟨?_, UL.admsLab regionLabels tail h.2⟩⟩
    · exact AdmsLab.mono (fun _ impossible => impossible.elim) (UL.admsLab regionLabels body c)
    · exact AdmsLab.mono (fun _ impossible => impossible.elim) xa
  | _, _, .foldExit kernel tail, S, h => by
    refine (AdmsLab_append S _ _).mpr ⟨?_, UL.admsLab regionLabels tail h.2⟩
    rcases kernel with rfl | ⟨a, rfl⟩
    · simp
    · simp [instrLabels]
end

end Silmaril.Wasm.Binaryen.Unwrap
