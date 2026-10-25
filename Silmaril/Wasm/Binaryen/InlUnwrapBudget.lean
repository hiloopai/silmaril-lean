module

public import Silmaril.Wasm.Binaryen.InlUnwrapLabels

@[expose] public section

/-! # Guarded unwrap preserves the escape-free runtime invariant

The budget component may forget its branch predicate, since `AdmsLab` separately
retains exact free-target safety. Together these components preserve `NoEsc`
through recursive runtime and related-callee phases of `UL`.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {R : List Instr}

private theorem all_shift {T : Nat → Prop} (all : ∀ n, T n) : ∀ n, shiftP T n
  | 0 => trivial
  | n + 1 => all n

mutual
/-- A fully permissive target branch predicate retains all nonbranch budgets. -/
theorem _root_.Silmaril.Wasm.Binaryen.AdmB.restrict_all {b : Bud} {S T : Nat → Prop}
    (all : ∀ n, T n) : ∀ {a : Admin}, AdmB b S a → AdmB b T a
  | .plain _, h => InstrB.restrict h (fun n _ => all n)
  | .label _ _ _, h => ⟨fun j hj => InstrB.restrict (h.1 j hj) (fun n _ => all n),
      AdmsB.restrict_all (all_shift all) h.2⟩
  | .handler _ _ _, h => h.elim
  | .ref _, _ => trivial
  | .callRefType _, h => h
  | .returnCallRefType _, h => h.elim
  | .frame _ _ _, h => h
  | .trap, h => h
/-- Sequence form of retaining a budget with unrestricted target branches. -/
theorem _root_.Silmaril.Wasm.Binaryen.AdmsB.restrict_all {b : Bud} {S T : Nat → Prop}
    (all : ∀ n, T n) : ∀ {code : List Admin}, AdmsB b S code → AdmsB b T code
  | [], _ => trivial
  | _ :: _, h => ⟨AdmB.restrict_all all h.1, AdmsB.restrict_all all h.2⟩
end

mutual
/-- Structural source pairs retain the unwrap budget. -/
theorem UI.budget (regionBudget : ∃ S, ∀ j ∈ R, InstrB budU S j) :
    ∀ {i j : Instr}, UI R i j → ∀ {S T : Nat → Prop}, (∀ n, T n) →
      InstrB budU S i → InstrB budU T j
  | _, _, .flat _, _, _, all, h => InstrB.restrict h (fun n _ => all n)
  | _, _, .block body, _, _, all, h =>
      .block (UIL.budget regionBudget body (all_shift all) (InstrB_block_iff.mp h))
  | _, _, .loop body, _, _, all, h =>
      .loop (InstrB_loop_iff.mp h).1
        (UIL.budget regionBudget body (all_shift all) (InstrB_loop_iff.mp h).2)
  | _, _, .if_ yes no, _, _, all, h =>
      .if_ (UIL.budget regionBudget yes (all_shift all) (InstrB_if_iff.mp h).1)
        (UIL.budget regionBudget no (all_shift all) (InstrB_if_iff.mp h).2)
  | _, _, .tryTable _, _, _, _, h => by cases h with | flat h => cases h
termination_by structural _ _ related _ _ _ _ => related
/-- A fixed region within `budU` can be exposed without introducing a return,
tail call, handler or other operation forbidden by that budget. -/
theorem UIL.budget (regionBudget : ∃ S, ∀ j ∈ R, InstrB budU S j) :
    ∀ {x y : List Instr}, UIL R x y → ∀ {S T : Nat → Prop}, (∀ n, T n) →
      (∀ i ∈ x, InstrB budU S i) → ∀ j ∈ y, InstrB budU T j
  | _, _, .nil, _, _, _, _ => by intro j hj; cases hj
  | _, _, .cons head tail, _, _, all, h => by
    have first := UI.budget regionBudget head all (h _ (List.mem_cons_self))
    have rest := UIL.budget regionBudget tail all (fun i hi => h i (List.mem_cons_of_mem _ hi))
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact first
    · exact rest j hj
  | _, _, .site _ tail, _, _, all, h => by
    intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨S, budget⟩ := regionBudget
      exact InstrB.restrict (budget j hj) (fun n _ => all n)
    · exact UIL.budget regionBudget tail all (fun i hi => h i (List.mem_cons_of_mem _ hi)) j hj
  | _, _, @UIL.fold _ bt A A' E E' X is is' yes no hA _ tail, _, T, all, h => by
    have arms := InstrB_if_iff.mp (h (.if_ bt (A ++ X) (E ++ X)) (List.mem_cons_self))
    have first : InstrB budU T (.if_ bt A' E') :=
      .if_ (UIL.budget regionBudget yes (all_shift all)
        (fun i hi => arms.1 i (List.mem_append_left _ hi)))
        (UIL.budget regionBudget no (all_shift all)
          (fun i hi => arms.2 i (List.mem_append_left _ hi)))
    have rest := UIL.budget regionBudget tail all (fun i hi => h i (List.mem_cons_of_mem _ hi))
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact first
    · rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨S, budget⟩ := hA.1
        exact InstrB.restrict (budget j (List.mem_append_right _ hj)) (fun n _ => all n)
      · exact rest j hj
termination_by structural _ _ related _ _ _ _ => related
end

mutual
/-- Administrative heads retain nonbranch budget restrictions. -/
theorem UA.budget (regionBudget : ∃ S, ∀ j ∈ R, InstrB budU S j) :
    ∀ {a b : Admin}, UA R a b → ∀ {S T : Nat → Prop}, (∀ n, T n) →
      AdmB budU S a → AdmB budU T b
  | _, _, .plain related, _, _, all, h => UI.budget regionBudget related all h
  | _, _, .ref _, _, _, _, _ => trivial
  | _, _, .callRef _, _, _, _, h => h
  | _, _, .retCallRef _, _, _, _, h => h.elim
  | _, _, .label cont body, _, _, all, h =>
      ⟨UIL.budget regionBudget cont all h.1, UL.budget regionBudget body (all_shift all) h.2⟩
  | _, _, .handler _, _, _, _, h => h.elim
  | _, _, .frame _, _, _, _, h => h
  | _, _, .trap, _, _, _, h => h
/-- Running wrappers and guarded folding preserve the fixed unwrap budget. -/
theorem UL.budget (regionBudget : ∃ S, ∀ j ∈ R, InstrB budU S j) :
    ∀ {x y : List Admin}, UL R x y → ∀ {S T : Nat → Prop}, (∀ n, T n) →
      AdmsB budU S x → AdmsB budU T y
  | _, _, .nil, _, _, _, _ => trivial
  | _, _, .cons head tail, _, _, all, h =>
      ⟨UA.budget regionBudget head all h.1, UL.budget regionBudget tail all h.2⟩
  | _, _, .site _ tail, _, _, all, h => by
    refine (AdmsB_append _ _).mpr ⟨?_, UL.budget regionBudget tail all h.2⟩
    rw [AdmsB_expression]
    obtain ⟨S, budget⟩ := regionBudget
    exact fun j hj => InstrB.restrict (budget j hj) (fun n _ => all n)
  | _, _, .run body _ tail, _, _, all, h =>
      (AdmsB_append _ _).mpr ⟨UL.budget regionBudget body all h.1.2,
        UL.budget regionBudget tail all h.2⟩
  | _, _, @UL.foldIf _ bt A A' E E' X os ns yes no hA _ tail, _, _, all, h => by
    have arms := InstrB_if_iff.mp h.1
    refine ⟨InstrB.if_ (UIL.budget regionBudget yes (all_shift all)
      (fun i hi => arms.1 i (List.mem_append_left _ hi)))
      (UIL.budget regionBudget no (all_shift all)
        (fun i hi => arms.2 i (List.mem_append_left _ hi))),
      (AdmsB_append _ _).mpr ⟨?_, UL.budget regionBudget tail all h.2⟩⟩
    rw [AdmsB_expression]
    obtain ⟨S, budget⟩ := hA.1
    exact fun j hj => InstrB.restrict (budget j (List.mem_append_right _ hj)) (fun n _ => all n)
  | _, _, @UL.foldBlock _ bt A A' X os ns body hA tail, _, _, all, h => by
    have arm := InstrB_block_iff.mp h.1
    refine ⟨InstrB.block (UIL.budget regionBudget body (all_shift all)
      (fun i hi => arm i (List.mem_append_left _ hi))),
      (AdmsB_append _ _).mpr ⟨?_, UL.budget regionBudget tail all h.2⟩⟩
    rw [AdmsB_expression]
    obtain ⟨S, budget⟩ := hA.1
    exact fun j hj => InstrB.restrict (budget j (List.mem_append_right _ hj)) (fun n _ => all n)
  | _, _, .foldLabel body _ _ tail, _, _, all, h => by
    obtain ⟨c, xa⟩ := (AdmsB_append _ _).mp h.1.2
    exact ⟨⟨by simp, UL.budget regionBudget body (all_shift all) c⟩,
      (AdmsB_append _ _).mpr ⟨AdmsB.restrict_all all xa, UL.budget regionBudget tail all h.2⟩⟩
  | _, _, .foldExit kernel tail, _, _, all, h => by
    refine (AdmsB_append _ _).mpr ⟨?_, UL.budget regionBudget tail all h.2⟩
    rcases kernel with rfl | ⟨a, rfl⟩
    · simp [budU]
    · exact ⟨trivial, ⟨.flat trivial, trivial⟩⟩
end

/-- Guarded reverse phases retain an isolated region's full escape-free
invariant, which excludes branches, returns and tail calls exposed by `.run`. -/
theorem UL.noEsc (regionBudget : ∃ S, ∀ j ∈ R, InstrB budU S j)
    (regionLabels : instrsLabels R = []) {x y : List Admin}
    (related : UL R x y) (safe : NoEsc x) : NoEsc y := by
  obtain ⟨⟨S, budget⟩, labels⟩ := safe
  exact ⟨⟨fun _ => True, UL.budget regionBudget related (fun _ => trivial) budget⟩,
    UL.admsLab regionLabels related labels⟩

end Silmaril.Wasm.Binaryen.Unwrap
