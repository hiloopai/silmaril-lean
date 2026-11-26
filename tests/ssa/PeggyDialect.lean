module

import Silmaril.SSA.Peggy.Dialect.Thms

namespace Silmaril.SSA.Peggy.Dialect.Tests

open CategoryTheory
open PEG (EdgeKind Graph LoopForest Ref Ty Walk)

private abbrev value : Ty Unit := .data ()

private inductive SourceOp : List (Ty Unit) → Ty Unit → Type where
  | step : SourceOp [value] value
  | alternate : SourceOp [value] value

private inductive MiddleOp : List (Ty Unit) → Ty Unit → Type where
  | tick : MiddleOp [value] value

private inductive TargetOp : List (Ty Unit) → Ty Unit → Type where
  | advance : TargetOp [value] value

private def source : FixedSortSignature Unit := ⟨SourceOp⟩
private def middle : FixedSortSignature Unit := ⟨MiddleOp⟩
private def target : FixedSortSignature Unit := ⟨TargetOp⟩

private def identify : source ⟶ middle :=
  FixedSortSignature.ofOpcodeMap fun
    | .step | .alternate => .tick

private def rename : middle ⟶ target :=
  FixedSortSignature.ofOpcodeMap fun
    | .tick => .advance

private def frame : LoopForest 1 := ⟨fun _ => none⟩
private def sorts : Fin 3 → Ty Unit := fun _ => value
private def ref (i : Fin 3) : Ref sorts value := Ref.ofId sorts i

/-- One parameter initializes a theta; the opcode result feeds its next iteration. -/
private def recurrence (op : SourceOp [value] value) : Graph SourceOp [value] [value, value] 3 1 where
  forest := frame
  sort := sorts
  node i := match i with
    | 0 => .ofLabel (.param .head) .nil
    | 1 => .ofLabel (.theta 0) (.cons (ref 0) (.cons (ref 2) .nil))
    | 2 => .ofLabel (.op op) (.cons (ref 1) .nil)
  roots := .cons (ref 1) (.cons (ref 1) .nil)

private theorem edgeFacts {op : SourceOp [value] value} {a b : Fin 3} {k : EdgeKind (Fin 1)}
    (h : (recurrence op).Edge a k b) : (¬ k.IsFeedback → b.val < a.val) ∧
      ∀ l, ¬ k.IsObserverAt l := by
  have localFacts : ∀ (a : Fin 3) (i : Fin ((recurrence op).node a).inputs.length),
      let k := ((recurrence op).node a).label.kind i
      let b := ((recurrence op).node a).arg i
      (¬ k.IsFeedback → b.id.val < a.val) ∧ ∀ l, ¬ k.IsObserverAt l := by
    cases op <;> (unfold EdgeKind.IsObserverAt; decide)
  obtain ⟨i, rfl, rfl⟩ := h
  exact localFacts a i

private theorem noObserver {op : SourceOp [value] value} {a b : Fin 3} {ks : List (EdgeKind (Fin 1))}
    (walk : Walk (recurrence op).Edge a ks b) : ∀ k ∈ ks, ∀ l, ¬ k.IsObserverAt l := by
  induction walk with
  | nil => simp
  | cons edge _ ih =>
    intro k hk l
    rcases List.mem_cons.mp hk with rfl | tail
    · exact (edgeFacts edge).2 l
    · exact ih k tail l

private theorem admitted (op : SourceOp [value] value) : (recurrence op).WellFormed where
  forest := by
    intro i
    rintro ⟨ks, walk, nonempty⟩
    cases walk with
    | nil => exact nonempty rfl
    | cons edge _ => cases edge
  feedback := by
    intro a ks walk nonempty
    by_contra absent
    exact (Nat.lt_irrefl a.val) (walk.strictRank nonempty Fin.val
      (fun e hk => (edgeFacts e).1 (fun h => absent ⟨_, hk, h⟩)))
  loopScope := by
    intro a b ks start target walk ha hb
    have same : target = start := Subsingleton.elim _ _
    subst target
    exact .inl ⟨[], .nil start⟩
  outerFeedback := fun _ _ walk k hk l observer => (noObserver walk k hk l observer).elim

private def equation : Equation source where
  params := [value]
  results := [value, value]
  loops := 1
  forest := frame
  leftNodes := 3
  rightNodes := 3
  lhs := ⟨recurrence .step, rfl, admitted .step⟩
  rhs := ⟨recurrence .alternate, rfl, admitted .alternate⟩

example : (equation.lhs.graph.node ⟨2, by decide⟩).label = .op SourceOp.step := rfl
example : (equation.rhs.graph.node ⟨2, by decide⟩).label = .op SourceOp.alternate := rfl

example : ((equation.map identify).lhs.graph.node ⟨2, by decide⟩).label = .op MiddleOp.tick := rfl
example : ((equation.map identify).rhs.graph.node ⟨2, by decide⟩).label = .op MiddleOp.tick := rfl

example : (sentenceFunctor Unit).map (𝟙 source) equation = equation :=
  Equation.map_id source equation

example : (sentenceFunctor Unit).map (identify ≫ rename) equation =
    (equation.map identify).map rename :=
  Equation.map_comp identify rename equation

private def translated : Equation target := (sentenceFunctor Unit).map (identify ≫ rename) equation

example : (translated.lhs.graph.node ⟨2, by decide⟩).label = .op TargetOp.advance := rfl
example : (translated.lhs.graph.node ⟨1, by decide⟩).label = .theta ⟨0, by decide⟩ := rfl
example : PEG.refNumbers (translated.lhs.graph.node ⟨1, by decide⟩).args = [0, 2] := rfl
example : PEG.refNumbers translated.lhs.graph.roots = [1, 1] := rfl
example : translated.lhs.graph.forest = frame := translated.lhs.forest_eq
example : translated.lhs.graph.WellFormed := translated.lhs.wellFormed

end Silmaril.SSA.Peggy.Dialect.Tests
