module

public import Silmaril.SSA.Peggy.Bridge.Equational.Compiler

public section

namespace Silmaril.SSA.Peggy.Bridge.Equational.Proofs

open Silmaril.Logic.Algebraic
open RVSDG (Tuple)

set_option backward.isDefEq.respectTransparency false

variable {S : Type} {A : ManySorted.Signature S} {k n : Nat} {Γ : Fin k → S}
variable {rows : Fin n → Occurrence A Γ} {i : Fin n} {s : S}

@[simp] theorem get_pack {F : PEG.Ty S → Type} {arity : Nat} (w : Fin arity → S)
    (f : ∀ j, F (.data (w j))) (j : Fin arity) : (pack w f).get (port w j) = f j := by
  induction arity with
  | zero => exact j.elim0
  | succ arity ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · exact ih _ _ j

private theorem all_pack {F : PEG.Ty S → Type} {arity : Nat} (w : Fin arity → S)
    (f : ∀ j, F (.data (w j))) (p : ∀ {t}, F t → Prop) (h : ∀ j, p (f j))
    (j : Fin (profile w).length) : p ((pack w f).get (PEG.portAt _ j)) := by
  induction arity with
  | zero => exact j.elim0
  | succ arity ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact h 0
    · exact ih _ _ (fun j => h j.succ) j

private theorem collect_pack {F G : PEG.Ty S → Type} {arity : Nat} (w : Fin arity → S)
    (f : ∀ j, F (.data (w j))) (g : ∀ j, G (.data (w j)))
    (read : ∀ {t}, F t → Option (G t)) (h : ∀ j, read (f j) = some (g j)) :
    PEG.collect (profile w) (fun j => read ((pack w f).get (PEG.portAt _ j))) = some (pack w g) := by
  induction arity with
  | zero => rfl
  | succ arity ih =>
    let input (j : Fin ((profile (w ∘ Fin.succ)).length + 1)) :
        Option (G (.data (w 0) :: profile (w ∘ Fin.succ))[j]) :=
      read ((pack w f).get (PEG.portAt (.data (w 0) :: profile (w ∘ Fin.succ)) j))
    have head : input 0 = some (g 0) := h 0
    have tail : PEG.collect (profile (w ∘ Fin.succ)) (fun j => input j.succ) =
        some (pack (w ∘ Fin.succ) (fun j => g j.succ)) :=
      ih (w ∘ Fin.succ) (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ)
    change PEG.collect (.data (w 0) :: profile (w ∘ Fin.succ)) input = _
    rw [PEG.collect, head, tail]
    rfl

private theorem wiring_forward {t : ManySorted.Term A Γ s} (w : Wiring rows i t)
    (j : Fin w.node.inputs.length) : i.val < (w.node.arg j).id.val := by
  cases t with
  | var v => exact j.elim0
  | app op args =>
    exact all_pack _ (fun j => (w.children j).ref) (fun r => i.val < r.id.val)
      (fun j => (w.children j).after) j

theorem wellFormed {t : ManySorted.Term A Γ s} (code : Numbered t) : code.graph.WellFormed where
  forest := fun i => i.elim0
  feedback := by
    intro a ks path nonempty
    have increase : ∀ {a b kind}, code.graph.Edge a kind b →
        code.tailSize - b.val < code.tailSize - a.val := by
      rintro a b kind ⟨slot, _, rfl⟩
      have h : a.val < ((code.graph.node a).arg slot).id.val := wiring_forward (code.wiring a) slot
      have hb := ((code.graph.node a).arg slot).id.isLt
      omega
    exact (Nat.lt_irrefl _ (path.strictRank nonempty (fun i => code.tailSize - i.val)
      (fun edge _ => increase edge))).elim
  loopScope := fun _ _ _ i => i.elim0
  outerFeedback := fun _ _ _ _ _ i => i.elim0

variable (m : TotalPrimitiveModel ((signature S).obj A)) (env : Tuple m.val.Value (profile Γ))

abbrev assignment (j : Fin k) : (algebra m).carrier (Γ j) := env.get (port Γ j)

private theorem read_occurrence {a b : Occurrence A Γ} (h : a = b) :
    (show Option (m.val.Value (.data b.1)) from
      congrArg (fun (t : Occurrence A Γ) => PEG.Ty.data t.1) h ▸
        (some ((algebra m).eval (assignment m env) a.2) : Option (m.val.Value (.data a.1)))) =
        some ((algebra m).eval (assignment m env) b.2) := by
  cases h
  rfl

private theorem read_child {t : ManySorted.Term A Γ s} (c : Child rows i ⟨s, t⟩) :
    c.ref.read m.val.carrier (some ((algebra m).eval (assignment m env) (rows c.id).2)) =
      some ((algebra m).eval (assignment m env) t) := by
  exact read_occurrence m env c.term_eq

private theorem node_interpret {t : ManySorted.Term A Γ s} (w : Wiring rows i t)
    (idx : PEG.Index 0) :
    w.node.label.interpret m.val env idx (fun j _ _ =>
      let c := w.node.arg j
      c.read m.val.carrier (some ((algebra m).eval (assignment m env) (rows c.id).2))) =
      some ((algebra m).eval (assignment m env) t) := by
  cases t with
  | var v => rfl
  | @app arity inputs out op args =>
    let read {ty} (c : PEG.Ref (rowSort rows) ty) : Option (m.val.Value ty) :=
      c.read m.val.carrier (some ((algebra m).eval (assignment m env) (rows c.id).2))
    have collected := collect_pack (F := PEG.Ref (rowSort rows)) (G := m.val.Value) inputs (fun j => (w.children j).ref)
      (fun j => (algebra m).eval (assignment m env) (args j)) (@read)
      (fun j => read_child m env (w.children j))
    change (PEG.collect (profile inputs)
      (fun j => read ((pack inputs (fun j => (w.children j).ref)).get (PEG.portAt _ j)))).elim
        none (m.val.run (.app op)) = _
    rw [collected]
    exact (Option.some_get (m.property _ _)).symm

theorem observe {t : ManySorted.Term A Γ s} (code : Numbered t)
    (wf : WellFounded code.graph.Demand) (idx : PEG.Index 0) :
    code.graph.observe m.val (code.graph.denote m.val env wf) idx =
      .cons (some ((algebra m).eval (assignment m env) t)) .nil := by
  let values : code.graph.Valuation m.val := fun q =>
    some ((algebra m).eval (assignment m env) (code.rows q.1).2)
  have solves : code.graph.Solves m.val env values := fun q =>
    (node_interpret m env (code.wiring q.1) q.2).symm
  rw [code.graph.solves_unique m.val env wf (code.graph.denote_solves m.val env wf) solves]
  unfold PEG.Graph.observe
  change (Tuple.cons _ Tuple.nil : Tuple (fun ty => Option (m.val.Value ty)) [.data s]) = _
  exact congrArg (fun v => Tuple.cons v Tuple.nil) (read_occurrence m env code.root)

end Silmaril.SSA.Peggy.Bridge.Equational.Proofs
