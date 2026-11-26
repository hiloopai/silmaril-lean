module

public import Silmaril.SSA.Peggy.Bridge.Equational.Translation
import Silmaril.Proofs.SSA.Peggy.Bridge.Equational.Naturality
import Silmaril.Proofs.SSA.Peggy.Bridge.Equational.Semantics

public section

namespace Silmaril.SSA.Peggy.Bridge.Equational.Proofs

open CategoryTheory Silmaril.Logic.Algebraic
open RVSDG (Tuple)

set_option backward.isDefEq.respectTransparency false

variable {S : Type} {A B : ManySorted.Signature S} {k : Nat} {Γ : Fin k → S} {s : S}

private theorem openGraph_heq {n n' : Nat} (h : n = n')
    (g : Dialect.OpenGraph (Opcode A) (profile Γ) [.data s] n emptyForest)
    (g' : Dialect.OpenGraph (Opcode A) (profile Γ) [.data s] n' emptyForest)
    (graphs : HEq g.graph g'.graph) : HEq g g' := by
  subst n'
  exact heq_of_eq (Dialect.OpenGraph.ext (eq_of_heq graphs))

theorem compileTerm_map (f : A ⟶ B) (t : ManySorted.Term A Γ s) :
    compileTerm (ManySorted.Term.map f t) =
      ⟨(compileTerm t).1, (compileTerm t).2.map (mapOpcode f)⟩ := by
  have size : (compileTerm (ManySorted.Term.map f t)).1 = (compileTerm t).1 :=
    congrArg Nat.succ (size_map f t)
  exact Sigma.ext size (openGraph_heq size _ _ (graph_map f t))

theorem compileEquation_map (f : A ⟶ B) (e : ManySorted.Equation A) :
    compileEquation (ManySorted.Equation.map f e) = (compileEquation e).map ((signature S).map f) :=
  congrArg₂ equationOf (compileTerm_map f e.lhs) (compileTerm_map f e.rhs)

variable (m : TotalPrimitiveModel ((signature S).obj A))

theorem observe_compileTerm (t : ManySorted.Term A Γ s) (env : Tuple m.val.Value (profile Γ))
    (idx : PEG.Index 0) :
    (compileTerm t).2.observe m.val env idx =
      .cons (some ((algebra m).eval (fun j => env.get (port Γ j)) t)) .nil :=
  observe m env (Numbered.compile t) _ idx

theorem exact_satisfaction (e : ManySorted.Equation A) :
    (compileEquation e).Holds m.val ↔ e.Satisfies (algebra m) := by
  constructor
  · intro h ρ
    have equal := h (pack e.context ρ) Fin.elim0
    change (compileTerm e.lhs).2.observe m.val (pack e.context ρ) Fin.elim0 =
      (compileTerm e.rhs).2.observe m.val (pack e.context ρ) Fin.elim0 at equal
    rw [observe_compileTerm, observe_compileTerm] at equal
    have root := congrArg (fun (xs : Tuple (fun ty => Option (m.val.Value ty)) [.data e.sort]) =>
      xs.get .head) equal
    exact Option.some.inj (by simpa only [get_pack, Tuple.get] using root)
  · intro h env idx
    change (compileTerm e.lhs).2.observe m.val env idx = (compileTerm e.rhs).2.observe m.val env idx
    rw [observe_compileTerm, observe_compileTerm]
    exact congrArg (fun x : (algebra m).carrier e.sort =>
      (Tuple.cons (some x) Tuple.nil : Tuple (fun ty => Option (m.val.Value ty)) [.data e.sort])) (h _)

theorem algebraFunctor_natural (f : A ⟶ B) :
    algebraFunctor B ⋙ ManySorted.Signature.Hom.reductFunctor f =
      Silmaril.Inst.Disc.functor (totalPrimitiveReduct ((signature S).map f)) ⋙ algebraFunctor A := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro m
    rfl
  · intro M N h
    rcases h with ⟨rfl⟩
    rfl

theorem algebra_expand (M : ManySorted.Model A) : algebra (expand M) = M := by
  cases M with
  | mk carrier operation =>
    apply congrArg (ManySorted.Model.mk carrier)
    funext arity inputs out op args
    change operation op (fun j => (pack (F := PEG.Ty.Value carrier) inputs args).get (port inputs j)) =
      operation op args
    simp only [get_pack]

end Silmaril.SSA.Peggy.Bridge.Equational.Proofs
