module

public import Silmaril.Logic.HOLLight.Logic
public import Silmaril.Logic.HOLLight.Semantics.Substitution
public import Silmaril.Logic.HOLLight.Semantics.Boolean

@[expose] public section

/-! # Interpreting the defined logical vocabulary -/

namespace Silmaril.Logic.HOLLight

universe u

namespace Eval

variable {sig : Signature} {M : Model.{u} sig} {ρ : TypeValuation.{u}}
  {ν : FreeEnv M ρ} {Γ : List Ty} {η : BoundEnv M ρ Γ}
  {A B : Ty} {s t p q f : Tm}

theorem equal {x y : Value M ρ A} (hs : Eval M ρ ν η s A x) (ht : Eval M ρ ν η t A y) :
    Eval M ρ ν η (Tm.equal A s t) .bool (Carrier.eq (A.denote M.toTypeModel ρ) x y) :=
  .app (.app (.const η (.eq hs.typing.wf)) hs) ht

theorem equal_inv {value : Value M ρ .bool}
    (h : Eval M ρ ν η (Tm.equal A s t) .bool value) :
    ∃ x y : Value M ρ A, Eval M ρ ν η s A x ∧ Eval M ρ ν η t A y ∧
      value = Carrier.eq (A.denote M.toTypeModel ρ) x y := by
  cases h with
  | app hf ht =>
      cases hf with
      | app hc hs =>
          cases hc with
          | const _ heq => cases heq; exact ⟨_, _, hs, ht, rfl⟩

theorem identity (hA : A.WellFormed sig.tyOps) :
    Eval M ρ ν η (Tm.identity A) (.arr A A) id :=
  .lam hA (fun x => .bvar (η.extend x) rfl hA)

theorem truth : Eval M ρ ν η Tm.truth .bool Carrier.truth :=
  equal (identity trivial) (identity trivial)

theorem all {P : Tm} {predicate : Value M ρ (.arr A .bool)}
    (hA : A.WellFormed sig.tyOps) (hP : Eval M ρ ν η P (.arr A .bool) predicate) :
    Eval M ρ ν η (Tm.all A P) .bool (Carrier.all (A.denote M.toTypeModel ρ) predicate) :=
  equal hP (.lam hA (fun _ => truth))

theorem falsity : Eval M ρ ν η Tm.falsity .bool Carrier.falsity :=
  all trivial (identity trivial)

theorem select {P : Tm} {predicate : Value M ρ (.arr A .bool)}
    (hP : Eval M ρ ν η P (.arr A .bool) predicate) :
    Eval M ρ ν η (Tm.select A P) A
      (Carrier.choose (A.denote M.toTypeModel ρ) predicate) :=
  .app (.const η (.select hP.typing.wf.1)) hP

theorem conj {x y : Value M ρ .bool}
    (hp : Eval M ρ ν η p .bool x) (hq : Eval M ρ ν η q .bool y) :
    Eval M ρ ν η (Tm.conj p q) .bool (Carrier.conj x y) := by
  unfold Tm.conj Carrier.conj
  apply equal
  · exact Eval.lam (A := .arr .bool (.arr .bool .bool)) ⟨trivial, trivial, trivial⟩ (fun f =>
      .app (.app (Eval.bvar (A := .arr .bool (.arr .bool .bool)) (η.extend f) rfl ⟨trivial, trivial, trivial⟩)
        (hp.weaken f)) (hq.weaken f))
  · exact Eval.lam (A := .arr .bool (.arr .bool .bool)) ⟨trivial, trivial, trivial⟩ (fun f =>
      .app (.app (Eval.bvar (A := .arr .bool (.arr .bool .bool)) (η.extend f) rfl ⟨trivial, trivial, trivial⟩) truth) truth)

theorem imp {x y : Value M ρ .bool}
    (hp : Eval M ρ ν η p .bool x) (hq : Eval M ρ ν η q .bool y) :
    Eval M ρ ν η (Tm.imp p q) .bool (Carrier.imp x y) :=
  equal (conj hp hq) hp

theorem neg {x : Value M ρ .bool} (hp : Eval M ρ ν η p .bool x) :
    Eval M ρ ν η (Tm.neg p) .bool (Carrier.neg x) := imp hp falsity

theorem disj {x y : Value M ρ .bool}
    (hp : Eval M ρ ν η p .bool x) (hq : Eval M ρ ν η q .bool y) :
    Eval M ρ ν η (Tm.disj p q) .bool (Carrier.disj x y) := by
  unfold Tm.disj Carrier.disj
  apply all (A := .bool) trivial
  apply Eval.lam (A := .bool) trivial
  intro r
  have hr : Eval M ρ ν (η.extend r) (.bvar 0) .bool r := .bvar _ rfl trivial
  exact imp (imp (hp.weaken r) hr) (imp (imp (hq.weaken r) hr) hr)

theorem ex {P : Tm} {predicate : Value M ρ (.arr A .bool)}
    (hA : A.WellFormed sig.tyOps) (hP : Eval M ρ ν η P (.arr A .bool) predicate) :
    Eval M ρ ν η (Tm.ex A P) .bool (Carrier.ex (A.denote M.toTypeModel ρ) predicate) := by
  unfold Tm.ex Carrier.ex
  apply all (A := .bool) trivial
  apply Eval.lam (A := .bool) trivial
  intro r
  apply imp
  · apply all hA
    apply Eval.lam hA
    intro x
    exact imp (.app ((hP.weaken r).weaken x) (.bvar _ rfl hA)) (.bvar _ rfl trivial)
  · exact .bvar _ rfl trivial

theorem injective {function : Value M ρ (.arr A B)}
    (hA : A.WellFormed sig.tyOps) (hf : Eval M ρ ν η f (.arr A B) function) :
    Eval M ρ ν η (Tm.injective A B f) .bool
      (Carrier.injective (A.denote M.toTypeModel ρ) (B.denote M.toTypeModel ρ) function) := by
  unfold Tm.injective Carrier.injective
  apply all hA
  apply Eval.lam hA
  intro x
  apply all hA
  apply Eval.lam hA
  intro y
  have hx : Eval M ρ ν ((η.extend x).extend y) (.bvar 1) A x := .bvar _ rfl hA
  have hy : Eval M ρ ν ((η.extend x).extend y) (.bvar 0) A y := .bvar _ rfl hA
  exact imp (equal (.app ((hf.weaken x).weaken y) hx)
    (.app ((hf.weaken x).weaken y) hy)) (equal hx hy)

theorem surjective {function : Value M ρ (.arr A B)}
    (hA : A.WellFormed sig.tyOps) (hB : B.WellFormed sig.tyOps)
    (hf : Eval M ρ ν η f (.arr A B) function) :
    Eval M ρ ν η (Tm.surjective A B f) .bool
      (Carrier.surjective (A.denote M.toTypeModel ρ) (B.denote M.toTypeModel ρ) function) := by
  unfold Tm.surjective Carrier.surjective
  apply all hB
  apply Eval.lam hB
  intro y
  apply ex hA
  apply Eval.lam hA
  intro x
  exact equal (.app ((hf.weaken y).weaken x) (.bvar _ rfl hA)) (.bvar _ rfl hB)

theorem infinity : Eval M ρ ν η Tm.infinity .bool
    (Carrier.ex (Carrier.arr Carrier.ind Carrier.ind) (fun f =>
      Carrier.conj (Carrier.injective Carrier.ind Carrier.ind f)
        (Carrier.neg (Carrier.surjective Carrier.ind Carrier.ind f)))) := by
  unfold Tm.infinity
  apply ex (A := .arr .ind .ind) ⟨trivial, trivial⟩
  apply Eval.lam (A := .arr .ind .ind) ⟨trivial, trivial⟩
  intro f
  have hf : Eval M ρ ν (η.extend f) (.bvar 0) (.arr .ind .ind) f :=
    .bvar _ rfl ⟨trivial, trivial⟩
  exact conj (injective trivial hf) (neg (surjective trivial trivial hf))

theorem eta {function : Value M ρ (.arr A B)} (hA : A.WellFormed sig.tyOps)
    (hf : Eval M ρ ν η f (.arr A B) function) :
    Eval M ρ ν η (Tm.eta A B f) .bool
      (Carrier.eq ((Ty.arr A B).denote M.toTypeModel ρ) (fun x => function x) function) :=
  equal (.lam hA (fun x => .app (hf.weaken x) (.bvar _ rfl hA))) hf

theorem selection {P x : Tm} {predicate : Value M ρ (.arr A .bool)} {value : Value M ρ A}
    (hP : Eval M ρ ν η P (.arr A .bool) predicate) (hx : Eval M ρ ν η x A value) :
    Eval M ρ ν η (Tm.selection A P x) .bool
      (Carrier.imp (predicate value)
        (predicate (Carrier.choose (A.denote M.toTypeModel ρ) predicate))) :=
  imp (.app hP hx) (.app hP (select hP))

end Eval

end Silmaril.Logic.HOLLight
