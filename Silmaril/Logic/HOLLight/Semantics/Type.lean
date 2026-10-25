module

public import Silmaril.Logic.HOLLight.Type

@[expose] public section

/-!
# Full set-theoretic interpretation of HOL types

Every HOL type denotes a nonempty type in an arbitrary universe. Function
types denote full function spaces. Lifted Booleans and naturals provide the
Boolean and individual carriers without restricting the model to `Type 0`.
-/

namespace Silmaril.Logic.HOLLight

universe u

/-- A nonempty set represented by a Lean type in the chosen universe. -/
abbrev Carrier := {A : Type u // Nonempty A}

namespace Carrier

instance : CoeSort Carrier.{u} (Type u) := ⟨Subtype.val⟩
instance (A : Carrier.{u}) : Nonempty A := A.property

abbrev unit : Carrier.{u} := ⟨ULift.{u} Unit, inferInstance⟩
abbrev bool : Carrier.{u} := ⟨ULift.{u} Bool, inferInstance⟩
abbrev ind : Carrier.{u} := ⟨ULift.{u} Nat, inferInstance⟩
abbrev arr (A B : Carrier.{u}) : Carrier.{u} := ⟨A → B, inferInstance⟩

/-- Designated truth in the standard two-valued Boolean carrier. -/
def Truth (b : bool.{u}) : Prop := b.down = true

noncomputable def ofProp (p : Prop) : bool.{u} :=
  ⟨@decide p (Classical.propDecidable p)⟩

@[simp] theorem truth_ofProp (p : Prop) : Truth (ofProp.{u} p) ↔ p := by
  classical
  simp [Truth, ofProp]

/-- HOL equality is actual equality in the interpreted carrier. -/
noncomputable def eq (A : Carrier.{u}) (x y : A) : bool.{u} := ofProp (x = y)

@[simp] theorem truth_eq {A : Carrier.{u}} (x y : A) : Truth (eq A x y) ↔ x = y :=
  truth_ofProp _

/-- Hilbert choice depends only on its carrier and predicate. -/
noncomputable def choose (A : Carrier.{u}) (p : A → bool.{u}) : A := by
  classical
  exact if h : ∃ a, Truth (p a) then Classical.choose h else Classical.choice A.property

theorem choose_spec {A : Carrier.{u}} (p : A → bool.{u}) {x : A}
    (hx : Truth (p x)) : Truth (p (choose A p)) := by
  unfold choose
  rw [dite_eq_left ⟨x, hx⟩]
  exact Classical.choose_spec (show ∃ a, Truth (p a) from ⟨x, hx⟩)

theorem funext {A B : Carrier.{u}} {f g : arr A B}
    (h : ∀ x, f x = g x) : f = g := _root_.funext h

theorem bool_ext {p q : bool.{u}} (h : Truth p ↔ Truth q) : p = q := by
  cases p with
  | up p =>
    cases q with
    | up q => cases p <;> cases q <;> simp_all [Truth] <;> rfl

end Carrier

abbrev TypeValuation := Nat → Carrier.{u}

/-- The finite assignment supplied when interpreting a constant scheme. -/
def Carrier.assignment (args : List Carrier.{u}) : TypeValuation.{u} :=
  fun i => args[i]?.getD Carrier.unit

/-- Raw interpretation is total; syntax formation enforces declared arities. -/
structure TypeModel where
  typeOp : Nat → List Carrier.{u} → Carrier.{u}

namespace TypeModel

/-- The initial signature has no added type operators. This total default also
provides a simple interpretation for otherwise unused operator symbols. -/
def standard : TypeModel.{u} := ⟨fun _ _ => Carrier.unit⟩

end TypeModel

namespace Ty

mutual
def denote (M : TypeModel.{u}) (ρ : TypeValuation.{u}) : Ty → Carrier.{u}
  | .var i => ρ i
  | .bool => Carrier.bool
  | .ind => Carrier.ind
  | .arr A B => Carrier.arr (denote M ρ A) (denote M ρ B)
  | .app c args => M.typeOp c (denoteList M ρ args)
termination_by structural A => A

def denoteList (M : TypeModel.{u}) (ρ : TypeValuation.{u}) : List Ty → List Carrier.{u}
  | [] => []
  | A :: args => denote M ρ A :: denoteList M ρ args
termination_by structural args => args
end

@[simp] theorem denoteList_eq_map (M : TypeModel.{u}) (ρ : TypeValuation.{u}) (args : List Ty) :
    denoteList M ρ args = args.map (denote M ρ) := by
  induction args with
  | nil => rfl
  | cons A args ih => simp [denoteList, ih]

@[simp] theorem denote_var (M : TypeModel.{u}) (ρ : TypeValuation.{u}) (i : Nat) :
    denote M ρ (.var i) = ρ i := by simp [denote]
@[simp] theorem denote_bool (M : TypeModel.{u}) (ρ : TypeValuation.{u}) :
    denote M ρ .bool = Carrier.bool := by simp [denote]
@[simp] theorem denote_ind (M : TypeModel.{u}) (ρ : TypeValuation.{u}) :
    denote M ρ .ind = Carrier.ind := by simp [denote]
@[simp] theorem denote_arr (M : TypeModel.{u}) (ρ : TypeValuation.{u}) (A B : Ty) :
    denote M ρ (.arr A B) = Carrier.arr (denote M ρ A) (denote M ρ B) := by simp [denote]
@[simp] theorem denote_app (M : TypeModel.{u}) (ρ : TypeValuation.{u})
    (c : Nat) (args : List Ty) :
    denote M ρ (.app c args) = M.typeOp c (args.map (denote M ρ)) := by simp [denote]

/-- Syntactic type substitution is semantic reassignment of schematic types. -/
theorem denote_subst (M : TypeModel.{u}) (ρ : TypeValuation.{u}) (σ : Nat → Ty)
    (A : Ty) :
    denote M ρ (A.subst σ) = denote M (fun i => denote M ρ (σ i)) A := by
  induction A using induction_on with
  | var i => simp
  | bool => simp
  | ind => simp
  | arr A B ihA ihB => simp [ihA, ihB]
  | app c args ih =>
    simp only [subst_app, denote_app, List.map_map]
    apply congrArg (M.typeOp c)
    exact List.map_congr_left ih

theorem denote_congr_scoped (M : TypeModel.{u}) {n : Nat} {A : Ty}
    (hA : A.Scoped n) {ρ τ : TypeValuation.{u}}
    (h : ∀ i, i < n → ρ i = τ i) : denote M ρ A = denote M τ A := by
  induction A using induction_on with
  | var i => exact (denote_var M ρ i).trans ((h i (by simpa [Scoped] using hA)).trans
      (denote_var M τ i).symm)
  | bool => simp
  | ind => simp
  | arr A B ihA ihB =>
    simp only [Scoped] at hA
    simp [ihA hA.1, ihB hA.2]
  | app c args ih =>
    simp only [Scoped, scopedList_iff] at hA
    simp only [denote_app]
    apply congrArg (M.typeOp c)
    exact List.map_congr_left (fun A hmem => ih A hmem (hA A hmem))

/-- A scheme's semantics depends only on its supplied carrier arguments. -/
theorem denote_instantiate (M : TypeModel.{u}) (ρ : TypeValuation.{u})
    {n : Nat} {A : Ty} (hA : A.Scoped n) {args : List Ty}
    (hlen : args.length = n) :
    denote M ρ (A.instantiate args) =
      denote M (Carrier.assignment (args.map (denote M ρ))) A := by
  unfold instantiate
  rw [denote_subst]
  apply denote_congr_scoped M hA
  intro i hi
  have hi' : i < args.length := hlen ▸ hi
  simp [Carrier.assignment, List.getElem?_map, List.getElem?_eq_getElem hi']

end Ty

end Silmaril.Logic.HOLLight
