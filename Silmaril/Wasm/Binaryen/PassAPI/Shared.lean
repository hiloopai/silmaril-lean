module

public import Silmaril.Wasm.Binaryen.PassAPI.Checked
public import Silmaril.Compile.PassAPI.Checked

@[expose] public section

/-! # Lossless compatibility with the shared pass API

The original Binaryen API remains unchanged. These conversions retain its relation,
invariant, transformation and checker exactly; in particular, they do not weaken
export equivalence to refinement. The pass equivalence preserves the diagrammatic
monoid product, pipelines and checked identity fallback.
-/

namespace Silmaril.Wasm.Binaryen.PassAPI

universe u

namespace Contract

variable {X : Type u}

/-- The same contract in the shared, language-independent API. -/
def toShared (C : Contract X) : Silmaril.Compile.PassAPI.Contract X :=
  ⟨C.Rel, C.refl, C.trans, C.Inv⟩

/-- Recover an original Binaryen contract without changing its fields. -/
def ofShared (C : Silmaril.Compile.PassAPI.Contract X) : Contract X :=
  ⟨C.Rel, C.refl, C.trans, C.Inv⟩

@[simp] theorem ofShared_toShared (C : Contract X) : ofShared C.toShared = C := by
  cases C
  rfl

@[simp] theorem toShared_ofShared (C : Silmaril.Compile.PassAPI.Contract X) :
    (ofShared C).toShared = C := by
  cases C
  rfl

@[simp] theorem toShared_rel (C : Contract X) (x y : X) :
    C.toShared.Rel x y = C.Rel x y := rfl

@[simp] theorem toShared_inv (C : Contract X) (x : X) :
    C.toShared.Inv x = C.Inv x := rfl

end Contract

variable {X : Type u} {C : Contract X}

namespace Pass

/-- A Binaryen pass in the shared API, with the identical run function and proofs. -/
def toShared (p : Pass C) : Silmaril.Compile.PassAPI.Pass C.toShared :=
  ⟨p.run, p.inv_run, p.sound⟩

/-- Recover a Binaryen pass for the original contract. -/
def ofShared (p : Silmaril.Compile.PassAPI.Pass C.toShared) : Pass C :=
  ⟨p.run, p.inv_run, p.sound⟩

@[simp] theorem toShared_run (p : Pass C) : p.toShared.run = p.run := rfl

@[simp] theorem ofShared_run (p : Silmaril.Compile.PassAPI.Pass C.toShared) :
    (ofShared p).run = p.run := rfl

@[simp] theorem ofShared_toShared (p : Pass C) : ofShared p.toShared = p := by
  cases p
  rfl

@[simp] theorem toShared_ofShared (p : Silmaril.Compile.PassAPI.Pass C.toShared) :
    (ofShared p).toShared = p := by
  cases p
  rfl

/-- The conversion retains invariant preservation on exactly the original domain. -/
theorem toShared_inv_run (p : Pass C) {x : X} (hx : C.Inv x) :
    C.Inv (p.toShared.run x) := p.inv_run hx

/-- The conversion retains the exact original semantic relation. -/
theorem toShared_sound (p : Pass C) {x : X} (hx : C.Inv x) :
    C.Rel x (p.toShared.run x) := p.sound hx

@[simp] theorem toShared_one : (1 : Pass C).toShared = 1 := rfl

@[simp] theorem toShared_mul (p q : Pass C) :
    (p * q).toShared = p.toShared * q.toShared := rfl

/-- The old and shared pass monoids are isomorphic, without changing execution. -/
def sharedEquiv (C : Contract X) : Pass C ≃* Silmaril.Compile.PassAPI.Pass C.toShared where
  toFun := toShared
  invFun := ofShared
  left_inv := ofShared_toShared
  right_inv := toShared_ofShared
  map_mul' := toShared_mul

/-- Conversion preserves arbitrary pipeline length and phase order. -/
@[simp] theorem toShared_pipeline (ps : List (Pass C)) :
    (pipeline ps).toShared =
      Silmaril.Compile.PassAPI.Pass.pipeline (ps.map toShared) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pipeline_cons, toShared_mul, List.map_cons,
      Silmaril.Compile.PassAPI.Pass.pipeline_cons, ih]

@[simp] theorem toShared_pow (p : Pass C) (n : Nat) :
    (p ^ n).toShared = p.toShared ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, toShared_mul, ih, pow_succ]

end Pass

namespace CheckedPass

/-- Preserve both the untrusted proposal and the verified check, including rejection. -/
def toShared (c : CheckedPass C) : Silmaril.Compile.PassAPI.CheckedPass C.toShared :=
  ⟨c.transform, c.check, c.check_sound⟩

/-- Recover an original checked pass with the identical checker. -/
def ofShared (c : Silmaril.Compile.PassAPI.CheckedPass C.toShared) : CheckedPass C :=
  ⟨c.transform, c.check, c.check_sound⟩

@[simp] theorem ofShared_toShared (c : CheckedPass C) : ofShared c.toShared = c := by
  cases c
  rfl

@[simp] theorem toShared_ofShared (c : Silmaril.Compile.PassAPI.CheckedPass C.toShared) :
    (ofShared c).toShared = c := by
  cases c
  rfl

/-- Checked-pass compatibility preserves the proposal, checker and soundness proof. -/
def sharedEquiv (C : Contract X) :
    CheckedPass C ≃ Silmaril.Compile.PassAPI.CheckedPass C.toShared where
  toFun := toShared
  invFun := ofShared
  left_inv := ofShared_toShared
  right_inv := toShared_ofShared

@[simp] theorem toShared_transform (c : CheckedPass C) :
    c.toShared.transform = c.transform := rfl

@[simp] theorem toShared_check (c : CheckedPass C) : c.toShared.check = c.check := rfl

/-- Acceptance and identity fallback are preserved, not only successful proposals. -/
@[simp] theorem toShared_checked (c : CheckedPass C) :
    c.checked.toShared = c.toShared.checked := rfl

@[simp] theorem toShared_seq (c d : CheckedPass C) :
    (c.seq d).toShared = c.toShared.seq d.toShared := rfl

end CheckedPass

end Silmaril.Wasm.Binaryen.PassAPI
