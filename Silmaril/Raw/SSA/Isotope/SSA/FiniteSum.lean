module

public import Silmaril.SSA.Isotope.Types.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.List.OfFn

/-! Heterogeneous finite label families, represented by right-nested sums. -/

@[expose] public section

universe u

namespace Silmaril.Isotope.SSA.FiniteSum

variable {τ : Type u}

/-- A finite coproduct with an explicit empty tail. No equations on the type
operations are required. -/
def sumTy [HasCoproduct τ] [HasEmpty τ] : {n : Nat} → (Fin n → τ) → τ
  | 0, _ => Silmaril.empty
  | _ + 1, A => Silmaril.coprod (A 0) (sumTy (fun i => A i.succ))

@[simp] theorem sumTy_zero [HasCoproduct τ] [HasEmpty τ] (A : Fin 0 → τ) :
    sumTy A = Silmaril.empty := rfl

@[simp] theorem sumTy_succ [HasCoproduct τ] [HasEmpty τ] {n : Nat} (A : Fin (n + 1) → τ) :
    sumTy A = Silmaril.coprod (A 0) (sumTy (fun i => A i.succ)) := rfl

/-- Internal labels precede external labels in the positional CFG convention. -/
def append {n m : Nat} (A : Fin n → τ) (B : Fin m → τ) : Fin (n + m) → τ :=
  Fin.addCases A B

@[simp] theorem append_left {n m : Nat} (A : Fin n → τ) (B : Fin m → τ) (i : Fin n) :
    append A B (i.castAdd m) = A i := by simp [append]

@[simp] theorem append_right {n m : Nat} (A : Fin n → τ) (B : Fin m → τ) (i : Fin m) :
    append A B (i.natAdd n) = B i := by simp [append]

@[simp] theorem ofFn_append {n m : Nat} (A : Fin n → τ) (B : Fin m → τ) :
    List.ofFn (append A B) = List.ofFn A ++ List.ofFn B := by
  simp [List.ofFn_add, append]
  funext i
  change Fin.addCases A B (i.castAdd m) = A i
  simp

@[simp] theorem at_ofFn {n : Nat} (A : Fin n → τ) (i : Fin n) :
    (List.ofFn A)[i.val]? = some (A i) := by simp

end Silmaril.Isotope.SSA.FiniteSum
