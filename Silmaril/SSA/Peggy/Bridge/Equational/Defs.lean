module

public import Silmaril.Logic.Algebraic.ManySorted.Defs
public import Silmaril.SSA.Peggy.Institution.Thms

/-! # Fixed-sort equational signatures in Peggy -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational

open CategoryTheory
open Silmaril.Logic.Algebraic
open Dialect (FixedSortSignature)
open RVSDG (Port Tuple)

variable {S : Type} {A B : ManySorted.Signature S}

/-- Ordered PEG data ports for a finite sorted context or operation profile. -/
def profile : {n : Nat} → (Fin n → S) → List (PEG.Ty S)
  | 0, _ => []
  | _ + 1, w => .data (w 0) :: profile (w ∘ Fin.succ)

/-- Construct the ordered tuple from its components at the source positions. -/
def pack {F : PEG.Ty S → Type} : {n : Nat} → (w : Fin n → S) →
    (∀ i, F (.data (w i))) → Tuple F (profile w)
  | 0, _, _ => .nil
  | _ + 1, w, f => .cons (f 0) (pack (w ∘ Fin.succ) (fun i => f i.succ))

/-- Translate a variable position into the corresponding typed PEG parameter port. -/
def port : {n : Nat} → (w : Fin n → S) → (i : Fin n) → Port (profile w) (.data (w i))
  | 0, _, i => i.elim0
  | _ + 1, w, i => Fin.cases .head (fun j => .tail (port (w ∘ Fin.succ) j)) i

/-- A source operation becomes one primitive with the same ordered data profile. -/
inductive Opcode (A : ManySorted.Signature S) : PEG.InstructionSet S where
  | app {n w s} (op : A.operations n w s) : Opcode A (profile w) (.data s)

def mapOpcode (f : A ⟶ B) : PEG.InstructionMap (Opcode A) (Opcode B)
  | _, _, .app op => .app (f.operations op)

/-- The fixed-sort signature functor. The source sorts are embedded using `PEG.Ty.data`. -/
def signature (S : Type) : ManySorted.Signature S ⥤ FixedSortSignature S where
  obj A := ⟨Opcode A⟩
  map f := FixedSortSignature.ofOpcodeMap (mapOpcode f)
  map_id _ := by
    apply congrArg FixedSortSignature.Hom.mk
    funext _ _ op
    cases op
    rfl
  map_comp _ _ := by
    apply congrArg FixedSortSignature.Hom.mk
    funext _ _ op
    cases op
    rfl

/-- The operation contract requires a defined result on every tuple of defined operands. -/
def PrimitivesTotal {P : PEG.InstructionSet S} (m : PEG.Interpretation.{0,0,0} P) : Prop :=
  ∀ {ins out} (op : P ins out) (args : Tuple m.Value ins), (m.run op args).isSome

abbrev TotalPrimitiveModel (T : FixedSortSignature.{0,0} S) :=
  { m : Institution.Model.{0,0,0} T // PrimitivesTotal m }

def totalPrimitiveReduct {T U : FixedSortSignature.{0,0} S} (f : T ⟶ U) (m : TotalPrimitiveModel U) : TotalPrimitiveModel T :=
  ⟨Institution.reduct f m.val, fun op args => m.property (FixedSortSignature.opcodeMap f op) args⟩

/-- The Peggy subinstitution with total primitive operations. Sentences and guarded termination
are inherited from Peggy, so graphs can still yield bottom through their control operators. -/
def totalPrimitivePlain (S : Type) : Silmaril.Inst.Plain (FixedSortSignature.{0,0} S) where
  Sen := Dialect.Equation
  map := Dialect.Equation.map
  map_id := Dialect.Equation.map_id
  map_comp := Dialect.Equation.map_comp
  Mod := TotalPrimitiveModel
  reduct := totalPrimitiveReduct
  reduct_id _ _ := rfl
  reduct_comp _ _ _ := rfl
  Sat m e := e.Holds m.val
  sat_map f m e := Dialect.Equation.holds_map f m.val e

/-- Fixed-sort Peggy with its model categories restricted to total primitives. -/
abbrev totalPrimitiveInst (S : Type) := (totalPrimitivePlain S).toInst

/-- Pull a total Peggy model back to an ordinary many-sorted algebra. -/
def algebra (m : TotalPrimitiveModel ((signature S).obj A)) : ManySorted.Model A where
  carrier := m.val.carrier
  operation op args := (m.val.run (.app op) (pack _ args)).get (m.property _ _)

/-- Every source algebra expands to a Peggy model with total primitives. -/
def expand (m : ManySorted.Model A) : TotalPrimitiveModel ((signature S).obj A) :=
  ⟨{ carrier := m.carrier
     run := fun op args => match op with
       | .app (w := w) op => some (m.operation op (fun i => args.get (port w i))) },
   fun op args => by cases op; rfl⟩

end Silmaril.SSA.Peggy.Bridge.Equational
