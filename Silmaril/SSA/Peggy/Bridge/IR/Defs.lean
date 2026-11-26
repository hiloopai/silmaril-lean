module

public import Silmaril.SSA.Peggy.Bridge.Equational.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
public import Silmaril.SSA.MLIR.Institution.Thms

/-! # Fixed-sort signature maps for the ordered Peggy value fragment -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.IR

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG.Bridge (Operation Opcode Symbol Ordered TotalModel)

variable {Data : Type}
variable {S T : FixedSortSignature.{0,0} Data}
variable {P Q : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {n : Nat}

/-- Copy and select are structural symbols. A signature arrow only changes
the PEG primitive at its original ordered operand and result profile. -/
def mapOperation (f : PEG.InstructionMap P Q) {ins out} :
    Operation P ins out → Operation Q ins out
  | .copy => .copy
  | .primitive op => .primitive (f op)
  | .select => .select

def mapOpcode (f : PEG.InstructionMap P Q) : RVSDG.Institution.OpcodeMap (Opcode P) (Opcode Q)
  | _, _, .apply op => .apply (mapOperation f op)

/-- The existing RVSDG signatures underlying the fixed-sort family. -/
def rvsdgSignature (Data : Type) :
    FixedSortSignature.{0,0} Data ⥤ RVSDG.Institution.Signature (PEG.Ty Data) PUnit where
  obj S := ⟨Opcode S.ops⟩
  map f := ⟨mapOpcode (FixedSortSignature.opcodeMap f)⟩
  map_id _ := by
    apply congrArg RVSDG.Institution.Signature.Hom.mk
    funext _ _ op
    cases op with | apply op => cases op <;> rfl
  map_comp _ _ := by
    apply congrArg RVSDG.Institution.Signature.Hom.mk
    funext _ _ op
    cases op with | apply op => cases op <;> rfl

def mapSymbol (f : S ⟶ T) :
    PEG.Bridge.signature S.ops ⟶ PEG.Bridge.signature T.ops where
  sort := id
  symbol
    | .apply op => .apply (mapOperation (FixedSortSignature.opcodeMap f) op)

/-- The existing regionless MLIR signatures underlying the same family.
The sort map is the identity on the fixed Peggy sorts. -/
def mlirSignature (Data : Type) :
    FixedSortSignature.{0,0} Data ⥤ Silmaril.MLIR.Institution.Signature false where
  obj S := PEG.Bridge.signature S.ops
  map := mapSymbol
  map_id S := by
    apply congrArg (Silmaril.MLIR.Institution.Signature.Hom.mk
      (S := PEG.Bridge.signature S.ops) (T := PEG.Bridge.signature S.ops) id)
    funext _ _ symbol
    cases symbol with | apply op => cases op <;> rfl
  map_comp {S _ U} _ _ := by
    apply congrArg (Silmaril.MLIR.Institution.Signature.Hom.mk
      (S := PEG.Bridge.signature S.ops) (T := PEG.Bridge.signature U.ops) id)
    funext _ _ symbol
    cases symbol with | apply op => cases op <;> rfl

theorem ordered_map (f : PEG.InstructionMap P Q) (g : PEG.Graph P params results n 0)
    (h : Ordered g) : Ordered (g.mapOps f) := by
  intro i p
  rw [show ((g.mapOps f).node i).arg p = ((g.node i).arg p).reindex (Equiv.refl (Fin n)) from
    PEG.Node.arg_relabel (g.node i) f (Equiv.refl (Fin n)) (Equiv.refl (Fin 0)).symm p]
  exact h i p

/-- Relabelling a restricted equation keeps the topological numbering and the
entire ordered boundary. -/
def mapPEG (f : S ⟶ T) (e : PEG.Bridge.Equation S.ops) : PEG.Bridge.Equation T.ops :=
  let op : PEG.InstructionMap S.ops T.ops := fun i => FixedSortSignature.opcodeMap f i
  ⟨e.params, e.results, e.leftCount, e.rightCount, e.lhs.mapOps op, e.rhs.mapOps op,
    ordered_map op e.lhs e.leftOrdered, ordered_map op e.rhs e.rightOrdered⟩

/-- Induced models have the original PEG data carriers, fixed Boolean and
count carriers, and total primitive functions. -/
def reduct (f : S ⟶ T) (m : TotalModel T.ops) : TotalModel S.ops :=
  ⟨m.carrier, fun op => m.run (FixedSortSignature.opcodeMap f op)⟩

/-- A presentation by total functions gives a total-primitive Peggy model. -/
def toTotalPrimitive (m : TotalModel S.ops) : Equational.TotalPrimitiveModel S :=
  ⟨m.toPEG, fun _ _ => rfl⟩

/-- Recover the total functions in a total-primitive Peggy model. -/
def fromTotalPrimitive (m : Equational.TotalPrimitiveModel S) : TotalModel S.ops :=
  ⟨m.val.carrier, fun op xs => (m.val.run op xs).get (m.property op xs)⟩

def emptyForest : PEG.LoopForest 0 := ⟨Fin.elim0⟩

theorem ordered_wellFormed (g : PEG.Graph P params results n 0) (h : Ordered g) : g.WellFormed :=
  ⟨fun i => i.elim0, fun a _ w ne => (Nat.lt_irrefl a.val (w.strictRank ne Fin.val
    (fun ⟨i, _, edge⟩ _ => edge ▸ h _ i))).elim, fun _ _ _ i => i.elim0, fun _ _ _ _ _ i => i.elim0⟩

def toOpenGraph (g : PEG.Graph P params results n 0) (h : Ordered g) :
    Dialect.OpenGraph P params results n emptyForest :=
  ⟨g, congrArg PEG.LoopForest.mk (funext fun i => i.elim0), ordered_wellFormed g h⟩

/-- The identical ordered table as a Peggy equation with the empty loop frame. -/
def toPeggy (e : PEG.Bridge.Equation S.ops) : Dialect.Equation S :=
  ⟨e.params, e.results, 0, emptyForest, e.leftCount, e.rightCount,
    toOpenGraph e.lhs e.leftOrdered, toOpenGraph e.rhs e.rightOrdered⟩

end Silmaril.SSA.Peggy.Bridge.IR
