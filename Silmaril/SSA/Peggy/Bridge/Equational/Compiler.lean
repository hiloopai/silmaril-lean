module

public import Silmaril.SSA.Peggy.Bridge.Equational.Numbering

/-! # Loop-free PEG tables for equational terms -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Equational

open Silmaril.Logic.Algebraic
open RVSDG (Tuple)

variable {S : Type} {A : ManySorted.Signature S} {k n : Nat} {Γ : Fin k → S}
variable {rows : Fin n → Occurrence A Γ} {i : Fin n} {s : S}

/-- The result type declared at each row is its source term's data sort. -/
abbrev rowSort (rows : Fin n → Occurrence A Γ) (i : Fin n) : PEG.Ty S := .data (rows i).1

def Child.ref {t : Occurrence A Γ} (c : Child rows i t) : PEG.Ref (rowSort rows) (.data t.1) :=
  ⟨c.id, congrArg (fun (t : Occurrence A Γ) => PEG.Ty.data t.1) c.term_eq⟩

def Wiring.node {t : ManySorted.Term A Γ s} (w : Wiring rows i t) :
    PEG.Node (Opcode A) (profile Γ) (Fin 0) (rowSort rows) (.data s) :=
  match t with
  | .var v => .ofLabel (.param (port Γ v)) .nil
  | .app (inputs := inputs) op _ =>
    .ofLabel (.op (.app op)) (pack inputs (fun j => (w.children j).ref))

/-- The sole loop frame for compiled terms. -/
def emptyForest : PEG.LoopForest 0 := ⟨Fin.elim0⟩

def Numbered.graph {t : ManySorted.Term A Γ s} (code : Numbered t) :
    PEG.Graph (Opcode A) (profile Γ) [.data s] (code.tailSize + 1) 0 where
  forest := emptyForest
  sort := rowSort code.rows
  node i := (code.wiring i).node
  roots := .cons ⟨0, congrArg (fun (t : Occurrence A Γ) => PEG.Ty.data t.1) code.root⟩ .nil

end Silmaril.SSA.Peggy.Bridge.Equational
