module

public import Silmaril.SSA.RVSDG.Interprocedural.Terms.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Terms.Defs

/-! Typed vertex renumbering for translation units and their inductive bindings. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {args args' outs outs' : Ports (Ty V S)}
variable {past past' sigs sigs' : List (Ports (Ty V S))}
variable {fn : Function V S} {value : ValueSort V S} {members : List (Function V S)}

/-- Capture ports retain their types and order. An origin's vertex number may
change, while argument positions and producer output positions stay fixed. -/
def CaptureRenumbered (ids : Nat → Nat) {context context' : Ports (Ty V S)}
    (left : Wires args past context) (right : Wires args' past' context') : Prop :=
  context = context' ∧ left.addresses.map (Address.rename ids) = right.addresses

/-- Match λ closure captures in the enclosing numbering and its body in a
fresh numbering. The function signature fixes the remaining body boundary. -/
def Lambda.Renumbered (ids : Nat → Nat)
    (left : Lambda Op args past fn) (right : Lambda Op args' past' fn) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    NestedTheta.Graph.Isomorphic (Instruction Op) left.body right.body

/-- A δ initializer is still a primitive/γ region with one right-hand-side value. -/
def Delta.Renumbered (ids : Nat → Nat)
    (left : Delta Op args past value) (right : Delta Op args' past' value) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    RVSDG.Graph.Isomorphic Op left.initializer right.initializer

/-- Member order fixes the recursion arguments, physical λ slots and result
origins in the current φ representation. A member body can be renumbered
independently. A capture of an earlier member keeps that member's slot. -/
def Phi.Renumbered (ids : Nat → Nat)
    (left : Phi Op args past members) (right : Phi Op args' past' members) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    ∀ i, (left.definitions i).Renumbered id (right.definitions i)

/-- Match the structural kind and its ordered output interface. -/
inductive Vertex.Renumbered (Op : Dialect.{u, v} (ValueSort V S) S) (ids : Nat → Nat) :
    {outs outs' : Ports (Ty V S)} →
    Vertex Op args past outs → Vertex Op args' past' outs' → Prop where
  | lambda {fn : Function V S} {left : Lambda Op args past fn} {right : Lambda Op args' past' fn}
      (related : left.Renumbered ids right) : Vertex.Renumbered Op ids (.lambda left) (.lambda right)
  | delta {value : ValueSort V S} {left : Delta Op args past value} {right : Delta Op args' past' value}
      (related : left.Renumbered ids right) : Vertex.Renumbered Op ids (.delta left) (.delta right)
  | phi {members : List (Function V S)} {left : Phi Op args past members} {right : Phi Op args' past' members}
      (related : left.Renumbered ids right) : Vertex.Renumbered Op ids (.phi left) (.phi right)

/-- A typed graph isomorphism with a chosen vertex bijection at ω. The shared
indices keep ordered imports and exports fixed. Capture and export edges
use the bijection, and the paired vertices check their children recursively. -/
structure Omega.RenumberedBy (left : Omega Op args outs sigs) (right : Omega Op args outs sigs')
    (ids : Fin sigs.length ≃ Fin sigs'.length) : Prop where
  vertices : ∀ i, Vertex.Renumbered Op (renameVertex ids)
    (left.region.vertices i) (right.region.vertices (ids i))
  exports : left.region.results.addresses.map (Address.rename (renameVertex ids)) =
    right.region.results.addresses

def Omega.Isomorphic (left : Omega Op args outs sigs) (right : Omega Op args outs sigs') : Prop :=
  ∃ ids, left.RenumberedBy right ids

/-! The term-side view reads actual bindings, capture edges and child
terms directly. The acyclic δ initializer uses the primitive inclusion
into the nested term language. -/

def LambdaTerm.Renumbered (ids : Nat → Nat)
    (left : LambdaTerm Op args past fn) (right : LambdaTerm Op args' past' fn) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    NestedTheta.Term.Isomorphic (Instruction Op) left.body right.body

def DeltaTerm.Renumbered (ids : Nat → Nat)
    (left : DeltaTerm Op args past value) (right : DeltaTerm Op args' past' value) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    NestedTheta.Term.Isomorphic Op (.ofBase left.initializer) (.ofBase right.initializer)

def PhiTerm.Renumbered (ids : Nat → Nat)
    (left : PhiTerm Op args past members) (right : PhiTerm Op args' past' members) : Prop :=
  CaptureRenumbered ids left.captures right.captures ∧
    ∀ i, (left.definitions.get i).Renumbered id (right.definitions.get i)

/-- Match two inductive binding headers and the regions under them. -/
inductive VertexTerm.Renumbered (Op : Dialect.{u, v} (ValueSort V S) S) (ids : Nat → Nat) :
    {outs outs' : Ports (Ty V S)} →
    VertexTerm Op args past outs → VertexTerm Op args' past' outs' → Prop where
  | lambda {fn : Function V S} {left : LambdaTerm Op args past fn} {right : LambdaTerm Op args' past' fn}
      (related : left.Renumbered ids right) : VertexTerm.Renumbered Op ids (.lambda left) (.lambda right)
  | delta {value : ValueSort V S} {left : DeltaTerm Op args past value} {right : DeltaTerm Op args' past' value}
      (related : left.Renumbered ids right) : VertexTerm.Renumbered Op ids (.delta left) (.delta right)
  | phi {members : List (Function V S)}
      {left : PhiTerm Op args past members} {right : PhiTerm Op args' past' members}
      (related : left.Renumbered ids right) : VertexTerm.Renumbered Op ids (.phi left) (.phi right)

/-- Look up a binding by position in the inductive spine, retaining the
prefix of available producers at the binding. -/
def ModuleTerm.bindingAt :
    {past sigs : List (Ports (Ty V S))} → ModuleTerm Op args past sigs outs →
    (i : Fin sigs.length) → VertexTerm Op args (site past sigs i).1 (site past sigs i).2
  | _, _, .ret _, i => i.elim0
  | _, _, .bind definition rest, i => Fin.cases definition rest.bindingAt i

/-- A typed renaming of two well-scoped let sequences. It compares ordered
captures and the final export wires in their own prefixes. -/
structure OmegaTerm.RenumberedBy (left : OmegaTerm Op args outs sigs)
    (right : OmegaTerm Op args outs sigs') (ids : Fin sigs.length ≃ Fin sigs'.length) : Prop where
  bindings : ∀ i, VertexTerm.Renumbered Op (renameVertex ids)
    (left.region.bindingAt i) (right.region.bindingAt (ids i))
  exports : left.region.results.addresses.map (Address.rename (renameVertex ids)) =
    right.region.results.addresses

def OmegaTerm.Isomorphic (left : OmegaTerm Op args outs sigs) (right : OmegaTerm Op args outs sigs') : Prop :=
  ∃ ids, left.RenumberedBy right ids

end Silmaril.SSA.RVSDG.Interprocedural
