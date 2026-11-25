module

public import Silmaril.Process.BlockRead.Defs
public import Silmaril.Semantics.MemoryRefinement.Thms
import Silmaril.Proofs.Process.BlockRead.Basic

/-! # A layout is a sound morphism, not a conversion of all flat pointers back to objects -/

@[expose] public section

namespace Silmaril.Process.BlockRead

open Silmaril.Semantics.MemoryRefinement

theorem read_placed {Block} {base : Block → Nat} {obj : Request Block} {flat : FlatRequest} {out}
    (related : Placed base obj flat) (ok : obj.read = some out) : flat.read = some out :=
  Proofs.Process.BlockRead.read_placed related ok

def layout {Block} (base : Block → Nat) : Hom (objects Block) flat :=
  Hom.ofEval (Placed base) read_placed

/-- Exactly the obligations at the object interface, with no address or ISA hypothesis. -/
theorem wp_iff {Block} (req : Request Block) (post : List Byte → Prop) :
    (objects Block).wp post req ↔ ∃ bytes, req.heap req.block = some bytes ∧
      0 < req.width ∧ req.offset + req.width ≤ bytes.length ∧ post ((bytes.drop req.offset).take req.width) := by
  refine (wp_ofEval (eval := Request.read) (entry := req) (post := post)).trans ?_
  cases h : req.heap req.block <;> simp [Request.read, h, and_assoc]

end Silmaril.Process.BlockRead
