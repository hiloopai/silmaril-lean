module

public import Silmaril.Formats.Blake3Cas.Evidence.Thms

@[expose] public section

namespace Silmaril.Formats.Blake3Cas.RangeFacts.Grouped

open Silmaril.Crypto.Blake3

/-- Grouped evidence on a fixed BLAKE3 geometry, not a new tree with wider chunks. -/
inductive Evidence : Shape → Type where
  | raw {shape : Shape} (bytes : Bytes) : Evidence shape
  | opaque {shape : Shape} (cv : CV) : Evidence shape
  | fork {left right : Shape} : Evidence left → Evidence right → Evidence (.fork left right)

def Evidence.expand {shape : Shape} : Evidence shape → Opening
  | .raw bytes => disclose shape bytes
  | .opaque cv => .opaque cv
  | .fork lhs rhs => .fork lhs.expand rhs.expand

def Evidence.check? {shape : Shape} (root : Bool) : Evidence shape → Option CV
  | .raw bytes => subtreeCV? root shape bytes
  | .opaque cv => if root then none else some cv
  | .fork lhs rhs => do
    let left ← lhs.check? false
    let right ← rhs.check? false
    return parentCV root left right

/-- A cut can omit a non-root subtree, reveal all of it as one raw field, or
recurse at an original fork. No constructor can commit an opaque ROOT. -/
inductive Cut : Bool → Shape → Type where
  | raw {root : Bool} {shape : Shape} : Cut root shape
  | opaque {shape : Shape} : Cut false shape
  | fork {root : Bool} {left right : Shape} : Cut false left → Cut false right → Cut root (.fork left right)

def Cut.emit? {root : Bool} {shape : Shape} (cut : Cut root shape) (bytes : Bytes) : Option (Evidence shape) :=
  match cut with
  | .raw => some (.raw bytes)
  | .opaque => (subtreeCV? false shape bytes).map Evidence.opaque
  | .fork (left := left) lhs rhs => do
    let l ← lhs.emit? (bytes.take left.size)
    let r ← rhs.emit? (bytes.drop left.size)
    return .fork l r

def Cut.opensEdge {root : Bool} {shape : Shape} : Cut root shape → Bool
  | .raw => true
  | .opaque => false
  | .fork _ rhs => rhs.opensEdge

def chunkIndices : Shape → List Nat
  | .leaf chunk _ => [chunk]
  | .fork left right => chunkIndices left ++ chunkIndices right

def Cut.revealed {root : Bool} {shape : Shape} : Cut root shape → List Nat
  | .raw => chunkIndices shape
  | .opaque => []
  | .fork lhs rhs => lhs.revealed ++ rhs.revealed

/-- Skip at most `layers` bottom layers of CV pairs when all leaves of a reached
subtree are selected. Otherwise descend, or leave an unselected non-root subtree
opaque. On `geometry 0 size` this groups only actual aligned BLAKE3 subtrees,
including a short final group. The predicate is on absolute chunk counters. -/
def Cut.forLayers (layers : Nat) (selected : Nat → Bool) (root : Bool) (shape : Shape) : Cut root shape :=
  if !root && !(chunkIndices shape).any selected then
    match root with
    | false => .opaque
    | true => .raw
  else if (shapeSpan shape).count ≤ 2 ^ layers && (chunkIndices shape).all selected then .raw
  else
    match shape with
    | .leaf .. => .raw
    | .fork left right => .fork (forLayers layers selected false left) (forLayers layers selected false right)

end Silmaril.Formats.Blake3Cas.RangeFacts.Grouped
