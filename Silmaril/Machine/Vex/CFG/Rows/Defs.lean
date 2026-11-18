module

public import Silmaril.Machine.Vex.CFG.CallEdges.Defs
public import Silmaril.Semantics.Region.Abstract.Named.Defs

/-! # Ordinary and call-edge fillings of the same Region/BB signature -/

@[expose] public section

namespace Silmaril.Machine.Vex.ControlFlow

open Silmaril.Semantics.Region.Abstract (SegmentRegionModel)
open Silmaril.Semantics.Region.Tree (FlatCFG)

variable {Image Context Label Function : Type*}

/-- Structural boundary of a declared support. Calls are always explicit
departures (including recursion); fake returns are separate caller-local
annotations, exposed here only when they leave the support. -/
def boundary (edges : Label → Set (Edge Label)) (support : Set Label) : Set (Edge Label) :=
  {edge | ∃ origin ∈ support, edge ∈ edges origin ∧ match edge with
    | .ordinary target | .fakeReturn target => target ∉ support
    | .call _ => True}

def GraphRow (wellFormed : Image → Context → Prop) (blocks : Image → Set Label)
    (edges : Image → Label → Set (Edge Label)) (image : Image) (context : Context)
    (support : Set Label) (entry : Label) (exits : Set (Edge Label)) : Prop :=
  wellFormed image context ∧ entry ∈ support ∧ support ⊆ blocks image ∧ exits = boundary (edges image) support

/-- A structural filling: a segment is one block label. Region rows declare
support and its exact tagged graph boundary, not dynamic reachability. -/
def graphFilling (wellFormed : Image → Context → Prop) (blocks : Image → Set Label)
    (edges : Image → Label → Set (Edge Label)) :
    SegmentRegionModel Image Context Label (Set Label) Label (Set (Edge Label)) where
  SegBB image context block := wellFormed image context ∧ block ∈ blocks image
  BB image context block entry exits := entry = block ∧ GraphRow wellFormed blocks edges image context {block} entry exits
  Reg := GraphRow wellFormed blocks edges
  SR image context support entry exit := GraphRow wellFormed blocks edges image context support entry {.ordinary exit}
  SR' image context support entry exit :=
    GraphRow wellFormed blocks edges image context support entry {edge | ∃ label, exit = some label ∧ edge = .ordinary label}

def flatFilling (Label Function : Type*) :
    SegmentRegionModel (FlatCFG Label) (Partition Label Function × Function)
      Label (Set Label) Label (Set (Edge Label)) :=
  graphFilling (fun graph ctx => FlatWellFormed ctx.1 ctx.2 graph) FlatCFG.internal ordinaryEdges

def callFilling (Label Function : Type*) :
    SegmentRegionModel (CallCFG Label) (Partition Label Function × Function)
      Label (Set Label) Label (Set (Edge Label)) :=
  graphFilling (fun graph ctx => CallCFG.WellFormed ctx.1 ctx.2 graph) (fun graph => graph.flow.internal) CallCFG.edges

end Silmaril.Machine.Vex.ControlFlow
