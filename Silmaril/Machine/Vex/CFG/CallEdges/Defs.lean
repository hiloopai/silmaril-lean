module

public import Silmaril.Semantics.Region.Tree.CFG.Defs

/-! # Abstract direct-call CFGs, independent of instruction semantics -/

@[expose] public section

namespace Silmaril.Machine.Vex.ControlFlow

open Silmaril.Semantics.Region.Tree (FlatCFG)

/-- Ownership classifies calls relative to the supplied program, not to the
current function. An unowned label is external only if explicitly declared. -/
structure Partition (Label Function : Type*) where
  owner : Label → Option Function
  entry : Function → Label
  externals : Set Label

def Partition.Internal {Label Function : Type*} (part : Partition Label Function) (label : Label) : Prop :=
  ∃ callee, part.owner label = some callee

def Partition.External {Label Function : Type*} (part : Partition Label Function) (label : Label) : Prop :=
  part.owner label = none ∧ label ∈ part.externals

/-- Ordinary edges stay in the selected function or end at an unowned,
declared boundary. They do not stand for calls or resumption edges. -/
structure FlatWellFormed {Label Function : Type*} (part : Partition Label Function)
    (focus : Function) (graph : FlatCFG Label) : Prop where
  entry_eq : graph.entry = part.entry focus
  entry_owned : part.owner graph.entry = some focus
  internal_eq : graph.internal = {label | part.owner label = some focus}
  sources : graph.SourceClosed
  targets : ∀ origin target, target ∈ graph.successors origin → target ∈ graph.internal ∪ graph.exits
  exits_unowned : ∀ label ∈ graph.exits, part.owner label = none

inductive Edge (Label : Type*) where
  | ordinary (target : Label)
  | call (callee : Label)
  | fakeReturn (continuation : Label)
  deriving DecidableEq, Repr

/-- A candidate caller-local continuation is not a callee return edge and
does not assert the callee returns. -/
structure CallSite (Label : Type*) where
  callee : Label
  continuation : Option Label
  deriving DecidableEq, Repr

/-- The slice for one function; callee labels can point outside this slice.
There is at most one known direct call at the end of a given block. -/
structure CallCFG (Label : Type*) where
  flow : FlatCFG Label
  calls : Label → Option (CallSite Label)

def CallCFG.embed {Label : Type*} (graph : FlatCFG Label) : CallCFG Label := ⟨graph, fun _ => none⟩

def ordinaryEdges {Label : Type*} (graph : FlatCFG Label) (origin : Label) : Set (Edge Label) :=
  {edge | match edge with
  | .ordinary target => target ∈ graph.successors origin
  | _ => False}

def CallCFG.edges {Label : Type*} (graph : CallCFG Label) (origin : Label) : Set (Edge Label) :=
  {edge | match edge with
  | .ordinary target => target ∈ graph.flow.successors origin
  | .call callee => ∃ site, graph.calls origin = some site ∧ site.callee = callee
  | .fakeReturn next => ∃ site, graph.calls origin = some site ∧ site.continuation = some next}

structure CallCFG.WellFormed {Label Function : Type*} (part : Partition Label Function)
    (focus : Function) (graph : CallCFG Label) : Prop where
  flow : FlatWellFormed part focus graph.flow
  callSite : ∀ origin site, graph.calls origin = some site →
    origin ∈ graph.flow.internal ∧ graph.flow.successors origin = ∅ ∧
    ((∃ callee, part.owner site.callee = some callee ∧ site.callee = part.entry callee) ∨
      part.External site.callee) ∧
    ∀ next, site.continuation = some next → next ∈ graph.flow.internal

def CallCFG.HasInternalCall {Label Function : Type*} (part : Partition Label Function) (graph : CallCFG Label) : Prop :=
  ∃ origin callee, .call callee ∈ graph.edges origin ∧ part.Internal callee

def CallCFG.HasExternalCall {Label Function : Type*} (part : Partition Label Function) (graph : CallCFG Label) : Prop :=
  ∃ origin callee, .call callee ∈ graph.edges origin ∧ part.External callee

def CallCFG.NoCalls {Label : Type*} (graph : CallCFG Label) : Prop := ∀ origin, graph.calls origin = none

/-- Exact representation by an ordinary graph, not equality of the lossy
ordinary projection `flow`. -/
def CallCFG.InFlatImage {Label Function : Type*} (part : Partition Label Function)
    (focus : Function) (graph : CallCFG Label) : Prop :=
  ∃ flat, FlatWellFormed part focus flat ∧ CallCFG.embed flat = graph

end Silmaril.Machine.Vex.ControlFlow
