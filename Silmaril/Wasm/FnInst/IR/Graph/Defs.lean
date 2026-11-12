module

public import Silmaril.Wasm.FnInst.IR.Bodies.Thms
public import Silmaril.Logic.Inst.Graph.Defs

/-!
# The logic graph of the function-body variants

Five nodes over a signature frame `F`, all with the Binaryen environment
`Store H × ModuleInst` (the fragment and SSA languages ignore it):

```
  bir ──ofBir──▶ fragNative ──nativeIncl──▶ frag ──toSSA──▶ ssa
                                             ▲               ▲
                                           ofSSA          decIncl
                                             └──── ssaDec ───┘
```

Every edge is the comorphism of an exact translation with the identity environment map, so
every path is model-expansive (`graph_pathModelExpansive`) and borrows validity and
consequence both ways (`GraphSpec.valid_path_iff`, `entails_path_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open CategoryTheory
open Silmaril.Inst
open Silmaril.Wasm.Execution.Core

/-- The body variants. -/
inductive Node : Type
  | bir
  | fragNative
  | frag
  | ssa
  | ssaDec
  deriving DecidableEq

/-- The body language of a node, for host type `H`. -/
def Node.lang (H : Type) : Node → Lang
  | .bir => IR.bir H
  | .fragNative => IR.fragNative (Store H × ModuleInst)
  | .frag => IR.frag (Store H × ModuleInst)
  | .ssa => IR.ssa (Store H × ModuleInst)
  | .ssaDec => IR.ssaDec (Store H × ModuleInst)

/-- The institution of a node. -/
abbrev Node.inst (H : Type) {Sig : Type} [Category.{0} Sig] (F : Frame Sig) (n : Node) :
    Institution₀ :=
  (n.lang H).inst F

variable (H : Type) {Sig : Type} [Category.{0} Sig] (F : Frame Sig)

/-- The graph of the body variants. -/
def graph : GraphSpec (Node.inst H F) where
  comors :=
    [⟨.bir, .fragNative, (ofBir H).comorphism F⟩,
     ⟨.fragNative, .frag, (nativeIncl _).comorphism F⟩,
     ⟨.frag, .ssa, (toSSA _).comorphism F⟩,
     ⟨.ssaDec, .frag, (ofSSA _).comorphism F⟩,
     ⟨.ssaDec, .ssa, (decIncl _).comorphism F⟩]

/-- Every path of the graph is model-expansive. -/
theorem graph_pathModelExpansive {a b : Node}
    (p : Quiver.Path (V := (graph H F).toLogicGraph.Idx) a b) :
    (graph H F).toLogicGraph.PathModelExpansive p :=
  (graph H F).pathModelExpansive ((graph H F).allModelExpansive_of_forall fun i => by
    match i with
    | ⟨0, _⟩ => exact (ofBir H).modelExpansive F (fun e => ⟨e, rfl⟩)
    | ⟨1, _⟩ => exact (nativeIncl _).modelExpansive F (fun e => ⟨e, rfl⟩)
    | ⟨2, _⟩ => exact (toSSA _).modelExpansive F (fun e => ⟨e, rfl⟩)
    | ⟨3, _⟩ => exact (ofSSA _).modelExpansive F (fun e => ⟨e, rfl⟩)
    | ⟨4, _⟩ => exact (decIncl _).modelExpansive F (fun e => ⟨e, rfl⟩)) p

end Silmaril.Wasm.FnInst.IR
