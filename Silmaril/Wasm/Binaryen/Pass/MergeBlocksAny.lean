module

public import Silmaril.Wasm.Binaryen.Pass.UnusedBlocks
public import Silmaril.Wasm.Binaryen.CtxTyping

@[expose] public section

/-! # Merge nested blocks throughout a function

Search bottom-up for an eligible block that is a direct child of another block.
The enclosing block and its siblings remain. A site records its one-hole context;
the soundness leaf uses the existing block-unwrapping theorem. Only one site per
function is spliced in a round, so contexts never refer to already changed code.
-/

namespace Silmaril.Wasm.Binaryen.MergeBlocksAny

/-- An unused inner block together with its surrounding function body. -/
structure Site where
  ctx : BCtx
  type : BlockType
  body : List BExpr

/-- Lift sites through an enclosing context. -/
def under (k : BCtx) (ss : List Site) : List Site :=
  ss.map fun s => { s with ctx := k.comp s.ctx }

/-- Search each child sequence, retaining its structured parent. -/
def children (search : List BExpr → Bool → List Site) : BExpr → List Site
  | .op i args => under (.op i [] .hole []) (search args false)
  | .block bt body => under (.block bt [] .hole []) (search body true)
  | .loop bt body => under (.loop bt [] .hole []) (search body false)
  | .if_ bt c t f =>
      under (.ifCond bt [] .hole [] t f) (search c false) ++
      under (.ifThen bt c [] .hole [] f) (search t false) ++
      under (.ifElse bt c t [] .hole []) (search f false)
  | .tryTable .. => []

/-- Only direct children of blocks qualify as block merges. -/
def here (e : BExpr) (inBlock : Bool) : List Site :=
  match e with
  | .block bt body => if inBlock && UnusedBlocks.eligible body then
      [⟨.hole, bt, body⟩] else []
  | _ => []

/-- Enumerate nested-block sites, visiting children before the current node.
The explicit tree-node bound exceeds every path through a body. -/
def sites : Nat → List BExpr → Bool → List Site
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | fuel + 1, e :: es, inBlock =>
    under (.seq [] .hole es) (children (sites fuel) e ++ here e inBlock) ++
      under (.seq [e] .hole []) (sites fuel es inBlock)

mutual
/-- Node count, independent of non-executable `SizeOf` instances. -/
def nodes : BExpr → Nat
  | .op _ a | .block _ a | .loop _ a | .tryTable _ _ a => 1 + nodesList a
  | .if_ _ c t e => 1 + nodesList c + nodesList t + nodesList e
/-- Count sequence cells as well as tree nodes to bound the search recursion. -/
def nodesList : List BExpr → Nat
  | [] => 1
  | e :: es => 1 + nodes e + nodesList es
end

/-- Splice the first eligible nested site of one defined function. -/
def mergeAt (m : BModule) (g : Nat) : BModule :=
  match m.body? g with
  | none => m
  | some body => match (sites (nodesList body) body false).head? with
    | none => m
    | some s => m.withBody g (s.ctx.plug s.body)

end MergeBlocksAny

/-- Merge one unused inner block per function, at arbitrary nesting depth. -/
def mergeBlocksAny : BModule → BModule := UnusedBlocks.sweep MergeBlocksAny.mergeAt

end Silmaril.Wasm.Binaryen
