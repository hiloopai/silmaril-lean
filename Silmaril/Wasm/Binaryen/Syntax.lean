module

public import Silmaril.Wasm.Modules

@[expose] public section

/-! # Binaryen-style IR, layer D: folded Core 3.0 with de Bruijn labels

This is the lower of the two IR layers (see `Silmaril.Wasm.Binaryen.Syntax`). A `BExpr` is
a *folded* Core 3.0 instruction: an operator together with the subtrees that
compute its operands, or a structured control construct whose bodies are again
folded lists. Labels stay de Bruijn indices, exactly as in Core 3.0, so the
lowering `BExpr.lower` (`Binaryen/Lower.lean`) is total, structural and
injective on structured trees, and **the meaning of an IR program is the Core 3.0
meaning of its lowering**. There is no separate IR semantics in this slice; the
native interpreter (`Binaryen/Interp.lean`) is a later milestone that must be
proved sound *and* complete against the lowering (a separate interpreter-adequacy development (not included in this package)).

Binaryen correspondence (pinned at tag `version_133`, commit `fba5005a`):

* `src/wasm.h` — `Expression` subclasses. Binaryen's IR is a tree whose
  operands are children; `BExpr.op i args` is that shape for every flat Core
  instruction `i`. Binaryen names its labels; the named surface is
  `Binaryen/Named.lean` (layer N), resolved to this layer once by
  `Binaryen/Resolve.lean`.
* Binaryen allows "stacky" code only at the binary boundary; this layer allows
  it everywhere (`op i []` with operands supplied by earlier siblings), because
  Core 3.0 does. `fold` (`Binaryen/Lower.lean`) reconstructs trees as
  `src/wasm/wasm-ir-builder.cpp` (`IRBuilder`) does when reading a binary.

The datatype does not force `i` in `op i args` to be flat: a structured `Instr`
leaf (`op (.block ..) []`) is allowed, which makes the flat lifting
`BModule.lift` exactly inverse to lowering (`lower_lift`). `BExpr.Structured`
says every structured instruction is a tree node, as passes expect.
-/

namespace Silmaril.Wasm.Binaryen

/-- **Layer D expressions.** A folded Core 3.0 instruction. `op i args` lowers to
`lower args ++ [i]`; `block`/`loop`/`if_`/`tryTable` lower to the Core construct
whose bodies are the lowered child lists. `if_` keeps its condition as a folded
list, mirroring Binaryen's `If::condition`. -/
inductive BExpr where
  /-- A flat Core instruction applied to the trees computing (a suffix of) its operands. -/
  | op (i : Instr) (args : List BExpr)
  | block (bt : BlockType) (body : List BExpr)
  | loop (bt : BlockType) (body : List BExpr)
  | if_ (bt : BlockType) (cond thn els : List BExpr)
  /-- Exception handling. Opaque to every analysis until the EH milestone. -/
  | tryTable (bt : BlockType) (cs : List Catch) (body : List BExpr)
  deriving Repr

instance : Inhabited BExpr := ⟨.block .empty []⟩

/-- A function of layer D: Core 3.0's function declaration over folded bodies. -/
abbrev BFunc := Declaration.Func ValType (List BExpr)

/-- A module of layer D. Everything except the function bodies is Core 3.0 syntax
(`base`); `base.funcs` is ignored and replaced by the lowering of `funcs`. -/
structure BModule where
  base : Module
  funcs : List BFunc
  deriving Repr

/-- The structured Core instructions (those that carry bodies). -/
def structuredInstr : Instr → Bool
  | .block .. | .loop .. | .if_ .. | .tryTable .. => true
  | _ => false

mutual
/-- Every `op` node carries a flat instruction: structured control is a tree node. -/
def BExpr.structured : BExpr → Bool
  | .op i args => !structuredInstr i && BExpr.structuredList args
  | .block _ b => BExpr.structuredList b
  | .loop _ b => BExpr.structuredList b
  | .if_ _ c t e => BExpr.structuredList c && BExpr.structuredList t && BExpr.structuredList e
  | .tryTable _ _ b => BExpr.structuredList b
/-- `BExpr.structured` on a list. -/
def BExpr.structuredList : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.structured e && BExpr.structuredList es
end

/-- Update the element at `n` (no-op out of range). -/
def modifyAt {α : Type} (f : α → α) : Nat → List α → List α
  | _, [] => []
  | 0, a :: as => f a :: as
  | n + 1, a :: as => a :: modifyAt f n as

namespace BModule

/-- Number of imported functions: defined function `j` has index `numImportedFuncs + j`. -/
def numImportedFuncs (m : BModule) : Nat := m.base.importedFunctions.length

/-- Number of imported globals. -/
def numImportedGlobals (m : BModule) : Nat :=
  (m.base.imports.filter fun i => match i.type with | .global _ => true | _ => false).length

/-- The defined function with absolute index `f`, if any. -/
def defFunc? (m : BModule) (f : Nat) : Option BFunc :=
  if f < m.numImportedFuncs then none else m.funcs[f - m.numImportedFuncs]?

/-- Replace the body of defined function `g` (relative index). -/
def withBody (m : BModule) (g : Nat) (body : List BExpr) : BModule :=
  { m with funcs := modifyAt (fun f => { f with body := body }) g m.funcs }

/-- Replace defined function `g` (relative index). -/
def setFunc (m : BModule) (g : Nat) (f : BFunc) : BModule :=
  { m with funcs := modifyAt (fun _ => f) g m.funcs }

/-- The body of defined function `g`. -/
def body? (m : BModule) (g : Nat) : Option (List BExpr) := (m.funcs[g]?).map (·.body)

/-- The function type at a type index, read off the module's type section. -/
def funcType? (m : BModule) (t : TypeIdx) : Option FuncType :=
  match m.base.typeDefinitions[t.toNat]? with
  | some ⟨_, _, .func ft⟩ => some ft
  | _ => none

end BModule

end Silmaril.Wasm.Binaryen
