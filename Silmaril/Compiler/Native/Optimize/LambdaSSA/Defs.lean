module

public import Silmaril.Compiler.Native.Optimize.LocalSSA.Defs
public import Silmaril.Compiler.Native.Optimize.Validation.Defs
public import Silmaril.Machine.RTL.Thms
/-!
# Arithmetic optimization in the existing lambda-SSA representation

The C backend retains `Silmaril` declaration names, whereas the earlier RTL and
lambda-SSA port uses its own names. This adapter crosses that boundary explicitly
for integer constants, moves, extensions, and add/subtract/multiply/bitwise ops.
It rejects all other instructions, including memory access and symbolic calls.

An accepted local SSA block is translated by the existing `toLambdaSSA`, folded
under lexical binders, and flattened by `ofLambdaSSA?`. Mutable-register boundary
commits are restored and the independent validator checks the resulting block.
The folding traversal has semantic preservation proofs for the existing typed,
pure, total arithmetic fragment, including all finite region/CFG results.
Syntactic typing and exact region annotations are preserved for all existing
typed input syntax, independently of those semantic restrictions. Namespace
adapters, an admitted input view, flattening, restore/validation and the complete
selected optimizer still need their composition proofs. Existing RTL translation theorems retain
their original hypotheses.
-/

@[expose] public section

namespace Silmaril.Compiler.Native.Optimize.LambdaSSA

open Silmaril.Compile
open Silmaril.Machine

namespace Old
abbrev Unop := Silmaril.Machine.Lir.Unop
abbrev Binop := Silmaril.Machine.Lir.Binop
abbrev Op := Silmaril.Machine.RTL.SSA.Op Nat
abbrev Func := Silmaril.Machine.RTL.SSA.Func Nat
abbrev Opcode := Silmaril.Machine.RTL.Opcode ([] : List Silmaril.Machine.RTL.Signature)
abbrev Tm := Silmaril.Isotope.LambdaSSA.Tm Opcode
abbrev Region := Silmaril.Isotope.LambdaSSA.Region Opcode
end Old

def oldUnary : Lir.Unop → Old.Unop
  | .clz => .clz | .ctz => .ctz | .popcnt => .popcnt
  | .clz32 => .clz32 | .ctz32 => .ctz32 | .popcnt32 => .popcnt32
  | .sext8 => .sext8 | .sext16 => .sext16 | .sext32 => .sext32
  | .zext8 => .zext8 | .zext16 => .zext16 | .zext32 => .zext32
  | .eqz => .eqz

def newUnary : Old.Unop → Lir.Unop
  | .clz => .clz | .ctz => .ctz | .popcnt => .popcnt
  | .clz32 => .clz32 | .ctz32 => .ctz32 | .popcnt32 => .popcnt32
  | .sext8 => .sext8 | .sext16 => .sext16 | .sext32 => .sext32
  | .zext8 => .zext8 | .zext16 => .zext16 | .zext32 => .zext32
  | .eqz => .eqz

def oldBinary : Lir.Binop → Option Old.Binop
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .and => some .and | .or => some .or | .xor => some .xor
  | _ => none

def newBinary : Old.Binop → Option Lir.Binop
  | .add => some .add | .sub => some .sub | .mul => some .mul
  | .and => some .and | .or => some .or | .xor => some .xor
  | _ => none

def oldOp : Mir.Instr → Option Old.Op
  | .op (.const d w) => some (.const d w)
  | .op (.move d a) => some (.move d a)
  | .op (.unary op d a) => some (.unary (oldUnary op) d a)
  | .op (.binary op d a b) => (oldBinary op).map (.binary · d a b)
  | _ => none

def newOp (reg : Nat → Nat) : Old.Op → Option Mir.Instr
  | .const d w => some (.op (.const (reg d) w))
  | .move d a => some (.op (.move (reg d) (reg a)))
  | .unary op d a => some (.op (.unary (newUnary op) (reg d) (reg a)))
  | .binary op d a b => (newBinary op).map fun o =>
    .op (.binary o (reg d) (reg a) (reg b))
  | _ => none

/-- The exact lambda-SSA representation and flattening annotation for a local
arithmetic block. The exit returns its mutable-register boundary values. -/
structure View where
  inputs : List Nat
  outputs : List Nat
  region : Old.Region
  annotation : Silmaril.Machine.RTL.SSA.Ann

def view (base : Nat) (b : Mir.Block) : Option View := do
  let ssa := enter base b
  if !ssa.isSSA then none else do
    let ops ← ssa.body.instrs.toList.mapM oldOp
    let fn : Old.Func :=
      { sig := ⟨ssa.inputs.length, ssa.outputs.length⟩, entry := 0,
        blocks := [⟨ssa.inputs, ops, .ret (ssa.outputs.map (·.2))⟩] }
    let bodyAnn := ops.foldr (fun _ a => Silmaril.Machine.RTL.SSA.Ann.let₁ a) (.cfg [] .br [])
    let result : View :=
      { inputs := ssa.inputs, outputs := ssa.outputs.map (·.1),
        region := Silmaril.Machine.RTL.SSA.toLambdaSSA [] fn,
        annotation := .cfg [ssa.inputs.length] .br [bodyAnn] }
    return result

/-- Constant information about a packed tuple. Unknown components are retained
separately so projections of known tuple components can still be folded. -/
inductive Abstract where
  | unknown
  | word (value : Lir.Word)
  | unit
  | pair (left right : Abstract)
  deriving Inhabited, Repr

def packed (w : Lir.Word) : Abstract := .pair (.word w) .unit

def constantOp : Old.Opcode → Abstract → Option Lir.Word
  | .move, .pair (.word x) .unit => some x
  | .unary op, .pair (.word x) .unit => some (op.eval x)
  | .binary op, .pair (.word x) (.pair (.word y) .unit) => op.eval x y
  | _, _ => none

/-- Fold arithmetic in lambda-SSA terms under their actual lexical environment.
Tuple projections introduced by the RTL translation are analyzed through let₂. -/
def foldTm (env : List Abstract) : Old.Tm → Old.Tm × Abstract × Nat
  | .var i => (.var i, env.getD i .unknown, 0)
  | .unit => (.unit, .unit, 0)
  | .op (.const w) arg => (.op (.const w) arg, packed w, 0)
  | .op opcode arg =>
    let (arg', value, count) := foldTm env arg
    match constantOp opcode value with
    | some w => (.op (.const w) .unit, packed w, count + 1)
    | none => (.op opcode arg', .unknown, count)
  | .pair a b =>
    let (a', av, ac) := foldTm env a
    let (b', bv, bc) := foldTm env b
    (.pair a' b', .pair av bv, ac + bc)
  | .let₁ a b =>
    let (a', av, ac) := foldTm env a
    let (b', bv, bc) := foldTm (av :: env) b
    (.let₁ a' b', bv, ac + bc)
  | .let₂ a b =>
    let (a', av, ac) := foldTm env a
    let (left, right) := match av with
      | .pair left right => (left, right)
      | _ => (.unknown, .unknown)
    let (b', bv, bc) := foldTm (right :: left :: env) b
    (.let₂ a' b', bv, ac + bc)
  | .inl a => let (a', _, ac) := foldTm env a; (.inl a', .unknown, ac)
  | .inr a => let (a', _, ac) := foldTm env a; (.inr a', .unknown, ac)
  | .abort a => let (a', _, ac) := foldTm env a; (.abort a', .unknown, ac)
  | .case a left right =>
    let (a', _, ac) := foldTm env a
    let (left', _, lc) := foldTm (.unknown :: env) left
    let (right', _, rc) := foldTm (.unknown :: env) right
    (.case a' left' right', .unknown, ac + lc + rc)

def foldRegion (env : List Abstract) : Old.Region → Old.Region × Nat
  | .br label arg =>
    let (arg', _, count) := foldTm env arg
    (.br label arg', count)
  | .let₁ value body =>
    let (value', known, vc) := foldTm env value
    let (body', bc) := foldRegion (known :: env) body
    (.let₁ value' body', vc + bc)
  | .let₂ value body =>
    let (value', known, vc) := foldTm env value
    let (left, right) := match known with
      | .pair left right => (left, right)
      | _ => (.unknown, .unknown)
    let (body', bc) := foldRegion (right :: left :: env) body
    (.let₂ value' body', vc + bc)
  | .case discr left right =>
    let (discr', _, dc) := foldTm env discr
    let (left', lc) := foldRegion (.unknown :: env) left
    let (right', rc) := foldRegion (.unknown :: env) right
    (.case discr' left' right', dc + lc + rc)
  | .cfg entry k blocks =>
    let (entry', ec) := foldRegion env entry
    let folded := fun i => foldRegion (.unknown :: env) (blocks i)
    let count := (List.finRange k).foldl (fun n i => n + (folded i).2) ec
    (.cfg entry' k (fun i => (folded i).1), count)

/-- Restore a flattened pure local block to the surrounding symbolic Mir CFG. -/
def restore (base : Nat) (source : Mir.Block) (v : View) (region : Old.Region) :
    Option Mir.Block := do
  let fn ← Silmaril.Machine.RTL.SSA.ofLambdaSSA? [] region v.annotation
    v.inputs.length v.outputs.length
  if fn.entry != 0 || fn.blocks.length != 1 then none else do
    let b ← fn.blocks[0]?
    if b.params != List.range v.inputs.length then none else do
      let .ret values := b.term | none
      if values.length != v.outputs.length then none else do
        let reg := fun r => if r < v.inputs.length then v.inputs.getD r 0
          else base + (r - v.inputs.length)
        let instrs ← b.ops.mapM (newOp reg)
        let commits := (v.outputs.zip values).map fun (original, result) =>
          Mir.Instr.op (.move original (reg result))
        return ⟨(instrs ++ commits).toArray, source.term⟩

/-- A concrete lambda-SSA optimization route. Unsupported blocks, no-op folds,
failed flattening and validation failures return `none` for caller fallback. -/
def optimize? (base : Nat) (source : Mir.Block) : Option (Mir.Block × Nat) := do
  if source.instrs.size > 1024 then none else do
    let v ← view base source
    let (region, count) := foldRegion [.unknown] v.region
    if count = 0 then none else do
      let candidate ← restore base source v region
      if Validation.check base source candidate then some (candidate, count) else none

end Silmaril.Compiler.Native.Optimize.LambdaSSA
