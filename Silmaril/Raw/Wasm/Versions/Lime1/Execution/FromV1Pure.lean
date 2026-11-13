module

public import Silmaril.Wasm.Lime1.Execution.Transport

@[expose] public section
namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution.Runtime

/-- Each store-independent Wasm1 reduction has the same Lime1 reduction. -/
theorem PureStep.toLime {before after : List Admin} (h : PureStep before after)
    (types : List FuncType) : Lime1.Execution.PureStep types (codeToLime before) (codeToLime after) := by
  cases h with
  | nop => exact .nop
  | unreachable => exact .unreachable
  | drop v =>
    simpa [AdminInstr.map, Instr.toLime] using Lime1.Execution.PureStep.drop (types := types) v
  | selectZero a b sameType =>
    simpa [AdminInstr.map, Instr.toLime] using Lime1.Execution.PureStep.selectZero (types := types) a b sameType
  | selectNonzero a b sameType c h =>
    simpa [AdminInstr.map, Instr.toLime] using Lime1.Execution.PureStep.selectNonzero (types := types) a b sameType c h
  | block bt body =>
    simpa only [codeToLime_cons, codeToLime_nil, AdminInstr.map, Instr.toLime,
      map_expression, Lime1.Execution.values, List.map_nil, List.map_cons, List.length_nil, List.nil_append] using
      Lime1.Execution.PureStep.block bt.toLime (Expr.toLime body) ⟨[], bt.toList⟩
        (blockType_toLime types bt) [] rfl
  | loop bt body =>
    simpa only [codeToLime_cons, codeToLime_nil, AdminInstr.map, Instr.toLime,
      map_expression, Lime1.Execution.values, List.map_nil, List.map_cons, List.length_nil, List.nil_append] using
      Lime1.Execution.PureStep.loop bt.toLime (Expr.toLime body) ⟨[], bt.toList⟩
        (blockType_toLime types bt) [] rfl
  | ifZero bt left right =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.ifZero (types := types) bt.toLime (Expr.toLime left) (Expr.toLime right)
  | ifNonzero bt left right c h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.ifNonzero (types := types) bt.toLime (Expr.toLime left) (Expr.toLime right) c h
  | brIfZero l =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.brIfZero (types := types) l
  | brIfNonzero l c h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.brIfNonzero (types := types) l c h
  | brTable ls d c =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.brTable (types := types) ls d c
  | labelDone n cont vs =>
    simpa [AdminInstr.map, ← Expr.toLime_eq_map] using
      Lime1.Execution.PureStep.labelDone (types := types) n (Expr.toLime cont) vs
  | labelBranch n cont extra vs tail arity =>
    simpa [AdminInstr.map, Instr.toLime, ← Expr.toLime_eq_map] using
      Lime1.Execution.PureStep.labelBranch (types := types) n (Expr.toLime cont) extra vs
        (codeToLime tail) arity
  | labelBranchOuter n cont vs tail l outer =>
    simpa [AdminInstr.map, Instr.toLime, ← Expr.toLime_eq_map] using
      Lime1.Execution.PureStep.labelBranchOuter (types := types) n (Expr.toLime cont) vs
        (codeToLime tail) l outer
  | labelReturn n cont vs tail =>
    simpa [AdminInstr.map, Instr.toLime, ← Expr.toLime_eq_map] using
      Lime1.Execution.PureStep.labelReturn (types := types) n (Expr.toLime cont) vs (codeToLime tail)
  | frameDone n f vs arity =>
    simpa [AdminInstr.map] using
      Lime1.Execution.PureStep.frameDone (types := types) n f vs arity
  | frameReturn n f extra vs tail arity =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.frameReturn (types := types) n f extra vs (codeToLime tail) arity
  | trapValues v vs tail =>
    simpa [AdminInstr.map] using
      Lime1.Execution.PureStep.trapValues (types := types) v vs (codeToLime tail)
  | trapTail i tail =>
    simpa [AdminInstr.map] using
      Lime1.Execution.PureStep.trapTail (types := types) (AdminInstr.map Instr.toLime i) (codeToLime tail)
  | labelTrap n cont =>
    simpa [AdminInstr.map, ← Expr.toLime_eq_map] using
      Lime1.Execution.PureStep.labelTrap (types := types) n (Expr.toLime cont)
  | frameTrap n f =>
    simpa [AdminInstr.map] using
      Lime1.Execution.PureStep.frameTrap (types := types) n f
  | localTee i v =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.localTee (types := types) i v
  | intUnary t op x =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.intUnary (types := types) t op.toLime x (by cases op <;> rfl)
  | intBinary t op x y z h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.intBinary (types := types) t op x y z h
  | intBinaryTrap t op x y err h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.intBinaryTrap (types := types) t op x y err h
  | intTest t op x =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.intTest (types := types) t op x
  | intRel t op x y =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.intRel (types := types) t op x y
  | floatUnary t op x y h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.floatUnary (types := types) t op x y h
  | floatBinary t op x y z h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.floatBinary (types := types) t op x y z h
  | floatRel t op x y =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.floatRel (types := types) t op x y
  | convert op x y h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.convert (types := types) op.toCore x y h
  | convertTrap op x err h =>
    simpa [AdminInstr.map, Instr.toLime] using
      Lime1.Execution.PureStep.convertTrap (types := types) op.toCore x err h

end Silmaril.Wasm.V1.Execution
