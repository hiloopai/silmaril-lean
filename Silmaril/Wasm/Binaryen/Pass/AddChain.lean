module

public import Silmaril.Wasm.Binaryen.Pass.ConstBranch
public import Silmaril.Wasm.Binaryen.Exe.Encode

@[expose] public section

/-! Combine adjacent wrapping constant additions, preserving the evaluation of
all other operands. Both folded trees and flat stack instruction lists are visited. -/

namespace Silmaril.Wasm.Binaryen.AddChain

mutual
def foldE : BExpr → BExpr
  | .op (.intBinOp .i32 .add)
      [.op (.intBinOp .i32 .add) [x, .op (.intConst .i32 a) []], .op (.intConst .i32 b) []] =>
    .op (.intBinOp .i32 .add) [foldE x, .op (.intConst .i32 (a + b)) []]
  | .op (.intBinOp .i64 .add)
      [.op (.intBinOp .i64 .add) [x, .op (.intConst .i64 a) []], .op (.intConst .i64 b) []] =>
    .op (.intBinOp .i64 .add) [foldE x, .op (.intConst .i64 (a + b)) []]
  | .op i args => .op i (foldL args)
  | .block bt b => .block bt (foldL b)
  | .loop bt b => .loop bt (foldL b)
  | .if_ bt c t e => .if_ bt (foldL c) (foldL t) (foldL e)
  | .tryTable bt cs b => .tryTable bt cs (foldL b)
termination_by x => sizeOf x
decreasing_by all_goals simp_wf; all_goals omega

def foldL : List BExpr → List BExpr
  | .op (.intConst .i32 a) [] :: .op (.intBinOp .i32 .add) [] ::
      .op (.intConst .i32 b) [] :: .op (.intBinOp .i32 .add) [] :: es =>
    .op (.intConst .i32 (a + b)) [] :: .op (.intBinOp .i32 .add) [] :: foldL es
  | .op (.intConst .i64 a) [] :: .op (.intBinOp .i64 .add) [] ::
      .op (.intConst .i64 b) [] :: .op (.intBinOp .i64 .add) [] :: es =>
    .op (.intConst .i64 (a + b)) [] :: .op (.intBinOp .i64 .add) [] :: foldL es
  | [] => []
  | e :: es => foldE e :: foldL es
termination_by es => sizeOf es
decreasing_by all_goals simp_wf; all_goals omega
end

def addChain (m : BModule) : BModule :=
  { m with funcs := m.funcs.map fun f => { f with body := foldL f.body } }

/-- Reject invalid, unencodable, or larger results. -/
def addChainChecked (m : BModule) : BModule :=
  let m' := addChain m
  if ConstBranch.exportsFunc m && Exe.validOk m' then
    match Exe.encodeModule? m'.lower, Exe.encodeModule? m.lower with
    | .ok bs', .ok bs => if bs'.length ≤ bs.length then m' else m
    | _, _ => m
  else m

end Silmaril.Wasm.Binaryen.AddChain
