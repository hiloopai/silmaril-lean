module

public import Silmaril.Wasm.V1.Execution.Basic

/-!
# Store-independent reduction

Numeric relations include the permitted NaN choices. Control rules operate on
administrative labels and frames, with loop branches restarting the loop and
block branches leaving it. Literal values require no execution step.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution.Runtime

inductive PureStep : List Admin → List Admin → Prop where
  | nop : PureStep [.source .nop] []
  | unreachable : PureStep [.source .unreachable] [.trap]
  | drop (v : Value) : PureStep [value v, .source .drop] []
  | selectZero (a b : Value) (sameType : a.type = b.type) :
      PureStep [value a, value b, value (.int .i32 0), .source .select] [value b]
  | selectNonzero (a b : Value) (sameType : a.type = b.type) (c : BitVec 32) (h : c ≠ 0) :
      PureStep [value a, value b, value (.int .i32 c), .source .select] [value a]
  | block (bt : BlockType) (body : Expr) :
      PureStep [.source (.block bt body)] [.label bt.toList.length [] (expression body)]
  | loop (bt : BlockType) (body : Expr) :
      PureStep [.source (.loop bt body)] [.label 0 [.loop bt body] (expression body)]
  | ifZero (bt : BlockType) (left right : Expr) :
      PureStep [value (.int .i32 0), .source (.if_ bt left right)] [.source (.block bt right)]
  | ifNonzero (bt : BlockType) (left right : Expr) (c : BitVec 32) (h : c ≠ 0) :
      PureStep [value (.int .i32 c), .source (.if_ bt left right)] [.source (.block bt left)]
  | brIfZero (l : LabelIdx) :
      PureStep [value (.int .i32 0), .source (.brIf l)] []
  | brIfNonzero (l : LabelIdx) (c : BitVec 32) (h : c ≠ 0) :
      PureStep [value (.int .i32 c), .source (.brIf l)] [.source (.br l)]
  | brTable (ls : List LabelIdx) (default : LabelIdx) (c : BitVec 32) :
      PureStep [value (.int .i32 c), .source (.brTable ls default)]
        [.source (.br (ls[c.toNat]?.getD default))]
  | labelDone (n : Nat) (cont : Expr) (vs : List Value) :
      PureStep [.label n cont (values vs)] (values vs)
  | labelBranch (n : Nat) (cont : Expr) (extra vs : List Value) (tail : List Admin)
      (arity : vs.length = n) :
      PureStep [.label n cont (values extra ++ values vs ++ [.source (.br ⟨0⟩)] ++ tail)]
        (values vs ++ expression cont)
  | labelBranchOuter (n : Nat) (cont : Expr) (vs : List Value) (tail : List Admin)
      (l : LabelIdx) (outer : l.toNat ≠ 0) :
      PureStep [.label n cont (values vs ++ [.source (.br l)] ++ tail)]
        (values vs ++ [.source (.br (lowerLabel l))])
  | labelReturn (n : Nat) (cont : Expr) (vs : List Value) (tail : List Admin) :
      PureStep [.label n cont (values vs ++ [.source .return_] ++ tail)]
        (values vs ++ [.source .return_])
  | frameDone (n : Nat) (f : Frame) (vs : List Value) (arity : vs.length = n) :
      PureStep [.frame n f (values vs)] (values vs)
  | frameReturn (n : Nat) (f : Frame) (extra vs : List Value) (tail : List Admin)
      (arity : vs.length = n) :
      PureStep [.frame n f (values extra ++ values vs ++ [.source .return_] ++ tail)] (values vs)
  | trapValues (v : Value) (vs : List Value) (tail : List Admin) :
      PureStep (values (v :: vs) ++ [.trap] ++ tail) [.trap]
  | trapTail (i : Admin) (tail : List Admin) : PureStep (.trap :: i :: tail) [.trap]
  | labelTrap (n : Nat) (cont : Expr) : PureStep [.label n cont [.trap]] [.trap]
  | frameTrap (n : Nat) (f : Frame) : PureStep [.frame n f [.trap]] [.trap]
  | localTee (i : LocalIdx) (v : Value) :
      PureStep [value v, .source (.localTee i)] [value v, value v, .source (.localSet i)]
  | intUnary (t : IntType) (op : IntUnOp) (x : BitVec t.width) :
      PureStep [value (.int t x), .source (.intUnOp t op)]
        [value (.int t (Numerics.intUnOp t op.toCore x))]
  | intBinary (t : IntType) (op : IntBinOp) (x y z : BitVec t.width)
      (h : Numerics.intBinOp t op x y = .ok z) :
      PureStep [value (.int t x), value (.int t y), .source (.intBinOp t op)] [value (.int t z)]
  | intBinaryTrap (t : IntType) (op : IntBinOp) (x y : BitVec t.width) (err : Numerics.IntTrap)
      (h : Numerics.intBinOp t op x y = .error err) :
      PureStep [value (.int t x), value (.int t y), .source (.intBinOp t op)] [.trap]
  | intTest (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
      PureStep [value (.int t x), .source (.intTestOp t op)]
        [value (.int .i32 (Numerics.intTestOp t op x))]
  | intRel (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
      PureStep [value (.int t x), value (.int t y), .source (.intRelOp t op)]
        [value (.int .i32 (Numerics.intRelOp t op x y))]
  | floatUnary (t : FloatType) (op : FloatUnOp) (x y : BitVec t.width)
      (h : Numerics.floatUnOpRel t op x y) :
      PureStep [value (.float t x), .source (.floatUnOp t op)] [value (.float t y)]
  | floatBinary (t : FloatType) (op : FloatBinOp) (x y z : BitVec t.width)
      (h : Numerics.floatBinOpRel t op x y z) :
      PureStep [value (.float t x), value (.float t y), .source (.floatBinOp t op)]
        [value (.float t z)]
  | floatRel (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
      PureStep [value (.float t x), value (.float t y), .source (.floatRelOp t op)]
        [value (.int .i32 (Numerics.floatRelOp t op x y))]
  | convert (op : ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (y : Numerics.NumValue op.toCore.target) (h : Numerics.convertRel op.toCore x (.ok y)) :
      PureStep [value ⟨op.toCore.source, x⟩, .source (.convert op)] [value ⟨op.toCore.target, y⟩]
  | convertTrap (op : ConvertOp) (x : Numerics.NumValue op.toCore.source)
      (err : Numerics.FloatTrap) (h : Numerics.convertRel op.toCore x (.error err)) :
      PureStep [value ⟨op.toCore.source, x⟩, .source (.convert op)] [.trap]

end Silmaril.Wasm.V1.Execution
