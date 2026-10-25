module

public import Silmaril.Wasm.Validation.TypeOk

@[expose] public section

/-! # Typing family: numeric instructions (§2.3 "Numeric instructions")

Spec rules (all present): `Instr_ok/const`, `Instr_ok/unop`, `Instr_ok/binop`,
`Instr_ok/testop`, `Instr_ok/relop`, `Instr_ok/cvtop`.

The source syntax splits each spec rule by integer/float operator family. The
spec's syntactic side condition on `EXTEND sz` (`sz < |Inn|`, part of the grammar
of `unop_(Inn)`) is the premise `op.valid t = true`, since the Lean syntax does
not enforce it.
-/

namespace Silmaril.Wasm.Validation

inductive NumericInstrOk (C : Context) : Instr → InstrType → Prop where
  /-- `Instr_ok/const` (integers). -/
  | intConst (t : IntType) (b : BitVec t.width) :
      NumericInstrOk C (.intConst t b) (.plain [] [.num (.int t)])
  /-- `Instr_ok/const` (floats). -/
  | floatConst (t : FloatType) (b : BitVec t.width) :
      NumericInstrOk C (.floatConst t b) (.plain [] [.num (.float t)])
  /-- `Instr_ok/unop` (integers). -/
  | intUnOp {t : IntType} {op : IntUnOp} (h : op.valid t = true) :
      NumericInstrOk C (.intUnOp t op) (.plain [.num (.int t)] [.num (.int t)])
  /-- `Instr_ok/unop` (floats). -/
  | floatUnOp (t : FloatType) (op : FloatUnOp) :
      NumericInstrOk C (.floatUnOp t op) (.plain [.num (.float t)] [.num (.float t)])
  /-- `Instr_ok/binop` (integers). -/
  | intBinOp (t : IntType) (op : IntBinOp) :
      NumericInstrOk C (.intBinOp t op) (.plain [.num (.int t), .num (.int t)] [.num (.int t)])
  /-- `Instr_ok/binop` (floats). -/
  | floatBinOp (t : FloatType) (op : FloatBinOp) :
      NumericInstrOk C (.floatBinOp t op)
        (.plain [.num (.float t), .num (.float t)] [.num (.float t)])
  /-- `Instr_ok/testop`. -/
  | intTestOp (t : IntType) (op : IntTestOp) :
      NumericInstrOk C (.intTestOp t op) (.plain [.num (.int t)] [.i32])
  /-- `Instr_ok/relop` (integers). -/
  | intRelOp (t : IntType) (op : IntRelOp) :
      NumericInstrOk C (.intRelOp t op) (.plain [.num (.int t), .num (.int t)] [.i32])
  /-- `Instr_ok/relop` (floats). -/
  | floatRelOp (t : FloatType) (op : FloatRelOp) :
      NumericInstrOk C (.floatRelOp t op) (.plain [.num (.float t), .num (.float t)] [.i32])
  /-- `Instr_ok/cvtop`. -/
  | convert (op : ConvertOp) :
      NumericInstrOk C (.convert op) (.plain [.num op.source] [.num op.target])

end Silmaril.Wasm.Validation
