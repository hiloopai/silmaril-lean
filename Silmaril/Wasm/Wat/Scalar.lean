module

public meta import Silmaril.Wasm.Wat.Common

/-! # Shared scalar opcode families

The textual scalar operators share their spelling and immediate conventions
across Wasm1, Lime1, and Core3. Only the constructor namespace and the availability
of sign-extension/saturating conversions vary by profile.
-/

public meta section

namespace Silmaril.Wasm.Wat

structure ScalarSyntax where
  namespace_ : String
  extended : Bool
  packNamespace : String

def ScalarSyntax.cons (s : ScalarSyntax) (family name : String)
    (args : Array Term := #[]) : Lean.MacroM Term :=
  applyTerm (s.namespace_ ++ "." ++ family ++ "." ++ name) args

open Lean

def signTerm (signed : Bool) : MacroM Term :=
  coreTerm "Signedness" (if signed then "signed" else "unsigned")

def integerType (s : String) : MacroM Term := coreTerm "IntType" s
def floatType (s : String) : MacroM Term := coreTerm "FloatType" s

def conversionWith (p : ScalarSyntax) (ty op : String) : MacroM (Option Term) := do
  let finish (name : String) (args : Array Term := #[]) := do
    return some (← p.cons "Instr" "convert" #[← p.cons "ConvertOp" name args])
  if ty == "i32" && op == "wrap_i64" then return ← finish "wrap"
  if ty == "f32" && op == "demote_f64" then return ← finish "demote"
  if ty == "f64" && op == "promote_f32" then return ← finish "promote"
  if ty == "i64" then
    for (suffix, signed) in [("s", true), ("u", false)] do
      if op == "extend_i32_" ++ suffix then return ← finish "extend" #[← signTerm signed]
  if ty == "i32" || ty == "i64" then
    for source in ["f32", "f64"] do
      for (suffix, signed) in [("s", true), ("u", false)] do
        if op == "trunc_" ++ source ++ "_" ++ suffix then
          return ← finish "trunc" #[← floatType source, ← integerType ty, ← signTerm signed]
        if p.extended && op == "trunc_sat_" ++ source ++ "_" ++ suffix then
          return ← finish "truncSat" #[← floatType source, ← integerType ty, ← signTerm signed]
    let source := if ty == "i32" then "f32" else "f64"
    if op == "reinterpret_" ++ source then return ← finish "reinterpretInt" #[← floatType source]
  if ty == "f32" || ty == "f64" then
    for source in ["i32", "i64"] do
      for (suffix, signed) in [("s", true), ("u", false)] do
        if op == "convert_" ++ source ++ "_" ++ suffix then
          return ← finish "convert" #[← integerType source, ← floatType ty, ← signTerm signed]
    let source := if ty == "f32" then "i32" else "i64"
    if op == "reinterpret_" ++ source then return ← finish "reinterpretFloat" #[← integerType source]
  return none

def scalarOpWith (p : ScalarSyntax) (ty op : String) : MacroM (Option Term) := do
  if let some result ← conversionWith p ty op then return some result
  if ty == "i32" || ty == "i64" then
    let t ← integerType ty
    let finish (family : String) (oper : Term) := do
      return some (← p.cons "Instr" family #[t, oper])
    if ["clz", "ctz", "popcnt"].contains op then
      return ← finish "intUnOp" (← p.cons "IntUnOp" op)
    if p.extended then
      for size in ["8", "16", "32"] do
        if op == "extend" ++ size ++ "_s" && (ty == "i64" || size != "32") then
          return ← finish "intUnOp" (← p.cons "IntUnOp" "extend"
            #[← applyTerm (p.packNamespace ++ ".PackSize.i" ++ size)])
    if ["add", "sub", "mul", "and", "or", "xor", "shl", "rotl", "rotr"].contains op then
      return ← finish "intBinOp" (← coreTerm "IntBinOp" op)
    if op == "eqz" then return ← finish "intTestOp" (← coreTerm "IntTestOp" "eqz")
    if ["eq", "ne"].contains op then return ← finish "intRelOp" (← coreTerm "IntRelOp" op)
    for (suffix, signed) in [("s", true), ("u", false)] do
      for name in ["div", "rem", "shr"] do
        if op == name ++ "_" ++ suffix then
          return ← finish "intBinOp" (← coreTerm "IntBinOp" name #[← signTerm signed])
      for name in ["lt", "gt", "le", "ge"] do
        if op == name ++ "_" ++ suffix then
          return ← finish "intRelOp" (← coreTerm "IntRelOp" name #[← signTerm signed])
  if ty == "f32" || ty == "f64" then
    let t ← floatType ty
    if ["abs", "neg", "sqrt", "ceil", "floor", "trunc", "nearest"].contains op then
      return some (← p.cons "Instr" "floatUnOp" #[t, ← coreTerm "FloatUnOp" op])
    if ["add", "sub", "mul", "div", "min", "max", "copysign"].contains op then
      return some (← p.cons "Instr" "floatBinOp" #[t, ← coreTerm "FloatBinOp" op])
    if ["eq", "ne", "lt", "gt", "le", "ge"].contains op then
      return some (← p.cons "Instr" "floatRelOp" #[t, ← coreTerm "FloatRelOp" op])
  return none


end Silmaril.Wasm.Wat
