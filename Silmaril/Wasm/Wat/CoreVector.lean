module

public import Silmaril.Wasm.Instructions
public meta import Silmaril.Wasm.Wat.Scalar

/-! # Core3 SIMD text instructions

The mnemonic matrix follows the pinned Core3 text grammar, including relaxed
SIMD. The AST records source and target shapes explicitly; their order is not
inferred from a string after elaboration. Lane immediates have the grammar's byte
bound; validation of lane indices against a particular shape remains separate.
-/

public meta section

open Lean
namespace Silmaril.Wasm.Wat.Core

abbrev FloatParser := Nat → String → Except String Nat

structure VectorShape where
  name : String
  width : Nat
  lanes : Nat
  integer : Bool

def vectorShapes : List VectorShape :=
  [⟨"i8x16", 8, 16, true⟩, ⟨"i16x8", 16, 8, true⟩,
   ⟨"i32x4", 32, 4, true⟩, ⟨"i64x2", 64, 2, true⟩,
   ⟨"f32x4", 32, 4, false⟩, ⟨"f64x2", 64, 2, false⟩]

def VectorShape.shapeTerm (s : VectorShape) : MacroM Term := do
  coreTerm "Shape" (if s.integer then "int" else "float")
    #[← coreTerm (if s.integer then "IntShape" else "FloatShape") s.name]

def intShape (name : String) : MacroM Term := coreTerm "IntShape" name
def floatShape (name : String) : MacroM Term := coreTerm "FloatShape" name

def instr (name : String) (args : Array Term := #[]) : MacroM Term :=
  coreTerm "Instr" name args

/-- Scalar-lane operators whose complete instruction has no immediate operands. -/
def vectorOpcode (mnemonic : String) : MacroM (Option Term) := do
  let [ty, op] := mnemonic.splitOn "." | return none
  if ty == "v128" then
    if op == "not" then return some (← instr "vecUnOp" #[← coreTerm "VecUnOp" "not"])
    if ["and", "andnot", "or", "xor"].contains op then
      return some (← instr "vecBinOp" #[← coreTerm "VecBinOp" op])
    if op == "bitselect" then
      return some (← instr "vecTernOp" #[← coreTerm "VecTernOp" "bitselect"])
    if op == "any_true" then return some (← instr "vecTestOp" #[← coreTerm "VecTestOp" "anyTrue"])
  let some shape := vectorShapes.find? (·.name == ty) | return none
  if op == "splat" then return some (← instr "vecSplat" #[← shape.shapeTerm])
  if shape.integer then
    let s ← intShape ty
    let shaped (family name : String) (args : Array Term := #[]) := do
      instr family #[s, ← coreTerm (match family with
        | "vecIntUnOp" => "VecIntUnOp" | "vecIntBinOp" => "VecIntBinOp"
        | "vecIntTernOp" => "VecIntTernOp" | "vecIntRelOp" => "IntRelOp"
        | _ => "VecShiftOp") name args]
    if ["abs", "neg"].contains op || (ty == "i8x16" && op == "popcnt") then
      return some (← shaped "vecIntUnOp" op)
    if ["add", "sub"].contains op || (shape.width ≥ 16 && op == "mul") then
      return some (← shaped "vecIntBinOp" op)
    if shape.width ≤ 16 && op == "avgr_u" then return some (← shaped "vecIntBinOp" "avgrU")
    if ty == "i16x8" then
      if op == "q15mulr_sat_s" then return some (← shaped "vecIntBinOp" "q15mulrSatS")
      if op == "relaxed_q15mulr_s" then return some (← shaped "vecIntBinOp" "relaxedQ15mulrS")
    if op == "relaxed_laneselect" then return some (← shaped "vecIntTernOp" "relaxedLaneSelect")
    if op == "all_true" then return some (← instr "vecAllTrue" #[s])
    if op == "bitmask" then return some (← instr "vecBitmask" #[s])
    if ["eq", "ne"].contains op then return some (← shaped "vecIntRelOp" op)
    if op == "shl" then return some (← shaped "vecShiftOp" "shl")
    for (suffix, signed) in [("s", true), ("u", false)] do
      let sign ← signTerm signed
      if shape.width ≤ 16 then
        for (text, name) in [("add_sat", "addSat"), ("sub_sat", "subSat")] do
          if op == text ++ "_" ++ suffix then return some (← shaped "vecIntBinOp" name #[sign])
      if shape.width ≤ 32 then
        for name in ["min", "max"] do
          if op == name ++ "_" ++ suffix then return some (← shaped "vecIntBinOp" name #[sign])
      if shape.width ≤ 32 || signed then
        for name in ["lt", "gt", "le", "ge"] do
          if op == name ++ "_" ++ suffix then return some (← shaped "vecIntRelOp" name #[sign])
      if op == "shr_" ++ suffix then return some (← shaped "vecShiftOp" "shr" #[sign])
    if ty == "i8x16" && ["swizzle", "relaxed_swizzle"].contains op then
      return some (← instr "vecSwizzle" #[← coreTerm "VecSwizzleOp"
        (if op == "swizzle" then "swizzle" else "relaxedSwizzle")])
  else
    let s ← floatShape ty
    if ["abs", "neg", "sqrt", "ceil", "floor", "trunc", "nearest"].contains op then
      return some (← instr "vecFloatUnOp" #[s, ← coreTerm "FloatUnOp" op])
    if ["eq", "ne", "lt", "gt", "le", "ge"].contains op then
      return some (← instr "vecFloatRelOp" #[s, ← coreTerm "FloatRelOp" op])
    if ["add", "sub", "mul", "div", "min", "max", "pmin", "pmax"].contains op then
      return some (← instr "vecFloatBinOp" #[s, ← coreTerm "VecFloatBinOp" op])
    for (text, name) in [("relaxed_min", "relaxedMin"), ("relaxed_max", "relaxedMax")] do
      if op == text then return some (← instr "vecFloatBinOp" #[s, ← coreTerm "VecFloatBinOp" name])
    for (text, name) in [("relaxed_madd", "relaxedMadd"), ("relaxed_nmadd", "relaxedNmadd")] do
      if op == text then return some (← instr "vecFloatTernOp" #[s, ← coreTerm "VecFloatTernOp" name])
  -- Cross-shape operations name the destination first in WAT; the AST takes
  -- source, then destination. Keep this swap explicit at the construction site.
  for (source, target) in [("i8x16", "i16x8"), ("i16x8", "i32x4"), ("i32x4", "i64x2")] do
    for (suffix, signed) in [("s", true), ("u", false)] do
      let sign ← signTerm signed
      if ty == source && source != "i32x4" && op == "narrow_" ++ target ++ "_" ++ suffix then
        return some (← instr "vecNarrow" #[← intShape target, ← intShape source, sign])
      if ty == target then
        if target != "i64x2" && op == "extadd_pairwise_" ++ source ++ "_" ++ suffix then
          return some (← instr "vecExtUnOp" #[← intShape source, ← intShape target,
            ← coreTerm "VecExtUnOp" "extaddPairwise" #[sign]])
        for half in ["low", "high"] do
          let h ← coreTerm "Half" half
          if op == "extmul_" ++ half ++ "_" ++ source ++ "_" ++ suffix then
            return some (← instr "vecExtBinOp" #[← intShape source, ← intShape target,
              ← coreTerm "VecExtBinOp" "extmul" #[h, sign]])
          if op == "extend_" ++ half ++ "_" ++ source ++ "_" ++ suffix then
            return some (← instr "vecConvert" #[← coreTerm "Shape" "int" #[← intShape source],
              ← shape.shapeTerm, ← coreTerm "VecConvertOp" "extend" #[h, sign]])
  if ty == "i32x4" && op == "dot_i16x8_s" then
    return some (← instr "vecExtBinOp" #[← intShape "i16x8", ← intShape "i32x4",
      ← coreTerm "VecExtBinOp" "dotS"])
  if ty == "i16x8" && op == "relaxed_dot_i8x16_i7x16_s" then
    return some (← instr "vecExtBinOp" #[← intShape "i8x16", ← intShape "i16x8",
      ← coreTerm "VecExtBinOp" "relaxedDotS"])
  if ty == "i32x4" && op == "relaxed_dot_i8x16_i7x16_add_s" then
    return some (← instr "vecExtTernOp" #[← intShape "i8x16", ← intShape "i32x4",
      ← coreTerm "VecExtTernOp" "relaxedDotAddS"])
  let cvt (source : Term) (name : String) (args : Array Term := #[]) := do
    instr "vecConvert" #[source, ← shape.shapeTerm, ← coreTerm "VecConvertOp" name args]
  for (suffix, signed) in [("s", true), ("u", false)] do
    let sign ← signTerm signed
    if ty == "i32x4" then
      for (source, zero) in [("f32x4", false), ("f64x2", true)] do
        for (text, name) in [("trunc_sat", "truncSat"), ("relaxed_trunc", "relaxedTrunc")] do
          if op == text ++ "_" ++ source ++ "_" ++ suffix ++ (if zero then "_zero" else "") then
            return some (← cvt (← coreTerm "Shape" "float" #[← floatShape source]) name #[sign, quote zero])
    if ty == "f32x4" && op == "convert_i32x4_" ++ suffix then
      return some (← cvt (← coreTerm "Shape" "int" #[← intShape "i32x4"]) "convert" #[← `(none), sign])
    if ty == "f64x2" && op == "convert_low_i32x4_" ++ suffix then
      let half ← coreTerm "Half" "low"
      return some (← cvt (← coreTerm "Shape" "int" #[← intShape "i32x4"]) "convert" #[← `(some $half), sign])
  if ty == "f32x4" && op == "demote_f64x2_zero" then
    return some (← cvt (← coreTerm "Shape" "float" #[← floatShape "f64x2"]) "demoteZero")
  if ty == "f64x2" && op == "promote_low_f32x4" then
    return some (← cvt (← coreTerm "Shape" "float" #[← floatShape "f32x4"]) "promoteLow")
  return none

def lane (origin : Node) (nodes : List Node) : MacroM (Term × List Node) := do
  let n :: rest := nodes | watError origin "missing SIMD lane index"
  let i ← checked n (unsigned (← atom n))
  unless i < 256 do watError n "SIMD lane index exceeds unsigned byte range"
  return (natTerm i, rest)

/-- SIMD constants, lane instructions, and the fixed-size shuffle immediate. -/
def vectorPlain (floatBits : FloatParser) (origin : Node) (nodes : List Node) :
    MacroM (Option (Term × List Node)) := do
  let op ← atom origin
  if op == "v128.const" then
    let n :: remaining := nodes | watError origin "v128.const requires a lane shape"
    let name ← atom n
    let some shape := vectorShapes.find? (·.name == name) | watError n "unknown vector constant shape"
    let mut rest := remaining
    let mut bits := 0
    for i in [:shape.lanes] do
      let n :: tail := rest | watError origin s!"vector constant requires {shape.lanes} lane literals"
      let value ← checked n ((if shape.integer then integerBits else floatBits) shape.width (← atom n))
      bits := bits + value * Nat.pow 2 (shape.width * i)
      rest := tail
    let value ← `(BitVec.ofNat 128 $(natTerm bits))
    return some (← instr "vecConst" #[value], rest)
  if op == "i8x16.shuffle" then
    let mut lanes := []
    let mut rest := nodes
    for _ in [:16] do
      let (i, tail) ← lane origin rest
      lanes := lanes ++ [i]
      rest := tail
    return some (← instr "vecShuffle" #[← listTerm lanes], rest)
  if let [ty, op] := op.splitOn "." then
    if let some shape := vectorShapes.find? (·.name == ty) then
      if op == "replace_lane" then
        let (i, rest) ← lane origin nodes
        return some (← instr "vecReplaceLane" #[← shape.shapeTerm, i], rest)
      let signed := op == "extract_lane_s"
      if (shape.width < 32 && (signed || op == "extract_lane_u")) ||
          (shape.width ≥ 32 && op == "extract_lane") then
        let (i, rest) ← lane origin nodes
        let sign ← if shape.width < 32 then do let s ← signTerm signed; `(some $s) else `(none)
        return some (← instr "vecExtractLane" #[← shape.shapeTerm, sign, i], rest)
  return (← vectorOpcode op).map (·, nodes)

end Silmaril.Wasm.Wat.Core
