module

public meta import Silmaril.Wasm.Wat.CoreVector

/-! # Core3 memory and table instruction immediates

Memory indices are independent of the address width. Offsets and textual byte
alignments use the Core3 unsigned 64-bit grammar; the AST stores log₂ alignment.
-/

public meta section
open Lean
namespace Silmaril.Wasm.Wat.Core

def isIndex (n : Node) : Bool :=
  let s := n.atom?.getD ""
  s.startsWith "$" || s.toList.head?.any Char.isDigit

def optionalIndex (names : Names) (kind : String) (nodes : List Node) :
    MacroM (Term × List Node) := do
  if let n :: rest := nodes then
    if isIndex n then return (← indexTerm (← index names kind n), rest)
  return (← indexTerm 0, nodes)

def requiredIndex (origin : Node) (names : Names) (kind : String) (nodes : List Node) :
    MacroM (Term × List Node) := do
  let n :: rest := nodes | watError origin s!"missing {kind} index"
  return (← indexTerm (← index names kind n), rest)

def pairIndices (origin : Node) (names : Names) (kind : String) (nodes : List Node) :
    MacroM (Term × Term × List Node) := do
  if let n :: _ := nodes then
    if isIndex n then
      let (a, rest) ← requiredIndex origin names kind nodes
      let (b, rest) ← requiredIndex origin names kind rest
      return (a, b, rest)
  return (← indexTerm 0, ← indexTerm 0, nodes)

def segmentIndices (origin : Node) (targets segments : Names) (targetKind segmentKind : String)
    (nodes : List Node) : MacroM (Term × Term × List Node) := do
  let a :: rest := nodes | watError origin s!"missing {segmentKind} index"
  if let b :: tail := rest then
    if isIndex b then
      return (← indexTerm (← index targets targetKind a),
        ← indexTerm (← index segments segmentKind b), tail)
  return (← indexTerm 0, ← indexTerm (← index segments segmentKind a), rest)

def coreMemArg (naturalAlign : Nat) (nodes : List Node) : MacroM (Term × List Node) := do
  let (align, offset, rest) ← memoryAttributes 64 naturalAlign nodes
  return (← `(Silmaril.Wasm.MemArg.mk $(natTerm align) $(natTerm offset)), rest)

/-- A sole numeric immediate on a lane load/store denotes the lane, not a memory. -/
def memoryArgument (names : Names) (naturalAlign : Nat) (laneMode : Bool) (nodes : List Node) :
    MacroM (Term × Term × List Node) := do
  let mut explicitMemory := true
  if laneMode then
    if let n :: tail := nodes then
      if isIndex n && !(n.atom?.getD "").startsWith "$" then
        let afterAttrs := tail.dropWhile fun n =>
          let s := n.atom?.getD ""
          s.startsWith "offset=" || s.startsWith "align="
        explicitMemory := afterAttrs.head?.any isIndex
  let (memory, rest) ← if explicitMemory then optionalIndex names "memory" nodes
    else pure (← indexTerm 0, nodes)
  let (arg, rest) ← coreMemArg naturalAlign rest
  return (memory, arg, rest)

def coreMemoryOp (memories : Names) (origin : Node) (ty op : String) (nodes : List Node) :
    MacroM (Option (Term × List Node)) := do
  let integer := ty == "i32" || ty == "i64"
  let floating := ty == "f32" || ty == "f64"
  if integer || floating then
    let width := if ty == "i32" || ty == "f32" then 32 else 64
    let t ← if integer then integerType ty else floatType ty
    if op == "load" || op == "store" then
      let (mem, arg, rest) ← memoryArgument memories (if width == 32 then 2 else 3) false nodes
      let args ← if integer then do let no ← `(none); pure #[t, no, mem, arg]
        else pure #[t, mem, arg]
      return some (← instr ((if integer then "int" else "float") ++
        (if op == "load" then "Load" else "Store")) args, rest)
    if integer then
      for (size, log) in [(8, 0), (16, 1), (32, 2)] do
        if size < width then
          let pack ← coreTerm "PackSize" ("i" ++ toString size)
          if op == "store" ++ toString size then
            let (mem, arg, rest) ← memoryArgument memories log false nodes
            return some (← instr "intStore" #[t, ← `(some $pack), mem, arg], rest)
          for (suffix, signed) in [("s", true), ("u", false)] do
            if op == "load" ++ toString size ++ "_" ++ suffix then
              let (mem, arg, rest) ← memoryArgument memories log false nodes
              let sign ← signTerm signed
              return some (← instr "intLoad" #[t, ← `(some ($pack, $sign)), mem, arg], rest)
  if ty == "v128" then
    if op == "load" || op == "store" then
      let (mem, arg, rest) ← memoryArgument memories 4 false nodes
      return some (← if op == "store" then instr "vecStore" #[mem, arg]
        else instr "vecLoad" #[← coreTerm "VecLoadOp" "full", mem, arg], rest)
    for (size, log) in [(8, 0), (16, 1), (32, 2), (64, 3)] do
      let pack ← coreTerm "PackSize" ("i" ++ toString size)
      for (mnemonic, ctor) in [("load", "vecLoadLane"), ("store", "vecStoreLane")] do
        if op == mnemonic ++ toString size ++ "_lane" then
          let (mem, arg, rest) ← memoryArgument memories log true nodes
          let (lane, rest) ← lane origin rest
          return some (← instr ctor #[pack, mem, arg, lane], rest)
      if op == "load" ++ toString size ++ "_splat" then
        let (mem, arg, rest) ← memoryArgument memories log false nodes
        return some (← instr "vecLoad" #[← coreTerm "VecLoadOp" "splat" #[pack], mem, arg], rest)
      if size ≥ 32 && op == "load" ++ toString size ++ "_zero" then
        let (mem, arg, rest) ← memoryArgument memories log false nodes
        return some (← instr "vecLoad" #[← coreTerm "VecLoadOp" ("zero" ++ toString size), mem, arg], rest)
    for (shape, ctor) in [("8x8", "extend8x8"), ("16x4", "extend16x4"), ("32x2", "extend32x2")] do
      for (suffix, signed) in [("s", true), ("u", false)] do
        if op == "load" ++ shape ++ "_" ++ suffix then
          let (mem, arg, rest) ← memoryArgument memories 3 false nodes
          return some (← instr "vecLoad"
            #[← coreTerm "VecLoadOp" ctor #[← signTerm signed], mem, arg], rest)
  return none

end Silmaril.Wasm.Wat.Core
