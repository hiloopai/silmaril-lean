import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit
import Silmaril.Wasm.SingleThreaded.Exec.InvokeRun
import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Parse
import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Eval
import Silmaril.Raw.Wasm.SpecTec.Wasm.Numerics.IntegerN
import Silmaril.Wasm.SpecTecLean.Defs
import Silmaril.Wasm.SpecTec.Sim.Round6.Reading.Defs

/-! `wasm-conformance-lean`: the Lean columns of `tools/wasm-conformance`.

Reads the line-format script the Rust harness writes (`wast_lower::script`) and prints one
`idx outcome…` line per command it can answer.

```
wasm-conformance-lean core SCRIPT
wasm-conformance-lean spectec-il AST SCRIPT
wasm-conformance-lean spectec-il-builtins AST SCRIPT
wasm-conformance-lean spectec-lean SCRIPT
wasm-conformance-lean spectec-text AST SCRIPT
wasm-conformance-lean spectec-step AST SCRIPT
wasm-conformance-lean spectec-module AST SCRIPT
```

* `core`: silmaril-lean's binary decoder (`Binary.Core.Decode.decodeModule`), validator
  (`Validation.validate?`), concrete instantiation (`Execution.Core.instantiateInit?`, whose
  start code is run by the interpreter) and verified Core 3.0 interpreter (`SingleThreaded.Exec`:
  `runI`, `runInvoke?`; sound and complete for Core `Step` by `runInvoke?_sound`/`_complete`),
  deterministic profile `profile neverFail` (canonical NaNs, `grow` never fails spontaneously).
  Imports are resolved by name against the registered instances (`W` lines): the `spectest`
  host module the harness writes first, and `register`ed modules; the addresses must pass
  `externAddrsOk?` against the validator's import types (`Externaddr_ok`). `N` lines must fail
  to instantiate; a start function or segment that traps keeps its effects on the store (when
  the fast path `instantiateInit?` gives up on an out-of-bounds segment, `prepare?`'s
  configuration runs the segment code in the interpreter).
* `spectec-il`: SpecTec's IL, read at run time from the pinned `--ast` stream with the same
  reader `spectec_import` uses (`SExp.parseStream`, `IL.decodeScript?`), and evaluated by the IL
  evaluator `Sem.callDef` with no builtins: `$unop_`, `$binop_`, `$testop_`, `$relop_` on the
  operands of a `K` line (a single-instruction export), and `$cvtop__` on conversion kernels. The errata do not touch these functions
  (`Scripts.Wasm30.Fixed.changedIndices`), so the original stream is the right script.
* `spectec-il-builtins`: the same, with silmaril-lean's integer numerics (`Numerics.IntegerN`)
  installed as the IL's `hint(builtin)` primitives, as `Sim.IntNumeric.intCall` does, and its
  deterministic float numerics and conversions (`Numerics.floatUnOp`/`floatBinOp`/`floatRelOp`/
  `convert`) as the float primitives in the shapes of `Sim.Floats.floatCall'` (one result where
  `Sim` lists every result `Profile.spec` allows). Float and conversion kernels go through the
  IL's own `$unop_`/`$binop_`/`$relop_`/`$cvtop__` clauses and its `fN` encoding.
* `spectec-text`: SpecTec's text grammars `TiN(N)`/`TfN(N)` from the same stream, recognised by
  a memoising span parser (`pNT`) that evaluates attributes, premises and results with the IL
  evaluator; on the `t.const` literals of `L` lines (`accept` / `reject underivable …`).
* `spectec-step`: whole invocations on SpecTec's `Step`, read as `DDerivesB` (the backend
  reading) and run by the moded search `Derive.step` (unverified; see the section on the search below),
  with the builtins of `spectec-il-builtins`.  Modules are instantiated by the `core` driver; an
  `R` line's start configuration is Core's `invoke s a vs`, encoded by the simulation's `Sim.configV`,
  and stepped until it is a value sequence or `TRAP`.  Core's run of the same invocation then
  supplies the store for the next directive.
* `spectec-module`: whole text modules against SpecTec's text grammar (`WasmConformanceLean/TextModule`).
* `spectec-lean`: the official SpecTec Lean backend's model (`SpecTecLean`), on the numeric
  functions it renders as executable `def`s (`iadd_`, `isub_`, `imul_`, `ieq_`, `ine_`); its other
  numeric functions are `opaque` (`hint(builtin)`) or inductive relations, reported unsupported.
-/

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

namespace WasmConformance

/-! ## The script format -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit cs[2 * i]!, hexDigit cs[2 * i + 1]! with
    | some a, some b => out := out.push (UInt8.ofNat (16 * a + b))
    | _, _ => return none
  return some out

def unhexStr (s : String) : String :=
  match unhex s with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

/-- A harness value token, `kind:payload`. -/
def parseVal (t : String) : Option Val :=
  match t.splitOn ":" with
  | ["i32", n] => n.toNat?.map fun n => .num ⟨.int .i32, BitVec.ofNat 32 n⟩
  | ["i64", n] => n.toNat?.map fun n => .num ⟨.int .i64, BitVec.ofNat 64 n⟩
  | ["f32", n] => n.toNat?.map fun n => .num ⟨.float .f32, BitVec.ofNat 32 n⟩
  | ["f64", n] => n.toNat?.map fun n => .num ⟨.float .f64, BitVec.ofNat 64 n⟩
  | ["v128", h] =>
    (unhex h).map fun b => .vec (BitVec.ofNat 128 (b.foldl (fun a x => 256 * a + x.toNat) 0))
  | ["ref.null"] => some (.ref .null)
  | ["ref.extern", n] => n.toNat?.map fun n => .ref (.extern (.host n))
  | _ => none

def hex32 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (32 - s.length) '0') ++ s

def showVal : Val → String
  | .num ⟨.int .i32, b⟩ => s!"i32:{b.toNat}"
  | .num ⟨.int .i64, b⟩ => s!"i64:{b.toNat}"
  | .num ⟨.float .f32, b⟩ => s!"f32:{b.toNat}"
  | .num ⟨.float .f64, b⟩ => s!"f64:{b.toNat}"
  | .vec b => s!"v128:{hex32 b.toNat}"
  | .ref .null => "ref.null"
  | .ref (.extern (.host n)) => s!"ref.extern:{n}"
  | .ref (.func a) => s!"ref:func{a}"
  | .ref _ => "ref:other"

/-! ## The Core 3.0 interpreter -/

/-- Interpreter steps per invocation. -/
def fuel : Nat := 2000000

/-- Interpreter steps for an invocation the testsuite expects to exhaust the call stack (the
driver's cost per step grows with the nesting depth, so these are kept short). -/
def exhaustFuel : Nat := 20000

structure Inst where
  store : Store Nat
  module : ModuleInst

/-- The exports of an instance, by name. -/
def export? (i : Inst) (name : String) : Option ExternAddr :=
  (i.module.exports.find? (·.name == name)).map (·.addr)

/-- Decode, validate, resolve the imports against `reg`, instantiate and run the start code and
segments.  Returns the store to continue with (the input store when the module is rejected or
unlinkable; the store after a trap, whose writes to imported tables and memories persist) and
the instance or the reason there is none. -/
def instantiate (s : Store Nat) (reg : Std.HashMap String Inst) (bytes : ByteArray) :
    Store Nat × Except String Inst := Id.run do
  let m ← match Binary.Core.Decode.decodeModule bytes with
    | .ok m => pure m
    | .error e => return (s, .error s!"decode {e.take 40}")
  let some mt := Validation.validate? m | return (s, .error "invalid")
  let mut xas : List ExternAddr := []
  for imp in m.imports do
    match (reg.get? imp.moduleName).bind (export? · imp.name) with
    | some a => xas := xas ++ [a]
    | none => return (s, .error s!"unknown-import {imp.moduleName}.{imp.name}")
  unless externAddrsOk? s xas mt.imports do
    return (s, .error "incompatible-import-type")
  -- `instantiateInit?` initialises the segments directly and gives up (`none`) when one is out
  -- of bounds; then the allocated configuration of `prepare?` runs the segment code itself, in
  -- the interpreter, so that the writes before the trapping segment persist (Wasm 2.0+).
  let some c := (instantiateInit? s m xas).orElse fun _ =>
      (prepare? evalConst? s m xas).map fun (c, st) => c.withStart st
    | return (s, .error "instantiation-failed")
  let (c', stopped) := Exec.runI neverFail fuel c
  unless stopped do return (s, .error "start: fuel")
  match c'.outcome? with
  | some (.values _) => return (c'.store, .ok ⟨c'.store, c'.frame.module⟩)
  | some .trap => return (c'.store, .error "start: trap")
  | _ => return (s, .error "start: stuck")

/-- Run the commands on the Core interpreter.  With `onInvoke`, only `R`/`E` lines are reported,
and an `R` line's outcome is `onInvoke store addr args` (Core still runs it, to update the store). -/
def runCore (lines : List String)
    (onInvoke : Option (Store Nat → Nat → List Val → IO String) := none) : IO Unit := do
  let say (s : String) : IO Unit := if onInvoke.isNone then IO.println s else pure ()
  let mut store : Store Nat := {}
  let mut cur : Option Inst := none
  let mut named : Std.HashMap String (Option Inst) := {}
  let mut reg : Std.HashMap String Inst := {}
  for line in lines do
    match line.splitOn " " |>.filter (· ≠ "") with
    | ["M", i, _, id, h] =>
      let (store', r) := match unhex h with
        | some b => instantiate store reg b
        | none => (store, .error "hex")
      store := store'
      let inst := r.toOption
      match r with
      | .ok _ => say s!"{i} inst"
      | .error e => say s!"{i} noinst {e}"
      cur := inst
      if id != "-" then named := named.insert id inst
    | ["N", i, _, h] =>
      let (store', r) := match unhex h with
        | some b => instantiate store reg b
        | none => (store, .error "hex")
      store := store'
      match r with
      | .ok _ => say s!"{i} inst"
      | .error e => say s!"{i} noinst {e}"
    | ["W", i, _, id, name] =>
      let inst := if id == "-" then cur else (named.get? id).getD none
      match inst with
      | some inst =>
        -- A registered instance sees the current store when it is imported.
        reg := reg.insert (unhexStr name) inst
        say s!"{i} inst"
      | none => say s!"{i} unsupported no-instance"
    | ["G", i, _, id, name] =>
      let inst := if id == "-" then cur else (named.get? id).getD none
      match inst with
      | none => say s!"{i} unsupported no-instance"
      | some inst =>
        match export? inst (unhexStr name) with
        | some (.global a) =>
          match store.globals[a]? with
          | some g => say s!"{i} ok {showVal g.value}"
          | none => say s!"{i} error dangling"
        | _ => say s!"{i} error no-such-global"
    | ["V", i, _, h] =>
      match (unhex h).elim (.error "hex") Binary.Core.Decode.decodeModule with
      | .error e => say s!"{i} reject decode {e.take 60}"
      | .ok m =>
        match Validation.validate? m with
        | none => say s!"{i} reject invalid"
        | some _ => say s!"{i} accept"
    | r :: i :: _ :: id :: name :: args =>
      if r != "R" && r != "E" then continue
      -- `E`: expected to exhaust the call stack, which Core does not bound; a run that is still
      -- going after `exhaustFuel` steps is reported as fuel exhaustion.
      let fuel := if r == "E" then exhaustFuel else fuel
      let inst := if id == "-" then cur else (named.get? id).getD none
      match inst, args.mapM parseVal with
      | none, _ => IO.println s!"{i} unsupported no-instance"
      | _, none => IO.println s!"{i} unsupported argument"
      | some inst, some vs =>
        match export? inst (unhexStr name) with
        | some (.func a) =>
          if let some f := onInvoke then
            if r == "E" then IO.println s!"{i} unsupported exhaustion-unbounded"
            else IO.println s!"{i} {← f store a vs}"
            (← IO.getStdout).flush
          match Exec.runInvoke? neverFail fuel store a vs with
          | some (c, true, some (.values rs)) =>
            store := c.store
            say s!"{i} ok {" ".intercalate (rs.map showVal)}"
          | some (c, true, some .trap) => store := c.store; say s!"{i} trap"
          | some (c, true, some (.throw _)) => store := c.store; say s!"{i} stuck throw"
          | some (_, false, _) => say s!"{i} fuel"
          | _ => say s!"{i} stuck"
        | _ => IO.println s!"{i} error no-such-function"
    | _ => pure ()

/-! ## SpecTec's IL, evaluated -/

section il
open Silmaril.SpecTec Silmaril.SpecTec.Sem

def nullary (s : String) : Value := .case s (.tuple [])
def bitsV (n : Nat) : Value := .case "%" (.tuple [.num (.natN n)])
def sxV (signed : Bool) : Value := nullary (if signed then "S" else "U")

def asBits (N : Nat) : Value → Option (BitVec N)
  | .case "%" (.tuple [.num (.natN n)]) => some (BitVec.ofNat N n)
  | _ => none

def asSx : Value → Option Signedness
  | .case "U" (.tuple []) => some .unsigned
  | .case "S" (.tuple []) => some .signed
  | _ => none

def bv {N : Nat} (b : BitVec N) : Value := bitsV b.toNat

/-- A `u32` shift amount, as its natural number. -/
def asNat : Value → Option Nat
  | .case "%" (.tuple [.num (.natN n)]) => some n
  | _ => none

/-- silmaril-lean's integer numerics as the IL builtins (`Sim.IntNumeric.intCall`; `$truncz`
rounds a rational towards zero, the clause `3.1-numerics.scalar.spectec:78` leaves commented
out, here by Lean core's `Rat.floor`/`Rat.ceil` instead of Mathlib's `⌊·⌋`/`⌈·⌉`). -/
def intCall : IL.Id → List ArgV → Option Value
  | "iclz_", [.val (.num (.natN N)), .val a] => (asBits N a).map (bv ∘ Numerics.iclz_ N)
  | "ictz_", [.val (.num (.natN N)), .val a] => (asBits N a).map (bv ∘ Numerics.ictz_ N)
  | "ipopcnt_", [.val (.num (.natN N)), .val a] => (asBits N a).map (bv ∘ Numerics.ipopcnt_ N)
  | "iand_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.iand_ N (← asBits N a) (← asBits N b))
  | "ior_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.ior_ N (← asBits N a) (← asBits N b))
  | "ixor_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.ixor_ N (← asBits N a) (← asBits N b))
  | "irotl_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.irotl_ N (← asBits N a) (← asBits N b))
  | "irotr_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.irotr_ N (← asBits N a) (← asBits N b))
  | "ishl_", [.val (.num (.natN N)), .val a, .val b] =>
    return bv (Numerics.ishl_ N (← asBits N a) (← asNat b))
  | "ishr_", [.val (.num (.natN N)), .val s, .val a, .val b] =>
    return bv (Numerics.ishr_ N (← asSx s) (← asBits N a) (← asNat b))
  | "irem_", [.val (.num (.natN N)), .val s, .val a, .val b] =>
    return .opt ((Numerics.irem_ N (← asSx s) (← asBits N a) (← asBits N b)).map bv)
  | "truncz", [.val (.num (.ratN q))] =>
    some (.num (.intN (if 0 ≤ q then q.floor else q.ceil)))
  | _, _ => none

/-- A number type of a mnemonic prefix. -/
def numTy? : String → Option NumType
  | "i32" => some (.int .i32) | "i64" => some (.int .i64)
  | "f32" => some (.float .f32) | "f64" => some (.float .f64)
  | _ => none

def ntName : NumType → String
  | .int .i32 => "I32" | .int .i64 => "I64" | .float .f32 => "F32" | .float .f64 => "F64"

def ntTok : NumType → String
  | .int .i32 => "i32" | .int .i64 => "i64" | .float .f32 => "f32" | .float .f64 => "f64"

/-- A kernel's IL call: the function, its leading (operator) arguments, the operand type and
the result type (`$testop_`/`$relop_` return a `u32`).  `i32.div_s` ↦ `$binop_(I32, DIV S, …)`,
`f32.add` ↦ `$binop_(F32, ADD, …)`, `i64.extend_i32_s` ↦ `$cvtop__(I32, I64, EXTEND S, …)`, as
`Sim.IntNumeric`/`Sim.Floats` write them. -/
def ilOp (mn : String) : Option (String × List Value × NumType × NumType) := do
  let [ty, op] := mn.splitOn "." | none
  let t ← numTy? ty
  let nt := nullary (ntName t)
  let isInt := match t with | .int _ => true | .float _ => false
  let i32 : NumType := .int .i32
  let sxOf : String → Option Value
    | "s" => some (sxV true) | "u" => some (sxV false) | _ => none
  match op.splitOn "_", isInt with
  | ["add"], _ | ["sub"], _ | ["mul"], _ => some ("binop_", [nt, nullary op.toUpper], t, t)
  | ["and"], true | ["or"], true | ["xor"], true | ["shl"], true | ["rotl"], true
  | ["rotr"], true => some ("binop_", [nt, nullary op.toUpper], t, t)
  | ["div"], false | ["min"], false | ["max"], false | ["copysign"], false =>
    some ("binop_", [nt, nullary op.toUpper], t, t)
  | ["clz"], true | ["ctz"], true | ["popcnt"], true => some ("unop_", [nt, nullary op.toUpper], t, t)
  | ["abs"], false | ["neg"], false | ["sqrt"], false | ["ceil"], false | ["floor"], false
  | ["trunc"], false | ["nearest"], false => some ("unop_", [nt, nullary op.toUpper], t, t)
  | ["extend8", "s"], true => some ("unop_", [nt, .case "EXTEND" (.tuple [bitsV 8])], t, t)
  | ["extend16", "s"], true => some ("unop_", [nt, .case "EXTEND" (.tuple [bitsV 16])], t, t)
  | ["extend32", "s"], true => some ("unop_", [nt, .case "EXTEND" (.tuple [bitsV 32])], t, t)
  | ["eqz"], true => some ("testop_", [nt, nullary "EQZ"], t, i32)
  | ["eq"], _ | ["ne"], _ => some ("relop_", [nt, nullary op.toUpper], t, i32)
  | ["lt"], false | ["gt"], false | ["le"], false | ["ge"], false =>
    some ("relop_", [nt, nullary op.toUpper], t, i32)
  -- Conversions: `<target>.<op>_<source>[_sx]`, `$cvtop__(source, target, op, c)`.
  | ["wrap", src], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, nullary "WRAP"], s, t)
  | ["extend", src, sx], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, .case "EXTEND" (← sxOf sx)], s, t)
  | ["convert", src, sx], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, .case "CONVERT" (← sxOf sx)], s, t)
  | ["trunc", src, sx], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, .case "TRUNC" (← sxOf sx)], s, t)
  | ["trunc", "sat", src, sx], _ => do
    let s ← numTy? src
    some ("cvtop__", [nullary (ntName s), nt, .case "TRUNC_SAT" (← sxOf sx)], s, t)
  | ["demote", src], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, nullary "DEMOTE"], s, t)
  | ["promote", src], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, nullary "PROMOTE"], s, t)
  | ["reinterpret", src], _ => do
    let s ← numTy? src; some ("cvtop__", [nullary (ntName s), nt, nullary "REINTERPRET"], s, t)
  | [b, sx], true =>
    let sxv ← sxOf sx
    if ["div", "rem", "shr"].contains b then some ("binop_", [nt, .case b.toUpper sxv], t, t)
    else if ["lt", "gt", "le", "ge"].contains b then
      some ("relop_", [nt, .case b.toUpper sxv], t, i32)
    else none
  | _, _ => none

/-! ### Floats in the IL

`fN(N)` is `POS`/`NEG` of `NORM m exp`, `SUBNORM m`, `INF` or `NAN m` (`1.1-syntax.values`), as
`Sim`'s `floatV` encodes an IEEE bit pattern. -/

def fmt (w : Nat) : Nat × Nat := if w == 32 then (8, 23) else (11, 52)

/-- The IL `fN(w)` of the bit pattern `b` (`Sim.floatV`). -/
def floatEnc (w b : Nat) : Value :=
  let (ew, fw) := fmt w
  let m := b % 2 ^ fw
  let e := (b / 2 ^ fw) % 2 ^ ew
  let mag : Value :=
    if e = 0 then .case "SUBNORM" (.tuple [.num (.natN m)])
    else if e = 2 ^ ew - 1 then
      (if m = 0 then nullary "INF" else .case "NAN" (.tuple [.num (.natN m)]))
    else .case "NORM" (.tuple [.num (.natN m), .num (.intN ((e : Int) - ((2 ^ (ew - 1) - 1 : Nat) : Int)))])
  .case (if (b / 2 ^ (w - 1)) % 2 = 0 then "POS" else "NEG") mag

/-- The bit pattern of an IL `fN(w)`, the inverse of `floatEnc`. -/
def floatDec (w : Nat) : Value → Option Nat
  | .case sg mag => do
    let s ← if sg == "POS" then some 0 else if sg == "NEG" then some 1 else none
    let (ew, fw) := fmt w
    let (e, m) ← match mag with
      | .case "SUBNORM" (.tuple [.num (.natN m)]) => some (0, m)
      | .case "INF" (.tuple []) => some (2 ^ ew - 1, 0)
      | .case "NAN" (.tuple [.num (.natN m)]) => some (2 ^ ew - 1, m)
      | .case "NORM" (.tuple [.num (.natN m), .num (.intN x)]) =>
        some ((x + ((2 ^ (ew - 1) - 1 : Nat) : Int)).toNat, m)
      | _ => none
    guard (m < 2 ^ fw ∧ e < 2 ^ ew)
    some (s * 2 ^ (w - 1) + e * 2 ^ fw + m)
  | _ => none

/-- The IL value of a number of type `t` (`Sim.numV`). -/
def numEnc (t : NumType) (b : Nat) : Value :=
  match t with
  | .int _ => bitsV b
  | .float _ => floatEnc t.width b

/-- The bit pattern of an IL number of type `t`. -/
def numDec (t : NumType) (v : Value) : Option Nat :=
  match t with
  | .int _ => asNat v
  | .float _ => floatDec t.width v

def ftOf : Nat → Option FloatType | 32 => some .f32 | 64 => some .f64 | _ => none
def itOf : Nat → Option IntType | 32 => some .i32 | 64 => some .i64 | _ => none

def numTyOfV : Value → Option NumType
  | .case "I32" (.tuple []) => some (.int .i32) | .case "I64" (.tuple []) => some (.int .i64)
  | .case "F32" (.tuple []) => some (.float .f32) | .case "F64" (.tuple []) => some (.float .f64)
  | _ => none

/-- A float operand of width `N`. -/
def fArg (N : Nat) (a : Value) : Option ((t : FloatType) × BitVec t.width) := do
  let t ← ftOf N
  let b ← floatDec N a
  pure ⟨t, BitVec.ofNat t.width b⟩

/-- A conversion's result: the bits, as a number of the target type. -/
def convV (op : ConvertOp) (x : Nat) : Option Value :=
  match Numerics.convert op (BitVec.ofNat op.source.width x) with
  | .ok z => some (numEnc op.target z.toNat)
  | .error _ => none

/-- **Executable float and conversion builtins**: silmaril-lean's deterministic Core numerics
(canonical NaNs, the ones the `core` column's `profile neverFail` runs) in the shapes of `Sim`'s
`floatCall'` (`Silmaril.Wasm.SpecTec.Sim.Floats`).  Where `floatCall'` returns *every* result
`Profile.spec` allows (a list), this returns the one deterministic result as a singleton: a
sound under-approximation, so an `ok` here is one of the IL's results, and a NaN the testsuite
accepts as `nan:arithmetic` is matched as such by the harness. -/
def floatCall : IL.Id → List ArgV → Option Value
  | "fabs_", [.val (.num (.natN N)), .val a] => un .abs N a
  | "fneg_", [.val (.num (.natN N)), .val a] => un .neg N a
  | "fsqrt_", [.val (.num (.natN N)), .val a] => un .sqrt N a
  | "fceil_", [.val (.num (.natN N)), .val a] => un .ceil N a
  | "ffloor_", [.val (.num (.natN N)), .val a] => un .floor N a
  | "ftrunc_", [.val (.num (.natN N)), .val a] => un .trunc N a
  | "fnearest_", [.val (.num (.natN N)), .val a] => un .nearest N a
  | "fadd_", [.val (.num (.natN N)), .val a, .val b] => bin .add N a b
  | "fsub_", [.val (.num (.natN N)), .val a, .val b] => bin .sub N a b
  | "fmul_", [.val (.num (.natN N)), .val a, .val b] => bin .mul N a b
  | "fdiv_", [.val (.num (.natN N)), .val a, .val b] => bin .div N a b
  | "fmin_", [.val (.num (.natN N)), .val a, .val b] => bin .min N a b
  | "fmax_", [.val (.num (.natN N)), .val a, .val b] => bin .max N a b
  | "fcopysign_", [.val (.num (.natN N)), .val a, .val b] => bin .copysign N a b
  | "feq_", [.val (.num (.natN N)), .val a, .val b] => rel .eq N a b
  | "fne_", [.val (.num (.natN N)), .val a, .val b] => rel .ne N a b
  | "flt_", [.val (.num (.natN N)), .val a, .val b] => rel .lt N a b
  | "fgt_", [.val (.num (.natN N)), .val a, .val b] => rel .gt N a b
  | "fle_", [.val (.num (.natN N)), .val a, .val b] => rel .le N a b
  | "fge_", [.val (.num (.natN N)), .val a, .val b] => rel .ge N a b
  | "wrap__", [.val (.num (.natN N)), .val (.num (.natN N')), .val a] => do
    let x ← asNat a; pure (bitsV ((BitVec.ofNat N x).setWidth N').toNat)
  | "extend__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
    let x := BitVec.ofNat N (← asNat a)
    pure (bitsV (match ← asSx s with
      | .signed => (x.signExtend N').toNat | .unsigned => (x.setWidth N').toNat))
  | "trunc__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
    let op : ConvertOp := .trunc (← ftOf N) (← itOf N') (← asSx s)
    pure (.opt (convV op (← floatDec N a)))
  | "trunc_sat__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
    let op : ConvertOp := .truncSat (← ftOf N) (← itOf N') (← asSx s)
    pure (.opt (convV op (← floatDec N a)))
  | "convert__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
    let op : ConvertOp := .convert (← itOf N) (← ftOf N') (← asSx s)
    convV op (← asNat a)
  | "promote__", [.val (.num (.natN 32)), .val (.num (.natN 64)), .val a] => do
    pure (.list [← convV .promote (← floatDec 32 a)])
  | "demote__", [.val (.num (.natN 64)), .val (.num (.natN 32)), .val a] => do
    pure (.list [← convV .demote (← floatDec 64 a)])
  | "reinterpret__", [.val n₁, .val n₂, .val a] => do
    let t₁ ← numTyOfV n₁
    let t₂ ← numTyOfV n₂
    guard (t₁.width = t₂.width)
    pure (numEnc t₂ (← numDec t₁ a))
  | _, _ => none
where
  un (op : FloatUnOp) (N : Nat) (a : Value) : Option Value := do
    let ⟨t, x⟩ ← fArg N a
    pure (.list [floatEnc N (Numerics.floatUnOp t op x).toNat])
  bin (op : FloatBinOp) (N : Nat) (a b : Value) : Option Value := do
    let ⟨t, x⟩ ← fArg N a
    let y := BitVec.ofNat t.width (← floatDec N b)
    pure (.list [floatEnc N (Numerics.floatBinOp t op x y).toNat])
  rel (op : FloatRelOp) (N : Nat) (a b : Value) : Option Value := do
    let ⟨t, x⟩ ← fArg N a
    let y := BitVec.ofNat t.width (← floatDec N b)
    pure (bitsV (Numerics.floatRelOp t op x y).toNat)

/-- The IL evaluator's fuel (a depth bound). -/
def ilFuel : Nat := 400

/-- Apply the IL function of a `K` line to its operands (bit patterns of the operand type). -/
def ilApply (env : Env) (mn : String) (args : List Nat) : String :=
  match ilOp mn with
  | none => "unsupported op"
  | some (f, pre, t, rt) =>
    let names := (List.range pre.length).map (s!"p{·}") ++
      (List.range args.length).map (s!"a{·}")
    let vals := pre ++ args.map fun n => numEnc t (n % 2 ^ t.width)
    let ρ := VarEnv.empty.bindVals (names.zip vals)
    let call := callDef ilFuel env ρ f (names.map fun x => .expA (.varE x))
    let one (v : Value) : String :=
      match numDec rt v with
      | some b => s!"ok {ntTok rt}:{b}"
      | none => s!"error result-shape {(repr v).pretty.take 60}"
    match call with
    -- `$binop_`, `$unop_`, `$cvtop__` return a list of results: none is a trap, one is the
    -- result; more than one (a set-valued float result) is reported by its first element.
    | .ok (.list []) => "trap"
    | .ok (.list (v :: _)) => one v
    -- `$testop_`/`$relop_` return a `u32`.
    | .ok v => one v
    | .error .undef => "stuck undef"
    | .error .outOfFuel => "stuck fuel"

def readEnv (ast : String) (builtins : Bool) : IO Env := do
  let contents ← IO.FS.readFile ast
  let forms ← match SExp.parseStream contents with
    | .error e => throw <| IO.userError s!"{ast}: {e}"
    | .ok forms => pure forms
  let some script := IL.decodeScript? forms
    | throw <| IO.userError s!"{ast}: not a SpecTec IL script"
  let env := envOfScript script
  pure (if builtins then env.withBuiltins ⟨fun x xs => (intCall x xs).orElse fun _ => floatCall x xs⟩
    else env)

def runIL (env : Env) (lines : List String) : IO Unit := do
  for line in lines do
    match line.splitOn " " |>.filter (· ≠ "") with
    | "K" :: i :: _ :: mn :: args =>
      let nums := args.filterMap fun t => match t.splitOn ":" with
        | [_, n] => n.toNat?
        | _ => none
      if nums.length == args.length then IO.println s!"{i} {ilApply env mn nums}"
      else IO.println s!"{i} unsupported operand-type"
    | _ => pure ()

end il

/-! ## SpecTec's text grammars, recognised -/

section text
open Silmaril.SpecTec Silmaril.SpecTec.Sem

/-- Memo table of nonterminal results, keyed by name, argument values and span. -/
abbrev Memo := Std.HashMap String (List Value)

/-- The evaluator's fuel inside the recogniser (expressions, patterns, premises). -/
def tFuel : Nat := 200

mutual

/-- All `(scope, attribute)` results of `g` on exactly the span `[i, j)` of `inp` (Unicode
scalar values), in scope `ρ`.  A terminal's attribute is its scalar (`num`), as the byte
grammars' `actByte` has it; sequences thread the scope, so an `attr` binds the variables its
pattern names for the rest of the production.  Iterations (`?`, `*`, `+`) are recognised
without their list bindings (the lexical grammars iterate only `"_"` and `"."`). -/
partial def pSym (env : Env) (inp : Array Nat) (ρ : VarEnv) (g : IL.Sym) (i j : Nat) :
    StateM Memo (List (VarEnv × Value)) := do
  match g with
  | .numG n => return if j == i + 1 && inp[i]! == n then [(ρ, .num (.natN n))] else []
  | .textG t =>
    let cs := t.toList.map Char.toNat
    return if j == i + cs.length && (List.range cs.length).all (fun k => inp[i + k]! == cs[k]!)
      then [(ρ, .tuple [])] else []
  | .epsG => return if i == j then [(ρ, .tuple [])] else []
  | .rangeG (.numG a) (.numG b) =>
    return if j == i + 1 && a ≤ inp[i]! && inp[i]! ≤ b then [(ρ, .num (.natN inp[i]!))] else []
  | .rangeG _ _ => return []
  | .seqG [] => return if i == j then [(ρ, .tuple [])] else []
  | .seqG (g :: gs) =>
    let mut out := []
    for k in [i:j + 1] do
      for (ρ₁, _) in (← pSym env inp ρ g i k) do
        for (ρ₂, _) in (← pSym env inp ρ₁ (.seqG gs) k j) do
          out := out ++ [(ρ₂, .tuple [])]
    return out
  | .altG gs =>
    let mut out := []
    for g in gs do
      out := out ++ (← pSym env inp ρ g i j)
    return out
  | .attrG e g =>
    let mut out := []
    for (ρ₁, v) in (← pSym env inp ρ g i j) do
      match matchExp tFuel env ρ₁ e v with
      | .ok ρ₂ => out := out ++ [(ρ₂, v)]
      | .error _ => pure ()
    return out
  | .iterG g (.mk it _) =>
    match it with
    | .opt => return (if i == j then [(ρ, .tuple [])] else []) ++ (← pSym env inp ρ g i j)
    | .list => pStar env inp ρ g i j
    | .list1 =>
      let mut out := []
      for k in [i + 1:j + 1] do
        unless (← pSym env inp ρ g i k).isEmpty do
          unless (← pStar env inp ρ g k j).isEmpty do
            out := [(ρ, .tuple [])]
      return out
    | .listN _ _ => return []
  | .varG x args =>
    match evalArgs tFuel env ρ args with
    | .error _ => return []
    | .ok argVs => return (← pNT env inp x argVs i j).map (ρ, ·)

/-- `g*` on `[i, j)`. -/
partial def pStar (env : Env) (inp : Array Nat) (ρ : VarEnv) (g : IL.Sym) (i j : Nat) :
    StateM Memo (List (VarEnv × Value)) := do
  if i == j then return [(ρ, .tuple [])]
  for k in [i + 1:j + 1] do
    unless (← pSym env inp ρ g i k).isEmpty do
      unless (← pStar env inp ρ g k j).isEmpty do
        return [(ρ, .tuple [])]
  return []

/-- The attributes of nonterminal `x` (arguments `argVs`) on `[i, j)`: for every production,
its symbol on the span, then its premises, then its result expression, each by the IL
evaluator.  Memoised; an entry is `[]` while it is computed, which cuts left recursion
(`Tnum ::= Tnum "_"? Tdigit` re-enters only on its own span, where the rest is empty). -/
partial def pNT (env : Env) (inp : Array Nat) (x : IL.Id) (argVs : List ArgV) (i j : Nat) :
    StateM Memo (List Value) := do
  let key := s!"{x}|{(repr argVs).pretty}|{i}|{j}"
  if let some r := (← get).get? key then return r
  modify (·.insert key [])
  let some (ps, _, prods) := env.findGram? x | return []
  let ρ₀ := VarEnv.empty.bindVals ((ps.zip argVs).filterMap fun
    | (.expP y _, .val v) => some (y, v)
    | _ => none)
  let mut out := []
  for .prodD _ g e prems in prods do
    for (ρ₁, _) in (← pSym env inp ρ₀ g i j) do
      match premsHold tFuel env ρ₁ prems with
      | .ok ρ₂ =>
        match evalExp tFuel env ρ₂ e with
        | .ok v => out := out ++ [v]
        | .error _ => pure ()
      | .error _ => pure ()
  modify (·.insert key out)
  return out

end

/-- Whether SpecTec's `TiN(N)`/`TfN(N)` derives the literal `tok` of type `t` (`i32` …). -/
def literalOk (env : Env) (t tok : String) : Bool :=
  let (g, n) := match t with
    | "i32" => ("TiN", 32) | "i64" => ("TiN", 64) | "f32" => ("TfN", 32) | _ => ("TfN", 64)
  let inp := (tok.toList.map Char.toNat).toArray
  !((pNT env inp g [.val (.num (.natN n))] 0 inp.size).run' {}).isEmpty

/-- Whether the literal is a float the text grammars read as a rational (`Tsign` followed by
`Tfloat` or `Thexfloat`), which `TfNmag` then hands to `$ieee_`. -/
def ratOk (env : Env) (tok : String) : Bool :=
  let inp := (tok.toList.map Char.toNat).toArray
  let g : IL.Sym := .seqG [.varG "Tsign" [], .altG [.varG "Tfloat" [], .varG "Thexfloat" []]]
  !((pSym env inp VarEnv.empty g 0 inp.size).run' {}).isEmpty

/-- Classify the first underivable literal.  A float literal that `Tsign (Tfloat | Thexfloat)`
derives fails only at `$ieee_` (no clauses): `stuck ieee_` (not run), since the grammar would
derive it if `$ieee_` were defined.  In an `assert_malformed` module a float rejection is not
counted either (`unsupported float-literal`): the float grammar also rejects literals the
testsuite accepts, so it is no evidence for the malformation the assertion is about. -/
def runText (env : Env) (lines : List String) : IO Unit := do
  for line in lines do
    match line.splitOn " " |>.filter (· ≠ "") with
    | "L" :: i :: _ :: kind :: lits =>
      let parsed := lits.filterMap fun l => match l.splitOn ":" with
        | [t, h] => some (t, unhexStr h)
        | _ => none
      let isFloat (t : String) := t == "f32" || t == "f64"
      match parsed.find? (fun (t, tok) => !literalOk env t tok) with
      | some (t, tok) =>
        if isFloat t && ratOk env tok then
          IO.println s!"{i} stuck ieee_ {t}.const {tok}"
        else if kind == "bad" && isFloat t then
          IO.println s!"{i} unsupported float-literal {t}.const {tok}"
        else IO.println s!"{i} reject underivable {t}.const {tok}"
      | none =>
        if kind == "ok" then IO.println s!"{i} accept"
        else IO.println s!"{i} unsupported no-literal-error"
    | _ => pure ()

end text

/-! ## An executable search for `DDerivesB` derivations

The `spectec-step` column of `tools/wasm-conformance` runs whole Wasm invocations on SpecTec's
reduction relation `Step`, read as `Round6.Reading.DDerivesB` (the backend reading: a rule fires
when *some* typed assignment of its variables makes some alternative of its conclusion
(`conclAlts`) evaluate to the derived value and every premise hold).  `DDerivesB` is an inductive
`Prop`; this file is a **search** for its derivations, in the moded way an inductive backend runs
a relation:

* a relation instance `x(args) ⊢ e₁, …, eₖ` is solved with some components known (inputs) and
  the others unknown (outputs); a rule's conclusion alternative is matched against the known
  components (`matchK`: every split of a concatenation, lazily, first success wins), its premises
  are checked left to right, and the unknown components are then evaluated;
* an `if a = b` premise whose one side does not evaluate yet *binds* by matching it against the
  other side's value (and is re-checked afterwards); a relational premise is solved recursively
  in the same moded way; an `otherwise` premise holds when it is reached, because rules are tried
  in order and the first success is taken (`otherwiseB`'s "no earlier rule fires", assuming the
  search of the earlier rules is complete);
* the quantifiers of a rule (`QuantsOk`) are checked with the evaluator's typing `hasTyp` as soon
  as they are bound, except those of the configuration-sized types `skipTyps` (the input
  configuration is assumed typed, as the simulation's `Typed` hypothesis has it).

Two search restrictions keep a step polynomial: `Step/ctxt-instrs` is tried only on its canonical
split (the context's `instr*` ends at the first non-value instruction of the list), and a global
budget of rule attempts bounds every step.  Neither the search's soundness nor its completeness
with respect to `DDerivesB` is a Lean theorem: this is an unverified executable reading, checked
here only by the testsuite.  A search that runs out of budget, depth or evaluator fuel, or meets a
premise shape it does not handle, says so (`incomplete`), and the harness reports the directive
as not run rather than as a disagreement.
-/

end WasmConformance

namespace WasmConformance.Derive

open Silmaril.SpecTec Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod

variable {α : Type}
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (conclAlts)

/-- The evaluator's fuel (a depth bound, not a cost). -/
def evFuel : Nat := 400000

/-- The global work counter of a step: rule attempts in the step's search **and** in every
`clauseCall` it reaches (each of which runs a search of its own), so that nested function
clauses cannot multiply the per-search budgets.  Reset by `resetWork` before each step. -/
initialize workRef : IO.Ref Nat ← IO.mkRef 0

/-- Count one rule attempt against the global work counter; `false` once it is spent.  `salt`
only keeps calls apart for the compiler. -/
unsafe def tickImpl (salt : Nat) : Bool :=
  unsafeBaseIO do
    let n ← workRef.get
    if n == 0 then return salt == salt && false
    workRef.set (n - 1)
    return true

@[implemented_by tickImpl] opaque tick (salt : Nat) : Bool

/-- Search state: the remaining budget of rule attempts, and the first reason the search was
incomplete (if any). -/
structure St where
  budget : Nat
  incomplete : Option String := none
  /-- Trace lines, when tracing (`WASM_CONFORMANCE_TRACE`). -/
  trace : Option (Array String) := none
  /-- Per relation, per rule: the alternatives of its conclusion (`conclAlts`), with the operator
  the last instruction of each component must have (`lastOp`), computed once. -/
  alts : Std.HashMap IL.Id (Array (List (List Exp × List (Option String)))) := {}

abbrev M := StateM St

def log (f : Unit → String) : M Unit :=
  modify fun st => match st.trace with
    | some t => if t.size < 4000 then { st with trace := some (t.push (f ())) } else st
    | none => st

def short (e : α) [Repr α] (n : Nat := 160) : String := (((repr e).pretty 1000).take n).toString

/-- A value with long lists cut, for traces. -/
partial def trunc : Value → Value
  | .list vs => .list ((vs.take 3).map trunc)
  | .tuple vs => .tuple (vs.map trunc)
  | .case op v => .case op (trunc v)
  | .opt o => .opt (o.map trunc)
  | .struct fs => .struct (fs.map fun (a, v) => (a, trunc v))
  | v => v

def note (why : String) : M Unit :=
  modify fun st => if st.incomplete.isNone then { st with incomplete := some why } else st

/-- A `Res` as an option, noting fuel exhaustion. -/
def ofRes (r : Res α) (what : String) : M (Option α) := do
  match r with
  | .ok a => return some a
  | .error .undef => return none
  | .error .outOfFuel => note s!"evaluator fuel ({what})"; return none

/-- Types whose quantifiers are not re-checked: the configuration-sized ones, which a step binds
to sub-terms of its (typed) input configuration. -/
def skipTyps : List IL.Id :=
  ["state", "store", "frame", "config", "moduleinst", "instr", "funcinst", "tableinst",
   "meminst", "globalinst", "eleminst", "datainst", "structinst", "arrayinst", "exninst",
   "taginst", "expr", "func", "module", "byte"]

def skipTyp : Typ → Bool
  | .varT x _ => skipTyps.contains x
  | .iterT t _ => skipTyp t
  | _ => false

/-- The bound quantifiers of a rule have their declared types (`QuantsOk`, as far as they are
bound; `skipTyps` excepted).  An undecided typing does not reject. -/
def quantsOk (env : Env) (ρ : VarEnv) (qs : List Param) : Bool :=
  qs.all fun
    | .expP x t =>
      skipTyp t || match ρ.findVal? x with
        | none => true
        | some v => match hasTyp evFuel env ρ t v with
          | .ok b => b
          | .error _ => true
    | _ => true

/-- Is `v` a Wasm value (`val`)? -/
def isVal (env : Env) (v : Value) : Bool :=
  match v with
  | .case "CONST" _ | .case "VCONST" _ => true
  | .case op _ =>
    op.startsWith "REF." &&
      (match hasTyp evFuel env VarEnv.empty (.varT "val" []) v with
       | .ok b => b
       | .error _ => false)
  | _ => false

/-! ## Matching, every way, lazily -/

/-- The length a pattern certainly has, if the evaluator can tell (`patLen`). -/
def lenOf (env : Env) (ρ : VarEnv) (e : Exp) : Option Nat :=
  match patLen evFuel env ρ e with
  | .ok k => some k
  | .error _ => none

mutual
/-- Every way of matching the pattern `e` against `v` (extending `ρ`), in order, passed to the
continuation `k` until it succeeds.  Concatenations are split every way (left operand shortest
first) unless an operand's length is known; tuples, lists, cases, options and `SubE` are
descended into; every other pattern is matched by the evaluator's (deterministic) `matchExp`. -/
partial def matchK (env : Env) (ρ : VarEnv) (e : Exp) (v : Value)
    (k : VarEnv → M (Option α)) : M (Option α) := do
  match e, v with
  | .catE e₁ e₂, .list vs =>
    let split (i : Nat) : M (Option α) :=
      matchK env ρ e₁ (.list (vs.take i)) fun ρ₁ => matchK env ρ₁ e₂ (.list (vs.drop i)) k
    match lenOf env ρ e₁ with
    | some i => if i ≤ vs.length then split i else return none
    | none =>
      match lenOf env ρ e₂ with
      | some j => if j ≤ vs.length then split (vs.length - j) else return none
      | none =>
        for i in [0:vs.length + 1] do
          if let some r ← split i then return some r
        return none
  | .tupE es, .tuple vs => matchsK env ρ es vs k
  | .listE es, .list vs => matchsK env ρ es vs k
  | .caseE op e, .case op' w => if op == op' then matchK env ρ e w k else return none
  | .subE e _ _, v => matchK env ρ e v k
  | .optE (some e), .opt (some w) => matchK env ρ e w k
  | .binE op t a b, .num (.natN m) =>
    -- `n * k = m` and `n + k = m` over naturals bind `n` (`memory.size`'s
    -- `$(n * 64 Ki) = |bytes|`), when the other operand evaluates; exact inversions.
    let inv (k : Nat) : Option Nat := match op with
      | .mulOp => if k ≠ 0 ∧ m % k = 0 then some (m / k) else none
      | .addOp => if k ≤ m then some (m - k) else none
      | _ => none
    match evalExp evFuel env ρ (.binE op t a b) with
    | .ok w => if w == .num (.natN m) then k ρ else return none
    | .error .outOfFuel => note "evaluator fuel (arithmetic pattern)"; return none
    | .error .undef =>
      match evalExp evFuel env ρ b, evalExp evFuel env ρ a with
      | .ok (.num (.natN kb)), _ => match inv kb with
        | some x => matchK env ρ a (.num (.natN x)) k
        | none => return none
      | _, .ok (.num (.natN ka)) => match inv ka with
        | some x => matchK env ρ b (.num (.natN x)) k
        | none => return none
      | _, _ => return none
  | .callE f args, v =>
    -- A call pattern whose last argument is not yet bound is matched through the function's
    -- inverse `$inv_f` (SpecTec's `hint(inverse …)`, e.g. `$nbytes_`/`$inv_nbytes_` in the load
    -- rules), and the binding is checked by evaluating the call.
    match evalExp evFuel env ρ (.callE f args) with
    | .ok w => if w == v then k ρ else return none
    | .error .outOfFuel => note "evaluator fuel (call pattern)"; return none
    | .error .undef =>
      match args.reverse with
      | .expA last :: pre =>
        match env.findDef? ("inv_" ++ f) with
        | none => return none
        | some _ =>
          match evalArgs evFuel env ρ pre.reverse with
          | .ok preVs =>
            match env.builtins.call ("inv_" ++ f) (preVs ++ [.val v]) with
            | some u => matchK env ρ last u fun ρ' =>
                match evalExp evFuel env ρ' (.callE f args) with
                | .ok w => if w == v then k ρ' else return none
                | _ => return none
            | none => return none
          | .error _ => return none
      | _ => return none
  | e, v =>
    match ← ofRes (matchExp evFuel env ρ e v) "match" with
    | some ρ' => k ρ'
    | none => return none

partial def matchsK (env : Env) (ρ : VarEnv) (es : List Exp) (vs : List Value)
    (k : VarEnv → M (Option α)) : M (Option α) := do
  match es, vs with
  | [], [] => k ρ
  | e :: es, v :: vs => matchK env ρ e v fun ρ₁ => matchsK env ρ₁ es vs k
  | _, _ => return none
end

/-! ## Rules and premises -/

/-- The operator of the instruction a pattern certainly ends with: a list pattern whose last
part is a list literal ending in a case, or a configuration `z; instrs` with such `instrs`. -/
partial def lastOp : Exp → Option String
  | .listE es => es.getLast?.bind headOp
  | .catE _ b => lastOp b
  | .caseE "%;%" (.tupE [_, e]) => lastOp e
  | .subE e _ _ => lastOp e
  | _ => none
where
  headOp : Exp → Option String
    | .caseE op _ => some op
    | .subE e _ _ => headOp e
    | _ => none

/-- The operator of the last instruction of a value (`lastOp`'s counterpart). -/
def lastOpV : Value → Option String
  | .list vs => match vs.getLast? with
    | some (.case op _) => some op
    | _ => none
  | .case "%;%" (.tuple [_, v]) => lastOpV v
  | _ => none

/-- The components of a relation instance: a tuple's, or the instance itself. -/
def comps : Exp → List Exp
  | .tupE es => es
  | e => [e]

/-- Evaluate what can be evaluated: `some v` for a component whose variables are bound. -/
def tryEval (env : Env) (ρ : VarEnv) (e : Exp) : M (Option Value) :=
  ofRes (evalExp evFuel env ρ e) "eval"

/-- The canonical split of `Step/ctxt-instrs`: its `instr_1*` is what follows the first
non-value instruction of the input list. -/
def canonicalCtxt (env : Env) (input : List (Option Value)) (ρ : VarEnv) : Bool :=
  match input with
  | [some (.case "%;%" (.tuple [_, .list is]))] | some (.case "%;%" (.tuple [_, .list is])) :: _ =>
    match is.findIdx? (fun i => !isVal env i), ρ.findVal? "instr_1*" with
    | some p, some (.list rest) => rest.length == is.length - (p + 1)
    | _, _ => false
  | _ => false

mutual
/-- Solve relation `x` at `args` with the components `input` (`none`: unknown), passing the
full components of each derivation found to `k`, until it succeeds. -/
partial def solve (env : Env) (depth : Nat) (x : IL.Id) (args : List ArgV)
    (input : List (Option Value)) (k : List Value → M (Option α)) : M (Option α) := do
  if depth == 0 then note s!"depth ({x})"; return none
  let some (ps, _, _, rules) := env.findRel? x | note s!"no relation {x}"; return none
  let some ρ₀ := bindParams VarEnv.empty ps args | return none
  let alts ← match (← get).alts.get? x with
    | some a => pure a
    | none =>
      let a := (rules.map fun (.ruleD _ _ _ e _) => (conclAlts e).map fun e' =>
        let cs := comps e'
        (cs, cs.map lastOp)).toArray
      modify fun st => { st with alts := st.alts.insert x a }
      pure a
  -- Per input component: `none` when unknown, `some (lastOpV v)` when known.
  let inOps := input.map fun i => i.map lastOpV
  for r in rules, ra in alts do
    let .ruleD nm qs _ _ prems := r
    for (cs, ops) in ra do
      unless cs.length == input.length do continue
      -- A component ending in a known instruction cannot match an input ending in another.
      unless (ops.zip inOps).all (fun
          | (some o, some (some o')) => o == o'
          | (some _, some none) => false
          | _ => true) do continue
      let st ← get
      if st.budget == 0 || !tick (st.budget + depth) then note "budget"; return none
      set { st with budget := st.budget - 1 }
      -- Match the known components.
      let known := (cs.zip input).filterMap fun (c, i) => i.map (c, ·)
      let res ← matchsK env ρ₀ (known.map (·.1)) (known.map (·.2)) fun ρ₁ => do
        if x == "Step" && nm == "ctxt-instrs" && !canonicalCtxt env input ρ₁ then return none
        unless quantsOk env ρ₁ qs do log (fun _ => s!"{depth} {x}/{nm}: types"); return none
        log fun _ => s!"{depth} {x}/{nm}: matched"
        premsK env depth ρ₁ prems fun ρ₂ => do
          unless quantsOk env ρ₂ qs do return none
          let mut out := []
          for (c, i) in cs.zip input do
            match i with
            | some v => out := out ++ [v]
            | none =>
              match ← tryEval env ρ₂ c with
              | some v => out := out ++ [v]
              | none => note s!"output of {x}/{nm}"; return none
          k out
      if let some a := res then return some a
  return none

/-- The premises, threading the scope: first any `if` that can already be decided (premises
are a conjunction, so their order does not matter to `DDerivesB`; testing side conditions such as
`ctxt-instrs`'s `val* =/= eps \/ instr_1* =/= eps` before the recursive premise keeps the search
from re-entering the same instance), then left to right. -/
partial def premsK (env : Env) (depth : Nat) (ρ : VarEnv) (prems : List Prem)
    (k : VarEnv → M (Option α)) : M (Option α) := do
  let decided := prems.findIdx? fun
    | .ifPr e => match evalExp evFuel env ρ e with
      | .ok (.bool _) => true
      | _ => false
    | _ => false
  match decided with
  | some j =>
    match prems[j]? with
    | some (.ifPr e) =>
      if evalExp evFuel env ρ e == .ok (.bool true) then premsK env depth ρ (prems.eraseIdx j) k
      else return none
    | _ => return none
  | none =>
    -- Then an `if` that can bind (one side of an equation, or the collection of a membership,
    -- evaluates): `Deftype_ok` binds `subtype^n` in its last premise and uses it in its first.
    let evals (e : Exp) : Bool := (evalExp evFuel env ρ e).isOk
    let binding := prems.findIdx? fun
      | .ifPr (.cmpE .eqOp _ a b) => evals a || evals b
      | .ifPr (.memE _ b) => evals b
      | _ => false
    match binding, prems with
    | some j, _ =>
      match prems[j]? with
      | some p => premK env depth ρ p fun ρ₁ => premsK env depth ρ₁ (prems.eraseIdx j) k
      | none => return none
    | none, [] => k ρ
    | none, p :: ps => premK env depth ρ p fun ρ₁ => premsK env depth ρ₁ ps k

partial def premK (env : Env) (depth : Nat) (ρ : VarEnv) (p : Prem)
    (k : VarEnv → M (Option α)) : M (Option α) := do
  match p with
  | .elsePr =>
    -- `otherwise`: no earlier rule fired.  That holds when the earlier rules were searched
    -- completely; after any incomplete search in this step it is not claimed.
    if (← get).incomplete.isSome then note "otherwise after an incomplete search"; return none
    k ρ
  | .ifPr e =>
    match evalExp evFuel env ρ e with
    | .ok (.bool true) => k ρ
    | .ok _ => log (fun _ => s!"  if false: {short e}"); return none
    | .error .outOfFuel => note "evaluator fuel (if)"; return none
    | .error .undef =>
      -- An equation with an unbound side binds it by matching.
      let recheck (ρ' : VarEnv) : M (Option α) := do
        match evalExp evFuel env ρ' e with
        | .ok (.bool true) => k ρ'
        | _ => return none
      let r ← match e with
        | .cmpE .eqOp _ a b =>
          match evalExp evFuel env ρ a, evalExp evFuel env ρ b with
          | .ok va, _ =>
            log (fun _ => s!"  if binds by matching {short (trunc va) 1500}")
            matchK env ρ b va recheck
          | _, .ok vb =>
            log (fun _ => s!"  if binds by matching {short vb 400}")
            matchK env ρ a vb recheck
          | ea, eb =>
            log (fun _ => s!"  if: neither side evaluates ({ea == .error .undef}, {eb == .error .undef}); " ++
              (match b with
               | .callE f xs => s!"call {f}, args ok: {xs.map fun
                   | .expA e => (evalExp evFuel env ρ e).isOk | _ => true}"
               | _ => ""))
            pure none
        | .memE a b =>
          -- `a <- b*` with `a` unbound chooses an element (`binop-val`'s `c <- $binop_(…)`).
          match evalExp evFuel env ρ b with
          | .ok (.list ws) => do
            for w in ws do
              if let some r ← matchK env ρ a w recheck then return some r
            pure none
          | .ok (.opt (some w)) => matchK env ρ a w recheck
          | _ => pure none
        | _ => pure none
      if r.isNone then log fun _ => s!"  if failed: {short e}"
      return r
  | .letPr e₁ e₂ =>
    match ← tryEval env ρ e₂ with
    | some v => matchK env ρ e₁ v k
    | none => return none
  | .rulePr x args _ e =>
    let some avs ← ofRes (evalArgs evFuel env ρ args) "rule args" | return none
    let cs := comps e
    let mut input := []
    for c in cs do input := input ++ [← tryEval env ρ c]
    -- Only the unknown components are matched against the derivation's (the known ones are
    -- the derivation's inputs, unchanged; comparing them would compare whole states).
    let r ← solve env (depth - 1) x avs input fun outs =>
      let unknown := ((cs.zip input).zip outs).filterMap fun ((c, i), o) =>
        if i.isNone then some (c, o) else none
      matchsK env ρ (unknown.map (·.1)) (unknown.map (·.2)) k
    if r.isNone then
      log fun _ => s!"  premise {x} failed; known {input.map Option.isSome}"
    return r
  | .iterPr pr (.mk it ds) =>
    -- The domains that evaluate give the rounds; the others are outputs, collected round by
    -- round and matched against their domain expressions afterwards (`Subtype_ok2`'s
    -- `(if $unrollht_(C, typeuse) = SUB typeuse'* comptype')*` binds `typeuse'*`, `comptype'*`).
    let mut known : List (IL.Id × Value) := []
    let mut outs : List Dom := []
    for d in ds do
      match evalExp evFuel env ρ (domSrc d) with
      | .ok v => known := known ++ [(domVar d, v)]
      | .error .undef => outs := outs ++ [d]
      | .error .outOfFuel => note "evaluator fuel (iteration domain)"; return none
    if known.isEmpty then note "iterated premise with no bound domain"; return none
    let rows : Option (List (List (IL.Id × Value))) :=
      match it with
      | .opt =>
        if known.all (fun p => p.2 == .opt none) then some []
        else (Silmaril.Wasm.SpecTec.Sim.domSomes known).map ([·])
      | .list | .list1 => do
        let dls ← Silmaril.Wasm.SpecTec.Sim.domLists known
        let n := (dls.head?.map (·.2.length)).getD 0
        guard (dls.all (·.2.length == n))
        some (iterRows dls none n)
      | .listN _ _ => none
    let some rows := rows | note "iterated premise shape"; return none
    -- Every round must hold; the rounds' other bindings do not escape (`premIter`).
    roundsK env depth ρ pr (outs.map domVar) rows [] fun cols => do
      let collected : List Value := (List.range outs.length).map fun j =>
        let col := cols.map fun r => r[j]!
        match it with
        | .opt => .opt col.head?
        | _ => .list col
      matchsK env ρ (outs.map domSrc) collected k

/-- The rounds of an iterated premise, each in its own scope; `k` gets, per round, the values of
the output domain variables `ys`. -/
partial def roundsK (env : Env) (depth : Nat) (ρ : VarEnv) (pr : Prem) (ys : List IL.Id)
    (rows : List (List (IL.Id × Value))) (acc : List (List Value))
    (k : List (List Value) → M (Option α)) : M (Option α) := do
  match rows with
  | [] => k acc
  | row :: rest =>
    premK env depth (ρ.bindVals row) pr fun ρ' =>
      match ys.mapM ρ'.findVal? with
      | some vs => roundsK env depth ρ pr ys rest (acc ++ [vs]) k
      | none => do note "iterated premise output unbound"; return none
end

/-! ## Running `Step` -/

/-- The outcome of one step. -/
inductive StepRes where
  | next (c : Value)
  | none
  | incomplete (why : String)

/-- One step of `Step` from the configuration `c`, with a budget of rule attempts, and the trace
when `trace`. -/
def step (env : Env) (budget : Nat) (c : Value) (trace : Bool := false)
    (alts : Std.HashMap IL.Id (Array (List (List Exp × List (Option String))))) :
    StepRes × Array String × Std.HashMap IL.Id (Array (List (List Exp × List (Option String)))) :=
  let (r, st) := (solve env 64 "Step" [] [some c, none] fun
      | [_, c'] => return some c'
      | _ => return none).run { budget, trace := if trace then some #[] else none, alts }
  let t := st.trace.getD #[]
  match r, st.incomplete with
  | some c', _ => (.next c', t, st.alts)
  | none, some why => (.incomplete why, t, st.alts)
  | none, none => (.none, t, st.alts)

end WasmConformance.Derive

namespace WasmConformance

/-! ## SpecTec's `Step`, run on whole invocations (`DDerivesB`) -/

section step
open Silmaril.SpecTec Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod

/-! ### Executable primitives

The `hint(builtin)` functions a step reaches, computably: the numerics of `spectec-il-builtins`
(`intCall`, `floatCall`), Core's little-endian byte encodings `$nbytes_`/`$ibytes_`/`$zbytes_` and
their declared inverses `$inv_…` (what `Sim.FwdMem`/`Sim.ZBytes` interpret, there noncomputably),
and, for the functions whose clauses bind variables in premises (`$unrolldt`, `$blocktype_`,
`$growmem`, `$growtable`, …, which the evaluator cannot run: `Sim.Prims` answers them with Core's
own functions), the clauses themselves, run by the moded search (`clauseCall`) — so these come
from the SpecTec script, not from Core. -/

/-- Little-endian bytes of `n`, `%`-wrapped. -/
def leBytes (k n : Nat) : List Value :=
  (List.range k).map fun i => bitsV ((n / 256 ^ i) % 256)

/-- The number of a little-endian `%`-wrapped byte list. -/
def ofLeBytes (bs : List Value) : Option Nat :=
  bs.foldrM (fun b acc => (asNat b).map (· + 256 * acc)) 0

/-- The storage width (bytes) and the number type of a `storagetype`/`numtype` value. -/
def storageBytes : Value → Option (Nat × Option NumType)
  | .case "I8" (.tuple []) => some (1, none)
  | .case "I16" (.tuple []) => some (2, none)
  | .case "V128" (.tuple []) => some (16, none)
  | v => (numTyOfV v).map fun t => (t.width / 8, some t)

def bytesCall : IL.Id → List ArgV → Option Value
  | "ibytes_", [.val (.num (.natN N)), .val c] => do pure (.list (leBytes (N / 8) (← asNat c)))
  | "inv_ibytes_", [.val (.num (.natN N)), .val (.list bs)] => do
    guard (bs.length = N / 8); pure (bitsV (← ofLeBytes bs))
  | "nbytes_", [.val nt, .val c] => do
    let t ← numTyOfV nt; pure (.list (leBytes (t.width / 8) (← numDec t c)))
  | "inv_nbytes_", [.val nt, .val (.list bs)] => do
    let t ← numTyOfV nt; guard (bs.length = t.width / 8); pure (numEnc t (← ofLeBytes bs))
  | "zbytes_", [.val zt, .val c] => do
    let (k, t) ← storageBytes zt
    let n ← match t with | some t => numDec t c | none => asNat c
    pure (.list (leBytes k n))
  | "__rep", [.val (.num (.natN n)), .val v] => some (.list (List.replicate n v))
  -- `$growmem`'s one clause, transcribed (run through `clauseCall` it re-evaluates the
  -- 64 KiB byte list element by element): `{TYPE (at [i .. j?] PAGE), BYTES b*}` grows to
  -- `{TYPE (at [i' .. j?] PAGE), BYTES b* 0^(n * 64 Ki)}` with `i' = |b*| / 64 Ki + n`,
  -- `i' <= j` (when `j?` is present) and `i' <= 2^($size(at) - 16)`.
  | "growmem", [.val (.struct [("TYPE", .case "%%PAGE" (.tuple [aty, .case "[%..%]" (.tuple [_, j])])),
      ("BYTES", .list bs)]), .val (.num (.natN n))] => do
    let w ← match aty with
      | .case "I32" (.tuple []) => some 32
      | .case "I64" (.tuple []) => some 64
      | _ => none
    let i' := bs.length / 65536 + n
    match j with
    | .opt (some jv) => guard (i' ≤ (← asNat jv))
    | .opt none => pure ()
    | _ => none
    guard (i' ≤ 2 ^ (w - 16))
    pure (.struct [("TYPE", .case "%%PAGE" (.tuple [aty, .case "[%..%]" (.tuple [bitsV i', j])])),
      ("BYTES", .list (bs ++ List.replicate (n * 65536) (bitsV 0)))])
  | "inv_zbytes_", [.val zt, .val (.list bs)] => do
    let (k, t) ← storageBytes zt
    guard (bs.length = k)
    let n ← ofLeBytes bs
    pure (match t with | some t => numEnc t n | none => bitsV n)
  | _, _ => none

/-! ### Iterations without domain variables

The evaluator rejects an iteration with no domain variables (`evalIterE`, after
`eval.ml:377-379`), so `(0x00)^(n * 64 Ki)` in `$growmem` (and every `e^n` that repeats a
constant) does not evaluate.  Its meaning is `n` copies of `e`; the column reads it so by
rewriting `e^n` (no domain, no index variable) to a call of the primitive `$__rep(n, e)`. -/

mutual
partial def rwE : Exp → Exp
  | .iterE e (.mk (.listN n none) []) => .callE "__rep" [.expA (rwE n), .expA (rwE e)]
  | .iterE e (.mk it ds) => .iterE (rwE e) (.mk (rwI it) (ds.map fun (.mk x d) => .mk x (rwE d)))
  | .unE op t e => .unE op t (rwE e)
  | .binE op t a b => .binE op t (rwE a) (rwE b)
  | .cmpE op t a b => .cmpE op t (rwE a) (rwE b)
  | .tupE es => .tupE (es.map rwE)
  | .projE e i => .projE (rwE e) i
  | .caseE op e => .caseE op (rwE e)
  | .uncaseE e op => .uncaseE (rwE e) op
  | .optE eo => .optE (eo.map rwE)
  | .theE e => .theE (rwE e)
  | .strE fs => .strE (fs.map fun (.mk a e) => .mk a (rwE e))
  | .dotE e a => .dotE (rwE e) a
  | .compE a b => .compE (rwE a) (rwE b)
  | .listE es => .listE (es.map rwE)
  | .liftE e => .liftE (rwE e)
  | .memE a b => .memE (rwE a) (rwE b)
  | .lenE e => .lenE (rwE e)
  | .catE a b => .catE (rwE a) (rwE b)
  | .idxE a b => .idxE (rwE a) (rwE b)
  | .sliceE a b c => .sliceE (rwE a) (rwE b) (rwE c)
  | .updE a p b => .updE (rwE a) (rwP p) (rwE b)
  | .extE a p b => .extE (rwE a) (rwP p) (rwE b)
  | .callE x xs => .callE x (xs.map rwA)
  | .cvtE e t₁ t₂ => .cvtE (rwE e) t₁ t₂
  | .subE e t₁ t₂ => .subE (rwE e) t₁ t₂
  | e => e
partial def rwI : Iter → Iter
  | .listN e x => .listN (rwE e) x
  | it => it
partial def rwP : Path → Path
  | .idxP p e => .idxP (rwP p) (rwE e)
  | .sliceP p a b => .sliceP (rwP p) (rwE a) (rwE b)
  | .dotP p a => .dotP (rwP p) a
  | .rootP => .rootP
partial def rwA : Arg → Arg
  | .expA e => .expA (rwE e)
  | a => a
partial def rwPr : Prem → Prem
  | .rulePr x xs op e => .rulePr x (xs.map rwA) op (rwE e)
  | .ifPr e => .ifPr (rwE e)
  | .letPr a b => .letPr (rwE a) (rwE b)
  | .iterPr pr (.mk it ds) =>
    .iterPr (rwPr pr) (.mk (rwI it) (ds.map fun (.mk x d) => .mk x (rwE d)))
  | .elsePr => .elsePr
end

/-- `rwE` on every rule and clause of the environment (and the declaration of `$__rep`). -/
def rwEnv (env : Env) : Env :=
  { env with
    rels := env.rels.map fun (x, (ps, op, t, rules)) =>
      (x, (ps, op, t, rules.map fun (.ruleD nm qs op e prems) =>
        .ruleD nm qs op (rwE e) (prems.map rwPr)))
    defs := ("__rep", ([], .boolT, [])) :: env.defs.map fun (x, (ps, t, cs)) =>
      (x, (ps, t, cs.map fun (.defD qs xs e prems) =>
        .defD qs (xs.map rwA) (rwE e) (prems.map rwPr))) }

/-- The functions some clause of which has a premise (candidates for `clauseCall`). -/
def premiseFuns (env : Env) : List IL.Id :=
  env.defs.filterMap fun (x, (_, _, cs)) =>
    if cs.any (fun | .defD _ _ _ prems => !prems.isEmpty) then some x else none

/-- A function's clauses, first match, with their premises run by the moded search. -/
def clauseCall (trace : Bool) (env : Env) (x : IL.Id) (ws : List ArgV) : Option Value := Id.run do
  let some (_, _, cs) := env.findDef? x | return none
  for .defD _ pats e prems in cs do
    let .ok ρ := matchArgs Derive.evFuel env VarEnv.empty pats ws | continue
    let (r, st) := (Derive.premsK env 16 ρ prems fun ρ' =>
      return (match evalExp Derive.evFuel env ρ' e with
        | .ok v => some v
        | .error _ => none)).run { budget := 100000, trace := if trace then some #[] else none }
    let r := if trace then
        dbgTrace s!"clauseCall {x}: {r.isSome}\n{"\n".intercalate (st.trace.getD #[]).toList}" fun _ => r
      else r
    if let some v := r then return some v
  return none

/-- The environment of the `spectec-step` column: the script with the primitives above, and
`clauseCall` nested `depth` times for the premise-binding functions. -/
def stepEnv (trace : Bool) (base : Env) (funs : List IL.Id) : Nat → Env
  | 0 => base.withBuiltins ⟨prim⟩
  | n + 1 =>
    let inner := stepEnv trace base funs n
    base.withBuiltins ⟨fun x ws => (prim x ws).orElse fun _ =>
      -- `$growmem` is answered by its transcription alone (`none` is its clause failing).
      if funs.contains x && x != "growmem" then clauseCall trace inner x ws else none⟩
where
  prim (x : IL.Id) (ws : List ArgV) : Option Value :=
    (intCall x ws).orElse fun _ => (floatCall x ws).orElse fun _ => bytesCall x ws

/-- Steps per invocation. -/
def stepLimit : Nat := 20000

/-- Rule attempts per step. -/
def stepBudget : Nat := 200000

/-- A result value of the IL, in the harness's token format (the inverse of `Sim.valV`). -/
def ilValTok : Value → Option String
  | .case "CONST" (.tuple [nt, n]) => do
    let t ← numTyOfV nt
    let b ← numDec t n
    pure s!"{ntTok t}:{b}"
  | .case "VCONST" (.tuple [_, .case "%" (.tuple [.num (.natN n)])]) => some s!"v128:{hex32 n}"
  | .case "REF.NULL_ADDR" _ => some "ref.null"
  | .case "REF.EXTERN" (.case "REF.HOST_ADDR" (.num (.natN n))) => some s!"ref.extern:{n}"
  | .case "REF.FUNC_ADDR" (.num (.natN a)) => some s!"ref:func{a}"
  | .case op _ => if op.startsWith "REF." then some "ref:other" else none
  | _ => none

/-- The operator of an instruction, for messages. -/
def opName : Value → String
  | .case op _ => op
  | _ => "?"

/-- Run `Step` from `c` until the instructions are values or `TRAP`. -/
abbrev AltsCache := Std.HashMap IL.Id (Array (List (List Exp × List (Option String))))

/-- The conclusion alternatives, kept across steps and invocations. -/
initialize altsCache : IO.Ref AltsCache ← IO.mkRef {}

/-- Wall-clock limit per invocation (ms). -/
def stepTimeMs : Nat := 10000

def runSteps (env : Env) (c : Value) (trace : Bool) : IO String := do
  let mut c := c
  let t0 ← IO.monoMsNow
  for _ in [0:stepLimit] do
    if (← IO.monoMsNow) - t0 > stepTimeMs then return "stuck time-limit"
    let .case "%;%" (.tuple [_, .list is]) := c | return "error config-shape"
    if is == [.case "TRAP" (.tuple [])] then return "trap"
    if let some toks := is.mapM ilValTok then
      return s!"ok {" ".intercalate toks}"
    Derive.workRef.set stepBudget
    let (r, t, alts') := Derive.step env stepBudget c trace (← altsCache.get)
    altsCache.set alts'
    if trace then
      IO.eprintln s!"--- step on {(is.map opName)}"
      for l in t do IO.eprintln l
    match r with
    | .next c' => c := c'
    | .incomplete why => return s!"stuck search {why}"
    | .none =>
      let hd := (is.find? fun i => (ilValTok i).isNone).map opName
      return s!"stuck no-rule {hd.getD "?"}"
  return "stuck step-limit"

/-- The `spectec-step` outcome of invoking `a` with `vs` in `s`. -/
def stepInvoke (env : Env) (trace : Bool) (s : Store Nat) (a : Nat) (vs : List Val) : IO String :=
  runSteps env (Silmaril.Wasm.SpecTec.Sim.configV (fun h => s!"host{h}") (invoke s a vs)) trace

end step

/-! ## Whole text modules against SpecTec's text grammar (`spectec-module`)

The `spectec-text` column checks literals; this one parses whole modules.  The text grammars of
the IL are character-level and carry attributes and premises (identifier contexts `I`, which a
module defines in terms of its own declarations); `pNT` scales to tokens, not to modules.  So
the module is read at two levels:

* **tokens**: the source is split into the tokens of `6.0-text.lexical` (`Ttoken`, separated by
  `Tspace`: blanks, `;;` and nested `(; ;)` comments, `(@…)` annotations), by a hand-written lexer
  (`lexTokens`).  `offset=`/`align=` prefixes are split off their number, because the grammar
  writes `"offset=" Tu64` as two symbols.
* **structure**: the non-lexical grammars (`Tmodule`, `Tdecl_`, `Tplaininstr_`, …) are read as a
  context-free grammar over tokens, **dropping attributes, premises and expression arguments**
  (grammar arguments, as in `Tlist(Tfoo)`, are substituted), and recognised by an Earley chart
  (`earley`).  The lexical nonterminals (`lexical`) match one token each: integers, identifiers,
  strings and names by `pNT` on the token's characters (with their premises), floats by the prose
  float grammar (`floatTokOk`), since the IL's `TfN` derives no literal without an exponent and
  stops at `$ieee_` (findings 8 and 9, measured by `spectec-text`).

Dropping premises makes the context-free reading an over-approximation of the IL grammar's
language (up to the lexer and the token classes), so a rejection here is a rejection by the IL
grammar; an acceptance says only that the module has the IL grammar's shape.  `T` lines:
`accept`, or `reject at token k "…"` (for a malformed module, `stuck reject-unattributed`: the
rejection may have another cause than the malformation).  Nothing here is proved. -/

section module
open Silmaril.SpecTec Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod

/-! ### Tokens -/

def isSpaceChar (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The tokens of a text source (`Ttoken`s separated by `Tspace`), or the position of a lexical
error (an unterminated string or comment). -/
partial def lexTokens (src : String) : Except Nat (Array String) := Id.run do
  let cs := src.toList.toArray
  let n := cs.size
  let mut out : Array String := #[]
  let mut i := 0
  while i < n do
    let c := cs[i]!
    if isSpaceChar c then i := i + 1
    else if c == ';' && i + 1 < n && cs[i+1]! == ';' then
      while i < n && cs[i]! != '\n' do i := i + 1
    else if c == '(' && i + 1 < n && cs[i+1]! == ';' then
      let mut depth := 1
      i := i + 2
      while i < n && depth > 0 do
        if cs[i]! == '(' && i + 1 < n && cs[i+1]! == ';' then depth := depth + 1; i := i + 2
        else if cs[i]! == ';' && i + 1 < n && cs[i+1]! == ')' then depth := depth - 1; i := i + 2
        else i := i + 1
      if depth > 0 then return .error i
    else if c == '(' && i + 1 < n && cs[i+1]! == '@' then
      -- An annotation: skip to its balancing `)` (strings inside are skipped whole).
      let mut depth := 1
      i := i + 2
      while i < n && depth > 0 do
        if cs[i]! == '"' then
          i := i + 1
          while i < n && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
          i := i + 1
        else
          if cs[i]! == '(' then depth := depth + 1
          if cs[i]! == ')' then depth := depth - 1
          i := i + 1
      if depth > 0 then return .error i
    else if c == '(' || c == ')' then out := out.push c.toString; i := i + 1
    else
      -- A run of non-space, non-parenthesis characters, strings included (`Treserved` allows
      -- strings inside a token; a well-formed module has them standalone).
      let st := i
      while i < n && !isSpaceChar cs[i]! && cs[i]! != '(' && cs[i]! != ')' do
        if cs[i]! == '"' then
          i := i + 1
          while i < n && cs[i]! != '"' do i := i + (if cs[i]! == '\\' then 2 else 1)
          if i ≥ n then return .error st
          i := i + 1
        else i := i + 1
      let tok := String.ofList (cs.extract st i).toList
      let split (p : String) : Option (String × String) :=
        if tok.startsWith p && tok.length > p.length then some (p, (tok.drop p.length).toString)
        else none
      match split "offset=", split "align=" with
      | some (a, b), _ | none, some (a, b) => out := out.push a |>.push b
      | none, none => out := out.push tok
  return .ok out

/-! ### Lexical token classes -/

/-- The nonterminals matched by one token. -/
def lexical (x : IL.Id) : Bool :=
  ["TuN", "TsN", "TiN", "TfN", "Tnum", "Thexnum", "Tstring", "Tname", "Tid", "Tfloat",
   "Thexfloat", "Tkeyword", "Treserved", "Tu8", "Tu16", "Tu32", "Tu64", "Ti8", "Ti16", "Ti32",
   "Ti64", "Tf32", "Tf64"].contains x

/-- A float token of the prose grammar (sign, then a decimal or hexadecimal mantissa with an
optional exponent, `inf`, `nan` or `nan:0x…`). -/
def floatTokOk (tok : String) : Bool :=
  let t := if tok.startsWith "+" || tok.startsWith "-" then (tok.drop 1).toString else tok
  let digitsOk (s : String) (hex : Bool) : Bool :=
    !s.isEmpty && !s.startsWith "_" && !s.endsWith "_" && (s.splitOn "__").length == 1 &&
      s.all fun c => c == '_' || c.isDigit || (hex && ("abcdefABCDEF".toList.contains c))
  let mant (s : String) (hex : Bool) : Bool :=
    match s.splitOn "." with
    | [p] => digitsOk p hex
    | [p, ""] => digitsOk p hex
    | [p, q] => digitsOk p hex && digitsOk q hex
    | _ => false
  let expo (s : String) : Bool :=
    let s := if s.startsWith "+" || s.startsWith "-" then (s.drop 1).toString else s
    digitsOk s false
  if t == "inf" || t == "nan" then true
  else if t.startsWith "nan:0x" then digitsOk (t.drop 6).toString true
  else if t.startsWith "0x" then
    let b := (t.drop 2).toString
    match b.splitOn "p", b.splitOn "P" with
    | [m], [_] => mant m true
    | [m, e], _ | _, [m, e] => mant m true && expo e
    | _, _ => false
  else
    match t.splitOn "e", t.splitOn "E" with
    | [m], [_] => mant m false
    | [m, e], _ | _, [m, e] => mant m false && expo e
    | _, _ => false

/-- Whether the lexical nonterminal `x` (arguments `args`, evaluated in the empty scope; `64` when
they do not evaluate) derives the token. -/
def lexOk (env : Env) (x : IL.Id) (args : List Arg) (tok : String) : Bool :=
  let width : Nat := match evalArgs 200 env VarEnv.empty args with
    | .ok [.val (.num (.natN n))] => n
    | _ => 64
  let nat (k : Nat) : List ArgV := [.val (.num (.natN k))]
  let fixed : List (IL.Id × IL.Id × Nat) :=
    [("Tu8", "TuN", 8), ("Tu16", "TuN", 16), ("Tu32", "TuN", 32), ("Tu64", "TuN", 64),
     ("Ti8", "TiN", 8), ("Ti16", "TiN", 16), ("Ti32", "TiN", 32), ("Ti64", "TiN", 64)]
  let g : IL.Id := match fixed.lookup x with
    | some (g, _) => g
    | none => x
  let gas : List ArgV := match fixed.lookup x with
    | some (_, k) => nat k
    | none => if ["TuN", "TsN", "TiN"].contains x then nat width else []
  if ["TfN", "Tf32", "Tf64", "Tfloat", "Thexfloat"].contains x then floatTokOk tok
  else
    let inp := (tok.toList.map Char.toNat).toArray
    !((pNT env inp g gas 0 inp.size).run' {}).isEmpty

/-! ### The context-free reading, and an Earley chart -/

inductive GSym where
  | t (s : String)
  | lex (x : IL.Id) (args : List Arg)
  | n (id : Nat)

structure CFG where
  prods : Array (Nat × Array GSym) := #[]
  byLhs : Std.HashMap Nat (Array Nat) := {}
  insts : Std.HashMap String Nat := {}
  next : Nat := 0

abbrev CM := StateM CFG

def fresh : CM Nat := modifyGet fun g => (g.next, { g with next := g.next + 1 })

def addProd (lhs : Nat) (rhs : Array GSym) : CM Unit :=
  modify fun g =>
    { g with prods := g.prods.push (lhs, rhs),
             byLhs := g.byLhs.insert lhs (((g.byLhs.get? lhs).getD #[]).push g.prods.size) }

/-- Substitute grammar parameters in a symbol. -/
partial def substSym (σ : List (IL.Id × Sym)) : Sym → Sym
  | .varG x [] => (σ.lookup x).getD (.varG x [])
  | .varG x args => .varG x (args.map fun | .gramA g => .gramA (substSym σ g) | a => a)
  | .seqG gs => .seqG (gs.map (substSym σ))
  | .altG gs => .altG (gs.map (substSym σ))
  | .iterG g it => .iterG (substSym σ g) it
  | .attrG e g => .attrG e (substSym σ g)
  | g => g

mutual
/-- The context-free reading of a symbol, as a sequence of grammar symbols. -/
partial def compileSym (env : Env) (g : Sym) : CM (Array GSym) := do
  match g with
  | .textG t => return #[.t t]
  | .epsG => return #[]
  | .seqG gs => do
    let mut out := #[]
    for g in gs do out := out ++ (← compileSym env g)
    return out
  | .altG gs => do
    let x ← fresh
    for g in gs do addProd x (← compileSym env g)
    return #[.n x]
  | .iterG g (.mk it _) => do
    let body ← compileSym env g
    let x ← fresh
    match it with
    | .opt => addProd x #[]; addProd x body
    | .list1 =>
      let y ← fresh
      addProd y #[]; addProd y (body.push (.n y))
      addProd x (body.push (.n y))
    | _ => addProd x #[]; addProd x (body.push (.n x))
    return #[.n x]
  | .attrG _ g => compileSym env g
  | .varG x args =>
    if lexical x then return #[.lex x args]
    else return #[.n (← inst env x args)]
  | _ => return #[.t "\u0000"]

/-- The nonterminal of grammar `x` at the grammar arguments of `args`, compiled once. -/
partial def inst (env : Env) (x : IL.Id) (args : List Arg) : CM Nat := do
  let gargs := args.filterMap fun | .gramA g => some g | _ => none
  let key := s!"{x}|{(repr gargs).pretty 100000}"
  if let some i := (← get).insts.get? key then return i
  let i ← fresh
  modify fun g => { g with insts := g.insts.insert key i }
  let some (ps, _, prods) := env.findGram? x | return i
  let gps := ps.filterMap fun | .gramP p _ _ => some p | _ => none
  let σ := gps.zip gargs
  for .prodD _ g _ _ in prods do
    addProd i (← compileSym env (substSym σ g))
  return i
end

/-- The nullable nonterminals (a least fixed point). -/
def nullables (g : CFG) : Std.HashSet Nat := Id.run do
  let mut s : Std.HashSet Nat := {}
  let mut changed := true
  while changed do
    changed := false
    for (l, rhs) in g.prods do
      if !s.contains l && rhs.all (fun | .n m => s.contains m | _ => false) then
        s := s.insert l; changed := true
  return s

/-- An Earley item: production, dot, origin. -/
abbrev Item := Nat × Nat × Nat

/-- The item sets and their membership sets. -/
abbrev Chart := Array (Array Item) × Array (Std.HashSet Item)

def Chart.add (c : Chart) (k : Nat) (it : Item) : Chart :=
  if c.2[k]!.contains it then c else (c.1.modify k (·.push it), c.2.modify k (·.insert it))

/-- Earley recognition of `toks` from the nonterminal `start`: `none` on acceptance, or the
index of the first token no item can scan. -/
def earley (env : Env) (g : CFG) (start : Nat) (toks : Array String) : Option Nat := Id.run do
  let nul := nullables g
  let n := toks.size
  let mut c : Chart := (Array.replicate (n + 1) #[], Array.replicate (n + 1) {})
  let mut lexMemo : Std.HashMap (String × Nat) Bool := {}
  for p in (g.byLhs.get? start).getD #[] do
    c := c.add 0 (p, 0, 0)
  for k in [0:n + 1] do
    let mut j := 0
    while j < c.1[k]!.size do
      let (p, d, o) := c.1[k]![j]!
      j := j + 1
      let (lhs, rhs) := g.prods[p]!
      match rhs[d]? with
      | none =>
        -- Complete: advance every item at `o` waiting for `lhs`.
        let waiting := c.1[o]!
        for (p', d', o') in waiting do
          if let some (.n m) := g.prods[p']!.2[d']? then
            if m == lhs then c := c.add k (p', d' + 1, o')
      | some (.n m) =>
        for q in (g.byLhs.get? m).getD #[] do
          c := c.add k (q, 0, k)
        if nul.contains m then c := c.add k (p, d + 1, o)
      | some (.t s) =>
        if k < n && toks[k]! == s then c := c.add (k + 1) (p, d + 1, o)
      | some (.lex x args) =>
        if k < n then
          let key := (toks[k]!, p * 1000 + d)
          let ok := match lexMemo.get? key with
            | some b => b
            | none => lexOk env x args toks[k]!
          lexMemo := lexMemo.insert key ok
          if ok then c := c.add (k + 1) (p, d + 1, o)
  if c.1[n]!.any (fun (p, d, o) => o == 0 && g.prods[p]!.1 == start && d == g.prods[p]!.2.size)
  then return none
  -- The last position the chart reached: its token is the first one no item can scan.
  let last := (List.range (n + 1)).foldl (fun acc k => if c.1[k]!.isEmpty then acc else k) 0
  return some last

/-- The `spectec-module` column on the `T` lines. -/
def runModules (env : Env) (lines : List String) : IO Unit := do
  let (startNT, g) := (inst env "Tmodule" []).run {}
  for line in lines do
    match line.splitOn " " |>.filter (· ≠ "") with
    | ["T", i, _, kind, h] =>
      let src := unhexStr h
      match lexTokens src with
      | .error pos => IO.println s!"{i} reject lexical-error at {pos}"
      | .ok toks =>
        match earley env g startNT toks with
        | none => IO.println s!"{i} accept"
        | some k =>
          let tok := (toks[k]?).getD "<end>"
          -- A malformed module the grammar rejects may be rejected for a reason other than its
          -- malformation (the IL grammar has no abbreviations, see the section docstring): not
          -- counted.
          if kind == "ok" then IO.println s!"{i} reject at token {k} {tok.take 40}"
          else IO.println s!"{i} stuck reject-unattributed at token {k} {tok.take 40}"
      (← IO.getStdout).flush
    | _ => pure ()

end module

/-! ## The official SpecTec Lean backend's model -/

/-- The numeric functions `SpecTecLean` renders as executable `def`s. -/
def leanApply (mn : String) (args : List Nat) : String :=
  let w := if mn.startsWith "i64." then 64 else 32
  let ty := if w == 32 then "i32" else "i64"
  let u (n : Nat) : SpecTecLean.uN := .mk_uN (n % 2 ^ w)
  let num (r : SpecTecLean.uN) := s!"ok {ty}:{SpecTecLean.proj_uN_0 r}"
  let rel (r : SpecTecLean.uN) := s!"ok i32:{SpecTecLean.proj_uN_0 r}"
  match mn.splitOn ".", args with
  | [_, "add"], [a, b] => num (SpecTecLean.iadd_ w (u a) (u b))
  | [_, "sub"], [a, b] => num (SpecTecLean.isub_ w (u a) (u b))
  | [_, "mul"], [a, b] => num (SpecTecLean.imul_ w (u a) (u b))
  | [_, "eq"], [a, b] => rel (SpecTecLean.ieq_ w (u a) (u b))
  | [_, "ne"], [a, b] => rel (SpecTecLean.ine_ w (u a) (u b))
  | _, _ => "unsupported opaque-or-relational"

def runLean (lines : List String) : IO Unit := do
  for line in lines do
    match line.splitOn " " |>.filter (· ≠ "") with
    | "K" :: i :: _ :: mn :: args =>
      let nums := args.filterMap fun t => match t.splitOn ":" with
        | ["i32", n] | ["i64", n] => n.toNat?
        | _ => none
      if nums.length == args.length then IO.println s!"{i} {leanApply mn nums}"
      else IO.println s!"{i} unsupported operand-type"
    | _ => pure ()

end WasmConformance

open WasmConformance in
def main (args : List String) : IO UInt32 := do
  let lines (p : String) : IO (List String) := return (← IO.FS.readFile p).splitOn "\n"
  match args with
  | ["core", s] => runCore (← lines s); pure 0
  | ["spectec-il", ast, s] => runIL (← readEnv ast false) (← lines s); pure 0
  | ["spectec-il-builtins", ast, s] => runIL (← readEnv ast true) (← lines s); pure 0
  | ["spectec-lean", s] => runLean (← lines s); pure 0
  | ["spectec-text", ast, s] => runText (← readEnv ast false) (← lines s); pure 0
  | ["spectec-module", ast, s] => runModules (← readEnv ast false) (← lines s); pure 0
  | ["spectec-step", ast, s] =>
    let trace := (← IO.getEnv "WASM_CONFORMANCE_TRACE").isSome
    let base := rwEnv (← readEnv ast false)
    let env := stepEnv trace base (premiseFuns base) 4
    if trace then IO.eprintln s!"premise functions: {premiseFuns base}"
    runCore (← lines s) (some (stepInvoke env trace)); pure 0
  | _ =>
    IO.eprintln "usage: wasm-conformance-lean (core | spectec-il AST | spectec-il-builtins AST | spectec-lean | spectec-text AST | spectec-step AST | spectec-module AST) SCRIPT"
    pure 2
