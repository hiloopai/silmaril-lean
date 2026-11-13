module

public import Silmaril.Compiler.C.Sem.C7Format.Defs
/-! # C7 typed printf family and successful writes to the two standard streams -/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C7

open Silmaril.Compile.C
open C0 (Stop ub)
open C1 (wrap)
open C4 (Arg)

/-- Opaque stream pointers outside the bounded object memory and C4's function tokens. -/
def stdoutHandle : Int := 2^61
def stderrHandle : Int := 2^61 + 16

def checkStream (h : Int) : Except Stop Unit := do
  if h != stdoutHandle && h != stderrHandle then ub "an invalid standard stream handle"

def emitStream (env : Env) (h : Int) (bs : Array UInt8) : Except Stop Env := do
  checkStream h
  return if h == stdoutHandle then { env with out := bs.foldl (·.push ·) env.out } else env

/-- Read a live cursor, retaining its handle solely for a subsequent `va_end`. -/
def consumeCursor (env : Env) (h : Int) : Except Stop (List Arg × Env) := do
  if h ≤ 0 || env.consumed.contains h.toNat then ub "an invalid or consumed va_list"
  let some c := env.cursors[h.toNat]? | ub "an expired va_list"
  return (c.remaining, { env with consumed := env.consumed.insert h.toNat })

/-- Argument values for the fixed, nonfloating part of an external signature. -/
def integerArgs (args : List Arg) : Except Stop (List Int) :=
  args.mapM fun a => do
    if a.ty.isFloat then ub "a floating argument of an integer external parameter"
    match a.val with
    | .scalar v => pure v
    | .agg _ => throw (.unsupported "an aggregate argument of an external function")

/-- All printf destinations share the same typed formatter. -/
def printTo (name : String) (fixed : List Int) (args : List Arg) (env : Env) :
    Except Stop (Int × Env) := do
  let fmt ← match fixed.getLast? with
    | some f => pure f
    | none => throw (.unsupported "missing printf fixed arguments")
  let bs ← formatTyped env (← formatString env fmt none).toList args
  match name, fixed with
  | "printf", [_] => return (bs.size, ← emitStream env stdoutHandle bs)
  | "fprintf", [h, _] => return (bs.size, ← emitStream env h bs)
  | "sprintf", [s, _] =>
    env.access s.toNat (bs.size + 1)
    return (bs.size, ← env.withMem (·.writeBytes s.toNat (bs.push 0)))
  | "snprintf", [s, count, _] =>
    let count := (wrap 8 false count).toNat
    if count == 0 then return (bs.size, env)
    let bytes := (bs.toList.take (count - 1)).toArray.push 0
    env.access s.toNat bytes.size
    return (bs.size, ← env.withMem (·.writeBytes s.toNat bytes))
  | _, _ => throw (.unsupported "printf with the wrong fixed arguments")

/-- C7 external calls receive promoted argument types, including through function pointers. -/
def externalTyped (name : String) (args : List Arg) (env : Env) : Except Stop (Int × Env) := do
  let (baseName, isV) := match name with
    | "vprintf" => ("printf", true)
    | "vfprintf" => ("fprintf", true)
    | "vsprintf" => ("sprintf", true)
    | "vsnprintf" => ("snprintf", true)
    | n => (n, false)
  let fixedCount := match baseName with
    | "printf" => 1 | "fprintf" | "sprintf" => 2 | "snprintf" => 3 | _ => 0
  if fixedCount != 0 then
    let fixed ← integerArgs (args.take fixedCount)
    if fixed.length != fixedCount then ub "too few printf fixed arguments"
    if isV then
      let [h] ← integerArgs (args.drop fixedCount) | ub "a vprintf cursor argument"
      let (rest, env) ← consumeCursor env h
      return ← printTo baseName fixed rest env
    return ← printTo baseName fixed (args.drop fixedCount) env
  if let some (_, f) := C3.F.libm name then
    match args with
    | [⟨_, .scalar x⟩] => return (f x.toNat, env)
    | _ => throw (.unsupported "libm arity")
  let vs ← integerArgs args
  match name, vs with
  | "fputs", [s, h] =>
    checkStream h
    let bs ← formatString env s none
    return (1, ← emitStream env h bs)
  | "fputc", [c, h] | "putc", [c, h] =>
    let b := wrap 1 false c
    return (b, ← emitStream env h #[b.toNat.toUInt8])
  | "fwrite", [p, size, count, h] =>
    checkStream h
    let size := (wrap 8 false size).toNat
    let count := (wrap 8 false count).toNat
    if size == 0 || count == 0 then return (0, env)
    let n := size * count
    if n > C1.maxBytes then throw (.unsupported "a fwrite resource bound")
    env.access p.toNat n
    let bs ← env.mem.readBytes p.toNat n
    return (count, ← emitStream env h bs)
  | "fflush", [h] =>
    if h != 0 then checkStream h
    return (0, env)
  | "ferror", [h] | "clearerr", [h] =>
    checkStream h
    return (0, env)
  | _, _ => external name vs env

end Silmaril.Compile.C.Sem.C7
