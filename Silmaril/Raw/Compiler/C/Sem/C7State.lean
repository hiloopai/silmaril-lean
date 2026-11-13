module

public import Silmaril.Compiler.C.Sem.C6.Defs
/-! # C7 interpreter state: C5's heap, C6 literal slots, and consumed `va_list` handles. -/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C7

open Silmaril.Cerberus Silmaril.Cerberus.Ail
open Silmaril.Compile.C
open C0 (Stop ub Kont Result)
open C1 (Memory Place FunDef wrap convTo shape store base externals plainString)
open C2 (Agg Val Next aggOf lvType readAgg writeAgg depth)
open C3 (ofInt truthOf floatConst storeV layoutOf sizeAlignOf)
open C4 (Arg Cursor Prog codeAddress callTypes vaCompatible writeConst usualOf isFunction)

/-- C5's state and heap, plus the literal slots of the current activation. -/
structure Env extends toC5 : C5.Env where
  literals : Std.HashMap Nat Nat := {}
  consumed : Std.HashSet Nat := {}

@[inline] def Env.withMem (env : Env) (f : Memory → Except Stop Memory) : Except Stop Env := do
  return { env with mem := ← f env.mem }
@[inline] def Env.setReg (env : Env) (x : Nat) (v : Int) : Env :=
  { env with regs := env.regs.insert x v }
def Env.newCursor (env : Env) (c : Cursor) : Except Stop (Int × Env) := do
  let (h, e) ← env.toC5.newCursor c
  return (h, { env with toC5 := e })
def Env.takeArg (env : Env) (h : Int) : Except Stop (Arg × Env) := do
  if env.consumed.contains h.toNat then ub "va_arg after vprintf"
  let (a, e) ← env.toC5.takeArg h
  return (a, { env with toC5 := e })
def Env.expire (env : Env) (activation : Nat) : Env :=
  { env with toC5 := env.toC5.expire activation }
def Env.access (env : Env) (a n : Nat) : Except Stop Unit := env.toC5.access a n

def readPlace (fd : FunDef) (env : Env) (t : CType) (pl : Place) : Except Stop Int :=
  C5.readPlace fd env.toC5 t pl
def writePlace (env : Env) (t : CType) (v : Int) (pl : Place) : Except Stop Env := do
  return { env with toC5 := ← C5.writePlace env.toC5 t v pl }
def external (name : String) (args : List Int) (env : Env) : Except Stop (Int × Env) := do
  let (v, e) ← C5.external name args env.toC5
  return (v, { env with toC5 := e })


end Silmaril.Compile.C.Sem.C7
