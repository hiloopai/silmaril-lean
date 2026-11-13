module
public import Silmaril.Compiler.C.Sem.C1.Defs
/-! Shared nonrecursive C1 call setup and return projection. Keeping the body
runner abstract lets concrete call proofs normalize the calling convention
without unfolding the recursive statement interpreter. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.C1Call
open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- Parameter conversion, stack allocation and caller restoration, with an
abstract runner for the callee body. This is exactly the prelude of C1.callFn. -/
def callWith (P : C1.Prog) (params : List (Nat × CType))
    (locals : List (Nat × Ctype)) (ret : CType) (g : Sym)
    (vs : List Int) (env : C1.Env)
    (run : C1.Env → Except C0.Stop (Option Int × C1.Env)) : Except C0.Stop (Int × C1.Env) := do
  if params.length != vs.length then
    .error (.unsupported s!"call of {P.name g} with {vs.length} arguments")
  let ⟨caller, callerFrame, mem, out⟩ := env
  let sp := mem.sp
  let mut mem := mem
  let mut frame : Std.HashMap Nat Nat := {}
  for (x, ty) in locals do
    let (size, align) ← P.sizeAlign ty
    let (a, m) ← mem.alloc size align
    mem := m
    frame := frame.insert x a
  let mut regs : Std.HashMap Nat Int := {}
  for ((x, pt), v) in params.zip vs do
    let v ← C1.convTo pt v
    match frame[x]? with
    | some a => mem ← C1.store mem pt a v
    | none => regs := regs.insert x v
  let (r, ⟨_, _, mem', out⟩) ← run ⟨regs, frame, mem, out⟩
  return ((← C1.convTo ret (r.getD 0)), ⟨caller, callerFrame, {mem' with sp}, out⟩)

/-- The recursive evaluator occurs only as an opaque runner argument. -/
theorem callFn_decompose (P : C1.Prog) (fd : C1.FunDef) (g : Sym)
    (fuel : Nat) (initial : C1.Env) (args : List Int)
    (lookup : P.funcs[g.number]? = some fd) :
    C1.callFn P (fuel + 1) g args initial =
      callWith P fd.params fd.memLocals fd.ret g args initial (C1.loop P fuel fd (some fd.body) .stop) := by
  rw [C1.callFn, lookup]
  rfl

end Silmaril.Compile.C.Sem.C1Call
