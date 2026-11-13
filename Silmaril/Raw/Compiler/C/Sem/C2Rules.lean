module

public import Silmaril.Compiler.C.Sem.C2.Defs
/-!
Compositional rules for the C2 interpreter. In particular, a direct call can
reuse separate argument-evaluation and callee-execution proofs without reducing
the prepared program's function or prototype tables.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C2

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- A scalar direct call composes argument evaluation, callee execution and
conversion of the return value. This is a rule for the existing interpreter. -/
theorem evalE_direct_call (P : Prog) (n : Nat) (fd : C1.FunDef)
    (e f name : TypedExpression) (g : Sym) (args : List TypedExpression)
    (env env₁ env₂ : C1.Env) (vs : List Val) (v result : Int)
    (he : e.node = .call f args)
    (hf : f.node = .functionDecay name)
    (hg : name.node = .ident g)
    (hargs : evalArgs P n fd ((P.protos[g.number]?).getD []) args env = .ok (vs, env₁))
    (hcall : callFn P n g vs env₁ = .ok (.scalar v, env₂))
    (hresult : C1.convTo (typeOf e) v = .ok result) :
    evalE P (n + 1) fd e env = .ok (result, env₂) := by
  cases name with
  | mk loc annot attrs node =>
    simp only [Expression.node] at hg
    subst node
    simp only [evalE, he, hf, hargs, hcall, hresult, Bind.bind, Except.bind, pure, Except.pure]

/-- Discarding a scalar expression keeps its effects. -/
theorem evalD_of_scalar (P : Prog) (n : Nat) (fd : C1.FunDef)
    (e : TypedExpression) (env env' : C1.Env) (v : Int)
    (htype : aggOf (typeOf e) = none)
    (heval : evalE P n fd e env = .ok (v, env')) :
    evalD P (n + 1) fd e env = .ok env' := by
  simp only [evalD, htype, heval, Bind.bind, Except.bind, pure, Except.pure]

/-- An expression statement composes with an expression's effect contract. -/
theorem step_expr (P : Prog) (n : Nat) (fd : C1.FunDef)
    (s : TypedStatement) (e : TypedExpression) (k : C0.Kont)
    (env env' : C1.Env) (hs : s.node = .expr e)
    (heval : evalD P n fd e env = .ok env') :
    step P (n + 1) fd (some s) k env = .ok (.running none k, env') := by
  simp only [step, hs, heval, Bind.bind, Except.bind, pure, Except.pure]

/-- Execute one running step and reuse a contract for its continuation. -/
theorem loop_of_running (P : Prog) (n : Nat) (fd : C1.FunDef)
    (focus focus' : Option TypedStatement) (k k' : C0.Kont)
    (env env' returned : C1.Env) (r : Option Val)
    (hstep : step P n fd focus k env = .ok (.running focus' k', env'))
    (hrest : loop P n fd focus' k' env' = .ok (r, returned)) :
    loop P (n + 1) fd focus k env = .ok (r, returned) := by
  rw [loop, hstep]
  exact hrest

/-- A returning step finishes its activation. -/
theorem loop_of_returned (P : Prog) (n : Nat) (fd : C1.FunDef)
    (focus : Option TypedStatement) (k : C0.Kont)
    (env returned : C1.Env) (r : Option Val)
    (hstep : step P n fd focus k env = .ok (.returned r, returned)) :
    loop P (n + 1) fd focus k env = .ok (r, returned) := by
  rw [loop, hstep]

/-- A void function with one scalar parameter and no memory-resident locals
reuses a contract for its body. Caller registers/frame and stack pointer are
restored by the actual calling convention. -/
theorem callFn_single_scalar_void (P : Prog) (n : Nat) (g : Sym)
    (fd : C1.FunDef) (x : Nat) (pt : CType) (arg converted : Int)
    (caller returned : C1.Env)
    (hlookup : P.funcs[g.number]? = some fd)
    (hparams : fd.params = [(x, pt)])
    (hmem : fd.memLocals = []) (hret : fd.ret = .void)
    (harg : C1.convTo pt arg = .ok converted)
    (hbody : loop P n fd (some fd.body) .stop
      ⟨(∅ : Std.HashMap Nat Int).insert x converted, ∅, caller.mem, caller.out⟩ =
      .ok (none, returned)) :
    callFn P (n + 1) g [.scalar arg] caller =
      .ok (.scalar 0, ⟨caller.regs, caller.frame,
        { returned.mem with sp := caller.mem.sp }, returned.out⟩) := by
  cases caller with
  | mk regs frame mem out =>
    simp only [callFn, hlookup, hparams, hmem]
    simp [harg, hret, aggOf]
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [hbody]
    rfl

end Silmaril.Compile.C.Sem.C2
