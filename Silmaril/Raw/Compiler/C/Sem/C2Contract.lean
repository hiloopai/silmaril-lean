module

public import Silmaril.Compiler.C.Sem.C2Rules.Defs
public import Silmaril.Compiler.C.Sem.C2Mono.Defs
/-!
# Function contracts for the existing C2 interpreter

A contract describes calls by their arguments, initial environment, return value
and final environment. Its logical index can carry payloads, abstract states or
ownership witnesses. Implementation requires successful finite execution on every
permitted input; it does not identify a particular function body. Interpreter fuel
is hidden from clients and successful execution is stable at every larger bound.

These are contracts for C2 calls, not a new operational semantics, a general frame
rule, or a correctness theorem for a native linker or ABI. Memory ownership and
preservation of unrelated state must be stated in each contract's predicates.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C2

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- A function specification with ghost inputs independent of its C arguments. -/
structure FunContract (ι : Type) where
  pre : ι → List Val → C1.Env → Prop
  post : ι → List Val → C1.Env → Val → C1.Env → Prop

namespace FunContract

variable {ι : Type}

/-- Every permitted call terminates successfully and satisfies the contract.
An error return code is an ordinary successful scalar return; interpreter errors
and exhausted fuel do not implement a contract. -/
def Implements (spec : FunContract ι) (P : Prog) (g : Sym) : Prop :=
  ∀ i args before, spec.pre i args before →
    ∃ fuel value after, callFn P fuel g args before = .ok (value, after) ∧
      spec.post i args before value after

/-- A contract supplies one result which remains valid at every sufficiently
large fuel bound, even when the implementation uses a different amount of fuel. -/
theorem Implements.call {spec : FunContract ι} {P : Prog} {g : Sym}
    (himpl : spec.Implements P g) (i : ι) (args : List Val) (before : C1.Env)
    (hpre : spec.pre i args before) :
    ∃ threshold value after, spec.post i args before value after ∧
      ∀ fuel, threshold ≤ fuel → callFn P fuel g args before = .ok (value, after) := by
  obtain ⟨threshold, value, after, hcall, hpost⟩ := himpl i args before hpre
  refine ⟨threshold, value, after, hpost, ?_⟩
  intro fuel hle
  have hmono := callFn_mono P threshold (fuel - threshold) g args before
  have hstable := hmono (by simp [hcall])
  simpa only [Nat.add_sub_of_le hle, hcall] using hstable

/-- The postcondition holds for any observed successful execution, not only for
the fuel witness supplied by the implementation proof. -/
theorem Implements.post_of_call {spec : FunContract ι} {P : Prog} {g : Sym}
    (himpl : spec.Implements P g) (i : ι) (args : List Val) (before : C1.Env)
    (hpre : spec.pre i args before) (fuel : Nat) (value : Val) (after : C1.Env)
    (hcall : callFn P fuel g args before = .ok (value, after)) :
    spec.post i args before value after := by
  obtain ⟨witnessFuel, expected, final, hwitness, hpost⟩ := himpl i args before hpre
  have hleft : callFn P (fuel + witnessFuel) g args before = .ok (value, after) := by
    simpa only [hcall] using
      callFn_mono P fuel witnessFuel g args before (by simp [hcall])
  have hright : callFn P (fuel + witnessFuel) g args before = .ok (expected, final) := by
    simpa only [Nat.add_comm witnessFuel fuel, hwitness] using
      callFn_mono P witnessFuel fuel g args before (by simp [hwitness])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hleft.symm.trans hright))
  exact hpost

/-- Implementing a stronger specification also implements a weaker one.
The logical indices can change; their relation is chosen independently of code. -/
theorem Implements.consequence {κ : Type} {strong : FunContract ι}
    {weak : FunContract κ} {P : Prog} {g : Sym}
    (himpl : strong.Implements P g) (index : κ → ι)
    (hpre : ∀ i args before, weak.pre i args before → strong.pre (index i) args before)
    (hpost : ∀ i args before value after, weak.pre i args before →
      strong.post (index i) args before value after → weak.post i args before value after) :
    weak.Implements P g := by
  intro i args before hp
  obtain ⟨fuel, value, after, hcall, hq⟩ := himpl (index i) args before (hpre i args before hp)
  exact ⟨fuel, value, after, hcall, hpost i args before value after hp hq⟩

/-- A scalar direct call uses only a callee's contract. Argument evaluation and
callee execution may have unrelated fuel bounds. The client supplies the return
conversion and the property it needs from the callee's postcondition. -/
theorem evalE_direct_call {spec : FunContract ι} {P : Prog} {g : Sym}
    (himpl : spec.Implements P g) (i : ι)
    (fd : C1.FunDef) (e f name : TypedExpression) (args : List TypedExpression)
    (before passed : C1.Env) (vs : List Val) (argFuel : Nat)
    (R : Int → C1.Env → Prop)
    (he : e.node = .call f args) (hf : f.node = .functionDecay name)
    (hg : name.node = .ident g)
    (hargs : evalArgs P argFuel fd ((P.protos[g.number]?).getD []) args before =
      .ok (vs, passed))
    (hpre : spec.pre i vs passed)
    (hpost : ∀ value after, spec.post i vs passed value after →
      ∃ scalar result, value = .scalar scalar ∧
        C1.convTo (typeOf e) scalar = .ok result ∧ R result after) :
    ∃ fuel result after, evalE P fuel fd e before = .ok (result, after) ∧ R result after := by
  obtain ⟨callFuel, value, after, hcall, hq⟩ := himpl i vs passed hpre
  obtain ⟨scalar, result, rfl, hconvert, hr⟩ := hpost value after hq
  have hargs' : evalArgs P (argFuel + callFuel) fd ((P.protos[g.number]?).getD [])
      args before = .ok (vs, passed) := by
    have h := evalArgs_mono P argFuel callFuel fd ((P.protos[g.number]?).getD []) args before
    simpa only [hargs] using h (by simp [hargs])
  have hcall' : callFn P (argFuel + callFuel) g vs passed = .ok (.scalar scalar, after) := by
    have h := callFn_mono P callFuel argFuel g vs passed
    simpa only [Nat.add_comm callFuel argFuel, hcall] using h (by simp [hcall])
  exact ⟨argFuel + callFuel + 1, result, after,
    C2.evalE_direct_call P (argFuel + callFuel) fd e f name g args before passed after
      vs scalar result he hf hg hargs' hcall' hconvert, hr⟩

end FunContract

end Silmaril.Compile.C.Sem.C2
