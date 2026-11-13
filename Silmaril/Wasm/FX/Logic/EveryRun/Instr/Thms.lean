module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.SafeInstr

/-!
# The step-indexed instruction rules of the every-run WasmFX logic: statements

The rules for the stack-switching instructions for the step-indexed every-run predicate
`Safe` (partial correctness, `Silmaril.Wasm.FX.Logic.EveryRun.Defs`), over `StepFX'` without host
calls, at every profile (proofs in `Silmaril.Proofs.Wasm.FX.Logic.EveryRun.SafeInstr`). Each rule
takes one step: the instruction is safe for `n + 1` steps when every successor is safe for `n`.
Like `StepFX'`, the rules for `cont.bind`, `resume` and `resume_throw` quantify over **every**
split of the values below the continuation.

* `Safe.contNew`, **`Safe.contBind`**, **`Safe.resume`**, **`Safe.resumeThrow`**;
* `Safe.suspend`, `Safe.switch`: an unhandled `suspend` / `switch` stops;
* `TSafe.contBind`: the total-correctness rule for `cont.bind`, which an earlier step did not have.

The general rules `safe_last` / `safe_last_seq` (one instruction, then code, without `Inv`),
the Core rules `safe_inert`, `safe_block`, `safe_invoke`, `safe_dropCont` and the `HWP`
versions are in the proof module.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts newCont bindCont)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H} {s : Store H}
  {K : Conts} {f : Frame} {n : Nat}

/-- **`cont.new`** (step-indexed). -/
theorem Safe.contNew {V : List FVal} {a : Nat} {fi : FuncInst H} {ct : TypeIdx}
    (hf : s.funcs[a]? = some fi)
    (h : Safe P fx Q n ⟨s, K ++ [some (newCont a fi)], f, fvals V ++ [.contRef K.length]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.val (.ref (.func a))]) ++ [.fx (.contNew ct)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_contNew hf h

/-- **`cont.bind`** (step-indexed), for every split. -/
theorem Safe.contBind {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      Safe P fx Q n ⟨s, K.set k none ++ [some
          (bindCont C vs)], f, fvals V₁ ++ [.contRef K.length]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.contBind ct ct')]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_contBind hk h

/-- **`cont.bind`** (total correctness), for every split. -/
theorem TSafe.contBind {V : List FVal} {k : Nat} {C : ContFX} {ct ct' : TypeIdx}
    (hk : K[k]? = some (some C))
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      TSafe P fx Q ⟨s, K.set k none ++ [some
          (bindCont C vs)], f, fvals V₁ ++ [.contRef K.length]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.contBind ct ct')]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_contBind hk h

/-- **`resume`** (step-indexed), for every payload split. -/
theorem Safe.resume {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {hos : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      Safe P fx Q n ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_resume hk hr h

/-- **`resume_throw`** (step-indexed). -/
theorem Safe.resumeThrow {V : List FVal} {k : Nat} {C : ContFX} {ct : TypeIdx}
    {x : TagIdx} {hos : List OnClause} {hs' : List HClause} {ta : Nat} {ti : TagInst}
    (hk : K[k]? = some (some C)) (ht : s.tag? f x = some (ta, ti))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ liftV vs →
      Safe P fx Q n ⟨s.addExn ⟨ta, vs⟩, K.set k none, f,
        fvals V₁ ++ [.handler hs' (C.plug (cthrowing s.exns.length))]⟩) :
    Safe P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resumeThrow ct x hos)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_resumeThrow hk ht hr h

/-- **An unhandled `suspend`** stops. -/
theorem Safe.suspend {V : List FVal} {x : TagIdx}
    (h : ∀ E vs, E.plug (suspCode vs x) = fvals V ++ [.fx (.suspend x)] → Unhandled s f E x →
      Q s K f (.susp E vs x)) :
    Safe P fx Q n ⟨s, K, f, fvals V ++ [.fx (.suspend x)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_suspend h

/-- **An unhandled `switch`** stops. -/
theorem Safe.switch {V : List FVal} {k : Nat} {ct : TypeIdx} {x : TagIdx}
    (h : ∀ E vs, E.plug (switchCode vs k ct x) = fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)] →
      Unhandled s f E x → Q s K f (.swtch E vs k ct x)) :
    Safe P fx Q n ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.switch ct x)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_switch h

/-- info: 'Silmaril.Wasm.FX.Logic.EveryRun.Safe.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Safe.resume

/-- info: 'Silmaril.Wasm.FX.Logic.EveryRun.Safe.contBind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Safe.contBind

end Silmaril.Wasm.FX.Logic.EveryRun
