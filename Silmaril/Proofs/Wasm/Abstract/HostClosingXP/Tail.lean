module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Fwd

/-!
# Pending tail calls of the logged relation and their answers (proofs)

* `evalLXPh_tail_wf`: a pending tail call `tail a args n` of an `EvalLXPh` run names a function
  of the result's store, `n` its result arity (unconditionally, from the `tail` rule);
* `tailFlow_ansFlow`, `retVals_or_abrupt`: a closed answer read as a callee flow ends the frame
  as the oracle's flow does, and is one `CallXP.FrameP.tail` accepts;
* `tailAns_self`: a frame left by a pending tail call at the function's own arity ends as its
  callee.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes tailFlow)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP FrameP bodyCallXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP hostCallXP_fixpoint)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Pending tail calls of the logged relation -/

/-- **A pending tail call names a function of its result's store, at its result arity.** -/
theorem evalLXPh_tail_wf {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r) :
    ∀ a args n, r.2.2 = .tail a args n → ∃ (fi : FuncInst H) (ps rs : List Validation.CValType),
      r.1.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      n = rs.length := by
  induction h with
  | tail _ hres hfi hty hy _ =>
    intro a args n h
    cases h
    exact ⟨_, _, _, hfi, hty, rfl⟩
  | _ => first | (intro a args n h; cases h; done) | assumption

/-! ## Answers and flows -/

theorem tailFlow_ansFlow {k : Nat} {bfl fl : Binaryen.Flow} {s : Store H} {b : List Val ⊕ Nat}
    (hx : exitFlow k bfl = some fl) (hend : endOfFlow fl s = .ret b s) :
    tailFlow k (ansFlow b) = tailFlow k bfl := by
  rcases bfl with w | ⟨_ | j, w⟩ | w | _ | t <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, reduceCtorEq] at hend <;>
    obtain ⟨rfl, -⟩ := hend <;> simp [ansFlow, tailFlow]

theorem retVals_or_abrupt {k : Nat} {bfl fl : Binaryen.Flow} (hx : exitFlow k bfl = some fl) :
    (∃ vs, bfl.retVals = some vs) ∨ bfl.Abrupt := by
  rcases bfl with w | ⟨_ | j, w⟩ | w | _ | t <;>
    simp_all [exitFlow, Binaryen.Flow.retVals, Binaryen.Flow.Abrupt]

/-- A frame left by a pending tail call, at the function's own arity, ends as its callee. -/
theorem tailAns_self {m : Nat} {b b' : List Val ⊕ Nat} {s₂ s' : Store H}
    (h : tailAns m m b s₂ = .ret b' s') (hb : ∀ ws, b = .inl ws → ws.length ≤ m) :
    b' = b ∧ s' = s₂ := by
  rcases b with ws | t <;>
    simp only [tailAns, ansFlow, tailFlow, exitFlow, endOfFlow, End.ret.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h
    have hl := hb ws rfl
    refine ⟨?_, rfl⟩
    rw [List.take_take, Nat.min_self, List.take_of_length_le (by simpa using hl)]
    simp
  · exact ⟨h.1.symm, h.2.symm⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP

