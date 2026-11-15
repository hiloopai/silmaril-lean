module

public import Silmaril.Wasm.Abstract.DivO.Defs
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Divergence of the open native semantics at the closure (proofs)

At `C = closedCall` the open unfolding `DivStepO` is `Interp.DivStep`: terminating parts are
`EvalO closedCall = Eval` (`evalO_closed_iff`), and an answer of the closure is a terminating
callee body (`closedCall_eq`). Hence `EvalDivO closedCall = EvalDiv` and
`LocalDivO closedCall = LocalDiv`: `DivStepO` generalizes the existing divergence, it is not a
competing one.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.DivO

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (Problem DivStep)

variable {H : Type}

theorem divStepO_closed_iff {X Y : Problem H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} : DivStepO closedCall X Y s f stk es ↔ DivStep X Y s f stk es := by
  constructor
  · intro h
    cases h with
    | args h => exact .args h
    | callee hargs hfi hcode hty h => exact .callee (evalO_closed_iff.mp hargs) hfi hcode hty h
    | callRet hargs hfi hty hcall hvs h =>
      rw [closedCall_eq] at hcall
      obtain ⟨fi', fn, ps', rs', f₂, hf', hcode, hty', hbody⟩ := hcall
      have hf := funcs_of_func? hfi
      rw [hf] at hf'
      cases hf'
      rw [hty] at hty'
      cases hty'
      exact .callRet (evalO_closed_iff.mp hargs) hfi hcode hty hbody hvs h
    | opK hi hargs hflat h => exact .opK hi (evalO_closed_iff.mp hargs) hflat h
    | block har h => exact .block har h
    | blockK har hbody hvs h => exact .blockK har (evalO_closed_iff.mp hbody) hvs h
    | loop har h => exact .loop har h
    | loopK har hbody h => exact .loopK har (evalO_closed_iff.mp hbody) h
    | loopBack har hbody h => exact .loopBack har (evalO_closed_iff.mp hbody) h
    | cond h => exact .cond h
    | arm hc hb har h => exact .arm (evalO_closed_iff.mp hc) hb har h
    | ifK hc hb har harm hvs h =>
      exact .ifK (evalO_closed_iff.mp hc) hb har (evalO_closed_iff.mp harm) hvs h
  · intro h
    cases h with
    | args h => exact .args h
    | callee hargs hfi hcode hty h => exact .callee (evalO_closed_iff.mpr hargs) hfi hcode hty h
    | callRet hargs hfi hcode hty hbody hvs h =>
      refine .callRet (evalO_closed_iff.mpr hargs) hfi hty ?_ hvs h
      rw [closedCall_eq]
      exact ⟨_, _, _, _, _, funcs_of_func? hfi, hcode, hty, hbody⟩
    | opK hi hargs hflat h => exact .opK hi (evalO_closed_iff.mpr hargs) hflat h
    | block har h => exact .block har h
    | blockK har hbody hvs h => exact .blockK har (evalO_closed_iff.mpr hbody) hvs h
    | loop har h => exact .loop har h
    | loopK har hbody h => exact .loopK har (evalO_closed_iff.mpr hbody) h
    | loopBack har hbody h => exact .loopBack har (evalO_closed_iff.mpr hbody) h
    | cond h => exact .cond h
    | arm hc hb har h => exact .arm (evalO_closed_iff.mpr hc) hb har h
    | ifK hc hb har harm hvs h =>
      exact .ifK (evalO_closed_iff.mpr hc) hb har (evalO_closed_iff.mpr harm) hvs h

theorem divOpO_closed : divOpO (closedCall : CallRel H) = Interp.divOp := by
  ext X s f stk es
  exact divStepO_closed_iff

theorem localDivOpO_closed : localDivOpO (closedCall : CallRel H) = Interp.localDivOp := by
  ext X s f stk es
  exact divStepO_closed_iff

/-- **At the closure, open divergence is the recursive semantics' divergence.** -/
theorem evalDivO_closed : EvalDivO (closedCall : CallRel H) = Interp.EvalDiv := by
  unfold EvalDivO Interp.EvalDiv
  rw [divOpO_closed]

/-- **At the closure, local divergence is the recursive semantics' local divergence.** -/
theorem localDivO_closed : LocalDivO (closedCall : CallRel H) = Interp.LocalDiv := by
  unfold LocalDivO Interp.LocalDiv
  rw [localDivOpO_closed]

end Silmaril.Proofs.Wasm.Abstract.DivO
