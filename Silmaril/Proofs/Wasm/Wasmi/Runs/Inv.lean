module

public import Silmaril.Proofs.Wasm.Wasmi.Runs.Generic
public import Silmaril.Wasm.Wasmi.Observed.Thms
public import Silmaril.Wasm.Logic.Hoare.Thms

/-!
# Every Core 3.0 step of a rounding-function call (proofs)

For a function `local.get 0; t.op` (`Silmaril.Proofs.Wasm.Wasmi.Observed.RoundFn`), the Core 3.0
steps of the call `a x` from each configuration of its run, with all successors:

* `core_call`: the call enters `FRAME (LABEL (local.get 0; t.op))`, and nothing else;
* `core_get`: `local.get 0` reads `x`, and nothing else;
* `core_op`: the operator steps to `t.const z`, for exactly the `z` the profile allows;
* `core_label`, `core_frame`: the label and then the frame are left, and nothing else.

Generic inversions: `frame_label_inv` (a step of a frame around a label is a step of the
label's contents), `label_inert_inv` (a step of a label whose body's first non-value is an
ordinary instruction is a step of the body), and the bubbling steps of a label or a frame
around values (`label_vals_inv`, `frame_vals_inv`). They use silmaril-lean's inversions
`Sim.Closure.Step.frame_redex_aux`, `Sim.Closure.Step.label_inv` and
`SingleThreaded.inert_head_inv`, and the head inversions of `Silmaril.Wasm.Logic.Hoare`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Runs

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Wasmi.Observed
open Silmaril.Proofs.Wasm.Wasmi.Observed (RoundFn head_floatUnOp)
open Silmaril.Wasm.Logic.Hoare (call_step_inv callFrame head_localGet not_step_vals split_one)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- `RETURN_CALL_REF` forms are not values. -/
theorem val?_of_rcr {c : Admin} (h : c.IsReturnCallRef) : c.val? = none := by
  unfold Admin.IsReturnCallRef at h
  split at h <;> first | rfl | exact h.elim

/-! ## Frames and labels -/

/-- **A step of a frame around a label** is a step of the label, under the callee frame. -/
theorem frame_label_inv {s s' : Store H} {f f' F : Frame} {n m : Nat} {cont : List Instr}
    {b es' : List Admin}
    (h : Execution.Core.Step P host ⟨s, f, [.frame n F [.label m cont b]]⟩ ⟨s', f', es'⟩) :
    ∃ F' b', Execution.Core.Step P host ⟨s, F, [.label m cont b]⟩ ⟨s', F', b'⟩ ∧ f' = f ∧
      es' = [.frame n F' b'] := by
  obtain ⟨is₀, hc, hr⟩ := Sim.Closure.Step.frame_redex_aux h [] n F [.label m cont b] rfl
  generalize hb : [Admin.label m cont b] = b₀ at hr
  have hlab : (Admin.label m cont b).val? = none := rfl
  cases hr with
  | ctxt hs => exact ⟨_, _, hs, rfl, by simpa using hc⟩
  | values _ =>
    have hm : Admin.label m cont b ∈ vals _ := hb ▸ List.mem_singleton_self _
    exact absurd hm (not_mem_vals hlab _)
  | ret _ =>
    have hm : Admin.plain .return_ ∈ [Admin.label m cont b] := hb ▸ by simp
    exact absurd hm (by simp)
  | @callNull _ _ _ _ c _ hrc =>
    have hm : c = Admin.label m cont b := List.mem_singleton.mp (hb ▸ by simp)
    exact (hm ▸ hrc : Admin.IsReturnCallRef (.label m cont b)).elim
  | @callAddr _ _ _ _ _ _ c _ _ _ _ hrc _ _ _ =>
    have hm : c = Admin.label m cont b := List.mem_singleton.mp (hb ▸ by simp)
    exact (hm ▸ hrc : Admin.IsReturnCallRef (.label m cont b)).elim
  | throw =>
    have hm : Admin.plain .throwRef ∈ [Admin.label m cont b] := hb ▸ by simp
    exact absurd hm (by simp)
  | trap =>
    have hm : Admin.trap ∈ [Admin.label m cont b] := hb ▸ by simp
    exact absurd hm (by simp)

/-- The first non-value of `vals W ++ plain i :: rest` is `plain i`. -/
theorem first_plain {W ws : List Val} {i : Instr} {e : Admin} {rest t : List Admin}
    (hi : (Admin.plain i).val? = none) (he : e.val? = none)
    (h : vals W ++ .plain i :: rest = vals ws ++ e :: t) : e = .plain i :=
  (SingleThreaded.Det.vals_append_cons_inj h hi he).2.1.symm

/-- A plain `RETURN_CALL_REF`. -/
theorem rcr_plain {i : Instr} (h : (Admin.plain i).IsReturnCallRef) : ∃ x, i = .returnCallRef x := by
  cases i <;> first | exact ⟨_, rfl⟩ | exact h.elim

/-- **A step of a label whose body's first non-value is an ordinary instruction** is a step of
the body. -/
theorem label_inert_inv {s s' : Store H} {f f' : Frame} {m : Nat} {cont : List Instr}
    {W : List Val} {i : Instr} {rest es' : List Admin}
    (hi : (Admin.plain i).val? = none) (hbr : ∀ l, i ≠ .br l) (hr : i ≠ .return_)
    (hrc : ∀ x, i ≠ .returnCallRef x) (ht : i ≠ .throwRef)
    (h : Execution.Core.Step P host ⟨s, f, [.label m cont (vals W ++ .plain i :: rest)]⟩
      ⟨s', f', es'⟩) :
    ∃ b', Execution.Core.Step P host ⟨s, f, vals W ++ .plain i :: rest⟩ ⟨s', f', b'⟩ ∧
      es' = [.label m cont b'] := by
  obtain ⟨is', hl, rfl⟩ := Sim.Closure.Step.label_inv (us := []) h
  generalize hb : vals W ++ Admin.plain i :: rest = b at hl
  cases hl with
  | ctxt hs => exact ⟨_, hb ▸ hs, rfl⟩
  | values vs => exact absurd (hb ▸ (by simp) : Admin.plain i ∈ vals vs) (not_mem_vals hi vs)
  | @brZero vs' vs l rest' _ _ =>
    have he : Admin.plain (.br l) = .plain i :=
      first_plain (ws := vs' ++ vs) (t := rest') hi rfl (hb.trans (by simp))
    exact absurd (Admin.plain.inj he).symm (hbr l)
  | @brSucc vs l rest' _ =>
    have he : Admin.plain (.br l) = .plain i :=
      first_plain (ws := vs) (t := rest') hi rfl (hb.trans (by simp))
    exact absurd (Admin.plain.inj he).symm (hbr l)
  | @returnCallRef vs c rest' hc =>
    have he : c = .plain i :=
      first_plain (ws := vs) (t := rest') hi (val?_of_rcr hc) (hb.trans (by simp))
    have hx : ∃ x, i = .returnCallRef x := rcr_plain (he ▸ hc)
    exact absurd hx.choose_spec (hrc _)
  | @return_ vs rest' =>
    have he : Admin.plain .return_ = .plain i :=
      first_plain (ws := vs) (t := rest') hi rfl (hb.trans (by simp))
    exact absurd (Admin.plain.inj he).symm hr
  | throwRef a =>
    have he : Admin.plain .throwRef = .plain i := first_plain (W := W) (ws := [.ref (.exn a)])
      (t := []) hi rfl hb
    exact absurd (Admin.plain.inj he).symm ht
  | trap =>
    have he : Admin.trap = .plain i := first_plain (ws := []) (t := []) hi rfl hb
    exact absurd he (by simp)

/-- **A label around values** steps only by leaving the label. -/
theorem label_vals_inv {s s' : Store H} {f f' : Frame} {m : Nat} {cont : List Instr}
    {vs : List Val} {es' : List Admin}
    (h : Execution.Core.Step P host ⟨s, f, [.label m cont (vals vs)]⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs := by
  obtain ⟨is', hl, rfl⟩ := Sim.Closure.Step.label_inv (us := []) h
  generalize hb : vals vs = b at hl
  cases hl with
  | ctxt hs => exact (not_step_vals (hb ▸ hs)).elim
  | values ws => exact ⟨rfl, rfl, by simp⟩
  | @brZero _ _ l _ _ _ =>
    exact absurd (hb ▸ (by simp) : Admin.plain (.br l) ∈ vals vs) (not_mem_vals rfl vs)
  | @brSucc _ l _ _ =>
    exact absurd (hb ▸ (by simp) : Admin.plain (.br l) ∈ vals vs) (not_mem_vals rfl vs)
  | @returnCallRef _ c _ hc =>
    exact absurd (hb ▸ (by simp) : c ∈ vals vs) (not_mem_vals (val?_of_rcr hc) vs)
  | return_ => exact absurd (hb ▸ (by simp) : Admin.plain .return_ ∈ vals vs) (not_mem_vals rfl vs)
  | throwRef a =>
    exact absurd (hb ▸ (by simp) : Admin.plain .throwRef ∈ vals vs) (not_mem_vals rfl vs)
  | trap => exact absurd (hb ▸ (by simp) : Admin.trap ∈ vals vs) (not_mem_vals rfl vs)

/-- **A frame around values** steps only by leaving the frame. -/
theorem frame_vals_inv {s s' : Store H} {f f' F : Frame} {n : Nat} {vs : List Val}
    {es' : List Admin}
    (h : Execution.Core.Step P host ⟨s, f, [.frame n F (vals vs)]⟩ ⟨s', f', es'⟩) :
    s' = s ∧ f' = f ∧ es' = vals vs := by
  obtain ⟨is₀, hc, hr⟩ := Sim.Closure.Step.frame_redex_aux h [] n F (vals vs) rfl
  generalize hb : vals vs = b at hr
  cases hr with
  | ctxt hs => exact (not_step_vals (hb ▸ hs)).elim
  | @values _ _ _ ws _ =>
    have hv : vs = ws := vals_inj hb
    exact ⟨rfl, rfl, by simpa [hv] using hc⟩
  | ret _ => exact absurd (hb ▸ (by simp) : Admin.plain .return_ ∈ vals vs) (not_mem_vals rfl vs)
  | @callNull _ _ _ _ c _ hrc =>
    exact absurd (hb ▸ (by simp) : c ∈ vals vs) (not_mem_vals (val?_of_rcr hrc) vs)
  | @callAddr _ _ _ _ _ _ c _ _ _ _ hrc _ _ _ =>
    exact absurd (hb ▸ (by simp) : c ∈ vals vs) (not_mem_vals (val?_of_rcr hrc) vs)
  | throw => exact absurd (hb ▸ (by simp) : Admin.plain .throwRef ∈ vals vs) (not_mem_vals rfl vs)
  | trap => exact absurd (hb ▸ (by simp) : Admin.trap ∈ vals vs) (not_mem_vals rfl vs)

/-! ## The run of a rounding function -/

namespace RoundFn

variable {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp} (R : RoundFn s a t op)

/-- The configuration after leaving the label. -/
def frameCfg (R : RoundFn s a t op) (x y : FloatValue t) : Config H :=
  ⟨s, {}, [.frame R.rs.length (R.frame x) [.plain (.floatConst t y)]]⟩

include R in
/-- **The call step is the only step of `a x`.** -/
theorem core_call (x : FloatValue t) {c' : Config H}
    (h : Execution.Core.Step P host (invoke s a [fval t x]) c') :
    c' = R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)] := by
  have e : invoke s a [fval t x] =
      ⟨s, {}, vals [] ++ vals [fval t x] ++ [.ref (.func a), .callRefType R.fi.type]⟩ := by
    simp [invoke, R.hf]
  rw [e] at h
  rw [call_step_inv (c := .callRefType R.fi.type) trivial R.hf R.hcode R.he (by simp [R.hps]) h]
  simp [callFrame, RoundFn.cfg, RoundFn.frame, R.hbody, expression]

/-- **`local.get 0` is the only step**, and it reads `x`. -/
theorem core_get (x : FloatValue t) {c' : Config H}
    (h : Execution.Core.Step P host (R.cfg x [.plain (.localGet ⟨0⟩), .plain (.floatUnOp t op)])
      c') :
    c' = R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)] := by
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨F', b', hs, rfl, rfl⟩ := frame_label_inv h
  obtain ⟨b'', hs', rfl⟩ := label_inert_inv (W := []) (by simp [Admin.val?]) (by simp)
    (by simp) (by simp) (by simp) hs
  obtain ⟨vs, args, c₀, hW, hh, he⟩ := SingleThreaded.inert_head_inv (W := [])
    (by simp [Admin.val?]) (by simp) rfl hs'
  obtain ⟨rfl, v, hv, rfl⟩ := head_localGet hh
  obtain rfl : vs = [] := by simpa using hW
  rw [R.local0 x] at hv
  obtain rfl : fval t x = v := by injection hv with hv; injection hv
  simp only [Config.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rfl

/-- **The operator steps to `t.const z`, for exactly the allowed `z`.** -/
theorem core_op (x : FloatValue t) {c' : Config H}
    (h : Execution.Core.Step P host (R.cfg x [.plain (.floatConst t x), .plain (.floatUnOp t op)])
      c') :
    ∃ z, floatUnOpP P t op x z ∧ c' = R.cfg x [.plain (.floatConst t z)] := by
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨F', b', hs, rfl, rfl⟩ := frame_label_inv h
  obtain ⟨b'', hs', rfl⟩ := label_inert_inv (W := [fval t x]) (rest := [])
    (by simp [Admin.val?]) (by simp) (by simp) (by simp) (by simp) hs
  obtain ⟨vs, args, c₀, hW, hh, he⟩ := SingleThreaded.inert_head_inv (W := [fval t x])
    (by simp [Admin.val?]) (by simp) rfl hs'
  obtain ⟨x', z, rfl, hz, rfl⟩ := head_floatUnOp hh
  obtain ⟨rfl, hx⟩ := split_one (us := []) hW
  have hx' : x' = x := by
    injection hx with hx
    injection hx
  subst hx'
  simp only [Config.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨z, hz, rfl⟩

/-- **Leaving the label is the only step.** -/
theorem core_label (x y : FloatValue t) {c' : Config H}
    (h : Execution.Core.Step P host (R.cfg x [.plain (.floatConst t y)]) c') :
    c' = frameCfg R x y := by
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨F', b', hs, rfl, rfl⟩ := frame_label_inv h
  obtain ⟨rfl, rfl, rfl⟩ := label_vals_inv (vs := [fval t y]) hs
  rfl

/-- **Leaving the frame is the only step.** -/
theorem core_frame (x y : FloatValue t) {c' : Config H}
    (h : Execution.Core.Step P host (frameCfg R x y) c') :
    c' = ⟨s, {}, vals [fval t y]⟩ := by
  obtain ⟨s', f', es'⟩ := c'
  obtain ⟨rfl, rfl, rfl⟩ := frame_vals_inv (vs := [fval t y]) h
  rfl

end RoundFn

end Silmaril.Proofs.Wasm.Wasmi.Runs
