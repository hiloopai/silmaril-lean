module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackIf
public import Silmaril.Wasm.Execution.Core.Soundness

/-!
# The logged backward simulation of the canonical relation: the whole run (proofs)

`back_all`: by strong induction on the length of the run, and on the size of the trees, every
labelled Core run of a typed problem (`BackG`) and of a typed call (`CallG`) in the deterministic
profile `SingleThreaded.profile o` is read back as the logged canonical relation, its calls
resolved against `wasmEvFunXP`'s closure to exactly the run's log.

`evRun_wasmEvFunXP_vals`, `evRun_wasmEvFunXP_throw`, `evRun_wasmEvFunXP_trap`: a Core run of a
typed invocation, with its host events `cs`, to values, an uncaught exception or a trap is the
corresponding finished behaviour of `wasmEvFunXP` with exactly that log. The invocation is a call
in its `call_ref` form (`CallG`); the other two ends are excluded by determinism (`evRun_det_end`
against `close_trap_evRun`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

theorem size_args' {i : Instr} {args es : List Binaryen.BExpr} :
    sizeOf args < sizeOf (Binaryen.BExpr.op i args :: es) := by
  simp only [List.cons.sizeOf_spec, Binaryen.BExpr.op.sizeOf_spec]; omega

/-- **The logged backward simulation**, for runs of every length. -/
theorem back_all (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (n : Nat) : (∀ es, BackG tags o host n es) ∧ CallG tags o host n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have hC : CallG tags o host n :=
    callG_step hT hH hE (fun m hm => (ih m hm).1) (fun m hm => (ih m hm).2)
  have hCle : ∀ m ≤ n, CallG tags o host m := fun m hm => by
    rcases Nat.lt_or_eq_of_le hm with h | rfl
    · exact (ih m h).2
    · exact hC
  refine ⟨?_, hC⟩
  suffices key : ∀ k, ∀ es : List Binaryen.BExpr, sizeOf es < k → BackG tags o host n es from
    fun es => key _ es (Nat.lt_succ_self _)
  intro k
  induction k with
  | zero => intro es h; omega
  | succ k ihk =>
    intro es hes
    have ihle : ∀ es', sizeOf es' < sizeOf es → ∀ m ≤ n, BackG tags o host m es' :=
      fun es' hlt m hm => by
        rcases Nat.lt_or_eq_of_le hm with h | rfl
        · exact (ih m h).1 es'
        · exact ihk es' (by omega)
    match es with
    | [] => exact case_nil hH hE
    | .op i args :: es =>
      exact case_op hT hH hE (ihle _ size_args') (ihle _ size_tail') hCle
    | .block bt body :: es =>
      exact case_block hT hH hE (ihle _ size_body_block) (ihle _ size_tail')
    | .loop bt body :: es =>
      exact case_loop hT hH hE (ihle _ size_body_loop) (ihle _ size_tail')
        (fun m hm => (ih m hm).1 _)
    | .if_ bt c t el :: es =>
      exact case_if hT hH hE (ihle _ size_cond') (fun b => ihle _ (size_arm_block b))
    | .tryTable bt cs body :: es =>
      exact case_try hT hH hE (ihle _ size_body_try) (ihle _ size_tail')

section Invoke

variable {s : Store H} {a : Nat} {vs : List Val} {cs : List (Call (wasmHostSig H))}

/-- **A Core run of a typed invocation to an end** is a returning behaviour of the closure, the
run going on from its answer, or a trapping one with the whole log. -/
theorem invoke_out (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s)
    (hok : InvokeOk s a vs) {c : Config H} (hrun : EvRun (profile o) host (invoke s a vs) cs c)
    {oc : Outcome} (hfin : oc.Ends c.code) :
    (∃ (q : List (Call (wasmHostSig H))) (b : List Val ⊕ Nat) (s₃ : Store H) (m : Nat)
        (cs₂ : List (Call (wasmHostSig H))), (q, .ret b s₃) ∈ wasmEvFunXP s (a, vs) ∧
        cs = q ++ cs₂ ∧ EvRunN (profile o) host m ⟨s₃, {}, ansCode b⟩ cs₂ c) ∨
      (cs, .trap) ∈ wasmEvFunXP s (a, vs) := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  obtain ⟨fi, ps', rs', hfi, he, -⟩ := id hok
  have hty := funcType_of_expand' he
  have hlen : vs.length = ps'.toList.length := invokeOk_length hok hfi hty
  have hcode : (invoke s a vs).code = Interp.callCode [] vs a (.callRefType fi.type) [] := by
    simp [invoke, hfi, Interp.callCode, vals]
  obtain ⟨fi₀, ps₀, rs₀, -, -, hcok⟩ := invoke_ok hs hok
  have hct : Sim.ContextTyped ⟨s, {}, Interp.callCode [] vs a (.callRefType fi.type) []⟩ := by
    have := Sim.ContextTyped.of_configOk hcok
    rw [invoke_eq hfi] at this
    simpa [Interp.callCode, vals] using this
  have hn' : EvRunN (profile o) host n ⟨s, {}, Interp.callCode [] vs a (.callRefType fi.type) []⟩
      cs c := by
    rw [invoke_eq hfi] at hn
    simpa [Interp.callCode, vals] using hn
  have hend : ∀ c', ¬ Step (profile o) Det.noHost c c' := by
    obtain ⟨cst, cfr, ccd⟩ := c
    exact ends_stuck hfin cst cfr
  have hnd : decompose? c.store c.code = none := ends_decompose hfin c.store
  rcases (back_all hT hH hE n).2 s {} [] vs a (.callRefType fi.type) [] c cs trivial
      ⟨hS, hts, fi, ps'.toList, rs'.toList, hfi, hty, hlen⟩ hct hn' hend hnd with
    ⟨q, b, s₃, m, cs₂, hz, rfl, -, hk⟩ | hz
  · exact .inl ⟨q, b, s₃, m, cs₂, hz, rfl, by simpa [vals] using hk⟩
  · exact .inr hz

/-- **A trapping closed behaviour with the run's log forces the run's end to be a trap**
(determinism, against `close_trap_evRun`). -/
theorem trap_end (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    {c : Config H} (hrun : EvRun (profile o) host (invoke s a vs) cs c) {oc : Outcome}
    (hfin : oc.Ends c.code) (hz : (cs, .trap) ∈ wasmEvFunXP s (a, vs)) : c.code = [.trap] := by
  obtain ⟨fi, ps', rs', hfi, he, -⟩ := id hok
  have hty := funcType_of_expand' he
  have hcons : Cons host cs := evRun_consistent hrun
  obtain ⟨s', h'⟩ := close_trap_evRun (P := profile o) hH hE hz hcons hts hS hfi hty
    (invokeOk_length hok hfi hty) {} (.callRefType fi.type) trivial
  rw [← invoke_eq hfi] at h'
  obtain ⟨n, hn⟩ := evRunN_of_evRun hrun
  have hend : ∀ c', ¬ Step (profile o) Det.noHost c c' := by
    obtain ⟨cst, cfr, ccd⟩ := c
    exact ends_stuck hfin cst cfr
  rw [evRun_det_end h' (ends_stuck (o := .trap) rfl s' {}) hn hend]

/-- The code of an answer is a final form. -/
theorem ansCode_ends (b : List Val ⊕ Nat) : ∃ oc : Outcome, oc.Ends (ansCode b) := by
  rcases b with ws | t
  · exact ⟨.normal ws, rfl⟩
  · exact ⟨.throw t, rfl⟩

theorem throwing_ne_trap {t : Nat} : throwing t ≠ [.trap] := by simp [throwing]

/-- **Values, with exactly the run's log** (deterministic profile). -/
theorem evRun_wasmEvFunXP_vals (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) {s₂ : Store H} {f₂ : Frame} {ws : List Val}
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, vals ws⟩) :
    (cs, .ret (.inl ws) s₂) ∈ wasmEvFunXP s (a, vs) := by
  rcases invoke_out hT hH hE hs hS hts hok hrun (oc := .normal ws) rfl with
    ⟨q, b, s₃, m, cs₂, hz, rfl, hk⟩ | hz
  · obtain ⟨oc, hoc⟩ := ansCode_ends b
    obtain ⟨hc, rfl⟩ := evRunN_of_stuck (ends_stuck hoc s₃ {}) hk
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, -, hw⟩ := hc
    rcases b with ws' | t
    · obtain rfl : ws = ws' := Sim.vals_injective hw
      simpa using hz
    · exact (vals_ne_throwing hw).elim
  · exact (vals_ne_trap' (trap_end hH hE hS hts hok hrun (oc := .normal ws) rfl hz)).elim

/-- **An uncaught exception, with exactly the run's log** (deterministic profile). -/
theorem evRun_wasmEvFunXP_throw (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) {s₂ : Store H} {f₂ : Frame} {t : Nat}
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, throwing t⟩) :
    (cs, .ret (.inr t) s₂) ∈ wasmEvFunXP s (a, vs) := by
  rcases invoke_out hT hH hE hs hS hts hok hrun (oc := .throw t) rfl with
    ⟨q, b, s₃, m, cs₂, hz, rfl, hk⟩ | hz
  · obtain ⟨oc, hoc⟩ := ansCode_ends b
    obtain ⟨hc, rfl⟩ := evRunN_of_stuck (ends_stuck hoc s₃ {}) hk
    simp only [Config.mk.injEq] at hc
    obtain ⟨rfl, -, hw⟩ := hc
    rcases b with ws' | t'
    · exact (vals_ne_throwing hw.symm).elim
    · simp only [ansCode, throwing, List.cons.injEq, Admin.ref.injEq, Ref.exn.injEq,
        and_true] at hw
      subst hw
      simpa using hz
  · exact (throwing_ne_trap (trap_end hH hE hS hts hok hrun (oc := .throw t) rfl hz)).elim

/-- **A trap, with exactly the run's log** (deterministic profile). -/
theorem evRun_wasmEvFunXP_trap (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) {s₂ : Store H} {f₂ : Frame}
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, f₂, [.trap]⟩) :
    (cs, .trap) ∈ wasmEvFunXP s (a, vs) := by
  rcases invoke_out hT hH hE hs hS hts hok hrun (oc := .trap) rfl with
    ⟨q, b, s₃, m, cs₂, hz, rfl, hk⟩ | hz
  · obtain ⟨oc, hoc⟩ := ansCode_ends b
    obtain ⟨hc, rfl⟩ := evRunN_of_stuck (ends_stuck hoc s₃ {}) hk
    simp only [Config.mk.injEq] at hc
    obtain ⟨-, -, hw⟩ := hc
    rcases b with ws' | t'
    · exact (vals_ne_trap' hw.symm).elim
    · exact (throwing_ne_trap hw.symm).elim
  · exact hz

end Invoke

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
