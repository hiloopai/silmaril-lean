module

public import Silmaril.Wasm.Abstract.HostObs.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Thms

/-!
# The pending halves of the host-observation square, forward (proofs)

A pending host call of the logged closed semantics after a consistent host log
(`wasmEvPend`, `wasmEvPend_iff`) is reached by Core: if the host has no outcome for it,
Core is blocked there (`wasmEvPend_core_blocked`), and if the host may diverge on it,
Core diverges (`wasmEvPend_core_diverges`). A host function invoked directly is the
invocation itself; otherwise the call is reached through callee bodies
(`invoke_pendO_blocked`, `invoke_pendO_diverges`). Every profile.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostObs

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

/-- A directly invoked function's call configuration. -/
theorem invoke_call_facts {s : Store H} {a : Nat} {vs : List Val} {fi : FuncInst H}
    (hok : InvokeOk s a vs) (hf : s.funcs[a]? = some fi) :
    ∃ ps rs : Validation.Ty (.list .val), Validation.Expand fi.type (.func ps rs) ∧
      vs.length = ps.length ∧
      invoke s a vs = ⟨s, {}, vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []⟩ := by
  obtain ⟨fi', ps, rs, hf', he, hvt⟩ := hok
  rw [hf] at hf'
  cases hf'
  refine ⟨ps, rs, he, ?_, by simp [invoke, hf]⟩
  simpa [Validation.Ty.length] using hvt.length_eq

/-- **Forward, blocked**: a logged pending host call with no host outcome is a Core run of
the invocation to a stuck, blocked end. -/
theorem wasmEvPend_core_blocked {P : Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {hh : H} {s' : Store H} {us : List Val}
    (h : (cs, (hh, s', us)) ∈ wasmEvPend s (a, vs)) (hc : (coreHostRel host).Consistent cs)
    (hno : ∀ o, ¬ host hh s' us o) :
    ∃ c : Config H, Steps P host (invoke s a vs) c ∧ Pending host c.store c.code ∧
      ∀ c', ¬ Step P host c c' := by
  obtain ⟨y, fi, hh', hy, hf, hcode, hm⟩ := wasmEvPend_iff.mp ⟨cs, h, hc⟩
  simp only [Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  rcases hy with rfl | hy
  · obtain ⟨ps, rs, he, hn, hinv⟩ := invoke_call_facts hok hf
    have hp : Pending host s (vals [] ++ vals vs ++ .ref (.func a) :: .callRefType fi.type :: []) :=
      Pending.call hf hcode he hn hno
    exact ⟨invoke s a vs, .refl, hinv ▸ hp, hinv ▸ pending_stuck hp {}⟩
  · exact invoke_pendO_blocked hH hS hok hy hf hcode hno

/-- **Forward, host divergence**: a logged pending host call the host may diverge on makes
Core diverge. -/
theorem wasmEvPend_core_diverges {P : Numerics.Profile} (hH : Interp.NativeHostSlice host)
    {s : Store H} {a : Nat} {vs : List Val} (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} {hh : H} {s' : Store H} {us : List Val}
    (h : (cs, (hh, s', us)) ∈ wasmEvPend s (a, vs)) (hc : (coreHostRel host).Consistent cs)
    (hdiv : host hh s' us .diverged) : Diverges P host (invoke s a vs) := by
  obtain ⟨y, fi, hh', hy, hf, hcode, hm⟩ := wasmEvPend_iff.mp ⟨cs, h, hc⟩
  simp only [Prod.mk.injEq] at hm
  obtain ⟨rfl, rfl, rfl⟩ := hm
  rcases hy with rfl | hy
  · obtain ⟨ps, rs, he, hn, hinv⟩ := invoke_call_facts hok hf
    rw [hinv]
    exact pendingDiv_diverges (PendingDiv.call hf hcode he hn hdiv)
  · exact invoke_pendO_diverges hH hS hok hy hf hcode hdiv

end Silmaril.Proofs.Wasm.Abstract.HostObs
