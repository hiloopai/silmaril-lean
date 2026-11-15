module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Basic
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.Abstract.HostEval.Thms
public import Silmaril.Wasm.Abstract.HostClosing.Defs

/-!
# Productive prefixes are logged pending calls (proofs)

`coreInf_pend` (deterministic profile, typed checked invocations): every finite prefix
`streamTake ω n` of a productive Core run of an invocation is a logged pending prefix of
`wasmEvPend` at the run's next host call `(ω n).1`, with exactly that log. From
`wasmEvInf`'s prefix agreement and the exact same-log agreement `evRun_pend`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

theorem evRun_of_silent' {P : Silmaril.Wasm.Numerics.Profile} {c c' c'' : Config H}
    {cs : List (Call (wasmHostSig H))}
    (h : EvRun P host c cs c')
    (hs : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c' c'') :
    EvRun P host c cs c'' := by
  induction hs with
  | refl => exact h
  | tail _ hst ih => simpa using evRun_trans ih (.silent hst (.refl _))

theorem coreInf_pend {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
    {ω : Nat → Call (wasmHostSig H)}
    (h : CoreInf (SingleThreaded.profile o) host (invoke s a vs) ω) (n : Nat) :
    (streamTake ω n, (ω n).1) ∈ wasmEvPend s (a, vs) := by
  obtain ⟨c', hr, g, hg0, hg⟩ := wasmEvInf_prefix h n
  obtain ⟨c₁, hsil, hev⟩ := hg 0
  rw [hg0] at hsil
  have hr₁ := evRun_of_silent' hr hsil
  obtain ⟨E, a', hd, hst, -, -⟩ := hev
  have hp := evRun_pend hT hH hs hS hok hr₁ hd
  simp only [Nat.add_zero] at hst hp
  have e : (ω n).1 = ((ω n).1.1, c₁.store, (ω n).1.2.2) := by rw [← hst]
  rw [e]
  exact hp

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
