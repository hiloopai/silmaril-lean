module

public import Silmaril.Proofs.Wasm.Abstract.HostSquare.Basic
public import Silmaril.Wasm.Interp.Thms

/-!
# The exact-log commuting square at every profile (proofs)

`hostSquare` holds at the deterministic profile. For a store whose Wasm functions are
native-profile code (`Interp.NativeWasmFuncs`) and a host satisfying the explicit side condition
`Interp.HostNative`, every configuration reached from the invocation is native
(`Interp.NHConfig`), where Core steps do not depend on the profile (`Interp.step_profile`).

* `hEvStep_profile`: a labelled step from native code (`NAdmins`) is one at every profile. A
  host-free step transfers by `step_profile`; a stutter and an answered host call are given by
  `decompose?` and the host, and do not mention the profile;
* `evRun_profile`, `quietSteps_profile`, `diverges_noHost_profile`, `coreInf_profile`: labelled
  runs, event-free runs, host-free divergence and productive runs transfer, from an `NHConfig`
  configuration (the invariant carried along by `NHConfig.step`). Host-free divergence uses the
  host `fun _ _ _ _ => False`, which satisfies `HostNative` trivially (`hostNative_noHost`);
* `coreObsL_profile`: the Core observations of an invocation are the same at every profile;
* `hostSquare_profile`, `hostSquare_cover_profile`: the square and its coverage corollary at every
  profile.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostSquare

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

/-- A labelled step from native-profile code is a labelled step at every profile. -/
theorem hEvStep_profile {P P' : Numerics.Profile} {c c' : Config H}
    {e : Option (Call (wasmHostSig H))} (h : HEvStep P host c e c') (hc : Interp.NAdmins c.code) :
    HEvStep P' host c e c' := by
  cases e with
  | none =>
    rcases h with hs | hst
    · exact Or.inl (Interp.step_profile hs hc)
    · exact Or.inr hst
  | some e => exact h

/-- Labelled runs transfer between profiles from a native configuration; the end is native. -/
theorem evRun_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host) {c c' : Config H}
    {cs : List (Call (wasmHostSig H))} (h : EvRun P host c cs c') (hc : Interp.NHConfig c) :
    EvRun P' host c cs c' ∧ Interp.NHConfig c' := by
  induction h with
  | refl => exact ⟨.refl _, hc⟩
  | silent hs _ ih =>
    obtain ⟨h', hc'⟩ := ih (hc.step hN (hEvStep_step hs))
    exact ⟨.silent (hEvStep_profile hs hc.1) h', hc'⟩
  | event hs _ ih =>
    obtain ⟨h', hc'⟩ := ih (hc.step hN (hEvStep_step hs))
    exact ⟨.event (hEvStep_profile hs hc.1) h', hc'⟩

/-- Event-free labelled runs transfer between profiles from a native configuration. -/
theorem quietSteps_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host)
    {c c' : Config H} (h : Relation.ReflTransGen (fun a b => HEvStep P host a none b) c c')
    (hc : Interp.NHConfig c) :
    Relation.ReflTransGen (fun a b => HEvStep P' host a none b) c c' ∧ Interp.NHConfig c' := by
  induction h with
  | refl => exact ⟨.refl, hc⟩
  | tail _ hbc ih =>
    obtain ⟨r, hb⟩ := ih
    exact ⟨r.tail (hEvStep_profile hbc hb.1), hb.step hN (hEvStep_step hbc)⟩

/-- The host without outcomes stays in the native profile. -/
theorem hostNative_noHost : Interp.HostNative (fun _ _ _ _ => False : HostSemantics H) :=
  ⟨fun _ _ _ _ _ h _ => h.elim, fun _ _ _ _ _ h => h⟩

/-- Host-free divergence transfers between profiles from a native configuration. -/
theorem diverges_noHost_profile {P P' : Numerics.Profile} {c : Config H}
    (h : Diverges P (fun _ _ _ _ => False) c) (hc : Interp.NHConfig c) :
    Diverges P' (fun _ _ _ _ => False) c :=
  Interp.diverges_profileH hostNative_noHost h hc

/-- Productive runs transfer between profiles from a native configuration. -/
theorem coreInf_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host) {c : Config H}
    {ω : Nat → Call (wasmHostSig H)} (h : CoreInf P host c ω) (hc : Interp.NHConfig c) :
    CoreInf P' host c ω := by
  obtain ⟨g, hg0, hg⟩ := h
  have hgN : ∀ n, Interp.NHConfig (g n) := by
    intro n
    induction n with
    | zero => exact hg0 ▸ hc
    | succ n ih =>
      obtain ⟨c₁, hq, he⟩ := hg n
      exact (quietSteps_profile (P' := P) hN hq ih).2.step hN (hEvStep_step he)
  refine ⟨g, hg0, fun n => ?_⟩
  obtain ⟨c₁, hq, he⟩ := hg n
  obtain ⟨hq', hc₁⟩ := quietSteps_profile (P' := P') hN hq (hgN n)
  exact ⟨c₁, hq', hEvStep_profile he hc₁.1⟩

/-- **The Core observations of an invocation transfer between profiles**, for a store with
native-profile Wasm functions and a host satisfying `Interp.HostNative`. -/
theorem coreObsL_profile_of {P P' : Numerics.Profile} (hN : Interp.HostNative host)
    {s : Store H} {a : Nat} {vs : List Val} (hW : Interp.NativeWasmFuncs s.funcs)
    {x : FullObs H} (h : CoreObsL P host s a vs x) : CoreObsL P' host s a vs x := by
  have h0 := Interp.nhConfig_invoke hW a vs
  cases x with
  | done cs e =>
    rcases e with ⟨ws | t, s₂⟩ | _ | _
    · exact (evRun_profile hN h h0).1
    · exact h.elim
    · obtain ⟨s₂, hr⟩ := h
      exact ⟨s₂, (evRun_profile hN hr h0).1⟩
    · exact h.elim
  | blocked cs m =>
    obtain ⟨hh, s', us⟩ := m
    obtain ⟨c, E, a', hr, hd, hst, hno⟩ := h
    exact ⟨c, E, a', (evRun_profile hN hr h0).1, hd, hst, hno⟩
  | hostDiv cs m =>
    obtain ⟨hh, s', us⟩ := m
    obtain ⟨c, E, a', hr, hd, hst, hdv⟩ := h
    exact ⟨c, E, a', (evRun_profile hN hr h0).1, hd, hst, hdv⟩
  | div cs =>
    obtain ⟨c', hr, hdv⟩ := h
    obtain ⟨hr', hc'⟩ := evRun_profile (P' := P') hN hr h0
    exact ⟨c', hr', diverges_noHost_profile hdv hc'⟩
  | prod ω => exact coreInf_profile hN h h0

/-- `coreObsL_profile_of`, both directions. -/
theorem coreObsL_profile {P P' : Numerics.Profile} (hN : Interp.HostNative host)
    {s : Store H} {a : Nat} {vs : List Val} (hW : Interp.NativeWasmFuncs s.funcs)
    (x : FullObs H) : CoreObsL P host s a vs x ↔ CoreObsL P' host s a vs x :=
  ⟨coreObsL_profile_of hN hW, coreObsL_profile_of hN hW⟩

/-- **The exact-log commuting square at every profile**, for a store with native-profile Wasm
functions and a host satisfying `Interp.HostNative`. -/
theorem hostSquare_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs) (x : FullObs H) :
    NatObs host s a vs x ↔ CoreObsL P host s a vs x :=
  (hostSquare (o := fun _ _ _ _ => false) hT hH hs hS hok x).trans (coreObsL_profile hN hW x)

/-- **Completeness of the square at every profile**, for a store with native-profile Wasm
functions and a host satisfying `Interp.HostNative`: every Core run of the invocation extends to
a stuck end at the end's own log, or diverges. -/
theorem hostSquare_cover_profile {P : Numerics.Profile} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hN : Interp.HostNative host) {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hS : Interp.StoreChk s.funcs)
    (hW : Interp.NativeWasmFuncs s.funcs) (hok : InvokeOk s a vs) {c : Config H}
    (hrun : Steps P host (invoke s a vs) c) :
    (∃ (d : Config H) (cs : List (Call (wasmHostSig H))),
      Steps P host c d ∧ (∀ d', ¬ Step P host d d') ∧ EvRun P host (invoke s a vs) cs d ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd d e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, d.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? d.store d.code = some (E, a', hh, us))) ∨
      (Diverges P host c ∧
        ((∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
          ∃ ω, NatObs host s a vs (.prod ω))) := by
  have h0 := Interp.nhConfig_invoke hW a vs
  have hc : Interp.NHConfig c := h0.steps hN hrun
  rcases hostSquare_cover (o := fun _ _ _ _ => false) hT hH hs hS hok
      (Interp.steps_profileH hN hrun h0) with
    ⟨d, cs, hcd, hend, hev, hobs⟩ | ⟨hdiv, hobs⟩
  · have hd : Interp.NHConfig d := hc.steps hN hcd
    exact Or.inl ⟨d, cs, Interp.steps_profileH hN hcd hc,
      fun d' h => hend d' (Interp.step_profile h hd.1), (evRun_profile hN hev h0).1, hobs⟩
  · exact Or.inr ⟨Interp.diverges_profileH hN hdiv hc, hobs⟩

end Silmaril.Proofs.Wasm.Abstract.HostSquare
