module

public import Silmaril.Wasm.Abstract.HostSquare.Defs
public import Silmaril.Wasm.Abstract.HostObs.Thms
public import Silmaril.Wasm.Abstract.HostClosingInf.Thms

/-!
# The exact-log commuting square for host calls (proofs)

* `noAns_iff`: no answer of `coreHostRel host` is no outcome of `host`;
* `hostSquare` (deterministic profile, typed checked invocations, a host with typed answers in
  the native host slice): case by case from the exact-log pieces of
  `Silmaril.Wasm.Abstract.HostClosingInf`. A finished end that is a thrown exception or `div`
  is neither native (`wasmEv_core_done`: its Core end would agree with it, and `CoreEnd` has no
  such end) nor Core;
* `steps_evRun`: every Core run is a labelled run, with some log;
* `stuck_at_call`: a stuck configuration `Pending` a host call is at a host call
  (`decompose?`) with no host outcome. Against `totalize host` it diverges
  (`pendingDiv_diverges`); its first step is no step of `host`, so it is the stutter at the call;
* `hostSquare_stuck`, `hostSquare_diverges`: every stuck end and every divergence of the
  invocation is an observation of the square (`core_done_wasmEv`; `diverges_events`,
  `quiet_iff`);
* `steps_stuck_or_diverges`, `hostSquare_cover`: every Core run extends to a stuck end or
  diverges, so is a finite prefix of one of those observations.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostSquare

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type} {host : HostSemantics H}

/-- No answer of the relational host is no outcome of the host. -/
theorem noAns_iff {m : (wasmHostSig H).Op} :
    (∀ ans, ¬ coreHostRel host m ans) ↔ ∀ o, ¬ host m.1 m.2.1 m.2.2 o := by
  constructor
  · intro h o ho
    cases o with
    | returned s' r => exact h (.answer (s', r)) ho
    | diverged => exact h .diverge ho
  · intro h ans hans
    cases ans with
    | answer p => exact h _ hans
    | diverge => exact h _ hans

/-- **The square** (deterministic profile, typed checked invocations, a host with typed answers
in the native host slice). -/
theorem hostSquare {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) (x : FullObs H) :
    NatObs host s a vs x ↔ CoreObsL (SingleThreaded.profile o) host s a vs x := by
  cases x with
  | done cs e =>
    rcases e with ⟨ws | t, s₂⟩ | _ | _
    · exact wasmEvFun_vals_iff hT hH hs hS hok
    · refine ⟨fun h => ?_, fun h => h.elim⟩
      obtain ⟨c, -, -, hend⟩ :=
        wasmEv_core_done (P := SingleThreaded.profile o) hH hS hok h.1 h.2
      exact hend.elim
    · exact wasmEvFun_trap_iff hT hH hs hS hok
    · refine ⟨fun h => ?_, fun h => h.elim⟩
      obtain ⟨c, -, -, hend⟩ :=
        wasmEv_core_done (P := SingleThreaded.profile o) hH hS hok h.1 h.2
      exact hend.elim
  | blocked cs m =>
    obtain ⟨hh, s', us⟩ := m
    constructor
    · rintro ⟨h, hc, hno⟩
      obtain ⟨c, E, a', hrun, hd, hst⟩ :=
        wasmEvPend_evRun (P := SingleThreaded.profile o) hH hS hok h hc
      exact ⟨c, E, a', hrun, hd, hst, noAns_iff.mp hno⟩
    · rintro ⟨c, E, a', hrun, hd, rfl, hno⟩
      exact ⟨evRun_pend hT hH hs hS hok hrun hd, evRun_consistent hrun,
        noAns_iff.mpr hno⟩
  | hostDiv cs m =>
    obtain ⟨hh, s', us⟩ := m
    constructor
    · rintro ⟨h, hc, hdiv⟩
      obtain ⟨c, E, a', hrun, hd, hst⟩ :=
        wasmEvPend_evRun (P := SingleThreaded.profile o) hH hS hok h hc
      exact ⟨c, E, a', hrun, hd, hst, hdiv⟩
    · rintro ⟨c, E, a', hrun, hd, rfl, hdiv⟩
      exact ⟨evRun_pend hT hH hs hS hok hrun hd, evRun_consistent hrun, hdiv⟩
  | div cs => exact wasmEvFunD_div_iff hT hH hs hS hok
  | prod ω =>
    show ω ∈ hostObsInf (coreHostRel host) wasmEvInfN s (a, vs) ↔ _
    rw [← hostObsInf_wasmEvInf_eq hT hH hs hS hok]
    exact wasmEvInf_hostObsInf

/-- Every Core run is a labelled run, with some log. -/
theorem steps_evRun {P : Numerics.Profile} {c c' : Config H} (h : Steps P host c c') :
    ∃ cs, EvRun P host c cs c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .refl _⟩
  | head hst _ ih =>
    obtain ⟨cs, hr⟩ := ih
    obtain ⟨e, he⟩ := step_hEvStep hst
    cases e with
    | none => exact ⟨cs, .silent he hr⟩
    | some e => exact ⟨e :: cs, .event he hr⟩

/-- A pending call with no outcome is one the totalized host diverges on. -/
theorem pending_totalize {s : Store H} {es : List Admin} (h : Pending host s es) :
    PendingDiv (totalize host) s es := by
  induction h with
  | call hf hcode he hn hno => exact .call hf hcode he hn (Or.inr ⟨rfl, hno⟩)
  | label _ ih => exact .label ih
  | frame _ ih => exact .frame ih

/-- **A stuck configuration pending a host call is at that call**, which has no host outcome. -/
theorem stuck_at_call {P : Numerics.Profile} {c : Config H} (hp : Pending host c.store c.code)
    (hend : ∀ c', ¬ Step P host c c') :
    ∃ (E : SingleThreaded.Ctx) (a' : Nat) (hh : H) (us : List Val),
      SingleThreaded.decompose? c.store c.code = some (E, a', hh, us) ∧
      ∀ o, ¬ host hh c.store us o := by
  obtain ⟨c₁, hst, -⟩ :=
    (pendingDiv_diverges (P := P) (f := c.frame) (pending_totalize hp)).unfold
  obtain ⟨e, he⟩ := step_hEvStep hst
  cases e with
  | none =>
    rcases he with he | ⟨rfl, E, a', hh, us, hd, hdiv⟩
    · exact absurd (Step.host_mono (fun _ _ _ _ h => h.elim) he) (hend _)
    · rcases hdiv with hdiv | ⟨-, hno⟩
      · exact absurd (hEvStep_step (P := P) (host := host) (e := none)
          (Or.inr ⟨rfl, E, a', hh, us, hd, hdiv⟩)) (hend _)
      · exact ⟨E, a', hh, us, hd, hno⟩
  | some e =>
    obtain ⟨E, a', hd, hst', hans, hc'⟩ := he
    rcases hans with hans | ⟨he', -⟩
    · exact absurd (hEvStep_step (P := P) (host := host) (e := some e)
        ⟨E, a', hd, hst', hans, hc'⟩) (hend _)
    · cases he'

section Det

variable {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
  (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
  (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs)
include hT hH hs hS hok

/-- **Every stuck end is an observation of the square**, at the run's own log. -/
theorem hostSquare_stuck {c : Config H}
    (hrun : Steps (SingleThreaded.profile o) host (invoke s a vs) c)
    (hend : ∀ c', ¬ Step (SingleThreaded.profile o) host c c') :
    ∃ cs, EvRun (SingleThreaded.profile o) host (invoke s a vs) cs c ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd c e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, c.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? c.store c.code = some (E, a', hh, us)) := by
  obtain ⟨cs, hev⟩ := steps_evRun hrun
  obtain ⟨n, hn⟩ := stepsN_of_steps hrun
  refine ⟨cs, hev, ?_⟩
  rcases core_done_wasmEv hT hH hs hS hok hn hend with hp | ⟨-, e, -, -, hce⟩
  · obtain ⟨E, a', hh, us, hd, hno⟩ := stuck_at_call hp hend
    exact Or.inr ⟨hh, us, (hostSquare (o := o) hT hH hs hS hok _).mpr ⟨c, E, a', hev, hd, rfl, hno⟩,
      E, a', hd⟩
  · refine Or.inl ⟨e, (hostSquare (o := o) hT hH hs hS hok _).mpr ?_, hce⟩
    rcases e with ⟨ws | t, s₂⟩ | _ | _
    · obtain rfl : c = ⟨s₂, {}, vals ws⟩ := hce
      exact hev
    · exact hce.elim
    · obtain ⟨s₂, rfl⟩ := hce
      exact ⟨s₂, hev⟩
    · exact hce.elim

/-- **Every divergence is an observation of the square**: host-free divergence after a log,
host divergence at a pending call, or a productive run. -/
theorem hostSquare_diverges
    (hd : Diverges (SingleThreaded.profile o) host (invoke s a vs)) :
    (∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
      ∃ ω, NatObs host s a vs (.prod ω) := by
  rcases diverges_events.mp hd with ⟨cs, c', hrun, hq⟩ | ⟨ω, hω⟩
  · rcases quiet_iff.mp hq with hq | ⟨d, hfree, E, a', hh, us, hdec, hdiv⟩
    · exact Or.inl ⟨cs, (hostSquare (o := o) hT hH hs hS hok _).mpr ⟨c', hrun, hq⟩⟩
    · have hrun' := evRun_trans hrun (evRun_of_free hfree)
      rw [List.append_nil] at hrun'
      exact Or.inr (Or.inl ⟨cs, (hh, d.store, us),
        (hostSquare (o := o) hT hH hs hS hok _).mpr ⟨d, E, a', hrun', hdec, rfl, hdiv⟩⟩)
  · exact Or.inr (Or.inr ⟨ω, (hostSquare (o := o) hT hH hs hS hok _).mpr hω⟩)

end Det

/-- Every Core run extends to a stuck end, or diverges. -/
theorem steps_stuck_or_diverges {P : Numerics.Profile} {c : Config H} :
    (∃ d, Steps P host c d ∧ ∀ d', ¬ Step P host d d') ∨ Diverges P host c := by
  classical
  by_cases h : ∃ d, Steps P host c d ∧ ∀ d', ¬ Step P host d d'
  · exact Or.inl h
  · refine Or.inr ?_
    unfold Diverges
    refine Silmaril.InfiniteTrace.coinduct (fun x => Steps P host c x) ?_ .refl
    intro x hx
    by_contra hne
    exact h ⟨x, hx, fun d' hs => hne ⟨d', hs, hx.tail hs⟩⟩

/-- **Every Core run of the invocation is a finite prefix of an observation of the square**
(deterministic profile, typed checked invocations): it extends to a stuck end, a `done` or
`blocked` observation at the end's own log, or it diverges, a `div`, `hostDiv` or `prod`
observation. -/
theorem hostSquare_cover {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hS : Interp.StoreChk s.funcs) (hok : InvokeOk s a vs) {c : Config H}
    (hrun : Steps (SingleThreaded.profile o) host (invoke s a vs) c) :
    (∃ (d : Config H) (cs : List (Call (wasmHostSig H))),
      Steps (SingleThreaded.profile o) host c d ∧
      (∀ d', ¬ Step (SingleThreaded.profile o) host d d') ∧
      EvRun (SingleThreaded.profile o) host (invoke s a vs) cs d ∧
      ((∃ e, NatObs host s a vs (.done cs e) ∧ CoreEnd d e) ∨
        ∃ (hh : H) (us : List Val), NatObs host s a vs (.blocked cs (hh, d.store, us)) ∧
          ∃ (E : SingleThreaded.Ctx) (a' : Nat),
            SingleThreaded.decompose? d.store d.code = some (E, a', hh, us))) ∨
      (Diverges (SingleThreaded.profile o) host c ∧
        ((∃ cs, NatObs host s a vs (.div cs)) ∨ (∃ cs m, NatObs host s a vs (.hostDiv cs m)) ∨
          ∃ ω, NatObs host s a vs (.prod ω))) := by
  rcases steps_stuck_or_diverges (c := c) with ⟨d, hcd, hend⟩ | hdiv
  · obtain ⟨cs, hev, hobs⟩ := hostSquare_stuck hT hH hs hS hok (hrun.trans hcd) hend
    exact Or.inl ⟨d, cs, hcd, hend, hev, hobs⟩
  · exact Or.inr ⟨hdiv, hostSquare_diverges hT hH hs hS hok
      (Silmaril.InfiniteTrace.of_steps hrun hdiv)⟩

end Silmaril.Proofs.Wasm.Abstract.HostSquare
