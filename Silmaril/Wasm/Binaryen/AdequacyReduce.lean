module

public import Silmaril.Wasm.Binaryen.Interp
public import Silmaril.Wasm.Binaryen.NoThrow
public import Silmaril.Wasm.Execution.Core.Soundness
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.SingleThreaded.Agreement

@[expose] public section

/-! # Reducing adequacy to three simulation obligations

`lower_sound` and `lower_complete` (a separate interpreter-adequacy development (not included in this package)) split into

* `FwdSim`: a terminating native run is matched by a Core run to the same
  result (needs a typing invariant: `run` truncates stacks with `take`);
* `BwdSim`: a Core run to a result is matched by a native run (some fuel);
* `NoDivOfTerm`: a Core invocation that reaches a result has no infinite
  trace (weak implies strong normalisation for the deterministic profile;
  see `Behaviour/Refinement/Interpreter.lean`, it is open there too);

plus closed-store type safety, which is proved here (`diverges_of_not_terminal`):
the profile's `closedHost` fails `HostOk`, so Core progress is used for the
always-diverging host `SingleThreaded.divHost` and a host step is excluded
because every function of every reachable store is Wasm code.
-/

namespace Silmaril.Wasm.Binaryen

open Execution.Core Numerics

variable {H : Type}

/-! ## Closed-store type safety -/

/-- Typing is preserved along closed-host runs. -/
theorem closed_preserves {P : Profile} {c c' : Config H} {ts : List Validation.CValType}
    (hc : ConfigOk c ts) (h : Steps P closedHost c c') : ConfigOk c' ts := by
  induction h with
  | refl => exact hc
  | tail _ hst ih =>
    exact (Step.preservation SingleThreaded.divHost_ok ih
      (Step.of_noHost _ (hst : Step P (fun _ _ _ _ => False) _ _))).1

/-- **Closed-store progress**: a typed configuration whose store holds only Wasm
functions is terminal or takes a closed-host step. -/
theorem closed_progress {P : Profile} {c : Config H} {ts : List Validation.CValType}
    (hc : ConfigOk c ts) (hF : FuncsOk c.store.funcs) :
    c.Terminal ∨ ∃ c', Step P closedHost c c' := by
  rcases Config.progress (P := P) (host := SingleThreaded.divHost)
      SingleThreaded.divHost_ok hc with h | ⟨c', hc'⟩
  · exact Or.inl h
  · rcases SingleThreaded.Step.split_host hc' with h | ⟨E, a, hh, args, hd, -⟩
    · exact Or.inr ⟨c', h⟩
    · obtain ⟨fi, -, -, -, hfi, hcode, -⟩ := SingleThreaded.decompose?_sound hd
      obtain ⟨fn, hfn, -⟩ := hF fi (List.mem_of_getElem? hfi)
      rw [hcode] at hfn
      cases hfn

/-- Every function of a store reachable from a profile invocation is profile code. -/
theorem funcsOk_of_steps {P : Profile} {s : Store H} {a : Nat} {vs : List Val} {c : Config H}
    (hF : FuncsOk s.funcs) (hst : Steps P closedHost (invoke s a vs) c) :
    FuncsOk c.store.funcs := by
  have h0 : OkAdmins (invoke s a vs).code := by simp [invoke]
  rw [(okAdmins_steps hst h0 hF).2]
  exact hF

/-- **Closed-store type safety**: a typed profile invocation that never reaches a
result diverges. -/
theorem diverges_of_not_terminal {P : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hF : FuncsOk s.funcs) (hok : InvokeOk s a vs)
    (hnt : ∀ c, Steps P closedHost (invoke s a vs) c → ¬ c.Terminal) :
    Diverges P closedHost (invoke s a vs) := by
  obtain ⟨-, -, rs, -, -, hc⟩ := invoke_ok hs hok
  unfold Diverges
  refine InfiniteTrace.coinduct (fun c => Steps P closedHost (invoke s a vs) c) ?_ .refl
  intro c hst
  rcases closed_progress (closed_preserves hc hst) (funcsOk_of_steps hF hst) with ht | ⟨c', hc'⟩
  · exact absurd ht (hnt c hst)
  · exact ⟨c', hc', hst.tail hc'⟩

/-! ## The native side always reports a behaviour -/

theorem invokeRun_flowBeh {fuel : Nat} {s s' : Store H} {a : Nat} {vs : List Val} {fl : Flow}
    (h : invokeRun fuel s a vs = some (s', fl)) : ∃ b, flowBeh fl = some b := by
  unfold invokeRun at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨_, rfl⟩)
    | (simp at h)

/-! ## The three obligations and the reduction -/

/-- Forward simulation: a terminating native run is a Core run to the same result. -/
def FwdSim (P : Profile) (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  ∀ fuel s' fl b, invokeRun fuel s a vs = some (s', fl) → flowBeh fl = some b →
    ∃ (c : Config H) (r : Result), Steps P closedHost (invoke s a vs) c ∧ c.code = r.toAdmin ∧
      r.toBehaviour = b

/-- Backward simulation: a Core run to a result is found by the native interpreter. -/
def BwdSim (P : Profile) (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  ∀ (c : Config H) (r : Result), Steps P closedHost (invoke s a vs) c → c.code = r.toAdmin →
    ∃ fuel s' fl, invokeRun fuel s a vs = some (s', fl) ∧ flowBeh fl = some r.toBehaviour

/-- Weak implies strong normalisation at this invocation. -/
def NoDivOfTerm (P : Profile) (s : Store H) (a : Nat) (vs : List Val) : Prop :=
  (∃ c, Steps P closedHost (invoke s a vs) c ∧ c.Terminal) →
    ¬ Diverges P closedHost (invoke s a vs)

/-- `lower_sound` from the forward and backward simulations and type safety. -/
theorem nbeh_subset_of_sim {P : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hF : FuncsOk s.funcs) (hok : InvokeOk s a vs)
    (fwd : FwdSim P s a vs) (bwd : BwdSim P s a vs) :
    nbeh s a vs ⊆ behaviours P closedHost s a vs := by
  rintro b (⟨fuel, s', fl, hrun, hb⟩ | ⟨rfl, hnone⟩)
  · obtain ⟨c, r, hst, hc, rfl⟩ := fwd fuel s' fl b hrun hb
    exact Or.inl ⟨c, r, hst, hc, rfl⟩
  · refine Or.inr ⟨rfl, ?_⟩
    refine diverges_of_not_terminal hs hF hok ?_
    rintro c hst ⟨r, hr⟩
    obtain ⟨fuel, s', fl, h, -⟩ := bwd c r hst hr
    rw [hnone] at h
    cases h

/-- `lower_complete` from the forward and backward simulations and `NoDivOfTerm`. -/
theorem behaviours_subset_of_sim {P : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (fwd : FwdSim P s a vs) (bwd : BwdSim P s a vs) (sn : NoDivOfTerm P s a vs) :
    behaviours P closedHost s a vs ⊆ nbeh s a vs := by
  rintro b (⟨c, r, hst, hc, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨fuel, s', fl, h, hb⟩ := bwd c r hst hc
    exact Or.inl ⟨fuel, s', fl, h, hb⟩
  · refine Or.inr ⟨rfl, fun fuel => ?_⟩
    rcases h : invokeRun fuel s a vs with _ | ⟨s', fl⟩
    · rfl
    · obtain ⟨b, hb⟩ := invokeRun_flowBeh h
      obtain ⟨c, r, hst, hc, -⟩ := fwd fuel s' fl b h hb
      exact absurd hdiv (sn ⟨c, hst, r, hc⟩)

end Silmaril.Wasm.Binaryen
