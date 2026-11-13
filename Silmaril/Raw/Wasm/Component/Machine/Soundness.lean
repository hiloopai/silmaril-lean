module

public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Defs

public import Silmaril.Raw.Wasm.Component.Machine.Exec
public import Silmaril.Raw.Wasm.Component.Machine.Step

/-!
# Soundness of the executable machine

The executable machine of `Machine/Exec.lean` (`step?`, `hostStep?`, and the fuel
drivers `run`, `runTop`, `runTopCall`) only takes transitions of the relational machine
`Machine.Step` of `Machine/Step.lean`. Both interpret the specification programs
`Canon.P E σ` (the REF functions of `definitions.py` at component-model `a25fc0b`,
<https://github.com/WebAssembly/component-model/blob/a25fc0b372dd21f07f0242c46e98bd0f1ea0c0e1/design/mvp/canonical-abi/definitions.py>).

## Results (all proved, for every engine `E`, executable stepper `X : E.Exec`, oracle `o`,
dispatcher and host readiness `hr`)

* `step?_sound`: `step? dispatch X o m = some (l, st, m') → Step o.prof hr dispatch m l m'`.
  Core steps are sound through `X.step?_sound` (`E.Internal`); oracle answers through the
  `Allowed o.prof` check of `step?`; internal traps through `Fault`.
* `hostStep?_sound`: `hostStep? hr ev m = some (l, m') → Step prof hr dispatch m l m'` for every
  profile `prof` (host events consult no oracle).
* `run_sound`, `runTop_sound`, `runTopCall_sound`: the label trace of a run is a `Steps` trace
  from the start configuration to the final one (`runTopCall` starts with the invoke label).
* `run_outcome`, `runTop_outcome`: the outcome of a run is `outOfFuel` or `outcomeOf` of the
  final configuration; `outcomeOf_resolved` / `outcomeOf_trap` / `outcomeOf_deadlock` relate
  it to the terminal predicates `Resolved` / `Trapped` / `Deadlocked` of `Machine/Step.lean`.
* `run_sound_resolved`, `runTop_sound_resolved`: a `resolved` outcome gives a `Steps` trace to a
  `Resolved` configuration in whose `results` every pending top-level call appears;
  `runTopCall_sound_resolved`: in particular the issued call `c` has a result.
* `Step.pending_mono` / `Steps.pending_mono`: top-level calls are never forgotten.

The link between the two files' separately written host-frame programs and named store
updates (`Machine.invokeProg` / `StepDefs.invokeProg`, `CStoreOps.setThreadStatus` /
`StepDefs.threadStatusSt`, ...) is definitional (`invokeProg_eq`, ...).

## Design notes

* A run returns the record `RunResult` of `Machine/Exec.lean`
  (`config`, `labels`, `outcome`); the drivers also take `hr` and `X`.
* `Step` takes `hr`; `step?` does not depend on it, so `step?_sound` holds for every `hr`.

Not claimed here: completeness of `step?`, invariants, fairness, termination.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon

variable {E : CoreEngine} {σ : Type}

/-! ## Agreement of the named definitions of `Machine/Exec.lean` and `Machine/Step.lean` -/

theorem setThreadStatus_eq :
    CStoreOps.setThreadStatus (E := E) = StepDefs.threadStatusSt := rfl

theorem trapped_eq (m : Config E σ) : m.trapped = StepDefs.trapCfg m := rfl

/-! ## Soundness of one step -/

section StepSound

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- The oracle's next state is irrelevant to the relation: a stepped configuration is
reachable in one relational step. -/
theorem step?_steps {m : Config E σ} {l : Label E σ} {st : o.State} {m' : Config E σ}
    (h : step? dispatch X o m = some (l, st, m')) : Steps o.prof hr dispatch m [l] m' :=
  .single (step?_sound hr dispatch X o h)

end StepSound

/-! ## Inversion of `hostStep?`, one lemma per host event -/

section HostInv

variable {hr : HostReady σ} {m m' : Config E σ} {l : Label E σ}

end HostInv

/-! ## Monotonicity of the pending calls -/

section Pending

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

end Pending

/-! ## Outcomes and terminal predicates -/

section Outcome

variable (hr : HostReady σ)

/-- In a `Resolved` configuration every pending top-level call has a result. -/
theorem Resolved.result? {m : Config E σ} (h : Resolved m) {x : CallId × FuncId × List Val}
    (hx : x ∈ m.pending) : ∃ r, m.result? x.1 = some r := by
  have := h.2.2
  simp only [Config.allResolved, List.all_eq_true] at this
  exact Option.isSome_iff_exists.1 (this x hx)

end Outcome

/-! ## Soundness of the drivers -/

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

theorem runLoop_outcome (n : Nat) (st : o.State) (m : Config E σ) (acc : List (Label E σ)) :
    (runLoop hr dispatch X o n st m acc).outcome = .outOfFuel ∨
      (runLoop hr dispatch X o n st m acc).outcome =
        outcomeOf hr (runLoop hr dispatch X o n st m acc).config := by
  induction n generalizing st m acc with
  | zero =>
    simp only [runLoop]
    split
    · exact .inl rfl
    · exact .inr rfl
  | succ n ih =>
    cases e : step? dispatch X (o.at st) m with
    | none => exact .inr (by simp [runLoop, e])
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      simpa only [runLoop, e] using ih st' m' (l :: acc)

theorem run_outcome (fuel : Nat) (m : Config E σ) :
    (run hr dispatch X o fuel m).outcome = .outOfFuel ∨
      (run hr dispatch X o fuel m).outcome = outcomeOf hr (run hr dispatch X o fuel m).config :=
  runLoop_outcome hr dispatch X o fuel o.state m []

/-- **Resolved runs**: a `resolved` outcome gives a relational trace to a `Resolved`
configuration in which every top-level call issued so far (in particular every call pending
at the start) has a result. -/
theorem run_sound_resolved (fuel : Nat) (m : Config E σ)
    (h : (run hr dispatch X o fuel m).outcome = .resolved) :
    Steps o.prof hr dispatch m (run hr dispatch X o fuel m).labels
        (run hr dispatch X o fuel m).config ∧
      Resolved (run hr dispatch X o fuel m).config ∧
      ∀ x ∈ (run hr dispatch X o fuel m).config.pending,
        ∃ r, (run hr dispatch X o fuel m).config.result? x.1 = some r := by
  have hs := run_sound hr dispatch X o fuel m
  have hres : Resolved (run hr dispatch X o fuel m).config := by
    rcases run_outcome hr dispatch X o fuel m with e | e
    · rw [h] at e; cases e
    · exact outcomeOf_resolved hr (e ▸ h)
  exact ⟨hs, hres, fun x hx => hres.result? hx⟩

/-- **Soundness of `runTop`** (internal steps and host ticks). -/
theorem runTop_sound (fuel : Nat) (m : Config E σ) :
    Steps o.prof hr dispatch m (runTop hr dispatch X o fuel m).labels
      (runTop hr dispatch X o fuel m).config := by
  obtain ⟨tr, h₁, h₂⟩ := runTopLoop_sound hr dispatch X o fuel o.state m []
  simp only [runTop, h₁, List.reverse_nil, List.nil_append]
  exact h₂

theorem runTop_outcome (fuel : Nat) (m : Config E σ) :
    (runTop hr dispatch X o fuel m).outcome = .outOfFuel ∨
      (runTop hr dispatch X o fuel m).outcome =
        outcomeOf hr (runTop hr dispatch X o fuel m).config :=
  runTopLoop_outcome hr dispatch X o fuel o.state m []

/-- A `resolved` outcome of `runTop` gives a relational trace to a `Resolved` configuration
where every top-level call has a result. -/
theorem runTop_sound_resolved (fuel : Nat) (m : Config E σ)
    (h : (runTop hr dispatch X o fuel m).outcome = .resolved) :
    Steps o.prof hr dispatch m (runTop hr dispatch X o fuel m).labels
        (runTop hr dispatch X o fuel m).config ∧
      Resolved (runTop hr dispatch X o fuel m).config ∧
      ∀ x ∈ (runTop hr dispatch X o fuel m).config.pending,
        ∃ r, (runTop hr dispatch X o fuel m).config.result? x.1 = some r := by
  have hres : Resolved (runTop hr dispatch X o fuel m).config := by
    rcases runTop_outcome hr dispatch X o fuel m with e | e
    · rw [h] at e; cases e
    · exact outcomeOf_resolved hr (e ▸ h)
  exact ⟨runTop_sound hr dispatch X o fuel m, hres, fun x hx => hres.result? hx⟩

/-- **Resolved top-level calls** (`run_sound_resolved` for a call issued by the
driver): a `resolved` outcome of `runTopCall … c f args` gives a relational trace, starting with
the invoke of `c`, to a `Resolved` configuration whose `results` contain `c`. -/
theorem runTopCall_sound_resolved {fuel : Nat} {c : CallId} {f : FuncId} {args : List Val}
    {m : Config E σ} {r : RunResult E σ o.State}
    (h : runTopCall hr dispatch X o fuel c f args m = some r) (hr' : r.outcome = .resolved) :
    Steps o.prof hr dispatch m r.labels r.config ∧ Resolved r.config ∧
      ∃ res, r.config.result? c = some res := by
  obtain ⟨_, _, hs, hp⟩ := runTopCall_sound hr dispatch X o h
  have hout : r.outcome = .outOfFuel ∨ r.outcome = outcomeOf hr r.config := by
    unfold runTopCall at h
    cases e : hostStep? hr (.invoke c f args) m with
    | none => simp [e] at h
    | some p =>
      obtain ⟨l, m₁⟩ := p
      simp only [e, Option.map_some, Option.some.injEq] at h
      subst h
      exact runTopLoop_outcome hr dispatch X o fuel o.state m₁ [l]
  have hres : Resolved r.config := by
    rcases hout with e | e
    · rw [hr'] at e; cases e
    · exact outcomeOf_resolved hr (e ▸ hr')
  exact ⟨hs, hres, hres.result? hp⟩

end Drivers

/-! ## Example: the invoke test of `Machine/Exec.lean`, transported to the relation -/

section Examples

private def noHostReady : HostReady Unit := fun _ _ => false

/-- The test run of `Machine/Exec.lean` (`toyDispatch`, invoke resolved) is a relational trace
ending in a `Resolved` configuration where call `0` resolved. -/
example (X : E.Exec) : ∃ r, runTopCall noHostReady toyDispatch X (Oracle.first (E := E)) 50
      ⟨0⟩ ⟨0⟩ [] (Config.init CStore.empty ()) = some r ∧
    Steps (Oracle.first (E := E)).prof noHostReady toyDispatch (Config.init CStore.empty ())
      r.labels r.config ∧ Resolved r.config ∧ ∃ res, r.config.result? ⟨0⟩ = some res := by
  refine ⟨_, rfl, ?_⟩
  exact runTopCall_sound_resolved noHostReady toyDispatch X _ rfl rfl

end Examples

end Silmaril.Wasm.Component.Machine
