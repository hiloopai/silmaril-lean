module

public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Exec.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Exec.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Config.Thms

/-!
# `Machine.Soundness`: laws of the component reference

Theorems of the component reference copy `Machine.Soundness`, refined out of
`Silmaril.Raw.Wasm.Component.Machine.Soundness`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}

theorem invokeProg_eq (c : CallId) (f : FuncId) (args : List Val) :
    Machine.invokeProg (E := E) (σ := σ) c f args = StepDefs.invokeProg c f args := rfl

theorem tickProg_eq (hr : HostReady σ) :
    Machine.tickProg (E := E) hr = StepDefs.tickProg hr := rfl

theorem cancelProg_eq (r : CancelRef) :
    Machine.cancelProg (E := E) (σ := σ) r = StepDefs.cancelProg r := rfl

theorem runProg_eq (p : P E σ (Ret E)) : Machine.runProg p = StepDefs.runProg p := rfl

theorem lastCall?_eq (m : Config E σ) : m.lastCall? = StepDefs.lastCall? m := rfl

theorem observe_eq (m : Config E σ) (ob : HostObs) : m.observe ob = StepDefs.observe m ob := by
  cases ob <;> rfl

theorem hostReady_iff (m : Config E σ) : m.hostReady = true ↔ StepDefs.HostReadyCfg m := by
  simp [Config.hostReady, StepDefs.HostReadyCfg, and_assoc]

section StepSound

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

theorem opStep_sound {m : Config E σ} {th : Option ThreadId} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {op : Op E σ} {k : Op.Resp op → P E σ (Ret E)}
    {l : Label E σ} {st : o.State} {m' : Config E σ}
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) op k), segs⟩ :: rest)
    (h : opStep dispatch o m ⟨th, .prog (.op (S := Eff E σ) op k), segs⟩ rest op k =
      some (l, st, m')) :
    Step o.prof hr dispatch m l m' := by
  cases op with
  | get =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .get hc
  | modify f =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .modify hc
  | trap r =>
    simp only [opStep, trapStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .trap hc
  | choose kd =>
    simp only [opStep] at h
    split at h
    · cases h
    · split at h
      · rename_i ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .choose _ hc ha
      · cases h
  | callCore f args =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .callCore hc
  | call c =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .call hc
  | currentThread =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .currentThread hc
  | newThread b =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .newThread hc rfl
  | block sw =>
    cases th with
    | none =>
      simp only [opStep, trapStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .fault (.blockNoThread hc)
    | some t =>
      cases sw with
      | none =>
        simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact .block hc
      | some u =>
        simp only [opStep] at h
        split at h
        · rename_i hu
          simp only [trapStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .fault (.switchMissing hc hu)
        · rename_i au hu
          simp only [tauStep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact .blockSwitch hc hu
  | resumeThread u =>
    simp only [opStep] at h
    split at h
    · rename_i hu
      simp only [trapStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .fault (.resumeMissing hc hu)
    · rename_i au hu
      simp only [tauStep, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact .resumeThread hc hu
  | hostGet =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .hostGet hc
  | hostSet s =>
    simp only [opStep, tauStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .hostSet hc
  | emit ob =>
    simp only [opStep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [observe_eq]
    exact .emit hc

end StepSound

section Pending

variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

theorem hostFinish_pending (r : Ret E) (rest : List (Activation E σ)) (m : Config E σ) :
    (StepDefs.hostFinish r rest m).pending = m.pending := by
  unfold StepDefs.hostFinish
  split <;> rfl

theorem observe_pending (m : Config E σ) (ob : HostObs) :
    (StepDefs.observe m ob).pending = m.pending := by
  cases ob <;> rfl

/-- A step never forgets a top-level call. -/
theorem Step.pending_mono {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') {x : CallId × FuncId × List Val} (hx : x ∈ m.pending) :
    x ∈ m'.pending := by
  cases h with
  | hostDone => rw [hostFinish_pending]; exact hx
  | emit => simpa [observe_pending] using hx
  | hostInvoke => exact List.mem_append_left _ hx
  | _ => exact hx

/-- A run never forgets a top-level call. -/
theorem Steps.pending_mono {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') {x : CallId × FuncId × List Val} (hx : x ∈ m.pending) :
    x ∈ m'.pending := by
  induction h with
  | refl => exact hx
  | cons s _ ih => exact ih (s.pending_mono hx)

end Pending

section Outcome

variable (hr : HostReady σ)

theorem outcomeOf_resolved {m : Config E σ} (h : outcomeOf hr m = .resolved) : Resolved m := by
  unfold outcomeOf at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i hc
      split at h
      · rename_i ha
        exact ⟨by simpa using hc, by simpa using hl, ha⟩
      · split at h <;> cases h

theorem outcomeOf_trap {m : Config E σ} (h : outcomeOf hr m = .trap) : Trapped m := by
  unfold outcomeOf at h
  split at h
  · assumption
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h <;> cases h

theorem outcomeOf_deadlock {m : Config E σ} (h : outcomeOf hr m = .deadlock) :
    Deadlocked hr m := by
  unfold outcomeOf at h
  split at h
  · cases h
  · rename_i hl
    split at h
    · cases h
    · rename_i hc
      split at h
      · cases h
      · rename_i ha
        split at h
        · rename_i hcand
          simp only [List.isEmpty_iff] at hcand
          refine ⟨by simpa using hc, by simpa using hl, ?_, hcand⟩
          simp only [Config.allResolved, List.all_eq_true, not_forall] at ha
          obtain ⟨x, hx, hn⟩ := ha
          exact ⟨x, hx, by simpa using hn⟩
        · cases h

end Outcome

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

theorem runTopLoop_outcome (n : Nat) (st : o.State) (m : Config E σ)
    (acc : List (Label E σ)) :
    (runTopLoop hr dispatch X o n st m acc).outcome = .outOfFuel ∨
      (runTopLoop hr dispatch X o n st m acc).outcome =
        outcomeOf hr (runTopLoop hr dispatch X o n st m acc).config := by
  induction n generalizing st m acc with
  | zero =>
    simp only [runTopLoop]
    split
    · exact .inl rfl
    · exact .inr rfl
  | succ n ih =>
    cases e : step? dispatch X (o.at st) m with
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      simpa only [runTopLoop, e] using ih st' m' (l :: acc)
    | none =>
      by_cases w : wantsTick hr m = true
      · cases e' : hostStep? hr .tick m with
        | none => exact .inr (by simp [runTopLoop, e, w, e'])
        | some p =>
          obtain ⟨l, m'⟩ := p
          simpa only [runTopLoop, e, w, e', ↓reduceIte] using ih st m' (l :: acc)
      · exact .inr (by simp [runTopLoop, e, w])

end Drivers

end Silmaril.Wasm.Component.Machine

namespace Silmaril.Wasm.Component.Machine

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
variable {E : CoreEngine} {σ : Type}

section StepSound

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

/-- A silent transition: label `tau`, the oracle's state, the given configuration. -/
theorem tauStep_inv {m₀ m' : Config E σ} {l : Label E σ} {st : o.State}
    (h : tauStep o m₀ = some (l, st, m')) : l = .tau ∧ st = o.state ∧ m' = m₀ := by
  simp only [tauStep, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- A trap transition: label `trap r`, the oracle's state, the trapped configuration. -/
theorem trapStep_inv {m₀ m' : Config E σ} {r : TrapReason} {l : Label E σ} {st : o.State}
    (h : trapStep o m₀ r = some (l, st, m')) : l = .trap r ∧ st = o.state ∧ m' = m₀.trapped := by
  simp only [trapStep, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- A finished host frame is popped as `StepDefs.hostFinish` pops it. -/
theorem finish_host (m : Config E σ) (a : Activation E σ) (rest : List (Activation E σ))
    (r : Ret E) (ha : a.thread = none) :
    finish o m a rest r = tauStep o (StepDefs.hostFinish r rest m) := by
  simp only [finish, ha, StepDefs.hostFinish, ← lastCall?_eq]
  rcases rest with _ | ⟨_, _⟩ <;> cases r <;> cases m.lastCall? <;> rfl

theorem retStep_sound {m : Config E σ} {th : Option ThreadId} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {r : Ret E} {l : Label E σ} {st : o.State}
    {m' : Config E σ} (hc : m.ctl = ⟨th, .prog (.pure r), segs⟩ :: rest)
    (h : retStep o m ⟨th, .prog (.pure r), segs⟩ rest r = some (l, st, m')) :
    Step o.prof hr dispatch m l m' := by
  cases segs with
  | nil =>
    show Step o.prof hr dispatch m l m'
    cases th with
    | some t =>
      obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o h
      exact .threadExit hc
    | none =>
      have hf : tauStep o (StepDefs.hostFinish r rest m) = some (l, st, m') :=
        (finish_host o m ⟨none, .prog (.pure r), []⟩ rest r rfl).symm.trans h
      obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o hf
      exact .hostDone hc
  | cons s segs =>
    show Step o.prof hr dispatch m l m'
    cases s with
    | prog k =>
      obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o h
      exact .popProg hc
    | core t k =>
      cases r with
      | flat vs =>
        obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o h
        exact .popCore hc
      | _ =>
        obtain ⟨rfl, -, rfl⟩ : l = .trap _ ∧ st = o.state ∧ m' = _ := trapStep_inv o h
        exact .fault (.calloutBadRet hc fun _ e => nomatch e)

/-- `coreStep` on a core activation that is still running (or stuck) takes the stepper's
internal step, if any. -/
theorem coreStep_internal {m : Config E σ} {a : Activation E σ} {rest : List (Activation E σ)}
    {t : E.Thread (CanonHost E)} {k : List FlatValue → P E σ (Ret E)}
    (hs : E.status m.store.core t = .running ∨ E.status m.store.core t = .stuck) :
    coreStep dispatch X o m a rest t k =
      (X.step? (m.store.core, t)).map fun (c', t') =>
        (Label.core, o.state, (m.mapStore (CStoreOps.setCore c')).withCtl
          ({ a with focus := .core t' k } :: rest)) := by
  rcases hs with hs | hs <;> simp only [coreStep, hs] <;> split <;> simp_all

theorem coreStep_sound {m : Config E σ} {th : Option ThreadId} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {t : E.Thread (CanonHost E)}
    {k : List FlatValue → P E σ (Ret E)} {l : Label E σ} {st : o.State} {m' : Config E σ}
    (hc : m.ctl = ⟨th, .core t k, segs⟩ :: rest)
    (h : coreStep dispatch X o m ⟨th, .core t k, segs⟩ rest t k = some (l, st, m')) :
    Step o.prof hr dispatch m l m' := by
  have internal (hs : E.status m.store.core t = .running ∨ E.status m.store.core t = .stuck) :
      Step o.prof hr dispatch m l m' := by
    rw [coreStep_internal dispatch X o hs] at h
    obtain ⟨⟨c', t'⟩, he, hl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, -, rfl⟩ : Label.core = l ∧ o.state = st ∧ _ = m' := by
      simpa only [Prod.mk.injEq] using hl
    exact .coreInternal hc hs (X.step?_sound he)
  cases hs : E.status m.store.core t with
  | running => exact internal (.inl hs)
  | stuck => exact internal (.inr hs)
  | returned r =>
    show Step o.prof hr dispatch m l m'
    cases r with
    | values vs =>
      have he : tauStep o (m.withCtl ({ (⟨th, .core t k, segs⟩ : Activation E σ) with
          focus := .prog (k vs) } :: rest)) = some (l, st, m') := by
        simpa only [coreStep, hs] using h
      obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o he
      exact .coreReturned hc hs
    | trap =>
      have he : trapStep o m .coreTrap = some (l, st, m') := by
        simpa only [coreStep, hs] using h
      obtain ⟨rfl, -, rfl⟩ : l = .trap .coreTrap ∧ st = o.state ∧ m' = _ := trapStep_inv o he
      exact .coreTrap hc hs
  | callout hh args =>
    have he : tauStep o (m.withCtl ({ (⟨th, .core t k, segs⟩ : Activation E σ) with
        focus := .prog (dispatch (.hostCallout hh args)), segs := .core t k :: segs } :: rest)) =
        some (l, st, m') := by
      simpa only [coreStep, hs] using h
    obtain ⟨rfl, -, rfl⟩ : l = .tau ∧ st = o.state ∧ m' = _ := tauStep_inv o he
    exact .coreCallout hc hs

/-- **Soundness of `step?`** (executable against relational): every executable step is a relational
step with the same label, for every engine, stepper, oracle, dispatcher and host readiness. -/
theorem step?_sound {m : Config E σ} {l : Label E σ} {st : o.State} {m' : Config E σ}
    (h : step? dispatch X o m = some (l, st, m')) : Step o.prof hr dispatch m l m' := by
  unfold step? at h
  split at h
  · cases h
  · rename_i a rest hc
    obtain ⟨th, focus, segs⟩ := a
    cases focus with
    | prog p =>
      cases p with
      | pure r => exact retStep_sound hr dispatch o hc h
      | op op k => exact opStep_sound hr dispatch o hc h
    | core t k => exact coreStep_sound hr dispatch X o hc h

end StepSound

section HostInv

variable {hr : HostReady σ} {m m' : Config E σ} {l : Label E σ}

theorem hostStep?_invoke_inv {c : CallId} {f : FuncId} {args : List Val}
    (h : hostStep? hr (.invoke c f args) m = some (l, m')) :
    l = .host (.invoke c f args) ∧ (∀ x ∈ m.pending, x.1 ≠ c) ∧
      m' = ({ m with pending := m.pending ++ [(c, f, args)] } : Config E σ).withCtl
        [Activation.ofProg none (invokeProg c f args)] := by
  unfold hostStep? at h
  split at h
  · simp only at h
    split at h
    · cases h
    · rename_i hany
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨h.1.symm, fun x hx e => hany ?_, h.2.symm⟩
      simp only [List.any_eq_true, beq_iff_eq]
      exact ⟨x, hx, e⟩
  · cases h

theorem hostStep?_tick_inv (h : hostStep? hr .tick m = some (l, m')) :
    l = .host .tick ∧ m' = m.withCtl [Activation.ofProg none (tickProg hr)] := by
  unfold hostStep? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · cases h

theorem hostStep?_cancel_inv {c : CallId} (h : hostStep? hr (.cancel c) m = some (l, m')) :
    ∃ r, m.cancel? c = some r ∧ m.result? c = none ∧ l = .host (.cancel c) ∧
      m' = (m.dropCancel c).withCtl [Activation.ofProg none (cancelProg r)] := by
  unfold hostStep? at h
  split at h
  · simp only at h
    split at h
    · rename_i r hc hres
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨r, hc, hres, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

theorem hostStep?_run_inv {p : P E σ (Ret E)} (h : hostStep? hr (.run p) m = some (l, m')) :
    l = .host (.run p) ∧ m' = m.withCtl [Activation.ofProg none (runProg p)] := by
  unfold hostStep? at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · cases h

end HostInv

/-- **Soundness of `hostStep?`**: every executable host event is a relational host step, in
every profile. -/
theorem hostStep?_sound (prof : ProfileKind) (hr : HostReady σ)
    (dispatch : Call E → P E σ (Ret E)) {ev : HostEvent E σ} {m : Config E σ} {l : Label E σ}
    {m' : Config E σ} (h : hostStep? hr ev m = some (l, m')) :
    Step prof hr dispatch m l m' := by
  have hrdy : StepDefs.HostReadyCfg m := hostStep?_enabled h
  cases ev with
  | invoke c f args =>
    obtain ⟨rfl, hfresh, rfl⟩ : l = .host (.invoke c f args) ∧ (∀ x ∈ m.pending, x.1 ≠ c) ∧
        m' = _ := hostStep?_invoke_inv h
    exact .hostInvoke hrdy hfresh
  | tick =>
    obtain ⟨rfl, rfl⟩ : l = .host .tick ∧ m' = _ := hostStep?_tick_inv h
    exact .hostTick hrdy
  | cancel c =>
    obtain ⟨r, hc, hres, rfl, rfl⟩ : ∃ r, m.cancel? c = some r ∧ m.result? c = none ∧
        l = .host (.cancel c) ∧ m' = (m.dropCancel c).withCtl [Activation.ofProg none
          (cancelProg r)] := hostStep?_cancel_inv h
    exact .hostCancel hrdy hc hres
  | run p =>
    obtain ⟨rfl, rfl⟩ : l = .host (.run p) ∧ m' = _ := hostStep?_run_inv h
    exact .hostRun hrdy

section Drivers

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

theorem runLoop_sound (n : Nat) (st : o.State) (m : Config E σ) (acc : List (Label E σ)) :
    ∃ tr, (runLoop hr dispatch X o n st m acc).labels = acc.reverse ++ tr ∧
      Steps o.prof hr dispatch m tr (runLoop hr dispatch X o n st m acc).config := by
  induction n generalizing st m acc with
  | zero => exact ⟨[], by simp [runLoop], .refl _⟩
  | succ n ih =>
    cases e : step? dispatch X (o.at st) m with
    | none => exact ⟨[], by simp [runLoop, e], by simpa [runLoop, e] using .refl _⟩
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      obtain ⟨tr, h₁, h₂⟩ := ih st' m' (l :: acc)
      refine ⟨l :: tr, ?_, ?_⟩
      · simp only [runLoop, e, h₁, List.reverse_cons, List.append_assoc, List.singleton_append]
      · simp only [runLoop, e]
        exact .cons (step?_sound hr dispatch X (o.at st) e) h₂

/-- **Soundness of `run`**: the label trace of a bounded run is a relational trace from the
start configuration to the final one. -/
theorem run_sound (fuel : Nat) (m : Config E σ) :
    Steps o.prof hr dispatch m (run hr dispatch X o fuel m).labels
      (run hr dispatch X o fuel m).config := by
  obtain ⟨tr, h₁, h₂⟩ := runLoop_sound hr dispatch X o fuel o.state m []
  simp only [run, h₁, List.reverse_nil, List.nil_append]
  exact h₂

theorem runTopLoop_sound (n : Nat) (st : o.State) (m : Config E σ) (acc : List (Label E σ)) :
    ∃ tr, (runTopLoop hr dispatch X o n st m acc).labels = acc.reverse ++ tr ∧
      Steps o.prof hr dispatch m tr (runTopLoop hr dispatch X o n st m acc).config := by
  induction n generalizing st m acc with
  | zero => exact ⟨[], by simp [runTopLoop], .refl _⟩
  | succ n ih =>
    show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
      Steps o.prof hr dispatch m tr (runTopLoop hr dispatch X o (n + 1) st m acc).config
    cases e : step? dispatch X (o.at st) m with
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      obtain ⟨tr, h₁, h₂⟩ := ih st' m' (l :: acc)
      refine ⟨l :: tr, ?_, ?_⟩
      · simp only [runTopLoop, e, h₁, List.reverse_cons, List.append_assoc,
          List.singleton_append]
      · simp only [runTopLoop, e]
        exact .cons (step?_sound hr dispatch X (o.at st) e) h₂
    | none =>
      show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
        Steps o.prof hr dispatch m tr (runTopLoop hr dispatch X o (n + 1) st m acc).config
      by_cases w : wantsTick hr m = true
      · show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
          Steps o.prof hr dispatch m tr (runTopLoop hr dispatch X o (n + 1) st m acc).config
        cases e' : hostStep? hr .tick m with
        | none =>
          exact ⟨[], by simp [runTopLoop, e, w, e'],
            by simpa [runTopLoop, e, w, e'] using .refl _⟩
        | some p =>
          obtain ⟨l, m'⟩ := p
          obtain ⟨tr, h₁, h₂⟩ := ih st m' (l :: acc)
          refine ⟨l :: tr, ?_, ?_⟩
          · simp only [runTopLoop, e, w, e', ↓reduceIte, h₁, List.reverse_cons,
              List.append_assoc, List.singleton_append]
          · simp only [runTopLoop, e, w, e', ↓reduceIte]
            exact .cons (hostStep?_sound o.prof hr dispatch e') h₂
      · exact ⟨[], by simp [runTopLoop, e, w], by simpa [runTopLoop, e, w] using .refl _⟩

/-- **Soundness of `runTopCall`**: the trace starts with the invoke of `c` and is a relational
trace from the start configuration to the final one, in which `c` is pending. -/
theorem runTopCall_sound {fuel : Nat} {c : CallId} {f : FuncId} {args : List Val}
    {m : Config E σ} {r : RunResult E σ o.State}
    (h : runTopCall hr dispatch X o fuel c f args m = some r) :
    ∃ tr, r.labels = .host (.invoke c f args) :: tr ∧
      Steps o.prof hr dispatch m r.labels r.config ∧ (c, f, args) ∈ r.config.pending := by
  obtain ⟨⟨l, m₁⟩, e, hr₁⟩ := Option.map_eq_some_iff.mp h
  have hr₁ : runTopLoop hr dispatch X o fuel o.state m₁ [l] = r := hr₁
  have s₁ : Step o.prof hr dispatch m l m₁ := hostStep?_sound o.prof hr dispatch e
  have hinv := hostStep?_invoke_inv e
  have hl : l = .host (.invoke c f args) := hinv.1
  have hp : (c, f, args) ∈ m₁.pending := by
    rw [hinv.2.2]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨tr, h₁, h₂⟩ := runTopLoop_sound hr dispatch X o fuel o.state m₁ [l]
  have hlab : r.labels = l :: tr := by simpa [hr₁] using h₁
  have hsteps : Steps o.prof hr dispatch m₁ tr r.config := hr₁ ▸ h₂
  refine ⟨tr, hl ▸ hlab, ?_, hsteps.pending_mono hp⟩
  rw [hlab]
  exact .cons s₁ hsteps

end Drivers

end Silmaril.Wasm.Component.Machine
