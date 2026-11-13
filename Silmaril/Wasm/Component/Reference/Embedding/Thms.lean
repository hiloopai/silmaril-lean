module

public import Silmaril.Wasm.Component.Reference.Embedding.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Defs
public import Silmaril.Wasm.Component.Reference.Instantiate.Root.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.ErrorContext.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Resource.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Stream.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Task.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Builtins.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Callout.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Context.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Dispatch.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Effects.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Flat.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Handles.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lift.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Load.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Lower.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Prog.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Scalar.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Store.Thms
public import Silmaril.Wasm.Component.Reference.Canon.Strings.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Exec.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Soundness.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Step.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Arena.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Store.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.StreamOps.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Task.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Thread.Thms
public import Silmaril.Wasm.Component.Reference.Runtime.Waitable.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Thms
public import Silmaril.Wasm.Component.Reference.Types.Subtype.Check.Thms
public import Silmaril.Wasm.Component.Reference.Validation.Context.Thms
public import Silmaril.Wasm.Component.Reference.Machine.Config.Thms

/-!
# `Embedding`: laws of the component reference

Theorems of the component reference copy `Embedding`, refined out of
`Silmaril.Raw.Wasm.Component.Embedding`: those that other topics use through
`Silmaril.Wasm.Component.Reference.Laws.Thms`, and the laws their proofs need. The other theorems of
the copy stay in the Raw module, which imports this one.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
  _root_.Silmaril.Wasm.Component.Machine
variable {E : CoreEngine} {σ : Type}

theorem mapM_decodeExport?_encodeExport (es : List (String × FuncId)) :
    (es.map encodeExport).mapM decodeExport? = some es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨n, f⟩ := e
    simp [encodeExport, decodeExport?, nameVal, Val.u32, ih]

theorem decodeInstantiated?_instantiatedObs (inst : InstId) (es : List (String × FuncId)) :
    decodeInstantiated? (instantiatedObs inst es) = some (inst, es) := by
  simp only [instantiatedObs, decodeInstantiated?, Val.u32, ite_true,
    mapM_decodeExport?_encodeExport, Option.map_some, Int.toNat_natCast]

theorem runTopCall_outcome' (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E))
    (X : E.Exec) (o : Oracle E) {fuel : Nat} {c : CallId} {f : FuncId} {args : List Val}
    {m : Config E σ} {r : RunResult E σ o.State}
    (h : runTopCall hr dispatch X o fuel c f args m = some r) :
    r.outcome = .outOfFuel ∨ r.outcome = outcomeOf hr r.config := by
  unfold runTopCall at h
  cases e : hostStep? hr (.invoke c f args) m with
  | none => simp [e] at h
  | some p =>
    obtain ⟨l, m₁⟩ := p
    simp only [e, Option.map_some, Option.some.injEq] at h
    subst h
    exact runTopLoop_outcome hr dispatch X o fuel o.state m₁ [l]

end Silmaril.Wasm.Component

namespace Silmaril.Wasm.Component

open _root_.Silmaril.Wasm.Component.Engine _root_.Silmaril.Wasm.Component.Runtime
  _root_.Silmaril.Wasm.Component.Value _root_.Silmaril.Wasm.Component.Canon
  _root_.Silmaril.Wasm.Component.Machine
variable {E : CoreEngine} {σ : Type}

/-- The label of an executable host event is that event. -/
theorem hostStep?_label {hr : HostReady σ} {ev : HostEvent E σ} {m : Config E σ}
    {l : Label E σ} {m₁ : Config E σ} (h : hostStep? hr ev m = some (l, m₁)) :
    l = .host ev := by
  cases ev with
  | invoke c f args => exact (hostStep?_invoke_inv h).1
  | tick => exact (hostStep?_tick_inv h).1
  | cancel c =>
    obtain ⟨_, _, _, hl, _⟩ := hostStep?_cancel_inv h
    exact hl
  | run p => exact (hostStep?_run_inv h).1

theorem hostStep?_run_label {hr : HostReady σ} {p : P E σ (Ret E)} {m : Config E σ}
    {l : Label E σ} {m₁ : Config E σ} (h : hostStep? hr (.run p) m = some (l, m₁)) :
    l = .host (.run p) := hostStep?_label h

section Labels

variable (hr : HostReady σ) (dispatch : Call E → P E σ (Ret E)) (X : E.Exec) (o : Oracle E)

include hr in
/-- An executable internal step never carries a host label. -/
theorem step?_not_host {st : o.State} {m : Config E σ} {l : Label E σ} {st' : o.State}
    {m' : Config E σ} (h : step? dispatch X (o.at st) m = some (l, st', m')) :
    ∀ ev, l ≠ .host ev := by
  intro ev hl
  subst hl
  have hs := step?_sound hr dispatch X (o.at st) h
  have hc : m.ctl = [] := (Step.host_ready hs).1
  rw [step?_nil dispatch X (o.at st) m hc] at h
  cases h

/-- `runLoop` (hence `Machine.run`) adds no host label. -/
theorem runLoop_noHost (n : Nat) (st : o.State) (m : Config E σ) (acc : List (Label E σ)) :
    ∃ tr, (runLoop hr dispatch X o n st m acc).labels = acc.reverse ++ tr ∧
      ∀ ev, Label.host ev ∉ tr := by
  induction n generalizing st m acc with
  | zero => exact ⟨[], by simp [runLoop], by simp⟩
  | succ n ih =>
    cases e : step? dispatch X (o.at st) m with
    | none => exact ⟨[], by simp [runLoop, e], by simp⟩
    | some p =>
      obtain ⟨l, st', m'⟩ := p
      obtain ⟨tr, h₁, h₂⟩ := ih st' m' (l :: acc)
      refine ⟨l :: tr, ?_, ?_⟩
      · simp only [runLoop, e, h₁, List.reverse_cons, List.append_assoc, List.singleton_append]
      · intro ev hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact step?_not_host hr dispatch X o e ev hm.symm
        · exact h₂ ev hm

/-- The labels of `Machine.run` contain no host event. -/
theorem run_noHost (fuel : Nat) (m : Config E σ) :
    ∀ ev, Label.host ev ∉ (Machine.run hr dispatch X o fuel m).labels := by
  obtain ⟨tr, h₁, h₂⟩ := runLoop_noHost hr dispatch X o fuel o.state m []
  simpa [Machine.run, h₁] using h₂

/-- `runTopLoop` adds no host label other than `tick`. -/
theorem runTopLoop_ticks (n : Nat) (st : o.State) (m : Config E σ) (acc : List (Label E σ)) :
    ∃ tr, (runTopLoop hr dispatch X o n st m acc).labels = acc.reverse ++ tr ∧
      ∀ ev, Label.host ev ∈ tr → ev = .tick := by
  induction n generalizing st m acc with
  | zero => exact ⟨[], by simp [runTopLoop], by simp⟩
  | succ n ih =>
    show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
      ∀ ev, Label.host ev ∈ tr → ev = .tick
    cases e : step? dispatch X (o.at st) m with
    | some p =>
      show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
        ∀ ev, Label.host ev ∈ tr → ev = .tick
      obtain ⟨l, st', m'⟩ := p
      obtain ⟨tr, h₁, h₂⟩ := ih st' m' (l :: acc)
      refine ⟨l :: tr, ?_, ?_⟩
      · simp only [runTopLoop, e, h₁, List.reverse_cons, List.append_assoc,
          List.singleton_append]
      · intro ev hm
        rcases List.mem_cons.mp hm with hm | hm
        · exact absurd hm.symm (step?_not_host hr dispatch X o e ev)
        · exact h₂ ev hm
    | none =>
      show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
        ∀ ev, Label.host ev ∈ tr → ev = .tick
      by_cases w : wantsTick hr m = true
      · show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
          ∀ ev, Label.host ev ∈ tr → ev = .tick
        cases e' : hostStep? hr .tick m with
        | none => exact ⟨[], by simp [runTopLoop, e, w, e'], by simp⟩
        | some p =>
          show ∃ tr, (runTopLoop hr dispatch X o (n + 1) st m acc).labels = acc.reverse ++ tr ∧
            ∀ ev, Label.host ev ∈ tr → ev = .tick
          obtain ⟨l, m'⟩ := p
          obtain ⟨tr, h₁, h₂⟩ := ih st m' (l :: acc)
          have hl : l = .host .tick := hostStep?_label e'
          refine ⟨l :: tr, ?_, ?_⟩
          · simp only [runTopLoop, e, w, e', ↓reduceIte, h₁, List.reverse_cons,
              List.append_assoc, List.singleton_append]
          · intro ev hm
            rcases List.mem_cons.mp hm with hm | hm
            · exact Label.host.inj (hm.trans hl)
            · exact h₂ ev hm
      · exact ⟨[], by simp [runTopLoop, e, w], by simp⟩

/-- After its invoke, `runTopCall` issues only ticks. -/
theorem runTopCall_ticks {fuel : Nat} {c : CallId} {f : FuncId} {args : List Val}
    {m : Config E σ} {r : RunResult E σ o.State}
    (h : runTopCall hr dispatch X o fuel c f args m = some r) :
    ∃ tr, r.labels = .host (.invoke c f args) :: tr ∧
      ∀ ev, Label.host ev ∈ tr → ev = .tick := by
  unfold runTopCall at h
  cases e : hostStep? hr (.invoke c f args) m with
  | none => simp [e] at h
  | some p =>
    obtain ⟨l, m₁⟩ := p
    simp only [e, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨tr, h₁, h₂⟩ := runTopLoop_ticks hr dispatch X o fuel o.state m₁ [l]
    refine ⟨tr, ?_, h₂⟩
    rw [h₁, hostStep?_label e]
    rfl

end Labels

/-- The three classifications of `callOutcome?`. -/
theorem callOutcome?_eq_some {S : Type} {c : CallId} {r : RunResult E σ S} {out : CallOutcome}
    (ho : callOutcome? c r = some out) :
    (r.outcome = .resolved ∧ ∃ res, r.config.result? c = some res ∧ out = .resolved res) ∨
      (r.outcome = .trap ∧ r.labels.any Label.isInternalTrap = false ∧ out = .trap) ∨
      (r.outcome = .deadlock ∧ r.config.result? c = none ∧ out = .deadlock) := by
  unfold callOutcome? at ho
  split at ho
  · rename_i hk
    obtain ⟨res, h1, h2⟩ := Option.map_eq_some_iff.mp ho
    exact .inl ⟨hk, res, h1, h2.symm⟩
  · rename_i hk
    split at ho
    · cases ho
    · exact .inr (.inl ⟨hk, Bool.eq_false_iff.mpr ‹_›, (Option.some.inj ho).symm⟩)
  · rename_i hk
    split at ho
    · exact .inr (.inr ⟨hk, Option.isNone_iff_eq_none.mp ‹_›, (Option.some.inj ho).symm⟩)
    · cases ho
  · cases ho

/-- What `callOutcome?` reports holds of the final configuration of a run whose outcome is
`outOfFuel` or the outcome of its final configuration. -/
theorem callOutcome?_holds {S : Type} (hr : HostReady σ) {c : CallId} {r : RunResult E σ S}
    {out : CallOutcome} (hout : r.outcome = .outOfFuel ∨ r.outcome = outcomeOf hr r.config)
    (ho : callOutcome? c r = some out) : out.Holds hr c r.config := by
  have hof (k : Outcome) (hk : r.outcome = k) (hne : k ≠ .outOfFuel) : outcomeOf hr r.config = k :=
    (hout.resolve_left fun e => hne (hk.symm.trans e)).symm.trans hk
  rcases callOutcome?_eq_some ho with ⟨hk, res, hres, hout⟩ | ⟨hk, -, hout⟩ | ⟨hk, hres, hout⟩
  · have hR : Resolved r.config := outcomeOf_resolved hr (hof _ hk nofun)
    rw [hout]
    exact ⟨hR.1, hR.2.1, hres⟩
  · rw [hout]
    exact outcomeOf_trap hr (hof _ hk nofun)
  · rw [hout]
    exact ⟨outcomeOf_deadlock hr (hof _ hk nofun), hres⟩

namespace Embedder

variable [∀ a b, Decidable (E.ExternSub a b)] (emb : Embedder E σ) (o : Oracle E)

/-- **Soundness of `callTop`**: a classified executable top-level call is a `Calls` fact. -/
theorem callTop_sound {fuel : Nat} {c : CallId} {f : FuncId} {args : List Val}
    {m : Config E σ} {r : RunResult E σ o.State} {out : CallOutcome}
    (h : emb.callTop o fuel c f args m = some r) (ho : callOutcome? c r = some out) :
    Calls o.prof emb.hr emb.dispatch m c f args r.config out := by
  obtain ⟨tr, hl, hs, _⟩ := runTopCall_sound emb.hr emb.dispatch emb.X o h
  obtain ⟨tr', hl', ht⟩ := runTopCall_ticks emb.hr emb.dispatch emb.X o h
  have htr : tr' = tr := (List.cons.inj (hl'.symm.trans hl)).2
  have hticks : ∀ ev, Label.host ev ∈ tr → ev = .tick := htr ▸ ht
  have hint : out = .trap → ∀ msg, Label.trap (.internal msg) ∉ tr := by
    intro hout msg hm
    have hno : r.labels.any Label.isInternalTrap = false := by
      rcases callOutcome?_eq_some ho with ⟨_, _, _, h'⟩ | ⟨_, hn, _⟩ | ⟨_, _, h'⟩
      · exact absurd (hout.symm.trans h') nofun
      · exact hn
      · exact absurd (hout.symm.trans h') nofun
    have hyes : r.labels.any Label.isInternalTrap = true := by
      rw [hl]
      exact List.any_eq_true.mpr ⟨_, List.mem_cons_of_mem _ hm, rfl⟩
    exact absurd hyes (by simp [hno])
  have hholds : out.Holds emb.hr c r.config :=
    callOutcome?_holds emb.hr (runTopCall_outcome' emb.hr emb.dispatch emb.X o h) ho
  exact ⟨tr, hl ▸ hs, fun ev hm => .inl (hticks ev hm), hint, hholds⟩

/-- An instantiation run with a result: the host event, then a finished internal run whose
observations report the result. -/
theorem instantiateRun_inv {fuel : Nat} {c : Syntax.Component E.Module}
    {args : Instantiate.Exports E} {m : Config E σ} {r : RunResult E σ o.State}
    {inst : InstId} {es : List (String × FuncId)}
    (h : emb.instantiateRun o fuel c args m = some (r, inst, es)) :
    ∃ l m₁, hostStep? emb.hr (instantiateTop c args) m = some (l, m₁) ∧
      let r₁ := Machine.run emb.hr emb.dispatch emb.X o fuel m₁
      (r₁.config.ctl = [] ∧ r₁.config.store.lockdown = false) ∧
        (traceObs r₁.labels).findSome? decodeInstantiated? = some (inst, es) ∧
        r = { r₁ with labels := l :: r₁.labels } := by
  unfold instantiateRun at h
  split at h
  · cases h
  · rename_i l m₁ e
    dsimp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨l, m₁, e, ‹_›, ‹_›, rfl⟩
      · cases h
    · cases h

/-- **Soundness of `instantiateRun`**: an executable instantiation with a result is an
`Instantiates` fact about the final configuration. -/
theorem instantiateRun_sound {fuel : Nat} {c : Syntax.Component E.Module}
    {args : Instantiate.Exports E} {m : Config E σ} {r : RunResult E σ o.State}
    {inst : InstId} {es : List (String × FuncId)}
    (h : emb.instantiateRun o fuel c args m = some (r, inst, es)) :
    Instantiates o.prof emb.hr emb.dispatch m c args r.config inst es := by
  obtain ⟨l, m₁, e, hfin, hfind, hr⟩ := emb.instantiateRun_inv o h
  have hl : l = .host (instantiateTop c args) := hostStep?_run_label e
  have s₁ : Step o.prof emb.hr emb.dispatch m l m₁ :=
    hostStep?_sound o.prof emb.hr emb.dispatch e
  have hs : Steps o.prof emb.hr emb.dispatch m₁
      (Machine.run emb.hr emb.dispatch emb.X o fuel m₁).labels
      (Machine.run emb.hr emb.dispatch emb.X o fuel m₁).config :=
    Machine.run_sound emb.hr emb.dispatch emb.X o fuel m₁
  rw [hr]
  exact ⟨_, .cons (hl ▸ s₁) hs, run_noHost emb.hr emb.dispatch emb.X o fuel m₁, hfin.1, hfin.2,
    hfind⟩

end Embedder

end Silmaril.Wasm.Component
