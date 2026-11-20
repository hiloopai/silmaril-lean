module

public import Silmaril.Proofs.Wasm.Component.Reference.StartInst
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

/-!
# Programs in focus reaching their results, in any context

`Reach th p m Q`: from `m` (not locked down), the program `p` in focus on thread `th`, under
any continuation `f`, segments and rest of the control chain, runs on the machine (without host
events or traps) to `f a` at a configuration `m'` (not locked down) with `Q os a m'`, `os` the
run's observations. Unlike the big-step `RunsQ`, the end may depend on the context, so a
late-bound call answered by a machine run (R4) is a `Reach` (`LinkedGInit.Run`).

* `Reach.pure`, `Reach.bind`, `Reach.mono`: the monad laws;
* `Reach.ofRunsQ`, `Reach.ofSRuns`: big-step runs reach their result;
* `Reach.call`, `Reach.callItems`: a late-bound call whose dispatched program runs silently,
  one answering an export map.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {D : Call E → P E σ (Ret E)}

/-- The labels of a big-step run are `tau` and observations. -/
theorem runsQ_quiet {α : Type} {th : Option ThreadId} {p : P E σ α} {m m' : Config E σ}
    {tr : List (Label E σ)} {a : α} (h : RunsQ D th p m tr a m') :
    ∀ l ∈ tr, l = .tau ∨ ∃ o, l = .obs o := by
  induction h with
  | pure => intro l hl; cases hl
  | get _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | modify _ _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | hostGet _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | hostSet _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | currentThread _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | emit _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inr ⟨_, rfl⟩
    · exact ih l hl
  | newThread _ _ _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | readCore _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | memWrite _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | allocHost _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | prepare _ ih =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih l hl
  | call _ _ ih₁ ih₂ =>
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    rcases List.mem_append.1 hl with hl | hl
    · exact ih₁ l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact .inl rfl
    · exact ih₂ l hl

theorem noHost_of_quiet {tr : List (Label E σ)} (h : ∀ l ∈ tr, l = .tau ∨ ∃ o, l = .obs o) :
    (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) := by
  refine ⟨fun ev hm => ?_, fun r hm => ?_⟩
  · rcases h _ hm with e | ⟨o, e⟩ <;> cases e
  · rcases h _ hm with e | ⟨o, e⟩ <;> cases e

variable (prof hr D) in
/-- **The program `p` in focus reaches a result satisfying `Q`** (of the run's observations, the
result and the configuration reached), in any context. -/
def Reach {α : Type} (th : Option ThreadId) (p : P E σ α) (m : Config E σ)
    (Q : List HostObs → α → Config E σ → Prop) : Prop :=
  m.store.lockdown = false →
  ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
    ∃ (tr : List (Label E σ)) (a : α) (m' : Config E σ),
      Steps prof hr D { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } ∧
      (∀ ev, Label.host ev ∉ tr) ∧ (∀ r, Label.trap r ∉ tr) ∧ m'.store.lockdown = false ∧
      Q (traceObs tr) a m'

namespace Reach

variable {th : Option ThreadId}

theorem mono {α : Type} {p : P E σ α} {m : Config E σ}
    {Q Q' : List HostObs → α → Config E σ → Prop} (h : Reach prof hr D th p m Q)
    (hQ : ∀ os a m', Q os a m' → Q' os a m') : Reach prof hr D th p m Q' := by
  intro hl f segs rest
  obtain ⟨tr, a, m', s, h₁, h₂, hl', hq⟩ := h hl f segs rest
  exact ⟨tr, a, m', s, h₁, h₂, hl', hQ _ a m' hq⟩

theorem pure {α : Type} (a : α) (m : Config E σ) :
    Reach prof hr D th (Pure.pure a : P E σ α) m (fun os b m' => os = [] ∧ b = a ∧ m' = m) := by
  intro hl f segs rest
  refine ⟨[], a, m, ?_, fun _ h => (nomatch h), fun _ h => (nomatch h), hl, rfl, rfl, rfl⟩
  rw [pure_bind]
  exact .refl _

theorem bind {α β : Type} {p : P E σ α} {g : α → P E σ β} {m : Config E σ}
    {Q : List HostObs → α → Config E σ → Prop} {R : List HostObs → β → Config E σ → Prop}
    (h₁ : Reach prof hr D th p m Q)
    (h₂ : ∀ os a m', Q os a m' →
      Reach prof hr D th (g a) m' (fun os' b m'' => R (os ++ os') b m'')) :
    Reach prof hr D th (p >>= g) m R := by
  intro hl f segs rest
  obtain ⟨tr₁, a, m₁, s₁, h₁h, h₁t, hl₁, hQ⟩ := h₁ hl (fun a => g a >>= f) segs rest
  obtain ⟨tr₂, b, m₂, s₂, h₂h, h₂t, hl₂, hR⟩ := h₂ _ a m₁ hQ hl₁ f segs rest
  refine ⟨tr₁ ++ tr₂, b, m₂, ?_, fun ev h => ?_, fun r h => ?_, hl₂, ?_⟩
  · rw [bind_assoc]
    exact Adequacy.steps_append s₁ s₂
  · rcases List.mem_append.1 h with h | h
    · exact h₁h ev h
    · exact h₂h ev h
  · rcases List.mem_append.1 h with h | h
    · exact h₁t r h
    · exact h₂t r h
  · rw [traceObs_append]
    exact hR

/-- `bind` with a first part reaching a determined result silently. -/
theorem bind_eq {α β : Type} {p : P E σ α} {g : α → P E σ β} {m m₁ : Config E σ} {a : α}
    {R : List HostObs → β → Config E σ → Prop}
    (h₁ : Reach prof hr D th p m (fun os b m' => os = [] ∧ b = a ∧ m' = m₁))
    (h₂ : Reach prof hr D th (g a) m₁ R) : Reach prof hr D th (p >>= g) m R := by
  refine bind h₁ fun os b m' ⟨e₁, e₂, e₃⟩ => ?_
  subst e₁ e₂ e₃
  exact h₂.mono fun _ _ _ h => by rwa [List.nil_append]

/-- **A big-step run reaches its result.** -/
theorem ofRunsQ {α : Type} {p : P E σ α} {m m' : Config E σ} {tr : List (Label E σ)} {a : α}
    (h : RunsQ D th p m tr a m') :
    Reach prof hr D th p m (fun os b m'' => os = traceObs tr ∧ b = a ∧ m'' = m') := by
  intro hl f segs rest
  have q := noHost_of_quiet (runsQ_quiet h)
  exact ⟨tr, a, m', (h.lrun (prof := prof) (hr := hr) hl f segs rest).steps,
    q.1, q.2, h.lock.trans hl, rfl, rfl, rfl⟩

/-- **A silent run reaches its result**, with its observations. -/
theorem ofSRuns {α : Type} {p : P E σ α} {m m' : Config E σ} {os : List HostObs} {a : α}
    (h : SRuns p m os a m') :
    Reach prof hr D th p m (fun os' b m'' => os' = os ∧ b = a ∧ m'' = m') := by
  obtain ⟨tr, hr', ho⟩ := SRuns.runsQO (dispatch := D) h th
  exact (ofRunsQ (prof := prof) (hr := hr) hr').mono fun _ _ _ ⟨e, h⟩ => ⟨e.trans ho, h⟩

/-- **A late-bound call reaches the result of its dispatched program**, run silently. -/
theorem call {c : Call E} {m m' : Config E σ} {os : List HostObs} {r : Ret E}
    (h : SRuns (D c) m os r m') :
    Reach prof hr D th (callRet c : P E σ (Ret E)) m
      (fun os' b m'' => os' = os ∧ b = r ∧ m'' = m') := by
  obtain ⟨tr, hr', ho⟩ := SRuns.runsQO (dispatch := D) h th
  have hc : RunsQ D th (callRet c : P E σ (Ret E)) m (.tau :: (tr ++ [.tau])) r m' := by
    unfold callRet perform Prog.lift
    exact RunsQ.call hr' (RunsQ.pure _ _)
  have e : traceObs (.tau :: (tr ++ [.tau]) : List (Label E σ)) = os := by
    rw [← ho]
    show (Label.tau :: (tr ++ [Label.tau])).filterMap Label.obs? = tr.filterMap Label.obs?
    rw [List.filterMap_cons_none rfl, List.filterMap_append, List.filterMap_cons_none rfl,
      List.filterMap_nil, List.append_nil]
  exact (ofRunsQ (prof := prof) (hr := hr) hc).mono fun _ _ _ ⟨e', h⟩ => ⟨e'.trans e, h⟩

/-- **A late-bound call answering an export map.** -/
theorem callItems {c : Call E} {m : Config E σ} {Q : List HostObs → Ret E → Config E σ → Prop}
    {R : List HostObs → List (String × Instantiate.ItemVal E) → Config E σ → Prop}
    (h : Reach prof hr D th (callRet c : P E σ (Ret E)) m Q)
    (hQ : ∀ os r m', Q os r m' → ∃ es, r = .items es ∧ R os es m') :
    Reach prof hr D th (Canon.callItems c : P E σ _) m R := by
  unfold Canon.callItems
  refine bind h fun os r m' hq => ?_
  obtain ⟨es, rfl, hR⟩ := hQ os r m' hq
  exact (pure es m').mono fun _ _ _ ⟨e₁, e₂, e₃⟩ => by
    subst e₁ e₂ e₃
    rwa [List.append_nil]

end Reach

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
