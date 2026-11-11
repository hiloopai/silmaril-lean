module

public import Silmaril.Wasm.Game.Start.Defs
public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Diverge

/-!
# The start phase of the closed program is the Core start run

For every profile `P`, the instantiation phase of the closed program
`I.closedInstLTST P s t₀ K` (the environment's `K.dlts` below
`I.instSysT P s t₀`) runs the instantiation configuration `t₀.config s`
under the induced host `hostOf I.imports K`, step for step:

* `IRel c x` relates a Core configuration with a state of the instantiation
  phase: an instantiating state `(none, inst (s, t))` with the configuration
  of its thread, a state waiting for the environment's answer to `e`
  `(some e, iwait e _)` with the configuration stopped at the callout of `e`.
* Silent runs of the composite are Core runs and conversely
  (`steps_of_silent`, `silent_of_steps`); divergence is divergence
  (`diverges_iff`; both directions by coinduction, as in
  `Silmaril.Proofs.Wasm.Game.DivAdequacy.Diverge`).
* The answer to the instantiation question comes from a finished
  instantiating state (`ans_step_inv`).

Hence the instantiation traces are the Core start runs to results
(`traces_inst_iff`), the divergence after `[askInst]` is Core divergence of the
start run (`div_inst_iff`), and a run past a successful instantiation is a
Core start run to `values []` followed by a run from the persisted store
(`run_ready_iff`).

New proofs; the correspondence follows `DivAdequacy.Diverge` (no determinism
is used).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.Start

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game Silmaril.Proofs.Wasm.Game.ScalarInstance Silmaril
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {I : ScalarInstance} {P : Profile} {s₀ : Store Nat} {t₀ : Thread}
  {K : Silmaril.Wasm.Game.Env I.E}

/-- The closed program with its start phase, as a transition system
(`I.closedInstLTST P s₀ t₀ K`, `closedInstLTST_eq`). -/
noncomputable abbrev CI (I : ScalarInstance) (P : Profile) (s₀ : Store Nat) (t₀ : Thread)
    (K : Silmaril.Wasm.Game.Env I.E) : LTS Sig.empty (I.F.withInst (Behaviour Val)) :=
  K.dlts.comp (I.instSysT P s₀ t₀).toLTS

theorem closedInstLTS_eq {start : Option Nat} :
    I.closedInstLTS P s₀ start K = CI I P s₀ (startThread start) K := rfl

theorem closedInstLTST_eq : I.closedInstLTST P s₀ t₀ K = CI I P s₀ t₀ K := rfl

/-- Steps of the closed program are composite steps. -/
theorem ci_step {x : (CI I P s₀ t₀ K).State} {l : Option (Move Sig.empty (I.F.withInst (Behaviour Val)))}
    {y : (CI I P s₀ t₀ K).State} (h : (CI I P s₀ t₀ K).step x l y) :
    LTS.CompStep K.dlts (I.instSysT P s₀ t₀).toLTS x l y := h

theorem ci_step_inst {s : Store Nat} {t : Thread}
    {l : Option (Move Sig.empty (I.F.withInst (Behaviour Val)))} {y : (CI I P s₀ t₀ K).State}
    (h : (CI I P s₀ t₀ K).step (none, .inst (s, t)) l y) :
    LTS.CompStep K.dlts (I.instSysT P s₀ t₀).toLTS (none, .inst (s, t)) l y := h

theorem ci_step_iwait {e : I.E.Op} {k : I.E.Ar e → Store Nat × Thread}
    {l : Option (Move Sig.empty (I.F.withInst (Behaviour Val)))} {y : (CI I P s₀ t₀ K).State}
    (h : (CI I P s₀ t₀ K).step (some e, .iwait e k) l y) :
    LTS.CompStep K.dlts (I.instSysT P s₀ t₀).toLTS (some e, .iwait e k) l y := h

theorem ci_step_ready {s : Store Nat}
    {l : Option (Move Sig.empty (I.F.withInst (Behaviour Val)))} {y : (CI I P s₀ t₀ K).State}
    (h : (CI I P s₀ t₀ K).step (none, .ready s) l y) :
    LTS.CompStep K.dlts (I.instSysT P s₀ t₀).toLTS (none, .ready s) l y := h

/-- A host answer to the import call `e` is an answer of the environment, the store
unchanged. -/
theorem hostOf_returned {h : Nat} {args : List Val} {e : I.E.Op} {s s' : Store Nat}
    {r : Result} (hop : I.importOp? h args = some e)
    (hr : hostOf I.imports K h s args (.returned s' r)) :
    ∃ w, K.Answers e w ∧ s = s' ∧ Answer.toResult (ft := I.imports.get e.1) w = r := by
  rcases hostOf_op_eq hop hr with ⟨w, hw, hout⟩ | ⟨-, hout⟩
  · obtain ⟨h₁, h₂⟩ := Execution.Host.Outcome.returned.inj hout
    exact ⟨w, hw, h₁.symm, h₂.symm⟩
  · cases hout

/-- An import call of the host is a call of the import question of the callout. -/
theorem hostOf_op {h : Nat} {args : List Val} {s : Store Nat} {out : HostOutcome Nat}
    (hr : hostOf I.imports K h s args out) : ∃ e, I.importOp? h args = some e :=
  let ⟨e, he, _⟩ := hr
  ⟨e, he⟩

/-- States of the closed program with its start phase. -/
abbrev CSt (I : ScalarInstance) (P : Profile) (s₀ : Store Nat) (t₀ : Thread)
    (K : Silmaril.Wasm.Game.Env I.E) : Type :=
  (CI I P s₀ t₀ K).State

/-- The relation between Core configurations and states of the start phase. -/
def IRel (c : Config Nat) (x : CSt I P s₀ t₀ K) : Prop :=
  (∃ (s : Store Nat) (t : Thread), x = (none, .inst (s, t)) ∧ c = t.config s) ∨
  (∃ (s : Store Nat) (t : Thread) (e : I.E.Op),
    x = (some e, .iwait e (I.resumeK s t e)) ∧ c = t.config s ∧ I.CallsOut (s, t) e)

/-- A silent run as a run without visible moves. -/
theorem run_of_silent {E F : Sig.{0}} {L : LTS E F} {x y : L.State}
    (h : Relation.ReflTransGen L.Silent x y) : L.Run x [] y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .nil _
  | head hs _ ih => exact .tau hs ih

/-! ### Core steps from a thread -/

theorem irel_inst (s : Store Nat) (t : Thread) :
    IRel (K := K) (P := P) (s₀ := s₀) (t₀ := t₀) (t.config s) (none, .inst (s, t)) :=
  .inl ⟨s, t, rfl, rfl⟩

theorem irel_iwait {s : Store Nat} {t : Thread} {e : I.E.Op} (hout : I.CallsOut (s, t) e) :
    IRel (K := K) (P := P) (s₀ := s₀) (t₀ := t₀) (t.config s)
      (some e, .iwait e (I.resumeK s t e)) :=
  .inr ⟨s, t, e, rfl, rfl, hout⟩

/-- The import call of a stopped thread is unique. -/
theorem callsOut_unique {s : Store Nat} {t : Thread} {e e' : I.E.Op}
    (h : I.CallsOut (s, t) e) (h' : I.CallsOut (s, t) e') : e = e' := by
  obtain ⟨hh, args, hco, hop⟩ := h
  obtain ⟨hh', args', hco', hop'⟩ := h'
  obtain ⟨rfl, rfl⟩ := calloutAt_unique hco hco'
  exact Option.some.inj (hop.symm.trans hop')

/-- A thread at a callout has no host-free step. -/
theorem callsOut_no_internal {s : Store Nat} {t : Thread} {e : I.E.Op}
    (h : I.CallsOut (s, t) e) (y : Store Nat × Thread) : ¬ InternalP P (s, t) y :=
  let ⟨_, _, hco, _⟩ := h
  calloutAt_no_internal hco y

/-- A host call that `K` never answers diverges. -/
theorem hostOf_diverged {h : Nat} {args : List Val} {e : I.E.Op} {s : Store Nat}
    (hop : I.importOp? h args = some e) (hr : hostOf I.imports K h s args .diverged) :
    ∀ w, ¬ K.Answers e w := by
  rcases hostOf_op_eq hop hr with ⟨w, -, hout⟩ | ⟨hno, -⟩
  · cases hout
  · exact hno

/-- **A Core step from a thread** under the induced host: a host-free step, an import call
answered by `K`, or an import call that `K` never answers (a Core self-loop). -/
theorem core_step_cases {s : Store Nat} {t : Thread} {c₁ : Config Nat}
    (hst : Step P (hostOf I.imports K) (t.config s) c₁) :
    (∃ c', InternalP P (s, t) c' ∧ c₁ = c'.2.config c'.1) ∨
    ∃ e, I.CallsOut (s, t) e ∧ ((∃ w, K.Answers e w ∧ c₁ = (I.resumeK s t e w).2.config s) ∨
      ((∀ w, ¬ K.Answers e w) ∧ c₁ = t.config s)) := by
  rcases (stepP_iff P _ s t c₁).1 hst with ⟨s', f', code', hc, hi⟩ |
    ⟨E, a, h, args, hd, ⟨s', r, hr, hc⟩ | ⟨hdiv, hc⟩⟩
  · exact .inl ⟨_, hi, hc⟩
  · obtain ⟨e, hop⟩ := hostOf_op hr
    obtain ⟨w, hw, hs, hr'⟩ := hostOf_returned hop hr
    have hc' : c₁ = (I.resumeK s t e w).2.config s := by rw [hc, ← hs, ← hr']; rfl
    exact .inr ⟨e, ⟨h, args, ⟨E, a, hd⟩, hop⟩, .inl ⟨w, hw, hc'⟩⟩
  · obtain ⟨e, hop⟩ := hostOf_op hdiv
    exact .inr ⟨e, ⟨h, args, ⟨E, a, hd⟩, hop⟩, .inr ⟨hostOf_diverged hop hdiv, hc⟩⟩

/-- The Core step of an import call answered by `K`. -/
theorem core_step_answer {s : Store Nat} {t : Thread} {e : I.E.Op} {w : I.E.Ar e}
    (hout : I.CallsOut (s, t) e) (hw : K.Answers e w) :
    Step P (hostOf I.imports K) (t.config s) ((I.resumeK s t e w).2.config s) :=
  let ⟨_, _, hco, hop⟩ := hout
  calloutAt_step hco ⟨e, hop, .inl ⟨_, hw, rfl⟩⟩

/-- The Core self-loop of an import call that `K` never answers. -/
theorem core_step_loop {s : Store Nat} {t : Thread} {e : I.E.Op}
    (hout : I.CallsOut (s, t) e) (hno : ∀ w, ¬ K.Answers e w) :
    Step P (hostOf I.imports K) (t.config s) (t.config s) :=
  let ⟨h, args, ⟨E, a, hdc⟩, hop⟩ := hout
  (stepP_iff P _ s t _).2 (.inr ⟨E, a, h, args, hdc, .inr ⟨⟨e, hop, .inr ⟨hno, rfl⟩⟩, rfl⟩⟩)

/-! ### Silent steps of the start phase -/

theorem ci_itau {s : Store Nat} {t : Thread} {c' : Store Nat × Thread}
    (hi : InternalP P (s, t) c') :
    (CI I P s₀ t₀ K).step (none, .inst (s, t)) none (none, .inst c') :=
  .tau₂ (InstSystem.Step.itau hi)

theorem ci_ask {s : Store Nat} {t : Thread} {e : I.E.Op} (hout : I.CallsOut (s, t) e) :
    (CI I P s₀ t₀ K).step (none, .inst (s, t)) none (some e, .iwait e (I.resumeK s t e)) :=
  .sync (Ev.ask e) (Silmaril.Wasm.Game.Env.DStep.ask e) (InstSystem.Step.icall ⟨hout, rfl⟩)

theorem ci_ans {s : Store Nat} {t : Thread} {e : I.E.Op} {w : I.E.Ar e} (hw : K.Answers e w) :
    (CI I P s₀ t₀ K).step (some e, .iwait e (I.resumeK s t e)) none
      (none, .inst (I.resumeK s t e w)) :=
  .sync (Ev.ans e w) (Silmaril.Wasm.Game.Env.DStep.ans hw) (InstSystem.Step.iresume _ _ w)

theorem ci_loop {e : I.E.Op} {k : I.E.Ar e → Store Nat × Thread} (hno : ∀ w, ¬ K.Answers e w) :
    (CI I P s₀ t₀ K).step (some e, .iwait e k) none (some e, .iwait e k) :=
  .tau₁ (Silmaril.Wasm.Game.Env.DStep.loop hno)

/-- The silent steps of an instantiating state. -/
theorem silent_inst_cases {s : Store Nat} {t : Thread} {y : CSt I P s₀ t₀ K}
    (hs : (CI I P s₀ t₀ K).step (none, .inst (s, t)) none y) :
    (∃ c', InternalP P (s, t) c' ∧ y = (none, .inst c')) ∨
      ∃ e, I.CallsOut (s, t) e ∧ y = (some e, .iwait e (I.resumeK s t e)) := by
  cases ci_step_inst hs with
  | tau₁ hk => cases hk
  | tau₂ hi => cases hi with | itau hint => exact .inl ⟨_, hint, rfl⟩
  | sync g hk hi =>
    cases hk with
    | ask e => cases hi with | icall hcall => exact .inr ⟨e, hcall.1, by rw [hcall.2]; rfl⟩

/-- The silent steps of a waiting state. -/
theorem silent_iwait_cases {s : Store Nat} {t : Thread} {e : I.E.Op}
    {y : CSt I P s₀ t₀ K} (hs : (CI I P s₀ t₀ K).step (some e, .iwait e (I.resumeK s t e)) none y) :
    ((∀ w, ¬ K.Answers e w) ∧ y = (some e, .iwait e (I.resumeK s t e))) ∨
      ∃ w, K.Answers e w ∧ y = (none, .inst (I.resumeK s t e w)) := by
  cases ci_step_iwait hs with
  | tau₁ hk => cases hk with | loop hno => exact .inl ⟨hno, rfl⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hw => cases hi with | iresume _ _ _ => exact .inr ⟨_, hw, rfl⟩

/-! ### Silent steps are Core steps -/

/-- One silent step of the start phase is at most one Core step. -/
theorem silent_step {c : Config Nat} {x y : CSt I P s₀ t₀ K} (hc : IRel c x)
    (hs : (CI I P s₀ t₀ K).step x none y) :
    ∃ c', IRel c' y ∧ Steps P (hostOf I.imports K) c c' := by
  rcases hc with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, hout⟩
  · rcases silent_inst_cases hs with ⟨c', hi, rfl⟩ | ⟨e, hout, rfl⟩
    · exact ⟨_, irel_inst _ _, .single (InternalP.toStep P _ hi)⟩
    · exact ⟨_, irel_iwait hout, .refl⟩
  · rcases silent_iwait_cases hs with ⟨-, rfl⟩ | ⟨w, hw, rfl⟩
    · exact ⟨_, irel_iwait hout, .refl⟩
    · exact ⟨_, irel_inst _ _, .single (core_step_answer hout hw)⟩

/-- **Silent runs of the start phase are Core runs.** -/
theorem steps_of_silent {c : Config Nat} {x y : CSt I P s₀ t₀ K} (hc : IRel c x)
    (h : Relation.ReflTransGen (CI I P s₀ t₀ K).Silent x y) :
    ∃ c', IRel c' y ∧ Steps P (hostOf I.imports K) c c' := by
  induction h with
  | refl => exact ⟨c, hc, .refl⟩
  | tail _ hs ih =>
    obtain ⟨c₁, h₁, hst₁⟩ := ih
    obtain ⟨c₂, h₂, hst₂⟩ := silent_step h₁ hs
    exact ⟨c₂, h₂, hst₁.trans hst₂⟩

/-! ### Core steps are silent runs -/

/-- One Core step from a related configuration is a silent run of the start phase. -/
theorem silent_of_step {c c₁ : Config Nat} {x : CSt I P s₀ t₀ K} (hc : IRel c x)
    (hst : Step P (hostOf I.imports K) c c₁) :
    ∃ y, Relation.ReflTransGen (CI I P s₀ t₀ K).Silent x y ∧ IRel c₁ y := by
  rcases hc with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, hout⟩
  · rcases core_step_cases hst with ⟨c', hi, rfl⟩ | ⟨e, hout, ⟨w, hw, rfl⟩ | ⟨-, rfl⟩⟩
    · exact ⟨_, .single (ci_itau hi), irel_inst _ _⟩
    · exact ⟨_, .tail (.single (ci_ask hout)) (ci_ans hw), irel_inst _ _⟩
    · exact ⟨_, .refl, irel_inst _ _⟩
  · rcases core_step_cases hst with ⟨c', hi, -⟩ | ⟨e', hout', ⟨w, hw, rfl⟩ | ⟨-, rfl⟩⟩
    · exact absurd hi (callsOut_no_internal hout _)
    · obtain rfl : e' = e := callsOut_unique hout' hout
      exact ⟨_, .single (ci_ans hw), irel_inst _ _⟩
    · exact ⟨_, .refl, irel_iwait hout⟩

/-- **Core runs are silent runs of the start phase.** -/
theorem silent_of_steps {c c' : Config Nat} (h : Steps P (hostOf I.imports K) c c') :
    ∀ {x : CSt I P s₀ t₀ K}, IRel c x →
      ∃ y, Relation.ReflTransGen (CI I P s₀ t₀ K).Silent x y ∧ IRel c' y := by
  induction h with
  | refl => exact fun hc => ⟨_, .refl, hc⟩
  | tail _ hst ih =>
    intro x hc
    obtain ⟨y₁, h₁, hy₁⟩ := ih hc
    obtain ⟨y₂, h₂, hy₂⟩ := silent_of_step hy₁ hst
    exact ⟨y₂, h₁.trans h₂, hy₂⟩

/-! ### Divergence -/

/-- From a related state of an infinitely running configuration, a silent step to a related
state of an infinitely running configuration. -/
theorem cmp_step_of_inf {c : Config Nat} {x : CSt I P s₀ t₀ K} (hc : IRel c x)
    (hinf : InfiniteTrace (Step P (hostOf I.imports K)) c) :
    ∃ y, (CI I P s₀ t₀ K).step x none y ∧
      ∃ c', IRel c' y ∧ InfiniteTrace (Step P (hostOf I.imports K)) c' := by
  obtain ⟨c₁, hst, hinf₁⟩ := hinf.unfold
  rcases hc with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, hout⟩
  · rcases core_step_cases hst with ⟨c', hi, rfl⟩ | ⟨e, hout, -⟩
    · exact ⟨_, ci_itau hi, _, irel_inst _ _, hinf₁⟩
    · exact ⟨_, ci_ask hout, _, irel_iwait hout, hinf⟩
  · rcases core_step_cases hst with ⟨c', hi, -⟩ | ⟨e', hout', ⟨w, hw, rfl⟩ | ⟨hno, rfl⟩⟩
    · exact absurd hi (callsOut_no_internal hout _)
    · obtain rfl : e' = e := callsOut_unique hout' hout
      exact ⟨_, ci_ans hw, _, irel_inst _ _, hinf₁⟩
    · obtain rfl : e' = e := callsOut_unique hout' hout
      exact ⟨_, ci_loop hno, _, irel_iwait hout, hinf₁⟩

/-- From a diverging waiting state, a Core step to a related diverging state. -/
theorem core_step_waiting {s : Store Nat} {t : Thread} {e : I.E.Op}
    (hout : I.CallsOut (s, t) e)
    (hd : (CI I P s₀ t₀ K).Diverges (some e, .iwait e (I.resumeK s t e))) :
    ∃ c₁, Step P (hostOf I.imports K) (t.config s) c₁ ∧
      ∃ x₁, IRel c₁ x₁ ∧ (CI I P s₀ t₀ K).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  rcases silent_iwait_cases hs with ⟨hno, rfl⟩ | ⟨w, hw, rfl⟩
  · exact ⟨_, core_step_loop hout hno, _, irel_iwait hout, hd₁⟩
  · exact ⟨_, core_step_answer hout hw, _, irel_inst _ _, hd₁⟩

/-- From a diverging related state, a Core step to a related diverging state. -/
theorem core_step_of_div {c : Config Nat} {x : CSt I P s₀ t₀ K} (hc : IRel c x)
    (hd : (CI I P s₀ t₀ K).Diverges x) :
    ∃ c₁, Step P (hostOf I.imports K) c c₁ ∧
      ∃ x₁, IRel c₁ x₁ ∧ (CI I P s₀ t₀ K).Diverges x₁ := by
  rcases hc with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, hout⟩
  · obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
    rcases silent_inst_cases hs with ⟨c', hi, rfl⟩ | ⟨e, hout, rfl⟩
    · exact ⟨_, InternalP.toStep P _ hi, _, irel_inst _ _, hd₁⟩
    · exact core_step_waiting hout hd₁
  · exact core_step_waiting hout hd

/-- **Divergence of the start phase is Core divergence.** -/
theorem diverges_iff {c : Config Nat} {x : CSt I P s₀ t₀ K} (hc : IRel c x) :
    (CI I P s₀ t₀ K).Diverges x ↔ InfiniteTrace (Step P (hostOf I.imports K)) c := by
  constructor
  · intro hd
    refine InfiniteTrace.coinduct
      (fun c => ∃ x, IRel (P := P) (s₀ := s₀) (t₀ := t₀) (K := K) c x ∧
        (CI I P s₀ t₀ K).Diverges x) ?_ ⟨x, hc, hd⟩
    rintro c ⟨x, hx, hdx⟩
    exact core_step_of_div hx hdx
  · intro hinf
    refine InfiniteTrace.coinduct
      (fun x => ∃ c, IRel c x ∧ InfiniteTrace (Step P (hostOf I.imports K)) c) ?_ ⟨c, hc, hinf⟩
    rintro x ⟨c, hx, hic⟩
    exact cmp_step_of_inf hx hic

/-! ### The instantiation answer -/

/-- The answer to the instantiation question comes from a finished instantiating state. -/
theorem ans_step_inv {c : Config Nat} {x z : CSt I P s₀ t₀ K}
    {a : InstAns (Behaviour Val)} (hc : IRel c x)
    (hs : (CI I P s₀ t₀ K).step x (some (ansInst a)) z) :
    ∃ (s : Store Nat) (t : Thread), x = (none, .inst (s, t)) ∧ c = t.config s ∧
      ((a = .ready ∧ ResultAt s t (.values []) ∧ z = (none, .ready s)) ∨
        ∃ b, a = .fail b ∧ StartFailed (s, t) b ∧ z = (none, .dead)) := by
  rcases hc with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, -⟩
  · cases ci_step_inst hs with
    | right g hi =>
      cases hi with
      | iready hr =>
        obtain ⟨hres, hst⟩ := hr
        exact ⟨s, t, rfl, rfl, .inl ⟨rfl, hres, by rw [hst]; rfl⟩⟩
      | ifail hf => exact ⟨s, t, rfl, rfl, .inr ⟨_, rfl, hf, rfl⟩⟩
  · cases ci_step_iwait hs with
    | right g hi => cases hi

/-- The state reached by the question `askInst` from the initial state. -/
theorem run_askInst_inv {y : CSt I P s₀ t₀ K}
    (h : (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init [askInst] y) :
    Relation.ReflTransGen (CI I P s₀ t₀ K).Silent (none, .inst (s₀, t₀)) y := by
  cases h with
  | tau hs _ =>
    cases hs with
    | tau₁ hk => cases hk
    | tau₂ hi => cases hi
    | sync g hk hi => cases hk with | ask e => cases hi
  | vis hs hr =>
    cases hs with
    | right g hi =>
      cases hi with
      | askInst => exact silent_of_run_nil hr rfl

/-- The initial instantiating state is related to the start configuration. -/
theorem irel_init :
    IRel (I := I) (P := P) (s₀ := s₀) (t₀ := t₀) (K := K) (t₀.config s₀)
      (none, .inst (s₀, t₀)) :=
  .inl ⟨_, _, rfl, rfl⟩

/-- A ready state has no silent step. -/
theorem ready_silent {s : Store Nat} {y : CSt I P s₀ t₀ K}
    (h : Relation.ReflTransGen (CI I P s₀ t₀ K).Silent (none, .ready s) y) :
    y = (none, .ready s) := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    cases ci_step_ready hs with
    | tau₁ hk => cases hk
    | tau₂ hi => cases hi
    | sync g hk hi => cases hk with | ask e => cases hi

/-- The outcome of the instantiation question for a Core result. -/
def InstAnsOf (r : Result) (a : InstAns (Behaviour Val)) : Prop :=
  (r = .values [] ∧ a = .ready) ∨ ((r = .trap ∨ ∃ x, r = .throw x) ∧ a = .fail r.toBehaviour)

/-- An instantiating state related to a finished configuration answers. -/
theorem ans_step_of_result {s : Store Nat} {t : Thread} {r : Result}
    {a : InstAns (Behaviour Val)} (hr : (t.config s).code = r.toAdmin) (ha : InstAnsOf r a) :
    ∃ z, (CI I P s₀ t₀ K).step (none, .inst (s, t)) (some (ansInst a)) z := by
  rcases ha with ⟨rfl, rfl⟩ | ⟨hr', rfl⟩
  · exact ⟨_, .right _ (InstSystem.Step.iready ⟨hr, rfl⟩)⟩
  · rcases hr' with rfl | ⟨x, rfl⟩
    · exact ⟨_, .right _ (InstSystem.Step.ifail (.inl ⟨hr, rfl⟩))⟩
    · exact ⟨_, .right _ (InstSystem.Step.ifail (.inr ⟨x, hr, rfl⟩))⟩

/-- A related state of a finished configuration is instantiating. -/
theorem irel_result {c : Config Nat} {y : CSt I P s₀ t₀ K} {r : Result} (hy : IRel c y)
    (hr : c.code = r.toAdmin) : ∃ (s : Store Nat) (t : Thread), y = (none, .inst (s, t)) ∧
      c = t.config s := by
  rcases hy with ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, rfl, rfl, h, args, hco, -⟩
  · exact ⟨s, t, rfl, rfl⟩
  · exact absurd hco (resultAt_not_calloutAt hr)

/-- The answer to the instantiation question read off a step. -/
theorem instAnsOf_of_step {c : Config Nat} {x z : CSt I P s₀ t₀ K}
    {a : InstAns (Behaviour Val)} (hc : IRel c x)
    (hs : (CI I P s₀ t₀ K).step x (some (ansInst a)) z) :
    ∃ r, c.code = r.toAdmin ∧ InstAnsOf r a ∧
      (a = .ready → z = (none, .ready c.store)) := by
  obtain ⟨s, t, rfl, rfl, ⟨rfl, hres, rfl⟩ | ⟨b, rfl, hf, rfl⟩⟩ := ans_step_inv hc hs
  · exact ⟨_, hres, .inl ⟨rfl, rfl⟩, fun _ => by rw [Thread.config_store]⟩
  · rcases hf with ⟨hres, rfl⟩ | ⟨x, hres, rfl⟩
    · exact ⟨_, hres, .inr ⟨.inl rfl, rfl⟩, fun h => by cases h⟩
    · exact ⟨_, hres, .inr ⟨.inr ⟨x, rfl⟩, rfl⟩, fun h => by cases h⟩

/-! ### Traces of the instantiation phase -/

/-- **Instantiation traces are Core start runs to results.** -/
theorem traces_inst_iff {a : InstAns (Behaviour Val)} :
    [askInst, ansInst a] ∈ (CI I P s₀ t₀ K).Traces ↔
      ∃ (c' : Config Nat) (r : Result),
        Steps P (hostOf I.imports K) (t₀.config s₀) c' ∧ c'.code = r.toAdmin ∧
          InstAnsOf r a := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy, hr⟩ := LTS.Run.of_append (s := [askInst]) (t := [ansInst a]) hz
    obtain ⟨x₁, x₂, h₁, h₂, -⟩ := LTS.Run.cons_inv hr
    have hsil : Relation.ReflTransGen (CI I P s₀ t₀ K).Silent
        (none, .inst (s₀, t₀)) x₁ :=
      (run_askInst_inv hy).trans (silent_of_run_nil h₁ rfl)
    obtain ⟨c', hc', hsteps⟩ := steps_of_silent irel_init hsil
    obtain ⟨r, hr', ha, -⟩ := instAnsOf_of_step hc' h₂
    exact ⟨c', r, hsteps, hr', ha⟩
  · rintro ⟨c', r, hsteps, hr, ha⟩
    obtain ⟨y, hsil, hy⟩ := silent_of_steps hsteps irel_init
    obtain ⟨s, t, rfl, rfl⟩ := irel_result hy hr
    obtain ⟨z, hz⟩ := ans_step_of_result hr ha
    have hrun : (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init [askInst, ansInst a] z :=
      .vis (.right _ InstSystem.Step.askInst)
        ((run_of_silent hsil).append (LTS.Run.of_step hz))
    exact ⟨z, hrun⟩

/-- **Divergence after the instantiation question is Core divergence of the start run.** -/
theorem div_inst_iff :
    [askInst] ∈ (DStrategy.ofLTS (CI I P s₀ t₀ K)).div ↔
      Diverges P (hostOf I.imports K) (t₀.config s₀) := by
  refine (DStrategy.mem_div_ofLTS (L := CI I P s₀ t₀ K)).trans ?_
  constructor
  · rintro ⟨⟨y, hy, hdiv⟩, -⟩
    obtain ⟨c', hc', hsteps⟩ := steps_of_silent irel_init (run_askInst_inv hy)
    exact InfiniteTrace.of_steps hsteps ((diverges_iff hc').1 hdiv)
  · intro hdiv
    have hrun : (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init [askInst]
        (none, .inst (s₀, t₀)) :=
      .vis (.right _ InstSystem.Step.askInst) (.nil _)
    exact ⟨⟨_, hrun, (diverges_iff irel_init).2 hdiv⟩, none,
      .cons (Silmaril.Games.Step.ask (E := Sig.empty) (F := I.F.withInst (Behaviour Val)) none)
        (.nil _)⟩

/-- A run past a successful instantiation is a Core start run to `values []`, then a run
from the persisted store. -/
theorem run_ready_of {w : List (Move Sig.empty (I.F.withInst (Behaviour Val)))}
    {z : CSt I P s₀ t₀ K}
    (h : (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init ([askInst, ansInst .ready] ++ w) z) :
    ∃ c' : Config Nat, Steps P (hostOf I.imports K) (t₀.config s₀) c' ∧
      c'.code = (Result.values []).toAdmin ∧
      (CI I P s₀ t₀ K).Run (none, .ready c'.store) w z := by
  obtain ⟨y, hy, hw⟩ := LTS.Run.of_append h
  obtain ⟨y₁, hy₁, hr⟩ := LTS.Run.of_append (s := [askInst]) (t := [ansInst .ready]) hy
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hr
  have hsil : Relation.ReflTransGen (CI I P s₀ t₀ K).Silent
      (none, .inst (s₀, t₀)) x₁ :=
    (run_askInst_inv hy₁).trans (silent_of_run_nil h₁ rfl)
  obtain ⟨c', hc', hsteps⟩ := steps_of_silent irel_init hsil
  obtain ⟨r, hr', ha, hz⟩ := instAnsOf_of_step hc' h₂
  have hx₂ : x₂ = (none, .ready c'.store) := hz rfl
  have hr0 : r = .values [] := ha.elim And.left fun h => nomatch h.2
  have hy' : y = (none, .ready c'.store) := ready_silent (hx₂ ▸ silent_of_run_nil h₃ rfl)
  exact ⟨c', hsteps, hr0 ▸ hr', hy' ▸ hw⟩

/-- A Core start run to `values []` followed by a run from the persisted store is a run past a
successful instantiation. -/
theorem run_ready_to {w : List (Move Sig.empty (I.F.withInst (Behaviour Val)))}
    {z : CSt I P s₀ t₀ K} {c' : Config Nat}
    (hsteps : Steps P (hostOf I.imports K) (t₀.config s₀) c')
    (hr : c'.code = (Result.values []).toAdmin)
    (hw : (CI I P s₀ t₀ K).Run (none, .ready c'.store) w z) :
    (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init ([askInst, ansInst .ready] ++ w) z := by
  obtain ⟨y, hsil, hy⟩ := silent_of_steps hsteps irel_init
  obtain ⟨s, t, rfl, rfl⟩ := irel_result hy hr
  have hz : (CI I P s₀ t₀ K).step (none, .inst (s, t)) (some (ansInst .ready))
      (none, .ready s) := .right _ (InstSystem.Step.iready ⟨hr, rfl⟩)
  have hst : (t.config s).store = s := Thread.config_store s t
  have hrun : (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init [askInst, ansInst .ready]
      (none, .ready s) :=
    .vis (.right _ InstSystem.Step.askInst) ((run_of_silent hsil).append (LTS.Run.of_step hz))
  exact hrun.append (hst ▸ hw)

/-- **Runs past a successful instantiation**: a Core start run to `values []`, then a run
from the persisted store. -/
theorem run_ready_iff {w : List (Move Sig.empty (I.F.withInst (Behaviour Val)))}
    {z : CSt I P s₀ t₀ K} :
    (CI I P s₀ t₀ K).Run (CI I P s₀ t₀ K).init ([askInst, ansInst .ready] ++ w) z ↔
      ∃ c' : Config Nat, Steps P (hostOf I.imports K) (t₀.config s₀) c' ∧
        c'.code = (Result.values []).toAdmin ∧
        (CI I P s₀ t₀ K).Run (none, .ready c'.store) w z :=
  ⟨run_ready_of, fun ⟨_, h₁, h₂, h₃⟩ => run_ready_to h₁ h₂ h₃⟩

end Silmaril.Proofs.Wasm.Game.Start
