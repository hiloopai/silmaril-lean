module

public import Silmaril.Proofs.Wasm.Game.DivAdequacy.Traces
public import Silmaril.Proofs.Wasm.Game.Machine.Basic

/-!
# Divergence of the closed program is Core divergence

For every profile `P`, the invocation of an export call diverges under the
induced host (`Execution.Core.Diverges P (hostOf I.imports K)`) exactly when
the composite transition system `K.dlts.comp (I.dlts P s)` has an infinite
silent run after the export question (`diverges_iff_cmp`), that is, when the
divergence-observing closed program `I.closedD P s K` may diverge after
`[ask f]` (`mem_div_closedD_iff`).

The two infinite runs correspond step by step through `CRel`: a running state
is related to the configuration of its thread; a state waiting for the answer
to `e` (the environment holding the question) is related to the configuration
stopped at the callout of `e`. Host-free Core steps are silent instance steps;
an answered host call is the hidden exchange of the question and the answer
(two silent steps of the composite, one Core step); a host call that `K` never
answers is the environment's silent self-loop, matching the Core self-loop
`Step.callRefHostDiv`. Both directions are coinductions
(`InfiniteTrace.coinduct`); no determinism is used.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game

open Silmaril.Games Silmaril.Wasm.Game Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.SingleThreaded

namespace ScalarInstance

variable {I : Silmaril.Wasm.Game.ScalarInstance} {P : Profile} {s₀ : Store Nat}
  {K : Silmaril.Wasm.Game.Env I.E}

open Silmaril.Wasm.Game.ScalarInstance

/-- The composite transition system of the closed program. -/
abbrev Cmp (I : Silmaril.Wasm.Game.ScalarInstance) (P : Profile) (s₀ : Store Nat)
    (K : Silmaril.Wasm.Game.Env I.E) : LTS Sig.empty I.F :=
  K.dlts.comp (I.dlts P s₀)

/-- The relation between Core configurations and states of the composite system during the
export call `f`. -/
def CRel (f : I.F.Op) (c : Config Nat) (x : (Cmp I P s₀ K).State) : Prop :=
  (∃ (s : Store Nat) (t : Thread), x = (none, .running f s t) ∧ c = t.config s) ∨
  (∃ (s : Store Nat) (t : Thread) (e : I.E.Op) (h : Nat) (args : List Val),
    x = (some e, .waiting f s t e) ∧ c = t.config s ∧ CalloutAt s t h args ∧
      I.importOp? h args = some e)

/-- The import question of a host call under the induced host is the one of the callout. -/
theorem hostOf_op_eq {h : Nat} {args : List Val} {e : I.E.Op} {s : Store Nat}
    {out : HostOutcome Nat} (hop : I.importOp? h args = some e)
    (hh : hostOf I.imports K h s args out) :
    ((∃ w, K.Answers e w ∧ out = .returned s (Answer.toResult (ft := I.imports.get e.1) w)) ∨
      ((∀ w, ¬ K.Answers e w) ∧ out = .diverged)) := by
  obtain ⟨e', he', hout⟩ := hh
  have hee : e' = e := Option.some.inj (he'.symm.trans hop)
  exact hee ▸ hout

/-- The callout of a thread determines its host code and arguments. -/
theorem callout_args_eq {s : Store Nat} {t : Thread} {h h' : Nat} {args args' : List Val}
    {E : Ctx} {a : Nat} (hco : CalloutAt s t h args)
    (hd : decompose? s (t.config s).code = some (E, a, h', args')) : h' = h ∧ args' = args :=
  calloutAt_unique ⟨E, a, hd⟩ hco

/-! ### Core divergence to divergence of the composite -/

/-- From a waiting state related to an infinitely running configuration, the composite takes
a silent step to a related state. -/
theorem cmp_step_waiting (f : I.F.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hinf : InfiniteTrace (Step P (hostOf I.imports K)) (t.config s)) :
    ∃ y, (Cmp I P s₀ K).step (some e, .waiting f s t e) none y ∧
      ∃ c, CRel f c y ∧ InfiniteTrace (Step P (hostOf I.imports K)) c := by
  obtain ⟨c₁, hst, hinf₁⟩ := hinf.unfold
  rcases (stepP_iff P _ s t c₁).1 hst with ⟨s', f', code', -, hi⟩ |
    ⟨E, a, h', args', hd, ⟨s', r, hr, rfl⟩ | ⟨hdiv, rfl⟩⟩
  · exact absurd hi (calloutAt_no_internal hco _)
  · obtain ⟨rfl, rfl⟩ := callout_args_eq hco hd
    rcases hostOf_op_eq hop hr with ⟨w, hw, hout⟩ | ⟨-, hout⟩
    · obtain ⟨rfl, rfl⟩ : s' = s ∧ r = Answer.toResult (ft := I.imports.get e.1) w := by
        simpa using hout
      exact ⟨_, .sync (Ev.ans e w) (Silmaril.Wasm.Game.Env.DStep.ans hw) (DTrans.uret w),
        _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
    · exact absurd hout (by simp)
  · obtain ⟨rfl, rfl⟩ := callout_args_eq hco hd
    rcases hostOf_op_eq hop hdiv with ⟨w, -, hout⟩ | ⟨hno, -⟩
    · exact absurd hout (by simp)
    · exact ⟨_, .tau₁ (Silmaril.Wasm.Game.Env.DStep.loop hno), _,
        .inr ⟨s, t, e, _, _, rfl, rfl, hco, hop⟩, hinf₁⟩

/-- From a running state related to an infinitely running configuration, the composite takes
a silent step to a related state. -/
theorem cmp_step_running (f : I.F.Op) {s : Store Nat} {t : Thread}
    (hinf : InfiniteTrace (Step P (hostOf I.imports K)) (t.config s)) :
    ∃ y, (Cmp I P s₀ K).step (none, .running f s t) none y ∧
      ∃ c, CRel f c y ∧ InfiniteTrace (Step P (hostOf I.imports K)) c := by
  obtain ⟨c₁, hst, hinf₁⟩ := hinf.unfold
  rcases (stepP_iff P _ s t c₁).1 hst with ⟨s', f', code', rfl, hi⟩ |
    ⟨E, a, h, args, hd, ⟨s', r, hr, -⟩ | ⟨hdiv, -⟩⟩
  · exact ⟨_, .tau₂ (DTrans.tau hi), _, .inl ⟨_, _, rfl, rfl⟩, hinf₁⟩
  · obtain ⟨e, he, -⟩ := hr
    exact ⟨_, .sync (Ev.ask e) (Silmaril.Wasm.Game.Env.DStep.ask e) (DTrans.ucall ⟨E, a, hd⟩ he),
      _, .inr ⟨s, t, e, h, args, rfl, rfl, ⟨E, a, hd⟩, he⟩, hinf⟩
  · obtain ⟨e, he, -⟩ := hdiv
    exact ⟨_, .sync (Ev.ask e) (Silmaril.Wasm.Game.Env.DStep.ask e) (DTrans.ucall ⟨E, a, hd⟩ he),
      _, .inr ⟨s, t, e, h, args, rfl, rfl, ⟨E, a, hd⟩, he⟩, hinf⟩

/-- **Core divergence is divergence of the composite.** -/
theorem cmp_diverges_of_core (f : I.F.Op) {c : Config Nat} {x : (Cmp I P s₀ K).State}
    (hc : CRel f c x) (hinf : InfiniteTrace (Step P (hostOf I.imports K)) c) :
    (Cmp I P s₀ K).Diverges x := by
  refine InfiniteTrace.coinduct
    (fun x => ∃ c, CRel f c x ∧ InfiniteTrace (Step P (hostOf I.imports K)) c) ?_ ⟨c, hc, hinf⟩
  rintro x ⟨c, ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hinf⟩
  · exact cmp_step_running f hinf
  · exact cmp_step_waiting f hco hop hinf

/-! ### Divergence of the composite to Core divergence -/

/-- A diverging waiting state related to a configuration gives a Core step to a related,
diverging state. -/
theorem core_step_waiting (f : I.F.Op) {s : Store Nat} {t : Thread} {e : I.E.Op} {h : Nat}
    {args : List Val} (hco : CalloutAt s t h args) (hop : I.importOp? h args = some e)
    (hd : (Cmp I P s₀ K).Diverges (some e, .waiting f s t e)) :
    ∃ c₁, Step P (hostOf I.imports K) (t.config s) c₁ ∧
      ∃ x₁, CRel f c₁ x₁ ∧ (Cmp I P s₀ K).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk =>
    cases hk with
    | loop hno =>
      have hdiv : hostOf I.imports K h s args .diverged := ⟨e, hop, .inr ⟨hno, rfl⟩⟩
      obtain ⟨E, a, hdc⟩ := hco
      refine ⟨t.config s, (stepP_iff P _ s t _).2
        (.inr ⟨E, a, h, args, hdc, .inr ⟨hdiv, rfl⟩⟩), _,
        .inr ⟨s, t, e, h, args, rfl, rfl, ⟨E, a, hdc⟩, hop⟩, hd₁⟩
  | tau₂ hi => cases hi
  | sync g hk hi =>
    cases hk with
    | ans hw =>
      cases hi with
      | uret w =>
        exact ⟨_, calloutAt_step hco ⟨e, hop, .inl ⟨_, hw, rfl⟩⟩, _,
          .inl ⟨_, _, rfl, rfl⟩, hd₁⟩

/-- A diverging running state related to a configuration gives a Core step to a related,
diverging state. -/
theorem core_step_running (f : I.F.Op) {s : Store Nat} {t : Thread}
    (hd : (Cmp I P s₀ K).Diverges (none, .running f s t)) :
    ∃ c₁, Step P (hostOf I.imports K) (t.config s) c₁ ∧
      ∃ x₁, CRel f c₁ x₁ ∧ (Cmp I P s₀ K).Diverges x₁ := by
  obtain ⟨x₁, hs, hd₁⟩ := hd.unfold
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hi =>
    cases hi with
    | tau hint =>
      exact ⟨_, InternalP.toStep P _ hint, _, .inl ⟨_, _, rfl, rfl⟩, hd₁⟩
  | sync g hk hi =>
    cases hk with
    | ask e =>
      cases hi with
      | ucall hco hop => exact core_step_waiting f hco hop hd₁

/-- **Divergence of the composite is Core divergence.** -/
theorem core_diverges_of_cmp (f : I.F.Op) {c : Config Nat} {x : (Cmp I P s₀ K).State}
    (hc : CRel f c x) (hd : (Cmp I P s₀ K).Diverges x) :
    InfiniteTrace (Step P (hostOf I.imports K)) c := by
  refine InfiniteTrace.coinduct
    (fun c => ∃ x, CRel (s₀ := s₀) (K := K) (P := P) f c x ∧ (Cmp I P s₀ K).Diverges x) ?_
    ⟨x, hc, hd⟩
  rintro c ⟨x, ⟨s, t, rfl, rfl⟩ | ⟨s, t, e, h, args, rfl, rfl, hco, hop⟩, hd⟩
  · exact core_step_running f hd
  · exact core_step_waiting f hco hop hd

/-- **Divergence, every profile.** The invocation of the export call `f` from store `s`
diverges under the induced host exactly when the composite system diverges silently right
after the question `f`. -/
theorem diverges_iff_cmp (f : I.F.Op) {s : Store Nat} :
    Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) ↔
      (Cmp I P s K).Diverges (none, .running f s (I.initThread f)) := by
  have hc : CRel (s₀ := s) (K := K) (P := P) f (invoke s (I.addr f.1) f.2.1)
      (none, .running f s (I.initThread f)) := .inl ⟨s, I.initThread f, rfl, rfl⟩
  exact ⟨cmp_diverges_of_core f hc, core_diverges_of_cmp f hc⟩

/-! ### The divergent plays of the closed program -/

/-- A run without visible moves is a sequence of silent steps. -/
theorem silent_of_run_nil {E F : Sig.{0}} {L : LTS E F} {x y : L.State} {p : List (Move E F)}
    (h : L.Run x p y) (hp : p = []) : Relation.ReflTransGen L.Silent x y := by
  induction h with
  | nil x => exact .refl
  | tau hs _ ih => exact .head hs (ih hp)
  | vis _ _ _ => cases hp

/-- The runs of the composite reading the export question from its initial state. -/
theorem run_ask_inv {s : Store Nat} {f : I.F.Op} {y : (Cmp I P s K).State}
    (h : (Cmp I P s K).Run (Cmp I P s K).init [.inr (.ask f)] y) :
    Relation.ReflTransGen (Cmp I P s K).Silent (none, .running f s (I.initThread f)) y := by
  cases h with
  | tau hs _ =>
    cases hs with
    | tau₁ hk => cases hk
    | tau₂ hi => cases hi
    | sync g hk hi =>
      cases hk with
      | ask e => cases hi
  | vis hs hr =>
    cases hs with
    | right g hi =>
      cases hi with
      | call s' f' => exact silent_of_run_nil hr rfl

/-- **The divergent plays of the closed program after the export question.** -/
theorem mem_div_closedD_iff {s : Store Nat} (f : I.F.Op) :
    [.inr (.ask f)] ∈ (I.closedD P s K).div ↔
      Diverges P (hostOf I.imports K) (invoke s (I.addr f.1) f.2.1) := by
  refine (DStrategy.mem_div_ofLTS (L := Cmp I P s K)).trans ?_
  rw [diverges_iff_cmp f]
  constructor
  · rintro ⟨⟨y, hy, hdiv⟩, -⟩
    exact InfiniteTrace.of_steps (run_ask_inv hy) hdiv
  · intro hdiv
    have hrun : (Cmp I P s K).Run (Cmp I P s K).init [.inr (.ask f)]
        (none, .running f s (I.initThread f)) :=
      .vis (LTS.CompStep.right (Ev.ask f) (DTrans.call s f)) (.nil _)
    exact ⟨⟨_, hrun, hdiv⟩, f, .cons (.ask f) (.nil _)⟩

end ScalarInstance

end Silmaril.Proofs.Wasm.Game
