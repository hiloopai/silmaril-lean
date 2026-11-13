module

public import Silmaril.Proofs.Wasm.Game.ULink.Closed

/-!
# Closed programs: the observations agree

For an export call `f` from a store with the link's layout, against an environment satisfying
the untyped host contract and allocating no stub codes (`CHyp`):

* `cc_trace_of_lc`: an answer of the linked closed system is an answer of the composite closed
  system, to the stubbed question, with the stubbed store and the same result;
* `lc_trace_of_cc`: conversely, every answer of the composite closed system to the stubbed
  question is a stubbed answer of the linked closed system, with the same result;
* `div_iff`: they diverge after the question together;
* `link_closed_obs`: hence the observations of the two closed programs agree.

New proofs.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.ULink

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.ULink Silmaril Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- An answer of the divergence-observing strategy of a system denoting a strategy is a trace. -/
theorem responds_ofLTS {F : Sig.{0}} {X : LTS Sig.empty F} {σ : Strategy Sig.empty F}
    (hD : X.Denotes σ) {g : F.Op} {a : F.Ar g} :
    Responds (DStrategy.ofLTS X).toStrategy g a ↔ [.inr (.ask g), .inr (.ans g a)] ∈ X.Traces := by
  show _ ∈ Strategy.ofLTS X ↔ _
  rw [hD.ofLTS_eq]
  exact (hD _).symm

/-- A chain of silent steps is a silent run. -/
theorem run_nil_of_rtg {E F : Sig.{0}} {X : LTS E F} {a b : X.State}
    (h : Relation.ReflTransGen X.Silent a b) : X.Run a [] b := by
  induction h with
  | refl => exact .nil _
  | tail _ h ih => exact ih.append (.tau h (.nil _))

variable {L : ULink} {P : Profile} {Lenv : SEnv UImp} {q₀ : Lenv.S} {f : L.U.F.Op}
  {ps rs : Ty (.list .val)}

/-! ### The initial states -/

/-- The composite closed system after the question `g`. -/
abbrev ccStart (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) (g : L.U.F.Op) :
    (CC L P Lenv q₀).State :=
  ((q₀, none), (.idle, .running g g.store (L.U.init g)))

/-- The linked closed system after the question `f`. -/
abbrev lcStart (L : ULink) (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) (f : L.U.F.Op) :
    (LC L P Lenv q₀).State :=
  ((q₀, none), .running f f.store (L.U.init f))

/-- The invariant holds right after the question. -/
theorem good_start (hc : CHyp L Lenv f ps rs) : Good L P Lenv q₀ f (lcStart L P Lenv q₀ f) :=
  ⟨⟨_, .refl, .inl ⟨f.store, L.U.init f, rfl, rfl⟩⟩, hc.layout⟩

theorem cf_start (hc : CHyp L Lenv f ps rs) :
    CF L P Lenv q₀ f (ccStart L P Lenv q₀ (L.stubQ f)) (lcStart L P Lenv q₀ f) :=
  ⟨rfl, FRel.cons hc.layout hc.layout, good_start hc⟩

theorem cb_start (hc : CHyp L Lenv f ps rs) :
    CB L P Lenv q₀ f (lcStart L P Lenv q₀ f) (ccStart L P Lenv q₀ (L.stubQ f)) :=
  ⟨rfl, BRel.cons hc.layout hc.layout, good_start hc⟩

/-- The composite closed system starts by the question. -/
theorem cc_step_start (g : L.U.F.Op) :
    (CC L P Lenv q₀).step (CC L P Lenv q₀).init (some (.inr (.ask g))) (ccStart L P Lenv q₀ g) :=
  .right _ (.right _ (UInstance.Trans.call g))

/-- The linked closed system starts by the question. -/
theorem lc_step_start (f : L.U.F.Op) :
    (LC L P Lenv q₀).step (LC L P Lenv q₀).init (some (.inr (.ask f))) (lcStart L P Lenv q₀ f) :=
  .right _ (UInstance.Trans.call f)

/-- The initial composite closed state takes no silent step. -/
theorem cc_init_no_silent {x : (CC L P Lenv q₀).State}
    (hs : (CC L P Lenv q₀).step (CC L P Lenv q₀).init none x) : False := by
  cases hs with
  | tau₁ hk => cases hk
  | tau₂ hcs => exact tau_idle hcs
  | sync g hk hcs =>
    cases hk with
    | ask q e =>
      cases hcs with
      | left g hr => cases hr

/-- Silent runs from the initial composite closed state stay there. -/
theorem cc_init_run_nil {x y : (CC L P Lenv q₀).State} {p : List (Move Sig.empty L.U.F)}
    (h : (CC L P Lenv q₀).Run x p y) (hp : p = []) (hx : x = (CC L P Lenv q₀).init) :
    y = (CC L P Lenv q₀).init := by
  cases h with
  | nil => exact hx
  | tau hs _ => exact (cc_init_no_silent (hx ▸ hs)).elim
  | vis _ _ => cases hp

/-- Reading the question from the initial composite closed state. -/
theorem cc_step_ask_inv {g : L.U.F.Op} {x : (CC L P Lenv q₀).State}
    (hs : (CC L P Lenv q₀).step (CC L P Lenv q₀).init (some (.inr (.ask g))) x) :
    x = ccStart L P Lenv q₀ g := by
  cases hs with
  | right g' hcs =>
    cases hcs with
    | right g'' hi =>
      cases hi with
      | call f' => rfl

/-- The composite closed runs reading the question. -/
theorem cc_run_ask_inv {g : L.U.F.Op} {p : List (Move Sig.empty L.U.F)} {y : (CC L P Lenv q₀).State}
    (h : (CC L P Lenv q₀).Run (CC L P Lenv q₀).init (.inr (.ask g) :: p) y) :
    (CC L P Lenv q₀).Run (ccStart L P Lenv q₀ g) p y := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (CC L P Lenv q₀).init := cc_init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = ccStart L P Lenv q₀ g := cc_step_ask_inv (hx₁ ▸ hs₁)
  exact hx₂ ▸ hr₂

/-- The linked closed runs reading the question. -/
theorem lc_run_ask_inv {p : List (Move Sig.empty L.U.F)} {y : (LC L P Lenv q₀).State}
    (h : (LC L P Lenv q₀).Run (LC L P Lenv q₀).init (.inr (.ask f) :: p) y) :
    (LC L P Lenv q₀).Run (lcStart L P Lenv q₀ f) p y := by
  obtain ⟨x₁, x₂, hr₁, hs₁, hr₂⟩ := LTS.Run.cons_inv h
  have hx₁ : x₁ = (LC L P Lenv q₀).init := Untyped.init_run_nil hr₁ rfl rfl
  have hx₂ : x₂ = lcStart L P Lenv q₀ f := Untyped.step_ask_inv (hx₁ ▸ hs₁)
  exact hx₂ ▸ hr₂

/-! ### Answers -/

/-- An upper move of the linked closed system is a move of the linked module. -/
theorem lc_vis_inr {z z' : (LC L P Lenv q₀).State} {g : Ev L.U.F}
    (hs : (LC L P Lenv q₀).step z (some (.inr g)) z') :
    z'.1 = z.1 ∧ (L.U.lts P).step z.2 (some (.inr g)) z'.2 := by
  cases hs with
  | right g hi => exact ⟨rfl, hi⟩

/-- An upper move of the composite closed system is a move of the composite. -/
theorem cc_vis_inr {x x' : (CC L P Lenv q₀).State} {g : Ev L.U.F}
    (hs : (CC L P Lenv q₀).step x (some (.inr g)) x') :
    x'.1 = x.1 ∧ (Cmp L P).step x.2 (some (.inr g)) x'.2 := by
  cases hs with
  | right g hi => exact ⟨rfl, hi⟩

/-- A waiting consumer makes no upper move. -/
theorem cmp_waiting_no_inr {r : RState} {f' : L.U.F.Op} {σ : Store Nat} {t : Thread}
    {e : UCall Nat} {g : Ev L.U.F} {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (r, .waiting f' σ t e) (some (.inr g)) x') : False := by
  cases hs with
  | right g hc => cases hc

/-- An idle composite makes no answer. -/
theorem cmp_idle_no_ans {g : L.U.F.Op} {a' : UReply} {x' : (Cmp L P).State}
    (hs : (Cmp L P).step (.idle, .idle) (some (.inr (.ans g a'))) x') : False := by
  cases hs with
  | right g hc => cases hc

/-- A running consumer answers its question in its store. -/
theorem cmp_cons_ans {f' g : L.U.F.Op} {σ : Store Nat} {t : Thread} {a' : UReply}
    {x' : (Cmp L P).State} (hs : (Cmp L P).step (.idle, .running f' σ t) (some (.inr (.ans g a'))) x') :
    g = f' ∧ a' = ⟨σ, a'.result⟩ := by
  cases hs with
  | right g hc =>
    cases hc with
    | oret final => exact ⟨rfl, rfl⟩

/-- **The composite answers only as the consumer**, with a stubbed store of the layout. -/
theorem frel_ans_inv {x x' : (Cmp L P).State} {y : L.U.State} {g : L.U.F.Op} {a' : UReply}
    (hF : FRel L x y) (hs : (Cmp L P).step x (some (.inr (.ans g a'))) x') :
    ∃ (f' : L.U.F.Op) (s : Store Nat) (t : Thread), y = .running f' s t ∧ g = L.stubQ f' ∧
      a' = L.stubR ⟨s, a'.result⟩ ∧ L.Layout f'.store ∧ L.Layout s := by
  cases hF with
  | idle => exact (cmp_idle_no_ans hs).elim
  | cons hq hl =>
    obtain ⟨hg, ha⟩ := cmp_cons_ans hs
    exact ⟨_, _, _, rfl, hg, ha, hq, hl⟩
  | prov => exact (cmp_waiting_no_inr hs).elim
  | provWait => exact (cmp_waiting_no_inr hs).elim
  | stuck => exact (cmp_waiting_no_inr hs).elim
  | fwd => exact (cmp_waiting_no_inr hs).elim
  | fwdWait => exact (cmp_waiting_no_inr hs).elim
  | fwdRet => exact (cmp_waiting_no_inr hs).elim

/-- **Linked closed answers are composite closed answers**, stubbed. -/
theorem cc_trace_of_lc (hc : CHyp L Lenv f ps rs) {a : UReply}
    (h : [.inr (.ask f), .inr (.ans f a)] ∈ (LC L P Lenv q₀).Traces) :
    [.inr (.ask (L.stubQ f)), .inr (.ans (L.stubQ f) (L.stubR a))] ∈ (CC L P Lenv q₀).Traces := by
  obtain ⟨y, hy⟩ := h
  have hr₁ : (LC L P Lenv q₀).Run (lcStart L P Lenv q₀ f) [.inr (.ans f a)] y := lc_run_ask_inv hy
  obtain ⟨z₂, z₃, hr₂, hs₃, -⟩ := LTS.Run.cons_inv hr₁
  obtain ⟨x₂, hx₂, hB₂⟩ := cb_run_nil hc hr₂ rfl _ (cb_start hc)
  have hi : (L.U.lts P).step z₂.2 (some (.inr (.ans f a))) z₃.2 := (lc_vis_inr hs₃).2
  have hml : L.MoveLayout (.inr (.ans f a) : Move UImp L.U.F) :=
    ⟨hc.layout, ans_store_layout hB₂.2.2.2 hi⟩
  obtain ⟨xc₃, hx₃, -⟩ := bsim_vis hB₂.2.1 hi hml
  have hrun₃ : (CC L P Lenv q₀).Run (x₂.1, x₂.2) [.inr (.ans (L.stubQ f) (L.stubR a))]
      (x₂.1, xc₃) := cc_run_inr hx₃
  exact ⟨_, .vis (cc_step_start (L.stubQ f)) (hx₂.append hrun₃)⟩

/-- **Composite closed answers are stubbed linked closed answers**, with the same result. -/
theorem lc_trace_of_cc (hc : CHyp L Lenv f ps rs) {a' : UReply}
    (h : [.inr (.ask (L.stubQ f)), .inr (.ans (L.stubQ f) a')] ∈ (CC L P Lenv q₀).Traces) :
    ∃ s : Store Nat, [.inr (.ask f), .inr (.ans f ⟨s, a'.result⟩)] ∈ (LC L P Lenv q₀).Traces := by
  obtain ⟨x, hx⟩ := h
  have hr₁ : (CC L P Lenv q₀).Run (ccStart L P Lenv q₀ (L.stubQ f)) [.inr (.ans (L.stubQ f) a')] x :=
    cc_run_ask_inv hx
  obtain ⟨x₂, x₃, hr₂, hs₃, -⟩ := LTS.Run.cons_inv hr₁
  obtain ⟨z₂, hz₂, hF₂⟩ := cf_run_nil hc hr₂ rfl _ (cf_start hc)
  have hcs : (Cmp L P).step x₂.2 (some (.inr (.ans (L.stubQ f) a'))) x₃.2 := (cc_vis_inr hs₃).2
  obtain ⟨f', s, t, hy, hg, ha, hq', hl⟩ := frel_ans_inv hF₂.2.1 hcs
  have hff : f = f' := stubQ_inj hc.layout hq' hg
  subst hff
  have hm : (.inr (.ans (L.stubQ f) a') : Move UImp L.U.F) = L.stubUp (.inr (.ans f ⟨s, a'.result⟩)) := by
    rw [ha]
    rfl
  obtain ⟨y', hy', -⟩ := sim_vis hF₂.2.1 hcs hm ⟨hq', hl⟩
  have hz₃ : (LC L P Lenv q₀).step z₂ (some (.inr (.ans f ⟨s, a'.result⟩))) (z₂.1, y') :=
    .right _ hy'
  exact ⟨s, _, .vis (lc_step_start f) (hz₂.append (.vis hz₃ (.nil _)))⟩

/-! ### Divergence -/

/-- **The closed systems diverge after the question together.** -/
theorem div_iff (hc : CHyp L Lenv f ps rs) :
    (∃ y, (LC L P Lenv q₀).Run (LC L P Lenv q₀).init [.inr (.ask f)] y ∧ (LC L P Lenv q₀).Diverges y) ↔
      ∃ x, (CC L P Lenv q₀).Run (CC L P Lenv q₀).init [.inr (.ask (L.stubQ f))] x ∧
        (CC L P Lenv q₀).Diverges x := by
  constructor
  · rintro ⟨y, hy, hd⟩
    have hr : (LC L P Lenv q₀).Run (lcStart L P Lenv q₀ f) [] y := lc_run_ask_inv hy
    obtain ⟨x, hx, hB⟩ := cb_run_nil hc hr rfl _ (cb_start hc)
    exact ⟨x, .vis (cc_step_start (L.stubQ f)) hx, cb_diverges hc hB hd⟩
  · rintro ⟨x, hx, hd⟩
    have hr : (CC L P Lenv q₀).Run (ccStart L P Lenv q₀ (L.stubQ f)) [] x := cc_run_ask_inv hx
    obtain ⟨z, hz, hF⟩ := cf_run_nil hc hr rfl _ (cf_start hc)
    exact ⟨z, .vis (lc_step_start f) hz, cf_diverges hc hF hd⟩

/-! ### Observations -/

/-- The linked closed system denotes the linked closed program. -/
theorem lc_denotes (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) :
    (LC L P Lenv q₀).Denotes (L.U.closed P Lenv q₀) :=
  Untyped.cmp_denotes P Lenv q₀

/-- The composite closed system denotes the finite plays of the composite closed program. -/
theorem cc_denotes (P : Profile) (Lenv : SEnv UImp) (q₀ : Lenv.S) :
    (CC L P Lenv q₀).Denotes ((Lenv.strategy q₀).comp (L.compStrategy P)) :=
  LTS.Denotes.comp (SEnv.denotes_dlts Lenv q₀) (comp_denotes P)

/-- **The observations of the closed programs agree** (see the module docstring). -/
theorem link_closed_obs (hc : CHyp L Lenv f ps rs) :
    uDCompositeObs (L.U.closedD P Lenv q₀) f = uDCompositeObs (L.compClosedD P Lenv q₀) (L.stubQ f) := by
  have hlc : L.U.closedD P Lenv q₀ = DStrategy.ofLTS (LC L P Lenv q₀) :=
    Untyped.closedD_eq_ofLTS P Lenv q₀
  have hcc : L.compClosedD P Lenv q₀ = DStrategy.ofLTS (CC L P Lenv q₀) := compClosedD_eq_ofLTS P Lenv q₀
  rw [hlc, hcc]
  ext b
  constructor
  · rintro (⟨a, ha, rfl⟩ | ⟨rfl, hd⟩)
    · have ht := cc_trace_of_lc hc ((responds_ofLTS (lc_denotes P Lenv q₀)).1 ha)
      exact .inl ⟨L.stubR a, (responds_ofLTS (cc_denotes P Lenv q₀)).2 ht, rfl⟩
    · have hd' := (div_iff hc).1 (DStrategy.mem_div_ofLTS.1 hd).1
      exact .inr ⟨rfl, DStrategy.mem_div_ofLTS.2 ⟨hd', L.stubQ f, .cons (.ask _) (.nil _)⟩⟩
  · rintro (⟨a', ha', rfl⟩ | ⟨rfl, hd⟩)
    · obtain ⟨s, ht⟩ := lc_trace_of_cc hc ((responds_ofLTS (cc_denotes P Lenv q₀)).1 ha')
      exact .inl ⟨⟨s, a'.result⟩, (responds_ofLTS (lc_denotes P Lenv q₀)).2 ht, rfl⟩
    · have hd' := (div_iff hc).2 (DStrategy.mem_div_ofLTS.1 hd).1
      exact .inr ⟨rfl, DStrategy.mem_div_ofLTS.2 ⟨hd', f, .cons (.ask _) (.nil _)⟩⟩

end Silmaril.Proofs.Wasm.Game.ULink
