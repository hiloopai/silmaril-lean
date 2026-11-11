module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Match
public import Silmaril.Wasm.Binaryen.CodeSimModule

@[expose] public section

/-!
# Callers of equivalent strict leaf functions (proofs)

`Rel P c d`: `SRel`-related stores, equal frames, `CodeR`-related codes, and the left
configuration typed (`Sim.ContextTyped`). Under the closed host, at every profile:

* `run_transport`: a run of `c` to a result is matched by a run of `d` to the same result, with
  `SRel`-related final stores. By induction on the run: steps outside a `LeafPair` callee are
  matched by `step_match`; inside an `InFlight` pair the target waits (`ctx_step`,
  `frame_step`), and when the source callee returns, the target callee runs to the same result
  (`LBeh` inclusion, `frame_behaviours`, `ctx_lift_steps`);
* `div_transport`: divergence of `c` is divergence of `d`. A divergent source either diverges
  inside an in-flight callee (so does the target callee, `ctx_lift_diverges`) or leaves it after
  finitely many steps (silmaril's `InfiniteTrace.context_decompose`);
* `behaviours_srel`: **typed invocations of any function have the same Core behaviours in
  `SRel`-related typed stores** (callers of the replaced functions included).
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert
open Silmaril.Wasm.Binaryen (closedHost)

variable {H : Type} {P : Numerics.Profile}

/-- The simulation relation. -/
def Rel (P : Numerics.Profile) (c d : Config H) : Prop :=
  SRel P c.store d.store ∧ c.frame = d.frame ∧ CodeR P c.code d.code ∧ Sim.ContextTyped c

/-! ## Behaviours along steps -/

theorem behavioursOf_step_sub {H : Type} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') : behavioursOf P host c' ⊆ behavioursOf P host c := by
  rintro b (⟨c'', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩)
  · exact .inl ⟨c'', r, Relation.ReflTransGen.head h hs, hc, rfl⟩
  · exact .inr ⟨rfl, Silmaril.InfiniteTrace.fold h hd⟩

theorem behavioursOf_steps_sub {H : Type} {host : HostSemantics H} {c c' : Config H}
    (h : Steps P host c c') : behavioursOf P host c' ⊆ behavioursOf P host c := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact (behavioursOf_step_sub hs).trans ih

/-- The canonical form of a step of a strict frame. -/
theorem canon_step {H : Type} {host : HostSemantics H} {s s' : Store H} {F F' : Frame}
    {X : Admin} {l : List Admin} (hX : LFrame X) (h : Step P host ⟨s, F, [X]⟩ ⟨s', F', l⟩) :
    s' = s ∧ F' = F ∧ FrameNext l ∧ Step P closedHost (canon X) ⟨{}, {}, swapL {} l⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := frame_step hX h
  exact ⟨h1, h2, h3, h4 closedHost {} {} {}⟩

/-- A step of a context holding a strict frame: a strict frame of fewer behaviours, or a
result among its behaviours. -/
theorem lframe_step {E : Ctx} {X : Admin} (hX : LFrame X) {s : Store H} {F : Frame}
    {c' : Config H} (h : Step P closedHost ⟨s, F, E.plug [X]⟩ c') :
    c'.store = s ∧ c'.frame = F ∧
      ((∃ X', c'.code = E.plug [X'] ∧ LFrame X' ∧ LBeh P X' ⊆ LBeh P X ∧
          Step P closedHost (canon X) (canon X')) ∨
        ∃ r : Result, c'.code = E.plug r.toAdmin ∧ r.toBehaviour ∈ LBeh P X) := by
  obtain ⟨l, hst, hF, hcode⟩ := ctx_step hX h
  obtain ⟨hs, -, hn, hc⟩ := canon_step hX hst
  refine ⟨hs, hF, ?_⟩
  rcases hn with ⟨X', rfl, hX'⟩ | ⟨vs, rfl, -⟩ | rfl
  · exact .inl ⟨X', hcode, hX', behavioursOf_step_sub hc, hc⟩
  · refine .inr ⟨.values vs, hcode, ?_⟩
    exact mem_behavioursOf (Relation.ReflTransGen.single hc) (by simp [Result.toAdmin])
  · refine .inr ⟨.trap, hcode, ?_⟩
    exact mem_behavioursOf (Relation.ReflTransGen.single hc) rfl

/-- **The target callee reaches a result of the source callee**, in context. -/
theorem target_run {E : Ctx} {Y : Admin} (hY : LFrame Y) {r : Result}
    (hr : r.toBehaviour ∈ LBeh P Y) (t : Store H) (F : Frame) :
    Relation.TransGen (Step P closedHost) ⟨t, F, E.plug [Y]⟩ ⟨t, F, E.plug r.toAdmin⟩ := by
  rw [← frame_behaviours (host := closedHost) (s := t) (F := E.innerF F) hY] at hr
  rcases hr with ⟨c', r', hs, hc, hb⟩ | ⟨hb, -⟩
  · obtain rfl := Result.toBehaviour_injective hb
    have hrun := ctx_lift_steps E hY hs
    rw [hc] at hrun
    rcases Relation.ReflTransGen.cases_head hrun with he | ⟨d₁, h₁, h₂⟩
    · have he' : E.plug [Y] = E.plug r.toAdmin := congrArg Config.code he
      exact absurd (E.plug_inj he') ((Ctx.hole [] []).plug_ne_result hY r ∘ fun h => by
        simpa [Ctx.plug, vals] using h)
    · exact Relation.TransGen.head' h₁ h₂
  · exact absurd hb (Result.toBehaviour_ne_diverges r)

/-! ## One source step -/

/-- A source step from equal codes: one matched target step. -/
theorem rel_step_eq {c c₁ : Config H} {t : Store H} (hst : SRel P c.store t)
    (ht : Sim.ContextTyped c) (h : Step P closedHost c c₁) :
    ∃ d₁, Step P closedHost ⟨t, c.frame, c.code⟩ d₁ ∧ Rel P c₁ d₁ := by
  have ht' : Sim.ContextTyped (⟨c.store, c.frame, vals [] ++ c.code⟩ : Config H) := by
    simpa [vals] using ht
  obtain ⟨t', es, h1, h2, h3⟩ := step_match h [] ht' t hst
  exact ⟨⟨t', c₁.frame, es⟩, h1, h2, rfl, h3, ht.step h⟩

/-- A source step inside an in-flight callee: the target waits, or its callee runs to the
source callee's result. -/
theorem rel_step_flight {s t : Store H} {f : Frame} {E : Ctx} {X Y : Admin} {c₁ : Config H}
    (hst : SRel P s t) (ht : Sim.ContextTyped (⟨s, f, E.plug [X]⟩ : Config H))
    (hf : InFlight P X Y) (h : Step P closedHost ⟨s, f, E.plug [X]⟩ c₁) :
    ∃ d₁, Steps P closedHost ⟨t, f, E.plug [Y]⟩ d₁ ∧ Rel P c₁ d₁ := by
  have ht₁ : Sim.ContextTyped c₁ := ht.step h
  obtain ⟨hs₁, hF₁, hX₁ | ⟨r₁, hr₁, hb₁⟩⟩ := lframe_step hf.1 h
  · obtain ⟨X₁, hc₁, hl₁, hsub₁, -⟩ := hX₁
    exact ⟨_, .refl, hs₁ ▸ hst, hF₁, .inr ⟨E, X₁, Y, hc₁, rfl, hl₁, hf.2.1, hsub₁.trans hf.2.2⟩,
      ht₁⟩
  · have hrun : Relation.TransGen (Step P closedHost) ⟨t, f, E.plug [Y]⟩
        ⟨t, f, E.plug r₁.toAdmin⟩ := target_run (E := E) hf.2.1 (hf.2.2 hb₁) t f
    exact ⟨_, hrun.to_reflTransGen, hs₁ ▸ hst, hF₁, .inl hr₁, ht₁⟩

/-- **One source step** is matched by a target run. -/
theorem rel_step {c c₁ d : Config H} (hr : Rel P c d) (h : Step P closedHost c c₁) :
    ∃ d₁, Steps P closedHost d d₁ ∧ Rel P c₁ d₁ := by
  obtain ⟨t, F, dcode⟩ := d
  obtain ⟨hst, hfr, hcode, ht⟩ := hr
  dsimp only at hst hfr hcode
  rcases hcode with heq | ⟨E, X, Y, hX, hY, hf⟩
  · obtain ⟨d₁, h1, h2⟩ := rel_step_eq hst ht h
    rw [hfr, heq] at h1
    exact ⟨d₁, .single h1, h2⟩
  · obtain ⟨s, f, code⟩ := c
    dsimp only at hst hfr hX
    subst hX hfr hY
    exact rel_step_flight hst ht hf h

/-! ## Runs -/

/-- **Run transport.** -/
theorem run_transport {c c' : Config H} (h : Steps P closedHost c c') {r : Result}
    (hr : c'.code = r.toAdmin) : ∀ {d : Config H}, Rel P c d →
      ∃ d', Steps P closedHost d d' ∧ d'.code = r.toAdmin ∧ SRel P c'.store d'.store := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rintro d ⟨hst, -, hcode, -⟩
    rcases hcode with heq | ⟨E, X, Y, hX, -, hf⟩
    · exact ⟨d, .refl, heq ▸ hr, hst⟩
    · exact absurd (hX.symm.trans hr) (E.plug_ne_result hf.1 r)
  | head hstep _ ih =>
    intro d hrel
    obtain ⟨d₁, hd₁, hrel₁⟩ := rel_step hrel hstep
    obtain ⟨d', hd', hd'c, hs'⟩ := ih hrel₁
    exact ⟨d', hd₁.trans hd', hd'c, hs'⟩

/-! ## Divergence -/

/-- The configuration of a context holding `a`. -/
def plugC (s : Store H) (f : Frame) (E : Ctx) (a : Admin) : Config H := ⟨s, f, E.plug [a]⟩

/-- In-flight callee steps, in context and canonical. -/
def LocalR (P : Numerics.Profile) (s : Store H) (f : Frame) (E : Ctx) (a a' : Admin) : Prop :=
  LFrame a ∧ LFrame a' ∧ Step P closedHost (plugC s f E a) (plugC s f E a') ∧
    Step P closedHost (canon a) (canon a')

/-- Leaving an in-flight callee: it returns a result among its behaviours. -/
def Leave (P : Numerics.Profile) (s : Store H) (f : Frame) (E : Ctx) (a : Admin) (b : Config H) :
    Prop :=
  ¬ LFrame a ∨ (Step P closedHost (plugC s f E a) b ∧
    ∃ r : Result, b = ⟨s, f, E.plug r.toAdmin⟩ ∧ r.toBehaviour ∈ LBeh P a)

theorem flight_peel {s : Store H} {f : Frame} {E : Ctx} (a : Admin) (b : Config H)
    (hab : Step P closedHost (plugC s f E a) b) :
    (∃ next, LocalR P s f E a next ∧ b = plugC s f E next) ∨ Leave P s f E a b := by
  by_cases ha : LFrame a
  · obtain ⟨s₂, f₂, l₂⟩ := b
    obtain ⟨hs₁, hF₁, ⟨a', hc', ha', -, hcan⟩ | ⟨r, hr, hb⟩⟩ := lframe_step ha hab
    · have hb' : (⟨s₂, f₂, l₂⟩ : Config H) = plugC s f E a' := by
        dsimp only at hs₁ hF₁ hc'
        rw [hs₁, hF₁, hc']
        rfl
      exact .inl ⟨a', ⟨ha, ha', hb' ▸ hab, hcan⟩, hb'⟩
    · have hb' : (⟨s₂, f₂, l₂⟩ : Config H) = ⟨s, f, E.plug r.toAdmin⟩ := by
        dsimp only at hs₁ hF₁ hr
        rw [hs₁, hF₁, hr]
      exact .inr (.inr ⟨hab, r, hb', hb⟩)
  · exact .inr (.inl ha)

theorem localR_path {s : Store H} {f : Frame} {E : Ctx} {X a : Admin} (hX : LFrame X)
    (hp : Relation.ReflTransGen (LocalR P s f E) X a) :
    LFrame a ∧ Steps P closedHost (plugC s f E X) (plugC s f E a) ∧ LBeh P a ⊆ LBeh P X := by
  induction hp with
  | refl => exact ⟨hX, .refl, le_rfl⟩
  | tail _ hR ih =>
    exact ⟨hR.2.1, ih.2.1.tail hR.2.2.1, (behavioursOf_step_sub hR.2.2.2).trans ih.2.2⟩

/-- A callee diverging in flight: so does the target callee. -/
theorem flight_diverges {s t : Store H} {f : Frame} {E : Ctx} {X Y : Admin}
    (hf : InFlight P X Y) (hloc : Silmaril.InfiniteTrace (LocalR P s f E) X) :
    Diverges P closedHost ⟨t, f, E.plug [Y]⟩ := by
  have hcan : Diverges P closedHost (canon X) :=
    Silmaril.InfiniteTrace.map canon (fun _ _ h => h.2.2.2) hloc
  have hdivY : Behaviour.diverges ∈ behavioursOf P closedHost ⟨t, E.innerF f, [Y]⟩ := by
    rw [frame_behaviours hf.2.1]
    exact hf.2.2 (.inr ⟨rfl, hcan⟩)
  rcases hdivY with ⟨-, r, -, -, hb⟩ | ⟨-, hdY⟩
  · exact absurd hb.symm (Result.toBehaviour_ne_diverges r)
  · exact ctx_lift_diverges E hf.2.1 hdY

/-- One round of divergence transport inside an in-flight callee. -/
theorem div_flight {s t : Store H} {f : Frame} {E : Ctx} {X Y : Admin} (hst : SRel P s t)
    (ht : Sim.ContextTyped (⟨s, f, E.plug [X]⟩ : Config H)) (hf : InFlight P X Y)
    (hd : Diverges P closedHost ⟨s, f, E.plug [X]⟩) :
    Diverges P closedHost ⟨t, f, E.plug [Y]⟩ ∨ ∃ d', Relation.TransGen (Step P closedHost)
      ⟨t, f, E.plug [Y]⟩ d' ∧ ∃ c', Rel P c' d' ∧ Diverges P closedHost c' := by
  rcases Silmaril.InfiniteTrace.context_decompose (LocalR P s f E) (Step P closedHost)
      (plugC s f E) (Leave P s f E) flight_peel hd with hloc | ⟨a, b, hpath, hbd, hdb⟩
  · exact .inl (flight_diverges hf hloc)
  · obtain ⟨ha, hrun, hsuba⟩ := localR_path hf.1 hpath
    rcases hbd with hna | ⟨hab, r, rfl, hb⟩
    · exact (hna ha).elim
    · have htrun : Relation.TransGen (Step P closedHost) ⟨t, f, E.plug [Y]⟩
          ⟨t, f, E.plug r.toAdmin⟩ := target_run (E := E) hf.2.1 (hf.2.2 (hsuba hb)) t f
      exact .inr ⟨_, htrun, ⟨s, f, E.plug r.toAdmin⟩,
        ⟨hst, rfl, .inl rfl, ht.steps (hrun.tail hab)⟩, hdb⟩

/-- One round of divergence transport: the target diverges, or takes at least one step to a
configuration related to a divergent one. -/
theorem div_progress {c d : Config H} (hr : Rel P c d) (hd : Diverges P closedHost c) :
    Diverges P closedHost d ∨ ∃ d', Relation.TransGen (Step P closedHost) d d' ∧
      ∃ c', Rel P c' d' ∧ Diverges P closedHost c' := by
  obtain ⟨t, F, dcode⟩ := d
  obtain ⟨hst, hfr, hcode, ht⟩ := hr
  dsimp only at hst hfr hcode
  rcases hcode with heq | ⟨E, X, Y, hX, hY, hf⟩
  · obtain ⟨c₁, hstep, hd₁⟩ := hd.unfold
    obtain ⟨d₁, h1, h2⟩ := rel_step_eq hst ht hstep
    rw [hfr, heq] at h1
    exact .inr ⟨d₁, .single h1, c₁, h2, hd₁⟩
  · obtain ⟨s, f, code⟩ := c
    dsimp only at hst hfr hX
    subst hX hfr hY
    exact div_flight hst ht hf hd

/-- **Divergence transport.** -/
theorem div_transport {c d : Config H} (hr : Rel P c d) (hd : Diverges P closedHost c) :
    Diverges P closedHost d := by
  refine Silmaril.InfiniteTrace.coinduct (fun d => ∃ d₀, Steps P closedHost d d₀ ∧
      (Diverges P closedHost d₀ ∨ ∃ c, Rel P c d₀ ∧ Diverges P closedHost c)) ?_
    ⟨d, .refl, .inr ⟨c, hr, hd⟩⟩
  rintro d ⟨d₀, hp, hq⟩
  rcases Relation.ReflTransGen.cases_head hp with rfl | ⟨d₁, h₁, h₂⟩
  · rcases hq with hdd | ⟨c, hr, hd⟩
    · obtain ⟨d₁, h₁, hd₁⟩ := hdd.unfold
      exact ⟨d₁, h₁, d₁, .refl, .inl hd₁⟩
    · rcases div_progress hr hd with hdd | ⟨d', hp', c', hr', hd'⟩
      · obtain ⟨d₁, h₁, hd₁⟩ := hdd.unfold
        exact ⟨d₁, h₁, d₁, .refl, .inl hd₁⟩
      · obtain ⟨d₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp hp'
        exact ⟨d₁, h₁, d', h₂, .inr ⟨c', hr', hd'⟩⟩
  · exact ⟨d₁, h₁, d₀, h₂, hq⟩

/-- **Behaviour inclusion** for related configurations. -/
theorem behavioursOf_rel {c d : Config H} (hr : Rel P c d) :
    behavioursOf P closedHost c ⊆ behavioursOf P closedHost d := by
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, hd⟩)
  · obtain ⟨d', hd', hd'c, -⟩ := run_transport hs hc hr
    exact mem_behavioursOf hd' hd'c
  · exact .inr ⟨rfl, div_transport hr hd⟩

/-! ## Invocations -/

theorem invoke_rel {s t : Store H} (hst : SRel P s t) (hs : StoreOk s) {a : Nat} {vs : List Val}
    (hok : InvokeOk s a vs) : Rel P (invoke s a vs) (invoke t a vs) := by
  refine ⟨hst, rfl, .inl ?_, ?_⟩
  · simp only [invoke, ← List.getElem?_map, hst.types]
  · obtain ⟨_, _, _, -, -, hcfg⟩ := Silmaril.Wasm.Execution.Core.invoke_ok hs hok
    exact Sim.ContextTyped.of_configOk hcfg

/-- **Callers of equivalent strict leaf functions.** In typed stores related by `SRel P`
(functions equal, or equivalent strict leaf functions), every typed invocation of **any**
function has the same Core 3.0 behaviours under the closed host, divergence included. -/
theorem behaviours_srel {s t : Store H} (hst : SRel P s t) (hs : StoreOk s) (ht : StoreOk t)
    {a : Nat} {vs : List Val} (hok : InvokeOk s a vs) :
    behaviours P closedHost s a vs = behaviours P closedHost t a vs :=
  Set.Subset.antisymm (behavioursOf_rel (invoke_rel hst hs hok))
    (behavioursOf_rel (invoke_rel hst.symm ht (Binaryen.invokeOk_of_storeRel hst hok)))

end Silmaril.Proofs.Wasm.SSA.CoreCert
