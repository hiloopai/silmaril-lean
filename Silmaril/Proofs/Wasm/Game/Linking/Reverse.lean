module

public import Silmaril.Proofs.Wasm.Game.Linking.Simulation
public import Silmaril.Proofs.Wasm.Game.Linking.Inversion
public import Silmaril.Proofs.Wasm.Game.Machine.SoftJoin

/-!
# Static linking: the backward simulation, every profile

silmaril-lean proves that the linker relation `Simulation.Matching` is a forward simulation
of host-free Core steps under every profile (`WholeSimulation.step`), and leaves the backward
direction open (`Silmaril/Wasm/Link/LinkObservation.lean`, "Nondeterministic profile"). This
file proves it, for every profile `P`:

* `soft_back`: a `Soft` step of the linked configuration (a profile choice, i.e. a numeric,
  vector, table or memory step, or a bubble, under the context rules) is a step of every
  shared configuration related to it. Numeric and vector instructions are not relocated and
  their operands are equal, so the shared code takes the same choice; table and memory
  instructions only occur in unchanged code, where the stores agree on tables, memories,
  element and data segments (`table_back`, `memory_back`);
* `internal_reverse`: **lock-step backward simulation**. A typed shared configuration steps
  (progress), or is finished or at a host call, which the linked one then is too; the forward
  image of its step is the linked step, unless the linked step is `Soft`
  (`Choice.eq_or_soft`, determinism up to profile choices), and then `soft_back` applies;
* `reachReverse_all`: `ReachReverse P` for every profile, with no hypothesis.

New (no source file). The deterministic proof it replaces (`reach_reverse`, uniqueness of
normal forms) is in `Silmaril.Proofs.Wasm.Game.Linking.Simulation`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Proofs.Wasm.Game Silmaril.Proofs.Wasm.Game.Linking Silmaril.Proofs.Wasm.Game.Choice
  Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Link.GC
  Silmaril.Wasm.Link.GC.AdminRelation

namespace Linking

variable {H : Type}

/-! ### Choice steps -/

theorem famOf_plain_of_ne {e : Admin} (h : famOf e ≠ .control) : ∃ j, e = .plain j := by
  cases e with
  | plain j => exact ⟨j, rfl⟩
  | _ => exact absurd rfl h

/-- The left-hand side of a choice family rule. -/
theorem famRel_shape {P : Profile} {k : Fam} {s : Store H} {f : Frame} {code : List Admin}
    {c : Config H} (hk : ChoiceFam k) (h : FamRel P k s f code c) :
    ∃ args j, code = vals args ++ [.plain j] ∧ famOf (.plain j) = k := by
  have hs : FamShape k code := by
    cases k with
    | numeric => obtain ⟨_, hn, -⟩ := h; exact NumericStep.shape hn
    | vector => obtain ⟨_, hn, -⟩ := h; exact VectorStep.shape hn
    | table => exact TableStep.shape h
    | memory => exact MemoryStep.shape h
    | _ => exact hk.elim
  obtain ⟨args, e, rfl, -, he⟩ := hs
  have hne : famOf e ≠ .control := by intro hc; rw [hc] at he; subst he; exact hk
  obtain ⟨j, rfl⟩ := famOf_plain_of_ne hne
  exact ⟨args, j, rfl, he⟩

/-- The shared code at a linked choice redex is the same code. -/
theorem choice_code {mode : Mode} {m m' : ModuleInst} {code code' : List Admin} {args : List Val}
    {j : Instr} (h : Control mode m m' code code') (hcode : code' = vals args ++ [.plain j])
    (hk : ChoiceFam (famOf (.plain j))) :
    code = code' ∧ (mode = .same ∨ famOf (.plain j) = .numeric) := by
  rw [hcode] at h ⊢
  obtain ⟨A, B, hAB, hA, hB⟩ := Control.split_right h
  obtain ⟨x, hx, hone⟩ := Control.single_right hB
  obtain ⟨hxj, hm⟩ := hone.choice_right hk
  rw [hAB, hx, hxj, Control.values_right hA]
  exact ⟨rfl, hm⟩

theorem back_numeric {P : Profile} {mode : Mode} {s s' : Store H} {f f' : Frame}
    {code : List Admin} {d' : Config H} (h : FamRel P .numeric s' f' code d')
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', code⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching mode d d' := by
  obtain ⟨out, hn, hd⟩ := h
  rw [hd]
  exact ⟨⟨s, f, out⟩, .numeric hn,
    ⟨m.stores, m.frames, (LeafControlSimulation.numeric_control hn m.code).2⟩⟩

theorem back_vector {P : Profile} {mode : Mode} {s s' : Store H} {f f' : Frame}
    {code : List Admin} {d' : Config H} (h : FamRel P .vector s' f' code d')
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', code⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching mode d d' := by
  obtain ⟨out, hn, hd⟩ := h
  rw [hd]
  exact ⟨⟨s, f, out⟩, .vector hn,
    ⟨m.stores, m.frames, (LeafControlSimulation.vector_control hn m.code).2⟩⟩

theorem back_table {P : Profile} {s s' : Store H} {f : Frame} {code : List Admin}
    {d' : Config H} (h : FamRel P .table s' f code d')
    (m : Simulation.Matching .same ⟨s, f, code⟩ ⟨s', f, code⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching .same d d' := by
  rcases d' with ⟨s'', f'', out⟩
  obtain ⟨s₂, ht, hr⟩ := table_back m.stores h
  exact ⟨⟨s₂, f'', out⟩, .table ht, ⟨hr, Frames.same f'', Control.same _ _⟩⟩

theorem back_memory {P : Profile} {s s' : Store H} {f : Frame} {code : List Admin}
    {d' : Config H} (h : FamRel P .memory s' f code d')
    (m : Simulation.Matching .same ⟨s, f, code⟩ ⟨s', f, code⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching .same d d' := by
  rcases d' with ⟨s'', f'', out⟩
  obtain ⟨s₂, ht, hr⟩ := memory_back m.stores h
  exact ⟨⟨s₂, f'', out⟩, .memory ht, ⟨hr, Frames.same f'', Control.same _ _⟩⟩

/-- A choice step of the linked store outside the numeric family is in unchanged code. -/
theorem same_of_not_numeric {mode : Mode} {f f' : Frame} {m m' : ModuleInst}
    {code code' : List Admin} (hfr : Frames mode f f') (hc : Control mode m m' code code')
    {j : Instr} (hm : mode = .same ∨ famOf (.plain j) = .numeric)
    (hj : famOf (.plain j) ≠ .numeric) :
    mode = .same ∧ f = f' ∧ Control .same m m' code code' := by
  have hms : mode = .same := hm.resolve_right hj
  subst hms
  exact ⟨rfl, Frames.same_eq hfr, hc⟩

/-- **Choice steps go back**: the shared configuration takes the same choice. -/
theorem back_choice {P : Profile} {mode : Mode} {k : Fam} {s s' : Store H} {f f' : Frame}
    {code code' : List Admin} {d' : Config H} (hk : ChoiceFam k) (h : FamRel P k s' f' code' d')
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching mode d d' := by
  obtain ⟨args, j, hcode', hjk⟩ := famRel_shape hk h
  obtain ⟨hcc, hm⟩ : code = code' ∧ (mode = .same ∨ famOf (.plain j) = .numeric) :=
    choice_code m.code hcode' (hjk ▸ hk)
  have m' : Simulation.Matching mode ⟨s, f, code'⟩ ⟨s', f', code'⟩ := hcc ▸ m
  rw [hcc]
  cases k with
  | numeric => exact back_numeric h m'
  | vector => exact back_vector h m'
  | table =>
    obtain ⟨rfl, rfl, -⟩ := same_of_not_numeric m.frames m.code hm (by rw [hjk]; decide)
    exact back_table h m'
  | memory =>
    obtain ⟨rfl, rfl, -⟩ := same_of_not_numeric m.frames m.code hm (by rw [hjk]; decide)
    exact back_memory h m'
  | _ => exact hk.elim

/-! ### Bubbles -/

theorem bubble_control (mode : Mode) (m m' : ModuleInst) {X : List Admin} (hX : IsBubble X) :
    Control mode m m' X X := by
  rcases hX with rfl | ⟨a, rfl⟩
  · exact .trap .nil
  · exact .ref (.throwRef .nil)

theorem bubble_right {mode : Mode} {m m' : ModuleInst} {xs X : List Admin} (hX : IsBubble X)
    (h : Control mode m m' xs X) : xs = X := by
  rcases hX with rfl | ⟨a, rfl⟩
  · exact Control.trap_right h
  · exact Control.throwing_right h

/-- **Bubbles go back**: the shared code has the same bubble. -/
theorem back_bubble {P : Profile} {mode : Mode} {s s' : Store H} {f f' : Frame}
    {code code' : List Admin} {d' : Config H} (h : Bubble s' f' code' d')
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧ Simulation.Matching mode d d' := by
  obtain ⟨p, q, X, u, r, rfl, hX, hqu, rfl⟩ := h
  have hc : Control mode f.module f'.module code (vals (p ++ q) ++ X ++ (u ++ r)) := m.code
  obtain ⟨A, B, rfl, hA, hB⟩ := Control.split_right hc
  obtain ⟨V, X₀, rfl, hV, hX₀⟩ := Control.split_right hA
  obtain ⟨U, R, rfl, hU, hR⟩ := Control.split_right hB
  have hV' : V = vals (p ++ q) := Control.values_right hV
  have hX' : X₀ = X := bubble_right hX hX₀
  subst hV' hX'
  have hqU : q ≠ [] ∨ U ≠ [] := by
    have hl : U.length = u.length := hU.length_eq
    rcases hqu with hq | hu
    · exact .inl hq
    · exact .inr (fun h => hu (List.eq_nil_of_length_eq_zero (by rw [← hl, h]; rfl)))
  have hb : Bubble s f (vals (p ++ q) ++ X₀ ++ (U ++ R)) ⟨s, f, vals p ++ X₀ ++ R⟩ :=
    ⟨p, q, X₀, U, R, rfl, hX, hqU, rfl⟩
  refine ⟨_, bubble_step hb, m.stores, m.frames, ?_⟩
  exact ((Control.values mode _ _ p).append (bubble_control mode _ _ hX)).append hR

/-! ### Contexts -/

theorem back_instrs {P : Profile} {s s' s'' : Store H} {f f' f'' : Frame} {vs : List Val}
    {is' is'' rest' : List Admin} (hs : Soft P ⟨s', f', is'⟩ ⟨s'', f'', is''⟩)
    (ih : ∀ {mode : Mode} {c : Config H}, Simulation.Matching mode c ⟨s', f', is'⟩ →
      ∃ d, Step P noHost c d ∧ Simulation.Matching mode d ⟨s'', f'', is''⟩)
    {mode : Mode} {code : List Admin}
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', vals vs ++ is' ++ rest'⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧
      Simulation.Matching mode d ⟨s'', f'', vals vs ++ is'' ++ rest'⟩ := by
  have hc : Control mode f.module f'.module code (vals vs ++ is' ++ rest') := m.code
  obtain ⟨A, R, rfl, hA, hR⟩ := Control.split_right hc
  obtain ⟨V, I, rfl, hV, hI⟩ := Control.split_right hA
  have hV' : V = vals vs := Control.values_right hV
  subst hV'
  obtain ⟨d, hd, md⟩ := ih (c := ⟨s, f, I⟩) ⟨m.stores, m.frames, hI⟩
  have hfd : d.frame.module = f.module := Simulation.frame_module hd
  have hft : f''.module = f'.module := Simulation.frame_module (Soft.step hs)
  have hR' : Control mode d.frame.module f''.module R rest' := by rw [hfd, hft]; exact hR
  refine ⟨⟨d.store, d.frame, vals vs ++ d.code ++ R⟩, lift_instrs vs R _ _ hd, md.stores,
    md.frames, ?_⟩
  exact ((Control.values mode _ _ vs).append md.code).append hR'

theorem back_label {P : Profile} {s s' s'' : Store H} {f f' f'' : Frame} {n : Nat}
    {cont' : List Instr} {is' is'' : List Admin} (ih : ∀ {mode : Mode} {c : Config H},
      Simulation.Matching mode c ⟨s', f', is'⟩ →
      ∃ d, Step P noHost c d ∧ Simulation.Matching mode d ⟨s'', f'', is''⟩)
    {mode : Mode} {code : List Admin}
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', [.label n cont' is']⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧
      Simulation.Matching mode d ⟨s'', f'', [.label n cont' is'']⟩ := by
  have hc : Control mode f.module f'.module code [.label n cont' is'] := m.code
  obtain ⟨x, rfl, hx⟩ := Control.single_right hc
  obtain ⟨cont, is, rfl, hk, hi⟩ := hx.label_right
  obtain ⟨d, hd, md⟩ := ih (c := ⟨s, f, is⟩) ⟨m.stores, m.frames, hi⟩
  exact ⟨_, lift_label n cont _ _ hd, md.stores, md.frames, .label hk md.code .nil⟩

theorem back_handler {P : Profile} {s s' s'' : Store H} {f f' f'' : Frame} {n : Nat}
    {cs : List Catch} {is' is'' : List Admin} (ih : ∀ {mode : Mode} {c : Config H},
      Simulation.Matching mode c ⟨s', f', is'⟩ →
      ∃ d, Step P noHost c d ∧ Simulation.Matching mode d ⟨s'', f'', is''⟩)
    {mode : Mode} {code : List Admin}
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', [.handler n cs is']⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧
      Simulation.Matching mode d ⟨s'', f'', [.handler n cs is'']⟩ := by
  have hc : Control mode f.module f'.module code [.handler n cs is'] := m.code
  obtain ⟨x, rfl, hx⟩ := Control.single_right hc
  obtain ⟨rfl, hmod, is, rfl, hi⟩ := hx.handler_right
  have hi' : Control .same f.module f'.module is is' := by rw [← hmod]; exact hi
  obtain ⟨d, hd, md⟩ := ih (c := ⟨s, f, is⟩) ⟨m.stores, m.frames, hi'⟩
  have hmd : d.frame = f'' := Frames.same_eq md.frames
  have hin : Control .same d.frame.module d.frame.module d.code is'' := by
    have h := md.code
    rw [← hmd] at h
    exact h
  refine ⟨_, lift_handler n cs _ _ hd, md.stores, md.frames, ?_⟩
  rw [← hmd]
  exact .handler hin .nil

theorem back_frame {P : Profile} {s s' s'' : Store H} {f f' fi' fi'' : Frame} {n : Nat}
    {is' is'' : List Admin} (ih : ∀ {mode : Mode} {c : Config H},
      Simulation.Matching mode c ⟨s', fi', is'⟩ →
      ∃ d, Step P noHost c d ∧ Simulation.Matching mode d ⟨s'', fi'', is''⟩)
    {mode : Mode} {code : List Admin}
    (m : Simulation.Matching mode ⟨s, f, code⟩ ⟨s', f', [.frame n fi' is']⟩) :
    ∃ d, Step P noHost ⟨s, f, code⟩ d ∧
      Simulation.Matching mode d ⟨s'', f', [.frame n fi'' is'']⟩ := by
  have hc : Control mode f.module f'.module code [.frame n fi' is'] := m.code
  obtain ⟨x, rfl, hx⟩ := Control.single_right hc
  obtain ⟨innerMode, fi, is, rfl, hf, hi⟩ := hx.frame_right
  obtain ⟨d, hd, md⟩ := ih (mode := innerMode) (c := ⟨s, fi, is⟩) ⟨m.stores, hf, hi⟩
  exact ⟨⟨d.store, f, [.frame n d.frame d.code]⟩, lift_frame n f _ _ hd, md.stores, m.frames,
    .frame md.frames md.code .nil⟩

/-- **`Soft` steps go back**: a `Soft` step of the linked configuration is a step of every
shared configuration related to it. -/
theorem soft_back {P : Profile} {c' d' : Config H} (hs : Soft P c' d') :
    ∀ {mode : Mode} {c : Config H}, Simulation.Matching mode c c' →
      ∃ d, Step P noHost c d ∧ Simulation.Matching mode d d' := by
  induction hs with
  | choice hk h => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_choice hk h m
  | bubble h => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_bubble h m
  | instrs hs ih => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_instrs hs ih m
  | label _ ih => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_label ih m
  | handler _ ih => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_handler ih m
  | frame _ ih => intro mode c m; rcases c with ⟨_, _, _⟩; exact back_frame ih m

/-! ### The backward simulation -/

/-- A typed shared configuration related to a linked one that steps has a host-free step. -/
theorem source_internal {P : Profile} {x x' y' : Store Nat × Thread} {mode : Mode}
    {ts : List CValType} (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching mode (x.2.config x.1) (x'.2.config x'.1))
    (step : InternalP P x' y') : ∃ y, InternalP P x y := by
  rcases x with ⟨s, t⟩
  rcases x' with ⟨s', t'⟩
  rcases Config.progress (P := P) (host := divHost) divHost_ok typed with
    ⟨r, hr⟩ | ⟨c₁, hc₁⟩
  · show ∃ y, InternalP P (s, t) y
    have hr' : (t'.config s').code = r.toAdmin := by
      have hcode : Control mode (t.config s).frame.module (t'.config s').frame.module
          r.toAdmin (t'.config s').code := hr ▸ matching.code
      cases r with
      | values vs => exact hcode.values_left
      | trap => exact hcode.trap_singleton
      | throw a => exact hcode.throwing_left
    exact absurd step (toAdmin_no_internal hr' y')
  · show ∃ y, InternalP P (s, t) y
    rcases (stepP_iff P divHost s t c₁).mp hc₁ with ⟨s₁, f₁, code₁, -, hi⟩ |
      ⟨E, a, h, args, hd, -⟩
    · exact ⟨_, hi⟩
    · have hstores : StoreRelation.Related s s' := by
        simpa only [Thread.config_store] using matching.stores
      obtain ⟨E', hd', -⟩ := decompose?_transfer hstores matching.code hd
      exact absurd step (decompose?_no_internal hd' y')

theorem step_internalP {P : Profile} {x : Store Nat × Thread} {d : Config Nat}
    (h : Step P noHost (x.2.config x.1) d) : InternalP P x (d.store, .active d.frame d.code) :=
  ⟨d.frame, d.code, rfl, by rcases d with ⟨_, _, _⟩; exact h⟩

/-- **Backward simulation of host-free steps along the linker relation**, every profile: a
host-free step of the linked configuration is matched by one of the typed shared
configuration. -/
theorem internal_reverse {P : Profile} {x x' y' : Store Nat × Thread} {mode : Mode}
    {ts : List CValType} (typed : ConfigOk (x.2.config x.1) ts)
    (matching : Simulation.Matching mode (x.2.config x.1) (x'.2.config x'.1))
    (step : InternalP P x' y') :
    ∃ y, InternalP P x y ∧ Simulation.Matching mode (y.2.config y.1) (y'.2.config y'.1) := by
  obtain ⟨y₁, hy₁⟩ := source_internal typed matching step
  obtain ⟨y₁', hstep', hm₁⟩ := internal_simulation hy₁ typed matching
  have ht : Step P noHost (x'.2.config x'.1) (y'.2.config y'.1) := InternalP.toStep P _ step
  have ht' : Step P noHost (x'.2.config x'.1) (y₁'.2.config y₁'.1) :=
    InternalP.toStep P _ hstep'
  rcases eq_or_soft ht' ht with heq | hsoft
  · refine ⟨y₁, hy₁, ?_⟩
    rw [heq]
    exact hm₁
  · obtain ⟨d, hd, hmd⟩ := soft_back hsoft matching
    exact ⟨(d.store, .active d.frame d.code), step_internalP hd, hmd⟩

private theorem storeOk_of_typed' {x : Store Nat × Thread} {ts : List CValType}
    (typed : ConfigOk (x.2.config x.1) ts) : StoreOk x.1 := by
  have h := ConfigOk.storeOk typed
  rwa [Thread.config_store] at h

/-- **The reverse simulation of runs to a result holds for every profile.** -/
theorem reachReverse_all (P : Profile) : ReachReverse P := by
  intro x x' y' ts r typed matching run final
  induction run using Relation.ReflTransGen.head_induction_on generalizing x with
  | refl =>
    show ∃ y, Reach P x y ∧ ResultAt y.1 y.2 r ∧
      Simulation.Matching .same (y.2.config y.1) (y'.2.config y'.1)
    have hc : Control .same (x.2.config x.1).frame.module (y'.2.config y'.1).frame.module
        (x.2.config x.1).code r.toAdmin := by
      have h := matching.code
      rw [show (y'.2.config y'.1).code = r.toAdmin from final] at h
      exact h
    exact ⟨x, .refl, Control.result_right hc, matching⟩
  | head hstep _ ih =>
    obtain ⟨y, hy, hm⟩ := internal_reverse typed matching hstep
    have hty : ConfigOk (y.2.config y.1) ts :=
      (reachableP_typed (.single hy) (storeOk_of_typed' typed) typed).2
    obtain ⟨z, hz, hres, hmz⟩ := ih hty hm
    exact ⟨z, .head hy hz, hres, hmz⟩

end Linking

end Silmaril.Wasm.Game
