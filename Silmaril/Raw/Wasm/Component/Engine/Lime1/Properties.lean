module

public import Silmaril.Wasm.Component.Reference.Engine.Lime1.Properties.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Lime1
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Runtime.Host
public import Silmaril.Raw.Wasm.Component.Wasm.Execution.Memory.Lemmas

/-!
# The Lime1 core engine: laws and bridges

Properties of `lime1` (`Engine/Lime1.lean`):

* `Grows s s'`: the store relation that internal steps, host allocation, memory writes and
  preparation establish (functions are kept, tables and memories only grow, with the same
  maximum), and `Grows.extends`: it implies the engine-level `CoreEngine.Extends`. The callout
  field of `Extends` holds because a callout found by `decompose?` stays located in any store
  that keeps the existing functions (`status_callout_of_funcs`).
* `lawful : CoreEngine.Lawful lime1`.
* `HostStep host`: the component-level interleaving of `lime1` internal steps and callouts, each
  answered by the host relation (`host h s args (.returned s' r)`) and then resumed.
  `steps_bridge`: its finite runs are exactly the runs of `Lime1.Execution.Steps host` (from the
  `step_iff`, `Answer.iff` and `decompose?_complete`); `diverges_bridge`: an infinite
  `Lime1.Execution.Step host` trace is an infinite `HostStep` trace or reaches a callout whose
  host answer diverges (the machine's `invokeHostDiverges` self-loop), and conversely.
* `instantiation_bridge`: `Lime1.Execution.Instantiation host before m imports after inst outcome`
  holds iff the module is valid, the imports match, `lime1.prepare?` succeeds with instance `inst`,
  and the start thread (if any) runs by `HostStep host` to the outcome (no start: the prepared
  store with no values). The start code runs under the frame `⟨[], inst⟩` in `Lime1.Execution`
  and under the empty frame in the engine (`lime1.invoke`); `steps_reframe` shows that code
  made of values, traps, invocations and frames does not observe the outer frame.
* `instantiationDiverges_bridge`: `Lime1.Execution.InstantiationDiverges host before m imports`
  holds iff the module is valid, the imports match, `lime1.prepare?` returns a start function
  `a`, and the machine diverges from the start thread `lime1.invoke a []` (by
  `diverges_bridge`: an infinite `HostStep` trace or a run to a diverging host answer);
  `diverges_reframe` is the frame irrelevance of infinite traces.
* Tests: the inline adder module (`local.get 0; local.get 1; i32.add`) runs to `[x + y]` with
  `lime1Exec` (kernel `rfl`, for all `x y`, no memory); a function calling a host import pauses
  with status `callout` and the right arguments, and resumes to its result (kernel `rfl`).

Not claimed: `ResumeLawful lime1` (false for ill-typed host results), determinism of internal
steps (NaN results and `memory.grow` failure are nondeterministic), and any import typing of
`prepare?` (import matching is the separate `ImportsMatch` premise).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Lime1

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Semantics (MemoryView WasmSemantics)

/-! ## Store growth -/

/-! ## Status -/

/-! ## Preparation, allocation and memory writes grow the store -/

/-- Prepared start code is empty or a single invocation. -/
theorem prepare?_start {H : Type} {s : Wasm.Lime1.Execution.Store H} {m : Wasm.Lime1.Module}
    {imports : List ExternVal} {p : Wasm.Lime1.Execution.Prepared H}
    (h : Wasm.Lime1.Execution.prepare? s m imports = some p) :
    p.start = [] ∨ ∃ a, p.start = [.invoke a] := by
  simp only [Wasm.Lime1.Execution.prepare?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at h
  obtain ⟨⟨a, mod⟩, -, _, -, _, -, h⟩ := h
  split at h
  · obtain ⟨st, hst, e⟩ := Option.bind_eq_some_iff.mp h
    rw [← Option.some.inj e]
    cases hst
    exact .inl rfl
  · obtain ⟨st, hst, e⟩ := Option.bind_eq_some_iff.mp h
    rw [← Option.some.inj e]
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.mp hst
    exact .inr ⟨a, rfl⟩

theorem memWrite?_memories {H : Type} {s s' : Wasm.Lime1.Execution.Store H} {m : MemAddr}
    {st : Nat} {bs : ByteArray} (h : memWrite? s m st bs = some s') (m' : MemAddr) :
    (m' = m → ∃ mi d, s.memories[m.value]? = some mi ∧
      Memory.writeBytes mi.data st bs = some d ∧
      s'.memories[m'.value]? = some {mi with data := d}) ∧
    (m' ≠ m → s'.memories[m'.value]? = s.memories[m'.value]?) := by
  obtain ⟨mi, d, hmi, hd, rfl⟩ := memWrite?_eq_some h
  refine ⟨fun e => ⟨mi, d, hmi, hd, ?_⟩, fun e => ?_⟩
  · subst e
    exact List.getElem?_set_self (List.getElem?_eq_some_iff.1 hmi).1
  · have : m.value ≠ m'.value := fun e' => e (by cases m; cases m'; simp_all)
    exact List.getElem?_set_ne this

/-! ## Lawfulness -/

private theorem invoke_not_mem_result (a : FuncAddr) (r : Result) :
    AdminInstr.invoke a ∉ Wasm.Lime1.Execution.result r := by
  cases r with
  | trap => simp [Wasm.Lime1.Execution.result]
  | values vs =>
    simp only [Wasm.Lime1.Execution.result, Wasm.Lime1.Execution.values, List.mem_map, not_exists,
      not_and]
    intro v _ e
    rcases v with ⟨(t | t), b⟩ <;> cases e

theorem terminal?_invoke {H : Type} (a : FuncAddr) (args : List FlatValue) :
    Wasm.Lime1.Execution.terminal? (invoke (H := H) a args).code = none := by
  rw [Wasm.Lime1.Execution.terminal?_eq_none_iff]
  intro r e
  exact invoke_not_mem_result a r (e ▸ by simp [invoke])

/-! ## Component-level runs with a host relation -/

/-- Resuming the callout found by `decompose?` is `Lime1.Execution.resume` without its store. -/
theorem toConfig_resume {H : Type} {s s' : Wasm.Lime1.Execution.Store H} {t : Thread H}
    {c : Runtime.Callout H Wasm.Lime1.Instr}
    (hd : Wasm.Lime1.Execution.decompose? (toConfig (s, t)) = some c) (r : Result) :
    toConfig (s', resume s t (ofResult r)) =
      Wasm.Lime1.Execution.resume (toConfig (s, t)) c s' r := by
  simp only [resume, hd, toResult_ofResult]
  rfl

theorem HostStep.step {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {c c' : lime1.Config H} (h : HostStep host c c') :
    Wasm.Lime1.Execution.Step host (toConfig c) (toConfig c') := by
  cases h with
  | internal h => exact Wasm.Lime1.Execution.Step.of_internal h
  | answer hc hr =>
    obtain ⟨c₀, hd, rfl, rfl⟩ := status_eq_callout.mp hc
    change Wasm.Lime1.Execution.Step host _ (toConfig (_, resume _ _ _))
    rw [toConfig_resume hd]
    exact Wasm.Lime1.Execution.Step.callout_returned (Wasm.Lime1.Execution.decompose?_sound hd) hr

/-- Inversion of a machine step from an engine configuration: a component-level step, or the
self-loop of a callout whose host answer diverges. -/
theorem step_hostStep {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {c : lime1.Config H} {b : Wasm.Lime1.Execution.Config H}
    (h : Wasm.Lime1.Execution.Step host (toConfig c) b) :
    HostStep host c (ofConfig b) ∨ (b = toConfig c ∧ ∃ h args,
      lime1.status c.1 c.2 = .callout h args ∧ host h c.1 args .diverged) := by
  obtain ⟨s, t⟩ := c
  rcases Wasm.Lime1.Execution.step_iff.mp h with hi | ⟨cc, hc, hans⟩
  · exact .inl (.internal hi)
  · obtain ⟨c₀, hd, -, -, hh, ha, hres⟩ := Wasm.Lime1.Execution.decompose?_complete hc
    have hs : lime1.status s t = .callout cc.host cc.args :=
      status_eq_callout.mpr ⟨c₀, hd, hh, ha⟩
    cases hans with
    | returned s' r hr =>
      left
      have e : ofConfig (Wasm.Lime1.Execution.resume (toConfig (s, t)) cc s' r) =
          (s', resume s t (ofResult r)) := by
        rw [← hres, ← toConfig_resume hd, ofConfig_toConfig]
      rw [e]
      exact .answer hs hr
    | diverged hdv => exact .inr ⟨rfl, cc.host, cc.args, hs, hdv⟩

/-- **Finite bridge.** Component-level runs (internal steps, and callouts answered by the host
relation and resumed) are exactly the runs of `Lime1.Execution.Steps host`. -/
theorem steps_bridge {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H)
    (c c' : lime1.Config H) :
    HostSteps host c c' ↔ Wasm.Lime1.Execution.Steps host (toConfig c) (toConfig c') := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail step.step
  · intro h
    suffices ∀ b, Wasm.Lime1.Execution.Steps host (toConfig c) b → HostSteps host c (ofConfig b)
      from this _ h
    intro b hb
    induction hb with
    | refl => exact .refl
    | @tail b₁ b₂ _ step ih =>
      have step' : Wasm.Lime1.Execution.Step host (toConfig (ofConfig b₁)) b₂ := step
      rcases step_hostStep step' with hs | ⟨e, -⟩
      · exact ih.tail hs
      · rw [e, ofConfig_toConfig]
        exact ih

/-- **Divergence bridge.** An infinite trace of the machine under `host` from an engine
configuration is an infinite component-level trace, or a finite run to a callout whose host
answer diverges (the machine then loops at the callout by `invokeHostDiverges`). -/
theorem diverges_bridge {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H)
    (c : lime1.Config H) :
    Wasm.Lime1.Execution.Diverges host (toConfig c) ↔
      InfiniteTrace (HostStep host) c ∨ ∃ c', HostSteps host c c' ∧ ∃ h args,
        lime1.status c'.1 c'.2 = .callout h args ∧ host h c'.1 args .diverged := by
  constructor
  · intro hd
    rcases InfiniteTrace.context_decompose (HostStep host) (Wasm.Lime1.Execution.Step host)
        toConfig (fun a b => b = toConfig a ∧ ∃ h args,
          lime1.status a.1 a.2 = .callout h args ∧ host h a.1 args .diverged)
        (fun a b step => by
          rcases step_hostStep step with hs | hb
          · exact .inl ⟨ofConfig b, hs, rfl⟩
          · exact .inr hb) hd with inf | ⟨a, -, run, ⟨-, hdiv⟩, -⟩
    · exact .inl inf
    · exact .inr ⟨a, run, hdiv⟩
  · rintro (inf | ⟨c', run, h, args, hs, hdv⟩)
    · exact InfiniteTrace.map toConfig (fun _ _ step => step.step) inf
    · apply InfiniteTrace.of_steps ((steps_bridge host c c').mp run)
      obtain ⟨c₀, hd, rfl, rfl⟩ := status_eq_callout.mp hs
      have loop := Wasm.Lime1.Execution.Step.callout_diverged
        (Wasm.Lime1.Execution.decompose?_sound hd) hdv
      exact InfiniteTrace.coinduct (· = toConfig c') (fun _ e => ⟨_, e ▸ loop, rfl⟩) rfl

/-! ## Code that does not observe the outer frame -/

theorem topCode_values (vs : List Value) : TopCode (Wasm.Lime1.Execution.values vs) := by
  intro x hx
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
  exact topAdmin_value v

theorem topCode_result (r : Result) : TopCode (Wasm.Lime1.Execution.result r) := by
  cases r with
  | values vs => exact topCode_values vs
  | trap =>
    intro x hx
    simp only [Wasm.Lime1.Execution.result, List.mem_singleton] at hx
    subst hx
    rfl

theorem TopCode.append {l l' : List Wasm.Lime1.Execution.Admin} (h : TopCode l)
    (h' : TopCode l') : TopCode (l ++ l') := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem pureStep_reframe {types : List Wasm.Lime1.FuncType}
    {before after : List Wasm.Lime1.Execution.Admin}
    (h : Wasm.Lime1.Execution.PureStep types before after) (hb : TopCode before) :
    TopCode after ∧ ∀ types', Wasm.Lime1.Execution.PureStep types' before after := by
  cases h with
  | frameDone n f vs arity => exact ⟨topCode_values vs, fun _ => .frameDone n f vs arity⟩
  | frameReturn n f extra vs tail arity =>
    exact ⟨topCode_values vs, fun _ => .frameReturn n f extra vs tail arity⟩
  | frameTrap n f => exact ⟨topCode_result .trap, fun _ => .frameTrap n f⟩
  | trapValues v vs tail => exact ⟨topCode_result .trap, fun _ => .trapValues v vs tail⟩
  | trapTail i tail => exact ⟨topCode_result .trap, fun _ => .trapTail i tail⟩
  | block bt body =>
    exact absurd (hb _ (List.mem_append_right _ (List.mem_singleton_self _))) Bool.false_ne_true
  | loop bt body =>
    exact absurd (hb _ (List.mem_append_right _ (List.mem_singleton_self _))) Bool.false_ne_true
  | _ =>
    exfalso
    simp [TopCode, topAdmin, Wasm.Lime1.Execution.values, Wasm.Lime1.Execution.asValue?] at hb

/-- **Frame irrelevance.** A step of `TopCode` code keeps the outer frame, stays in `TopCode`,
and is a step under every outer frame. -/
theorem step_reframe {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {a b : Wasm.Lime1.Execution.Config H} (h : Wasm.Lime1.Execution.Step host a b)
    (ha : TopCode a.code) :
    b.frame = a.frame ∧ TopCode b.code ∧ ∀ g : Frame,
      Wasm.Lime1.Execution.Step host ⟨a.store, g, a.code⟩ ⟨b.store, g, b.code⟩ := by
  induction h with
  | pure s f hp =>
    obtain ⟨hA, hT⟩ := pureStep_reframe hp ha
    exact ⟨rfl, hA, fun g => .pure s g (hT _)⟩
  | @context s s' f f' before after _ vs tail ih =>
    have hb : TopCode before := fun x hx => ha x (by simp [hx])
    obtain ⟨hf, hA, hS⟩ := ih hb
    refine ⟨hf, ((topCode_values vs).append hA).append ?_, fun g => .context (hS g) vs tail⟩
    exact fun x hx => ha x (by simp [hx])
  | label =>
    exfalso
    simp [TopCode, topAdmin] at ha
  | frame h n outer =>
    exact ⟨rfl, by simp [TopCode, topAdmin], fun g => .frame h n g⟩
  | invokeWasm s f a ft module fn args found arity =>
    exact ⟨rfl, by simp [TopCode, topAdmin],
      fun g => .invokeWasm s g a ft module fn args found arity⟩
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact ⟨rfl, topCode_result r,
      fun g => .invokeHost s s' g a ft fn args r found arity behavior⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact ⟨rfl, ha, fun g => .invokeHostDiverges s g a ft fn args found arity behavior⟩
  | _ =>
    exfalso
    simp [TopCode, topAdmin, Wasm.Lime1.Execution.value, Wasm.Lime1.Execution.asValue?] at ha

theorem steps_reframe {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {a b : Wasm.Lime1.Execution.Config H} (h : Wasm.Lime1.Execution.Steps host a b)
    (ha : TopCode a.code) :
    b.frame = a.frame ∧ TopCode b.code ∧ ∀ g : Frame,
      Wasm.Lime1.Execution.Steps host ⟨a.store, g, a.code⟩ ⟨b.store, g, b.code⟩ := by
  induction h with
  | refl => exact ⟨rfl, ha, fun _ => .refl⟩
  | tail _ step ih =>
    obtain ⟨hf, hb, hS⟩ := ih
    obtain ⟨hf', hc, hS'⟩ := step_reframe step hb
    exact ⟨hf'.trans hf, hc, fun g => (hS g).tail (hS' g)⟩

/-- Frame irrelevance for infinite traces: a diverging run of `TopCode` code diverges under
every outer frame. -/
theorem diverges_reframe {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {a : Wasm.Lime1.Execution.Config H} (h : Wasm.Lime1.Execution.Diverges host a)
    (ha : TopCode a.code) (g : Frame) :
    Wasm.Lime1.Execution.Diverges host ⟨a.store, g, a.code⟩ := by
  apply InfiniteTrace.coinduct (fun x => ∃ y : Wasm.Lime1.Execution.Config H,
    Wasm.Lime1.Execution.Diverges host y ∧ TopCode y.code ∧ x = ⟨y.store, g, y.code⟩)
  · rintro x ⟨y, hy, hc, rfl⟩
    obtain ⟨z, step, hz⟩ := InfiniteTrace.unfold hy
    obtain ⟨-, hzc, hS⟩ := step_reframe step hc
    exact ⟨_, hS g, z, hz, hzc, rfl⟩
  · exact ⟨a, h, ha, rfl⟩

/-! ## Instantiation -/

theorem steps_nil {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {s : Wasm.Lime1.Execution.Store H} {f : Frame} {b : Wasm.Lime1.Execution.Config H}
    (h : Wasm.Lime1.Execution.Steps host ⟨s, f, []⟩ b) : b = ⟨s, f, []⟩ := by
  rcases Relation.ReflTransGen.cases_head h with e | ⟨c, step, -⟩
  · exact e.symm
  · obtain ⟨x, hx, -⟩ := Wasm.Lime1.Execution.Step.nonvalue step
    simp at hx

theorem result_eq_nil {r : Result} (h : Wasm.Lime1.Execution.result r = []) :
    r = .values [] := by
  cases r with
  | trap => simp [Wasm.Lime1.Execution.result] at h
  | values vs =>
    simp only [Wasm.Lime1.Execution.result, Wasm.Lime1.Execution.values, List.map_eq_nil_iff] at h
    rw [h]

/-- **Instantiation bridge.** `Lime1.Execution.Instantiation` is validity, import matching,
`lime1.prepare?`, and a component-level run of the start thread (if any) with the same host. -/
theorem instantiation_bridge {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H)
    (before : Wasm.Lime1.Execution.Store H) (m : Wasm.Lime1.Module) (imports : List ExternVal)
    (after : Wasm.Lime1.Execution.Store H) (inst : ModuleInst) (outcome : Result) :
    Wasm.Lime1.Execution.Instantiation host before m imports after inst outcome ↔
      lime1.Valid m ∧ Wasm.Lime1.Execution.ImportsMatch before m imports ∧
        ∃ s st, lime1.prepare? before m imports = some (s, inst, st) ∧
          StartRun host s st after outcome := by
  constructor
  · rintro ⟨valid, imps, p, hp, rfl, run⟩
    refine ⟨valid, imps, p.store, startAddr? p.start, ?_, ?_⟩
    · change (Wasm.Lime1.Execution.prepare? before m imports).map _ = _
      rw [hp]
      rfl
    · rcases prepare?_start hp with e | ⟨a, e⟩
      · rw [e] at run ⊢
        have := steps_nil run
        simp only [Runtime.Config.mk.injEq] at this
        exact ⟨this.1, result_eq_nil this.2.2⟩
      · rw [e] at run ⊢
        refine ⟨⟨⟨[], {}⟩, Wasm.Lime1.Execution.result outcome⟩, ?_, rfl⟩
        rw [steps_bridge]
        have htop : TopCode [AdminInstr.invoke a] := by simp [TopCode, topAdmin]
        exact (steps_reframe run htop).2.2 ⟨[], {}⟩
  · rintro ⟨valid, imps, s, st, hp, run⟩
    change (Wasm.Lime1.Execution.prepare? before m imports).map _ = _ at hp
    obtain ⟨p, hp', e⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨valid, imps, p, hp', rfl, ?_⟩
    rcases prepare?_start hp' with e | ⟨a, e⟩
    · rw [e] at run ⊢
      obtain ⟨rfl, rfl⟩ := run
      exact .refl
    · rw [e] at run ⊢
      obtain ⟨t, hrun, hcode⟩ := run
      have hsteps := (steps_bridge host _ _).mp hrun
      have htop : TopCode (toConfig (p.store, lime1.invoke (H := H) a [])).code := by
        simp [TopCode, topAdmin, toConfig, invoke, Wasm.Lime1.Execution.values]
      have := (steps_reframe hsteps htop).2.2 ⟨[], p.module⟩
      simp only [toConfig] at this
      rw [hcode] at this
      exact this

theorem not_diverges_nil {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {s : Wasm.Lime1.Execution.Store H} {f : Frame} :
    ¬ Wasm.Lime1.Execution.Diverges host ⟨s, f, []⟩ := by
  intro h
  obtain ⟨b, step, -⟩ := InfiniteTrace.unfold h
  obtain ⟨x, hx, -⟩ := Wasm.Lime1.Execution.Step.nonvalue step
  simp at hx

/-- **Diverging instantiation bridge.** `Lime1.Execution.InstantiationDiverges` is validity,
import matching, `lime1.prepare?` returning a start function, and divergence of the start
thread `lime1.invoke a []` with the same host (by `diverges_bridge`, an infinite `HostStep`
trace or a run to a callout whose host answer diverges). -/
theorem instantiationDiverges_bridge {H : Type} (host : Wasm.Lime1.Execution.HostSemantics H)
    (before : Wasm.Lime1.Execution.Store H) (m : Wasm.Lime1.Module)
    (imports : List ExternVal) :
    Wasm.Lime1.Execution.InstantiationDiverges host before m imports ↔
      lime1.Valid m ∧ Wasm.Lime1.Execution.ImportsMatch before m imports ∧
        ∃ s inst a, lime1.prepare? before m imports = some (s, inst, some a) ∧
          Wasm.Lime1.Execution.Diverges host (toConfig (s, lime1.invoke (H := H) a [])) := by
  constructor
  · rintro ⟨valid, imps, p, hp, dv⟩
    rcases prepare?_start hp with e | ⟨a, e⟩
    · rw [e] at dv
      exact absurd dv not_diverges_nil
    · rw [e] at dv
      refine ⟨valid, imps, p.store, p.module, a, ?_, ?_⟩
      · change (Wasm.Lime1.Execution.prepare? before m imports).map _ = _
        rw [hp]
        simp [e, startAddr?]
      · have htop : TopCode [AdminInstr.invoke a] := by simp [TopCode, topAdmin]
        exact diverges_reframe dv htop ⟨[], {}⟩
  · rintro ⟨valid, imps, s, inst, a, hp, dv⟩
    change (Wasm.Lime1.Execution.prepare? before m imports).map _ = _ at hp
    obtain ⟨p, hp', e⟩ := Option.map_eq_some_iff.mp hp
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, ha⟩ := e
    refine ⟨valid, imps, p, hp', ?_⟩
    rcases prepare?_start hp' with e | ⟨a', e⟩
    · rw [e] at ha
      simp [startAddr?] at ha
    · rw [e] at ha ⊢
      simp only [startAddr?, Option.some.injEq] at ha
      subst ha
      have htop : TopCode (toConfig (p.store, lime1.invoke (H := H) a' [])).code := by
        simp [TopCode, topAdmin, toConfig, invoke, Wasm.Lime1.Execution.values]
      simpa [toConfig, invoke, Wasm.Lime1.Execution.values] using
        diverges_reframe dv htop ⟨[], p.module⟩

/-! ## Tests -/

namespace Examples

open Wasm.Lime1.Execution (values)

theorem adderModule_prepares :
    lime1.prepare? (lime1.empty String) adderModule [] = some (adderStore, adderInst, none) := rfl

theorem adderModule_exportTypes :
    lime1.exportTypes adderModule = [("add", .func binaryType)] := rfl

/-- The adder runs to `[x + y]` under the executable stepper, and then reports `returned`. -/
theorem adder_runs (x y : BitVec 32) :
    lime1Exec.runCore 8 (adderStore, lime1.invoke ⟨0⟩ [.int .i32 x, .int .i32 y]) =
      ((adderStore, ⟨⟨[], {}⟩, values [.int .i32 (x + y)]⟩), true) := rfl

theorem adder_returns (x y : BitVec 32) :
    lime1.status adderStore (⟨⟨[], {}⟩, values [.int .i32 (x + y)]⟩ : Thread String) =
      .returned (.values [.int .i32 (x + y)]) := rfl

theorem adder_running (x y : BitVec 32) :
    lime1.status adderStore (lime1.invoke ⟨0⟩ [.int .i32 x, .int .i32 y]) = .running := rfl

theorem callerModule_importTypes :
    lime1.importTypes callerModule = [("env", "f", .func unaryType)] := rfl

/-- The host function `"f"` allocated in the empty store, at address `0`. -/
theorem allocHost_f :
    lime1.allocHost (lime1.empty String) unaryType "f" =
      (⟨[.host unaryType "f"], [], [], []⟩, ⟨0⟩) := rfl

theorem callerModule_prepares :
    lime1.prepare? (lime1.allocHost (lime1.empty String) unaryType "f").1 callerModule
      [.func ⟨0⟩] = some (callerStore, callerInst, none) := rfl

/-- The run stops (no executable step) ... -/
theorem caller_stops (x : BitVec 32) :
    (lime1Exec.runCore 8 (callerStore, lime1.invoke ⟨1⟩ [.int .i32 x])).2 = true := rfl

/-- ... parked on the host function `"f"` with the argument `x`. -/
theorem caller_callout (x : BitVec 32) :
    lime1.status (parked x).1 (parked x).2 = .callout "f" [.int .i32 x] := rfl

/-- Resuming with a host result `y` returns `[y]` from the exported function. -/
theorem caller_resume (x y : BitVec 32) :
    (lime1Exec.runCore 8 ((parked x).1,
      lime1.resume (parked x).1 (parked x).2 (.values [.int .i32 y]))).1 =
      (callerStore, ⟨⟨[], {}⟩, values [.int .i32 y]⟩) := rfl

/-- Resuming with a trap propagates it. -/
theorem caller_resume_trap (x : BitVec 32) :
    lime1.status callerStore (lime1Exec.runCore 8 ((parked x).1,
      lime1.resume (parked x).1 (parked x).2 .trap)).1.2 = .returned .trap := rfl

end Examples

end Silmaril.Wasm.Component.Engine.Lime1
