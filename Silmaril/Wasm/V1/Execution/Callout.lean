module

public import Silmaril.Wasm.V1.Execution.Step
public import Silmaril.Wasm.Lime1.Execution.Callout.Properties
public import Silmaril.Wasm.Lime1.Execution.Transport

/-!
# Suspending WebAssembly 1.0 execution at host calls

The WebAssembly 1.0 counterpart of `Lime1.Execution.Callout`. Both machines use the shared
runtime carriers of `Execution.Runtime`, so the evaluation contexts (`Runtime.EvalCtx`),
callout records (`Runtime.Callout`) and the decomposer (`Runtime.decomposeFrom?`), together with
its generic soundness and completeness lemmas (`Lime1/Execution/Callout/Properties.lean`), are
reused with the V1 value coding. This file supplies that coding, `CalloutAt`, `resume`,
`decompose?`, the host-free machine `Internal`, the labelled `OpenStep`, `Answer`, and the same
theorems as for Lime1: a step of `V1.Execution.Step host` is exactly a host-free step or a
callout completed by the host relation (`step_iff`), configurations parked at a callout take no
host-free step, and callouts are unique up to the resumed code.

Upstream correspondence and scope are as in `Lime1.Execution.Callout` (reference `cont_new`,
`resume`, `block`, `Thread.suspend`/`Thread.resume` in `definitions.py`; wasmtime
`suspend(SuspendReason)`).

No executable host-free stepper is provided for V1. Callouts are instead related to the
V1-to-Lime1 transport (`Lime1/Execution/Transport.lean`): the Lime1 decomposer on
`cfg.toLime` is exactly the image of the V1 decomposer (`decompose?_toLime`, with
`Runtime.Callout.toLime` mapping only the context's continuation code), V1 callouts are Lime1
callouts of the transported configuration (`CalloutAt.toLime`), and resumption commutes with
transport (`resume_toLime`). So a callout the Lime1 driver finds on `cfg.toLime` before any
internal step is the image of the V1 callout of `cfg`, and resuming it is the image of V1
resumption. What is *not* provided is a reflection of Lime1 host-free runs back to V1 callouts:
a callout reached by the Lime1 driver only after internal Lime1 steps is a Lime1 callout of a
Lime1 configuration. Finite Lime1 runs reflect back only as whole `Steps` derivations, via
`V1.Execution.Steps.ofLime` (a separate finite-run reflection development (not included in this package)), which additionally requires
`SingleResultStore` of the V1 store and `HostSemantics.PreservesSingleResult` of the host.
-/

@[expose] public section

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The inverse of `value` on administrative instructions. -/
def asValue? : Admin → Option Value
  | .source (.intConst t b) => some ⟨.int t, b⟩
  | .source (.floatConst t b) => some ⟨.float t, b⟩
  | _ => none

/-- WebAssembly 1.0's value encoding: constants. -/
def coding : ValueCoding Instr where
  encode := value
  decode := asValue?
  decode_encode v := by
    rcases v with ⟨t, b⟩
    cases t <;> rfl
  encode_of_decode {x v} h := by
    rcases x with (i | _ | _ | _ | _)
    · cases i <;> simp only [asValue?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl
    all_goals simp [asValue?] at h
  source_of_decode {x v} h := by
    rcases x with (i | _ | _ | _ | _) <;> simp [asValue?] at h ⊢

/-- `c` is the host-call redex of configuration `cfg`. -/
def CalloutAt {H : Type*} (cfg : Config H) (c : Runtime.Callout H Instr) : Prop :=
  c.Located coding cfg.store cfg.code

/-- Resume a parked configuration with the host's store and result (`.trap` included). -/
def resume {H : Type*} (cfg : Config H) (c : Runtime.Callout H Instr) (s' : Store H)
    (r : Result) : Config H :=
  ⟨s', cfg.frame, c.fill coding (result r)⟩

def decompose? {H : Type*} (cfg : Config H) : Option (Runtime.Callout H Instr) :=
  decomposeFrom? coding cfg.store [] cfg.code

/-- Host-free transitions: the existing machine with no host behavior. -/
abbrev Internal {H : Type*} : Config H → Config H → Prop := Step noHostCalls

inductive Transition (H : Type*) where
  | internal (next : Config H)
  | callout (callout : Runtime.Callout H Instr)

/-- The open machine: host-free steps, and an observable stop at each callout. -/
inductive OpenStep {H : Type*} : Config H → Transition H → Prop where
  | internal {a b : Config H} (h : Internal a b) : OpenStep a (.internal b)
  | callout {a : Config H} {c : Runtime.Callout H Instr} (h : CalloutAt a c) :
      OpenStep a (.callout c)

/-- How the atomic machine completes a callout under a host relation. -/
inductive Answer {H : Type*} (host : HostSemantics H) (cfg : Config H)
    (c : Runtime.Callout H Instr) : Config H → Prop where
  | returned (s' : Store H) (r : Result) (h : host c.host cfg.store c.args (.returned s' r)) :
      Answer host cfg c (resume cfg c s' r)
  | diverged (h : host c.host cfg.store c.args .diverged) : Answer host cfg c cfg

/-! ## Decomposition lemmas -/

@[simp] theorem asValue?_value (v : Value) : asValue? (value v) = some v := coding.decode_encode v

section Decompose

variable {H : Type*} (s : Store H)

@[simp] theorem decomposeFrom?_values_append (acc vs : List Value) (l : List Admin) :
    decomposeFrom? coding s acc (values vs ++ l) = decomposeFrom? coding s (acc ++ vs) l :=
  decomposeFrom?_encode_append coding s acc vs l

@[simp] theorem decomposeFrom?_values (acc vs : List Value) :
    decomposeFrom? coding s acc (values vs) = none :=
  decomposeFrom?_map_encode coding s acc vs

@[simp] theorem decomposeFrom?_value_cons (acc : List Value) (v : Value) (l : List Admin) :
    decomposeFrom? coding s acc (value v :: l) = decomposeFrom? coding s (acc ++ [v]) l :=
  decomposeFrom?_cons_encode coding s acc v l

@[simp] theorem decomposeFrom?_source_cons (acc : List Value) (i : Instr) (l : List Admin) :
    decomposeFrom? coding s acc (.source i :: l) =
      (asValue? (.source i)).bind fun v => decomposeFrom? coding s (acc ++ [v]) l := by
  cases h : asValue? (.source i) with
  | none => rw [decomposeFrom?_cons_of_decode coding s l h, decomposeHead?_source]; rfl
  | some v =>
    have hv : value v = .source i := coding.encode_of_decode h
    rw [← hv, decomposeFrom?_value_cons]
    rfl

@[simp] theorem decomposeFrom?_trap_cons (acc : List Value) (l : List Admin) :
    decomposeFrom? coding s acc (.trap :: l) = none := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_trap), decomposeHead?_trap]

@[simp] theorem decomposeFrom?_label_cons (acc : List Value) (n : Nat) (cont : Expr)
    (body l : List Admin) :
    decomposeFrom? coding s acc (.label n cont body :: l) =
      (decomposeFrom? coding s [] body).map fun c =>
        { c with context := .seq acc (.label n cont c.context) l } := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_label _ _ _), decomposeHead?_label]

@[simp] theorem decomposeFrom?_frame_cons (acc : List Value) (n : Nat) (fr : Frame)
    (body l : List Admin) :
    decomposeFrom? coding s acc (.frame n fr body :: l) =
      (decomposeFrom? coding s [] body).map fun c =>
        { c with context := .seq acc (.frame n fr c.context) l } := by
  rw [decomposeFrom?_cons_of_decode coding s l (coding.decode_frame _ _ _), decomposeHead?_frame]

theorem decomposeFrom?_invoke_cons (acc : List Value) (a : FuncAddr) (l : List Admin) :
    decomposeFrom? coding s acc (.invoke a :: l) = decomposeHead? coding s acc l (.invoke a) :=
  decomposeFrom?_cons_of_decode coding s l (coding.decode_invoke a)

end Decompose

/-! ## Plugging and the atomic host rule -/

theorem Step.plug {H : Type*} {host : HostSemantics H} {s s' : Store H} {x y : List Admin}
    (h : ∀ g, Step host ⟨s, g, x⟩ ⟨s', g, y⟩) (K : EvalCtx Instr) (f : Frame) :
    Step host ⟨s, f, K.plug value x⟩ ⟨s', f, K.plug value y⟩ := by
  induction K generalizing f with
  | hole => exact h f
  | seq vs K tail ih => exact .context (ih f) vs tail
  | label n cont K ih => exact .label (ih f) n cont
  | frame n fr K ih => exact .frame (ih fr) n f

/-- A step at the hole, taken in the frame in force there (`EvalCtx.activeFrame`) and leaving
that frame unchanged, lifts through the context. This is the sense in which `activeFrame` is the
caller frame of a callout (the frame whose module instance a canonical built-in would consult). -/
theorem Step.plug_activeFrame {H : Type*} {host : HostSemantics H} {s s' : Store H}
    {x y : List Admin} (K : EvalCtx Instr) (f : Frame)
    (h : Step host ⟨s, K.activeFrame f, x⟩ ⟨s', K.activeFrame f, y⟩) :
    Step host ⟨s, f, K.plug value x⟩ ⟨s', f, K.plug value y⟩ := by
  induction K generalizing f with
  | hole => exact h
  | seq vs K tail ih => exact .context (ih f h) vs tail
  | label n cont K ih => exact .label (ih f h) n cont
  | frame n fr K ih => exact .frame (ih fr h) n f

theorem Step.callout_returned {H : Type*} {host : HostSemantics H} {cfg : Config H}
    {c : Runtime.Callout H Instr} {s' : Store H} {r : Result} (hc : CalloutAt cfg c)
    (hr : host c.host cfg.store c.args (.returned s' r)) :
    Step host cfg (resume cfg c s' r) := by
  obtain ⟨s, f, code⟩ := cfg
  obtain ⟨plugged, found, arity⟩ := hc
  simp only at plugged found hr
  subst plugged
  exact Step.plug (fun g => .invokeHost s s' g c.function c.type c.host c.args r found arity hr)
    c.context f

theorem Step.callout_diverged {H : Type*} {host : HostSemantics H} {cfg : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt cfg c)
    (hd : host c.host cfg.store c.args .diverged) : Step host cfg cfg := by
  obtain ⟨s, f, code⟩ := cfg
  obtain ⟨plugged, found, arity⟩ := hc
  simp only at plugged found hd
  subst plugged
  exact Step.plug (fun g => .invokeHostDiverges s g c.function c.type c.host c.args found arity hd)
    c.context f

theorem Answer.step {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt a c) (h : Answer host a c b) : Step host a b := by
  cases h with
  | returned s' r hr => exact Step.callout_returned hc hr
  | diverged hd => exact Step.callout_diverged hc hd

theorem Answer.iff {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} :
    Answer host a c b ↔ (∃ s' r, host c.host a.store c.args (.returned s' r) ∧
      b = resume a c s' r) ∨ (host c.host a.store c.args .diverged ∧ b = a) := by
  constructor
  · rintro (⟨s', r, hr⟩ | hd)
    · exact .inl ⟨s', r, hr, rfl⟩
    · exact .inr ⟨hd, rfl⟩
  · rintro (⟨s', r, hr, rfl⟩ | ⟨hd, rfl⟩)
    · exact .returned s' r hr
    · exact .diverged hd

theorem Step.of_internal {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Internal a b) : Step host a b := by
  induction h with
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ =>
    first
    | (apply Step.pure <;> assumption)
    | (apply Step.localGet <;> assumption)
    | (apply Step.localSet <;> assumption)
    | (apply Step.globalGet <;> assumption)
    | (apply Step.globalSet <;> assumption)
    | (apply Step.call <;> assumption)
    | (apply Step.callIndirect <;> assumption)
    | (apply Step.callIndirectBounds <;> assumption)
    | (apply Step.callIndirectNull <;> assumption)
    | (apply Step.callIndirectType <;> assumption)
    | (apply Step.invokeWasm <;> assumption)
    | (apply Step.intLoad <;> assumption)
    | (apply Step.intLoadTrap <;> assumption)
    | (apply Step.floatLoad <;> assumption)
    | (apply Step.floatLoadTrap <;> assumption)
    | (apply Step.intStore <;> assumption)
    | (apply Step.intStoreTrap <;> assumption)
    | (apply Step.floatStore <;> assumption)
    | (apply Step.floatStoreTrap <;> assumption)
    | (apply Step.memorySize <;> assumption)
    | (apply Step.memoryGrow <;> assumption)

theorem Steps.of_internal {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Relation.ReflTransGen Internal a b) : Steps host a b := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (Step.of_internal hs)

theorem Step.internal_or_callout {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) :
    Internal a b ∨ ∃ c, CalloutAt a c ∧ Answer host a c b := by
  induction h with
  | invokeHost s s' f a ft fn args r found arity behavior =>
    exact .inr ⟨⟨.hole, a, ft, fn, args⟩, ⟨rfl, found, arity⟩, .returned s' r behavior⟩
  | invokeHostDiverges s f a ft fn args found arity behavior =>
    exact .inr ⟨⟨.hole, a, ft, fn, args⟩, ⟨rfl, found, arity⟩, .diverged behavior⟩
  | context h vs tail ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.context ih vs tail)
    · refine .inr ⟨{ c with context := .seq vs c.context tail }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | label h n cont ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.label ih n cont)
    · refine .inr ⟨{ c with context := .label n cont c.context }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | frame h n outer ih =>
    rcases ih with ih | ⟨c, hc, hans⟩
    · exact .inl (.frame ih n outer)
    · rename_i inner _ _ _
      refine .inr ⟨{ c with context := .frame n inner c.context }, ⟨?_, hc.found, hc.arity⟩, ?_⟩
      · simp only [CalloutAt] at hc ⊢
        rw [hc.plugged]
        rfl
      · rcases Answer.iff.mp hans with ⟨s'', r, hr, heq⟩ | ⟨hd, heq⟩
        · simp only [resume, Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .returned _ r hr
        · simp only [Config.mk.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          exact .diverged hd
  | _ =>
    refine .inl ?_
    first
    | (apply Step.pure <;> assumption)
    | (apply Step.localGet <;> assumption)
    | (apply Step.localSet <;> assumption)
    | (apply Step.globalGet <;> assumption)
    | (apply Step.globalSet <;> assumption)
    | (apply Step.call <;> assumption)
    | (apply Step.callIndirect <;> assumption)
    | (apply Step.callIndirectBounds <;> assumption)
    | (apply Step.callIndirectNull <;> assumption)
    | (apply Step.callIndirectType <;> assumption)
    | (apply Step.invokeWasm <;> assumption)
    | (apply Step.intLoad <;> assumption)
    | (apply Step.intLoadTrap <;> assumption)
    | (apply Step.floatLoad <;> assumption)
    | (apply Step.floatLoadTrap <;> assumption)
    | (apply Step.intStore <;> assumption)
    | (apply Step.intStoreTrap <;> assumption)
    | (apply Step.floatStore <;> assumption)
    | (apply Step.floatStoreTrap <;> assumption)
    | (apply Step.memorySize <;> assumption)
    | (apply Step.memoryGrow <;> assumption)

/-- **Adequacy of the open machine** for WebAssembly 1.0. -/
theorem step_iff {H : Type*} {host : HostSemantics H} {a b : Config H} :
    Step host a b ↔ Internal a b ∨ ∃ c, CalloutAt a c ∧ Answer host a c b := by
  constructor
  · exact Step.internal_or_callout
  · rintro (h | ⟨c, hc, hans⟩)
    · exact Step.of_internal h
    · exact hans.step hc

/-! ## The executable decomposition, and parking -/

theorem decompose?_sound {H : Type*} {cfg : Config H} {c : Runtime.Callout H Instr}
    (h : decompose? cfg = some c) : CalloutAt cfg c := by
  have h' := decomposeFrom?_sound coding cfg.store [] cfg.code c h
  simp only [List.map_nil, List.nil_append] at h'
  exact h'

theorem decompose?_complete {H : Type*} {cfg : Config H} {c : Runtime.Callout H Instr}
    (h : CalloutAt cfg c) :
    ∃ c', decompose? cfg = some c' ∧ c'.function = c.function ∧ c'.type = c.type ∧
      c'.host = c.host ∧ c'.args = c.args ∧ ∀ s' r, resume cfg c' s' r = resume cfg c s' r := by
  obtain ⟨c', hc, hf, ht, hh, ha, hfill⟩ := decomposeFrom?_complete coding cfg.store h
  exact ⟨c', hc, hf, ht, hh, ha, fun s' r => by simp only [resume, hfill]⟩

theorem exists_callout_iff {H : Type*} {cfg : Config H} :
    (∃ c, CalloutAt cfg c) ↔ (decompose? cfg).isSome := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨c', hc', -⟩ := decompose?_complete hc
    simp [hc']
  · intro h
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp h
    exact ⟨c, decompose?_sound hc⟩

theorem CalloutAt.unique {H : Type*} {cfg : Config H} {c d : Runtime.Callout H Instr}
    (hc : CalloutAt cfg c) (hd : CalloutAt cfg d) :
    c.function = d.function ∧ c.type = d.type ∧ c.host = d.host ∧ c.args = d.args ∧
      ∀ s' r, resume cfg c s' r = resume cfg d s' r := by
  obtain ⟨hf, ht, hh, ha, hfill⟩ := Callout.Located.unique coding cfg.store hc hd
  exact ⟨hf, ht, hh, ha, fun s' r => by simp only [resume, hfill]⟩

theorem Step.nonvalue {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : Step host a b) : ∃ x ∈ a.code, asValue? x = none := by
  induction h with
  | pure s f hp =>
    cases hp <;> first | (simp [values, asValue?]; done) | exact ⟨.trap, by simp, rfl⟩
  | context _ vs tail ih =>
    obtain ⟨x, hx, hv⟩ := ih
    exact ⟨x, by simp [hx], hv⟩
  | _ => simp [values, asValue?]

theorem Internal.decompose_none {H : Type*} {a b : Config H} (h : Internal a b) :
    ∀ acc, decomposeFrom? coding a.store acc a.code = none := by
  induction h with
  | pure s f hp =>
    intro acc
    cases hp <;> simp [asValue?]
  | context h vs tail ih =>
    intro acc
    obtain ⟨x, hx, hv⟩ := h.nonvalue
    simp only [List.append_assoc, decomposeFrom?_values_append]
    exact decomposeFrom?_append_eq_none coding _ tail ⟨x, hx, hv⟩ (ih _)
  | label h n cont ih =>
    intro acc
    simp [ih []]
  | frame h n outer ih =>
    intro acc
    simp [ih []]
  | invokeWasm s f a ft module fn args found arity =>
    intro acc
    simp [decomposeFrom?_invoke_cons, decomposeHead?, found]
  | invokeHost _ _ _ _ _ _ _ _ _ _ hb => exact hb.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ hb => exact hb.elim
  | _ => intro acc; simp [asValue?]

theorem CalloutAt.not_internal {H : Type*} {a b : Config H} {c : Runtime.Callout H Instr}
    (hc : CalloutAt a c) (h : Internal a b) : False := by
  obtain ⟨c', hc', -⟩ := decompose?_complete hc
  simp [decompose?, h.decompose_none []] at hc'

/-- On a configuration that is not parked at a callout, the atomic machine under any host takes
exactly the host-free steps: the open machine agrees with `Step host` on non-host redexes. -/
theorem Step.internal_iff_of_not_callout {H : Type*} {host : HostSemantics H} {a b : Config H}
    (h : ∀ c, ¬ CalloutAt a c) : Step host a b ↔ Internal a b := by
  refine ⟨fun hs => ?_, Step.of_internal⟩
  rcases hs.internal_or_callout with hi | ⟨c, hc, -⟩
  · exact hi
  · exact (h c hc).elim

/-! ## The open machine -/

theorem openStep_internal_iff {H : Type*} {a b : Config H} :
    OpenStep a (.internal b) ↔ Internal a b :=
  ⟨fun | .internal h => h, .internal⟩

theorem openStep_callout_iff {H : Type*} {a : Config H} {c : Runtime.Callout H Instr} :
    OpenStep a (.callout c) ↔ CalloutAt a c :=
  ⟨fun | .callout h => h, .callout⟩

theorem OpenStep.callout_stops {H : Type*} {a b : Config H} {c : Runtime.Callout H Instr}
    (hc : OpenStep a (.callout c)) (hb : OpenStep a (.internal b)) : False :=
  (openStep_callout_iff.mp hc).not_internal (openStep_internal_iff.mp hb)

theorem step_iff_openStep {H : Type*} {host : HostSemantics H} {a b : Config H} :
    Step host a b ↔
      OpenStep a (.internal b) ∨ ∃ c, OpenStep a (.callout c) ∧ Answer host a c b := by
  simp only [openStep_internal_iff, openStep_callout_iff]
  exact step_iff

theorem CalloutAt.step_iff {H : Type*} {host : HostSemantics H} {a b : Config H}
    {c : Runtime.Callout H Instr} (hc : CalloutAt a c) :
    Step host a b ↔ Answer host a c b := by
  constructor
  · intro h
    rcases h.internal_or_callout with h | ⟨d, hd, hans⟩
    · exact (hc.not_internal h).elim
    · obtain ⟨-, -, hh, ha, hres⟩ := hd.unique hc
      rcases Answer.iff.mp hans with ⟨s', r, hr, rfl⟩ | ⟨hdv, rfl⟩
      · rw [hres]
        exact .returned s' r (hh ▸ ha ▸ hr)
      · exact .diverged (hh ▸ ha ▸ hdv)
  · exact fun h => h.step hc

/-! ## Transport of callouts to Lime1

Callouts commute with the V1-to-Lime1 transport (`Config.toLime`): the Lime1 decomposer finds
on a transported configuration exactly the image (`Callout.toLime`) of the V1 callout, and
resuming commutes with transport. Since `Callout.toLime` keeps the address, type, host tag and
arguments, the host is consulted identically; only the continuation code is mapped. -/

end Silmaril.Wasm.V1.Execution

namespace Silmaril.Wasm.Execution.Runtime

/-- Map the source instructions stored in label continuations of a context. -/
def EvalCtx.map {I J : Type*} (f : I → J) : EvalCtx I → EvalCtx J
  | .hole => .hole
  | .seq vs inner tail => .seq vs (inner.map f) (AdminInstr.mapList f tail)
  | .label n cont inner => .label n (cont.map f) (inner.map f)
  | .frame n fr inner => .frame n fr (inner.map f)

theorem EvalCtx.plug_map {I J : Type*} (f : I → J) (C : ValueCoding I) (D : ValueCoding J)
    (henc : ∀ v, AdminInstr.map f (C.encode v) = D.encode v) (ctx : EvalCtx I)
    (code : List (AdminInstr I)) :
    (ctx.map f).plug D.encode (AdminInstr.mapList f code) =
      AdminInstr.mapList f (ctx.plug C.encode code) := by
  induction ctx with
  | hole => rfl
  | seq vs inner tail ih =>
    simp only [EvalCtx.map, EvalCtx.plug, AdminInstr.mapList_append, ih]
    simp [AdminInstr.mapList_eq_map, henc, Function.comp_def]
  | label n cont inner ih =>
    simp only [EvalCtx.map, EvalCtx.plug, ih, AdminInstr.mapList, AdminInstr.map]
  | frame n fr inner ih =>
    simp only [EvalCtx.map, EvalCtx.plug, ih, AdminInstr.mapList, AdminInstr.map]

@[simp] theorem EvalCtx.activeFrame_map {I J : Type*} (f : I → J) (ctx : EvalCtx I)
    (fr : Frame) : (ctx.map f).activeFrame fr = ctx.activeFrame fr := by
  induction ctx generalizing fr <;> simp_all [EvalCtx.map, EvalCtx.activeFrame]

/-- Map a callout's context; the address, type, host tag and arguments are unchanged. -/
def Callout.map {Host I J : Type*} (f : I → J) (c : Callout Host I) : Callout Host J :=
  { c with context := c.context.map f }

section MapDecompose

variable {A B Host I J : Type*} (f : I → J) (g : A → B) (C : ValueCoding I) (D : ValueCoding J)
  (s : Store A Host)

mutual
/-- The decomposer commutes with a code map that preserves values. -/
theorem decomposeFrom?_mapCode (hdec : ∀ x, D.decode (AdminInstr.map f x) = C.decode x) :
    ∀ (acc : List Value) (code : List (AdminInstr I)),
    decomposeFrom? D (s.mapCode g) acc (AdminInstr.mapList f code) =
      (decomposeFrom? C s acc code).map (Callout.map f)
  | _, [] => rfl
  | acc, x :: tail => by
    simp only [AdminInstr.mapList, decomposeFrom?, hdec]
    cases C.decode x with
    | some v => exact decomposeFrom?_mapCode hdec (acc ++ [v]) tail
    | none => exact decomposeHead?_mapCode hdec acc tail x
termination_by structural _ code => code

theorem decomposeHead?_mapCode (hdec : ∀ x, D.decode (AdminInstr.map f x) = C.decode x) :
    ∀ (acc : List Value) (tail : List (AdminInstr I))
    (x : AdminInstr I),
    decomposeHead? D (s.mapCode g) acc (AdminInstr.mapList f tail) (AdminInstr.map f x) =
      (decomposeHead? C s acc tail x).map (Callout.map f)
  | acc, tail, .invoke a => by
    simp only [AdminInstr.map, decomposeHead?, Store.mapCode_funcs_getElem?]
    cases s.funcs[a.value]? with
    | none => rfl
    | some fn =>
      cases fn with
      | wasm t m c => rfl
      | host ft h =>
        simp only [Option.map_some, FuncInst.mapCode]
        split <;> rfl
  | acc, tail, .label n cont body => by
    simp only [AdminInstr.map, decomposeHead?, decomposeFrom?_mapCode hdec [] body, Option.map_map]
    rfl
  | acc, tail, .frame n fr body => by
    simp only [AdminInstr.map, decomposeHead?, decomposeFrom?_mapCode hdec [] body, Option.map_map]
    rfl
  | _, _, .source i => by
    simp only [AdminInstr.map, decomposeHead?]
    rfl
  | _, _, .trap => rfl
termination_by structural _ _ x => x
end

end MapDecompose

end Silmaril.Wasm.Execution.Runtime

namespace Silmaril.Wasm.V1.Execution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime

/-- The Lime1 image of a V1 callout. -/
abbrev _root_.Silmaril.Wasm.Execution.Runtime.Callout.toLime {H : Type*}
    (c : Runtime.Callout H Instr) : Runtime.Callout H Lime1.Instr :=
  c.map Instr.toLime

theorem asValue?_toLime (x : Admin) :
    Lime1.Execution.asValue? (AdminInstr.map Instr.toLime x) = asValue? x := by
  rcases x with (i | _ | _ | _ | _)
  · cases i <;> rfl
  all_goals rfl

/-- The Lime1 decomposer on a transported configuration is the image of the V1 decomposer. -/
theorem decompose?_toLime {H : Type*} (cfg : Config H) :
    Lime1.Execution.decompose? cfg.toLime = (decompose? cfg).map Callout.toLime :=
  decomposeFrom?_mapCode Instr.toLime Func.toLime coding Lime1.Execution.coding cfg.store
    asValue?_toLime [] cfg.code

/-- Resuming commutes with transport. -/
theorem resume_toLime {H : Type*} (cfg : Config H) (c : Runtime.Callout H Instr) (s' : Store H)
    (r : Result) :
    (resume cfg c s' r).toLime =
      Lime1.Execution.resume cfg.toLime c.toLime (s'.mapCode Func.toLime) r := by
  simp only [resume, Lime1.Execution.resume, Config.toLime, Callout.fill, Callout.map]
  congr 1
  rw [← map_result r]
  exact (EvalCtx.plug_map Instr.toLime coding Lime1.Execution.coding map_value c.context
    (result r)).symm

/-- V1 callouts are Lime1 callouts of the transported configuration. -/
theorem CalloutAt.toLime {H : Type*} {cfg : Config H} {c : Runtime.Callout H Instr}
    (h : CalloutAt cfg c) : Lime1.Execution.CalloutAt cfg.toLime c.toLime := by
  refine ⟨?_, ?_, h.arity⟩
  · simp only [Config.toLime, Callout.fill, Callout.redex, Callout.map, h.plugged]
    show AdminInstr.mapList Instr.toLime _ = _
    rw [← EvalCtx.plug_map Instr.toLime coding Lime1.Execution.coding map_value]
    congr 1
    simp [AdminInstr.mapList_eq_map, AdminInstr.map]
    exact fun a _ => map_value a
  · simp [Config.toLime, Callout.map, Callout.toLime, h.found, FuncInst.mapCode]

end Silmaril.Wasm.V1.Execution
