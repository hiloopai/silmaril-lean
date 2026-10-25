module

public import Silmaril.Wasm.Execution.Core.Sim.Closure
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Typing witnesses for active runtime fragments

An administrative body need not be a well-typed standalone configuration: its
branches and returns can refer to surrounding labels and frames. `ContextTyped`
keeps the surrounding evaluation context instead. Its witness descends through
all runtime contexts and survives closed-host execution at any numerical profile.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

/-- Evaluation contexts that keep their hole active. Frame contexts remember the
outer frame while taking the current inner frame from the hole. -/
inductive ActiveCtx where
  | hole
  | suffix (rest : List Admin) (outer : ActiveCtx)
  | label (n : Nat) (cont : List Instr) (vs : List Val) (rest : List Admin) (outer : ActiveCtx)
  | handler (n : Nat) (cs : List Catch) (vs : List Val) (rest : List Admin) (outer : ActiveCtx)
  | frame (n : Nat) (f : Frame) (vs : List Val) (rest : List Admin) (outer : ActiveCtx)

def ActiveCtx.plug : ActiveCtx → Config H → Config H
  | .hole, c => c
  | .suffix rest E, c => E.plug ⟨c.store, c.frame, c.code ++ rest⟩
  | .label n cont vs rest E, c =>
      E.plug ⟨c.store, c.frame, vals vs ++ [.label n cont c.code] ++ rest⟩
  | .handler n cs vs rest E, c =>
      E.plug ⟨c.store, c.frame, vals vs ++ [.handler n cs c.code] ++ rest⟩
  | .frame n f vs rest E, c =>
      E.plug ⟨c.store, f, vals vs ++ [.frame n c.frame c.code] ++ rest⟩

/-- Every active context lifts each inner reduction, including changes to an
inner frame's local values. -/
theorem ActiveCtx.step {host : HostSemantics H} (E : ActiveCtx) {c c' : Config H}
    (h : Step P host c c') : Step P host (E.plug c) (E.plug c') := by
  induction E generalizing c c' with
  | hole => exact h
  | suffix rest E ih => exact ih (Step.append_right h rest)
  | label n cont vs rest E ih =>
    exact ih (Step.append_right (Step.vals_left (Step.ctxtLabel h) vs) rest)
  | handler n cs vs rest E ih =>
    exact ih (Step.append_right (Step.vals_left (Step.ctxtHandler h) vs) rest)
  | frame n f vs rest E ih =>
    exact ih (Step.append_right (Step.vals_left (Step.ctxtFrame h) vs) rest)

/-- The fragment occurs at the active hole of some typed whole configuration.
This allows ambient label and return contexts, unlike standalone `ConfigOk`. -/
def ContextTyped (c : Config H) : Prop :=
  ∃ (E : ActiveCtx) (ts : List CValType), ConfigOk (E.plug c) ts

theorem ContextTyped.of_configOk {c : Config H} {ts : List CValType}
    (h : ConfigOk c ts) : ContextTyped c := ⟨.hole, ts, h⟩

/-- Only a suffix can be stripped at sequence level: dropping a value prefix
could let a malformed fragment borrow operands from its surrounding context. -/
theorem ContextTyped.suffix {s : Store H} {f : Frame} {body rest : List Admin}
    (h : ContextTyped ⟨s, f, body ++ rest⟩) : ContextTyped ⟨s, f, body⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨.suffix rest E, ts, h⟩

theorem ContextTyped.label {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {body rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [.label n cont body] ++ rest⟩) :
    ContextTyped ⟨s, f, body⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨.label n cont vs rest E, ts, h⟩

theorem ContextTyped.handler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {body rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [.handler n cs body] ++ rest⟩) :
    ContextTyped ⟨s, f, body⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨.handler n cs vs rest E, ts, h⟩

theorem ContextTyped.frame {s : Store H} {f fi : Frame} {n : Nat}
    {vs : List Val} {body rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [.frame n fi body] ++ rest⟩) :
    ContextTyped ⟨s, fi, body⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact ⟨.frame n f vs rest E, ts, h⟩

/-- No progress assumption on the closed host is needed. Its reductions are
host-free, so preservation uses the lawful always-diverging host. -/
theorem ContextTyped.step {c c' : Config H} (h : ContextTyped c)
    (hs : Step P (fun _ _ _ _ => False) c c') : ContextTyped c' := by
  obtain ⟨E, ts, h⟩ := h
  refine ⟨E, ts, (Step.preservation (P := P) divHost_ok h ?_).1⟩
  exact E.step (Step.of_noHost divHost hs)

theorem ContextTyped.steps {c c' : Config H} (h : ContextTyped c)
    (hs : Steps P (fun _ _ _ _ => False) c c') : ContextTyped c' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

end Silmaril.Wasm.Execution.Core.Sim
