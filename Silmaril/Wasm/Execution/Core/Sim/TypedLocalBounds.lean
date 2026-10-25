module

public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress

@[expose] public section

/-! # Active instruction typing and actual frame-local bounds

The typing witness for the original active context retains the relationship
between static local types and the runtime frame. In particular, bounds on
local instructions refer to the actual frame rather than an unrelated typing
context. These facts do not require a deterministic numerical profile.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}

/-- Isolate the active instruction while retaining its actual frame invariant.
The surrounding value prefix and instruction suffix need not be empty. -/
theorem ContextTyped.active_admin_typed {s : Store H} {f : Frame} {vs : List Val}
    {a : Admin} {rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ a :: rest⟩) :
    ∃ C it, StoreOk s ∧ C.Wf ∧ CtxOk s f C ∧ AdminOk s C a it := by
  have typed : ContextTyped ⟨s, f, vals vs ++ [a]⟩ :=
    ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc,
      List.singleton_append] using h)
  obtain ⟨C, ts, xs, hs, hC, hc, hcode⟩ := typed.fragment_ctx
  obtain ⟨_, xs₁, _, hp, ht, _⟩ :=
    AdminsOk.split hcode hC (vals vs) [a] rfl (by simp)
  have hC' := hC.initLocals xs₁
  have hc' := hc.initLocals hp.vals_inits
  obtain ⟨_, it, ha, _⟩ := AdminsOk.single_inv hC'.types ht
  exact ⟨_, it, hs, hC', hc', ha⟩

/-- Every typed active local access indexes the original runtime frame. -/
theorem ContextTyped.active_local_bound {s : Store H} {f : Frame} {vs : List Val}
    {i : Instr} {rest : List Admin} {x : LocalIdx}
    (h : ContextTyped ⟨s, f, vals vs ++ .plain i :: rest⟩)
    (hlocal : i = .localGet x ∨ i = .localSet x ∨ i = .localTee x) :
    x.toNat < f.locals.length := by
  obtain ⟨C, it, _, _, hc, ha⟩ := h.active_admin_typed
  rw [← hc.len]
  rcases hlocal with rfl | rfl | rfl
  · obtain ⟨_, hx, _⟩ := ha.plain_inv_ne.localGet_invVar
    exact (List.getElem?_eq_some_iff.mp hx).1
  · obtain ⟨_, _, hx, _⟩ := ha.plain_inv_ne.localSet_invVar
    exact (List.getElem?_eq_some_iff.mp hx).1
  · obtain ⟨_, _, hx, _⟩ := ha.plain_inv_ne.localTee_invVar
    exact (List.getElem?_eq_some_iff.mp hx).1

theorem ContextTyped.active_localGet_bound {s : Store H} {f : Frame} {vs : List Val}
    {rest : List Admin} {x : LocalIdx}
    (h : ContextTyped ⟨s, f, vals vs ++ .plain (.localGet x) :: rest⟩) :
    x.toNat < f.locals.length := h.active_local_bound (.inl rfl)

theorem ContextTyped.active_localSet_bound {s : Store H} {f : Frame} {vs : List Val}
    {rest : List Admin} {x : LocalIdx}
    (h : ContextTyped ⟨s, f, vals vs ++ .plain (.localSet x) :: rest⟩) :
    x.toNat < f.locals.length := h.active_local_bound (.inr (.inl rfl))

theorem ContextTyped.active_localTee_bound {s : Store H} {f : Frame} {vs : List Val}
    {rest : List Admin} {x : LocalIdx}
    (h : ContextTyped ⟨s, f, vals vs ++ .plain (.localTee x) :: rest⟩) :
    x.toNat < f.locals.length := h.active_local_bound (.inr (.inr rfl))

/-- A selected runtime frame starts with no enclosing branch labels. Its body
has the frame's actual return arity and a context backed by `FrameOk`. -/
theorem ContextTyped.active_frame_typing {s : Store H} {f fr : Frame} {vs : List Val}
    {n : Nat} {body rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ .frame n fr body :: rest⟩) :
    ∃ C rs, C.Wf ∧ C.labels = [] ∧ C.return_ = some rs ∧ rs.length = n ∧
      AdminsOk s C body (.plain [] rs) ∧ CtxOk s fr C ∧
      ∃ Cf, FrameOk s fr Cf ∧ C = { Cf with return_ := some rs } := by
  obtain ⟨_, it, hs, _, _, ha⟩ := h.active_admin_typed
  obtain ⟨_, _, Cf, hf, hn, hb, hok⟩ := ha.frame_invCtl
  refine ⟨{ Cf with return_ := some it.results }, it.results, ?_,
    (hf.ctx_fields).1, rfl, hn, hb, .ofFrame hf _, Cf, hf, rfl⟩
  exact (hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩).withReturn
    (fun t ht => TyOk.of_empty _ (hok t ht))

end Silmaril.Wasm.Execution.Core.Sim
