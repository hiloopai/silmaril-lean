module

public import Silmaril.Wasm.Execution.Core.Sim.TypedBlock

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}

namespace TypedProgress

private theorem prefix_typing {s : Store H} {C : Context} {body rest : List Admin}
    {it : InstrType} (hC : C.Wf) (h : AdminsOk s C (body ++ rest) it) :
    ∃ xs ts, AdminsOk s C body ⟨it.params, xs, ts⟩ := by
  by_cases hr : rest = []
  · subst rest
    exact ⟨it.inits, it.results, by simpa using h⟩
  · obtain ⟨ts, xs, _, hb, _, _⟩ := AdminsOk.split h hC body rest rfl hr
    exact ⟨xs, ts, hb⟩

private theorem active_leaf {s : Store H} {f : Frame} {C : Context} {vs : List Val}
    {a : Admin} {rest : List Admin} {it : InstrType} (hC : C.Wf) (hc : CtxOk s f C)
    (h : AdminsOk s C (vals vs ++ a :: rest) it) :
    ∃ C' it', C'.Wf ∧ CtxOk s f C' ∧ AdminOk s C' a it' := by
  obtain ⟨_, xs, _, hp, ht, _⟩ :=
    AdminsOk.split h hC (vals vs) (a :: rest) rfl (List.cons_ne_nil _ _)
  have hC' := hC.initLocals xs
  have hc' := hc.initLocals hp.vals_inits
  obtain ⟨_, _, hsingle⟩ := prefix_typing hC' (body := [a]) (by simpa using ht)
  obtain ⟨_, it', ha, _⟩ := AdminsOk.single_inv hC'.types hsingle
  exact ⟨_, it', hC', hc', ha⟩

end TypedProgress

/-- The original active context preserves the frame/locals invariant needed by
Core progress, as well as typing from an empty operand stack. -/
theorem ActiveCtx.fragment_ctx (E : ActiveCtx) {c : Config H} {ts : List CValType}
    (h : ConfigOk (E.plug c) ts) :
    ∃ (C : Context) (ts' : List CValType) (xs : List Nat),
      StoreOk c.store ∧ C.Wf ∧ CtxOk c.store c.frame C ∧
        AdminsOk c.store C c.code ⟨[], xs, ts'⟩ := by
  induction E generalizing c ts with
  | hole =>
    obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := h
    exact ⟨C, ts, [], hs, hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩,
      CtxOk.ofFrame₀ hf, hcode⟩
  | suffix rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hc, hcode⟩ := ih h
    obtain ⟨xs', ts'', hp⟩ := TypedProgress.prefix_typing hC hcode
    exact ⟨C, ts'', xs', hs, hC, hc, hp⟩
  | label n cont vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hc, hcode⟩ := ih h
    obtain ⟨C', it, hC', hc', ha⟩ :=
      TypedProgress.active_leaf hC hc (by simpa using hcode)
    cases ha with
    | label hn hcont hb =>
      exact ⟨_, _, _, hs, hC'.withLabel (hcont.params_ok hC').1, hc'.withLabel _, hb⟩
  | handler n cs vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hc, hcode⟩ := ih h
    obtain ⟨C', it, hC', hc', ha⟩ :=
      TypedProgress.active_leaf hC hc (by simpa using hcode)
    cases ha with
    | handler hcs hb => exact ⟨_, _, _, hs, hC', hc', hb⟩
  | frame n f vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hc, hcode⟩ := ih h
    obtain ⟨C', it, hC', hc', ha⟩ :=
      TypedProgress.active_leaf hC hc (by simpa using hcode)
    cases ha with
    | frame hf hn hb hok =>
      exact ⟨_, _, [], hs,
        (hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩).withReturn
          (fun t ht => TyOk.of_empty _ (hok t ht)), CtxOk.ofFrame hf _, hb⟩

theorem ContextTyped.fragment_ctx {c : Config H} (h : ContextTyped c) :
    ∃ (C : Context) (ts : List CValType) (xs : List Nat),
      StoreOk c.store ∧ C.Wf ∧ CtxOk c.store c.frame C ∧
        AdminsOk c.store C c.code ⟨[], xs, ts⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact E.fragment_ctx h

end Silmaril.Wasm.Execution.Core.Sim
