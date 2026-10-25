module

public import Silmaril.Wasm.Execution.Core.Sim.TypedFragment

@[expose] public section

/-! # Typed block alignment in an arbitrary active context

The ambient typing witness retains the current frame's type table. This gives
both a resolved block signature and enough actual operands, including beneath
runtime labels, handlers and frames. No closed-host progress assumption is used.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

namespace TypedBlock

private theorem prefix_typing {s : Store H} {C : Context} {body rest : List Admin}
    {it : InstrType} (hC : C.Wf) (h : AdminsOk s C (body ++ rest) it) :
    ∃ xs ts, AdminsOk s C body ⟨it.params, xs, ts⟩ := by
  by_cases hr : rest = []
  · subst rest
    exact ⟨it.inits, it.results, by simpa using h⟩
  · obtain ⟨ts, xs, _, hb, _, _⟩ := AdminsOk.split h hC body rest rfl hr
    exact ⟨xs, ts, hb⟩

private theorem active_leaf {s : Store H} {C : Context} {vs : List Val}
    {a : Admin} {rest : List Admin} {it : InstrType} (hC : C.Wf)
    (h : AdminsOk s C (vals vs ++ a :: rest) it) :
    ∃ C' it', C'.Wf ∧ C'.types = C.types ∧ AdminOk s C' a it' := by
  obtain ⟨_, xs, _, _, htail, _⟩ :=
    AdminsOk.split h hC (vals vs) (a :: rest) rfl (List.cons_ne_nil _ _)
  have hC' := hC.initLocals xs
  obtain ⟨_, _, hsingle⟩ := prefix_typing hC' (body := [a]) (by simpa using htail)
  obtain ⟨_, it', ha, _⟩ := AdminsOk.single_inv hC'.types hsingle
  have htypes := congrArg (fun C : Context => C.types) (Context.initLocals_frameView C xs)
  exact ⟨_, it', hC', by simpa only [Context.frameView] using htypes, ha⟩

end TypedBlock

/-- General-context fragment typing retains the active frame's actual type table. -/
theorem ActiveCtx.fragment_types (E : ActiveCtx) {c : Config H} {ts : List CValType}
    (h : ConfigOk (E.plug c) ts) :
    ∃ (C : Context) (ts' : List CValType) (xs : List Nat),
      StoreOk c.store ∧ C.Wf ∧ C.types = c.frame.module.types ∧
        AdminsOk c.store C c.code ⟨[], xs, ts'⟩ := by
  induction E generalizing c ts with
  | hole =>
    obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := h
    exact ⟨C, ts, [], hs, hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩,
      hf.types_eq, hcode⟩
  | suffix rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, htypes, hcode⟩ := ih h
    obtain ⟨xs', ts'', hp⟩ := TypedBlock.prefix_typing hC hcode
    exact ⟨C, ts'', xs', hs, hC, htypes, hp⟩
  | label n cont vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, htypes, hcode⟩ := ih h
    obtain ⟨C', it, hC', htypes', ha⟩ := TypedBlock.active_leaf hC (by simpa using hcode)
    cases ha with
    | label hn hc hb =>
      exact ⟨_, _, _, hs, hC'.withLabel (hc.params_ok hC').1, htypes'.trans htypes, hb⟩
  | handler n cs vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, htypes, hcode⟩ := ih h
    obtain ⟨C', it, hC', htypes', ha⟩ := TypedBlock.active_leaf hC (by simpa using hcode)
    cases ha with
    | handler hc hb => exact ⟨_, _, _, hs, hC', htypes'.trans htypes, hb⟩
  | frame n f vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, htypes, hcode⟩ := ih h
    obtain ⟨C', it, hC', htypes', ha⟩ := TypedBlock.active_leaf hC (by simpa using hcode)
    cases ha with
    | frame hf hn hb hok =>
      exact ⟨_, _, [], hs,
        (hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩).withReturn
          (fun t ht => TyOk.of_empty _ (hok t ht)), hf.types_eq, hb⟩

theorem ContextTyped.fragment_types {c : Config H} (h : ContextTyped c) :
    ∃ (C : Context) (ts : List CValType) (xs : List Nat),
      StoreOk c.store ∧ C.Wf ∧ C.types = c.frame.module.types ∧
        AdminsOk c.store C c.code ⟨[], xs, ts⟩ := by
  obtain ⟨E, ts, h⟩ := h
  exact E.fragment_types h

/-- Typing supplies the actual block signature and the exact trailing operand
segment, while preserving every earlier stack value. -/
theorem ContextTyped.block_ready {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType} {body : List Instr} {rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt body)] ++ rest⟩) :
    ∃ (pre args : List Val) (ps rs : List CValType), vs = pre ++ args ∧
      f.module.blockType? bt = some (ps, rs) ∧ args.length = ps.length := by
  obtain ⟨C, ts, xs, hs, hC, htypes, hcode⟩ := h.fragment_types
  obtain ⟨mid, xs₁, _, hp, ht, _⟩ := AdminsOk.split hcode hC (vals vs)
    (.plain (.block bt body) :: rest) (by simp) (List.cons_ne_nil _ _)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨_, _, hsingle⟩ := TypedBlock.prefix_typing hC' (body := [.plain (.block bt body)])
    (by simpa using ht)
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hsingle
  cases ha with
  | plain hi =>
    cases hi with
    | block hbt hb =>
      have htypes₀ := congrArg (fun C : Context => C.types) (Context.initLocals_frameView C xs₁)
      have htypes' : (C.initLocals xs₁).types = f.module.types :=
        (show (C.initLocals xs₁).types = C.types by
          simpa only [Context.frameView] using htypes₀).trans htypes
      obtain ⟨ps, rs, resolved, plen, _⟩ := blockType_of_types htypes' hbt
      have h₁ := hv.length_eq
      have h₂ := hsub.length_eq
      have h₃ := hsub'.1.length_eq
      simp only [List.nil_append, List.length_append] at h₁ h₂ h₃
      have enough : ps.length ≤ vs.length := by omega
      refine ⟨vs.take (vs.length - ps.length), vs.drop (vs.length - ps.length), ps, rs,
        (List.take_append_drop _ _).symm, resolved, ?_⟩
      rw [List.length_drop]
      omega
    | _ => rename_i h; cases h

/-- The original block can always take its entry step; closed-host progress is
not assumed, and the same ambient typing witness survives the entry. -/
theorem ContextTyped.block_entry {s : Store H} {f : Frame} {vs : List Val}
    {bt : BlockType} {body : List Instr} {rest : List Admin}
    (h : ContextTyped ⟨s, f, vals vs ++ [.plain (.block bt body)] ++ rest⟩) :
    ∃ (pre args : List Val) (ps rs : List CValType), vs = pre ++ args ∧
      f.module.blockType? bt = some (ps, rs) ∧ args.length = ps.length ∧
      Step P (fun _ _ _ _ => False)
        ⟨s, f, vals vs ++ [.plain (.block bt body)] ++ rest⟩
        ⟨s, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)] ++ rest⟩ ∧
      ContextTyped
        ⟨s, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)] ++ rest⟩ := by
  obtain ⟨pre, args, ps, rs, stack, resolved, arity⟩ := h.block_ready
  have entry : Step P (fun _ _ _ _ => False)
      ⟨s, f, vals vs ++ [.plain (.block bt body)] ++ rest⟩
      ⟨s, f, vals pre ++ [.label rs.length [] (vals args ++ expression body)] ++ rest⟩ := by
    rw [stack]
    simpa only [vals_append, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.block resolved arity) pre) rest
  exact ⟨pre, args, ps, rs, stack, resolved, arity, entry, h.step entry⟩

end Silmaril.Wasm.Execution.Core.Sim
