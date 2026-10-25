module

public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

@[expose] public section

/-! Extracting general-context typing from an active whole-configuration witness.
The fragment starts with an empty abstract stack, while its labels and return
context may be supplied by the enclosing runtime syntax.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Validation Numerics SingleThreaded

variable {H : Type}

def FragmentTyped (c : Config H) : Prop :=
  ∃ (C : Context) (ts : List CValType) (xs : List Nat),
    StoreOk c.store ∧ C.Wf ∧ AdminsOk c.store C c.code ⟨[], xs, ts⟩

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
    ∃ C' it', C'.Wf ∧ AdminOk s C' a it' := by
  obtain ⟨_, xs, _, _, htail, _⟩ :=
    AdminsOk.split h hC (vals vs) (a :: rest) rfl (List.cons_ne_nil _ _)
  have hC' := hC.initLocals xs
  obtain ⟨_, _, hsingle⟩ := prefix_typing hC' (body := [a]) (by simpa using htail)
  obtain ⟨_, it', ha, _⟩ := AdminsOk.single_inv hC'.types hsingle
  exact ⟨_, it', hC', ha⟩

/-- Active fragments remain typed from an empty abstract operand stack; the
surrounding label and return context is retained rather than erased. -/
theorem ActiveCtx.fragment (E : ActiveCtx) {c : Config H} {ts : List CValType}
    (h : ConfigOk (E.plug c) ts) : FragmentTyped c := by
  induction E generalizing c ts with
  | hole =>
    obtain ⟨C, ⟨hs, hf⟩, hcode⟩ := h
    exact ⟨C, ts, [], hs, hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩, hcode⟩
  | suffix rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hcode⟩ := ih h
    obtain ⟨xs', ts'', hp⟩ := prefix_typing hC hcode
    exact ⟨C, ts'', xs', hs, hC, hp⟩
  | label n cont vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hcode⟩ := ih h
    obtain ⟨C', it, hC', ha⟩ := active_leaf hC (by simpa using hcode)
    cases ha with
    | label hn hc hb =>
      exact ⟨_, _, _, hs, hC'.withLabel (hc.params_ok hC').1, hb⟩
  | handler n cs vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hcode⟩ := ih h
    obtain ⟨C', it, hC', ha⟩ := active_leaf hC (by simpa using hcode)
    cases ha with
    | handler hc hb => exact ⟨_, _, _, hs, hC', hb⟩
  | frame n f vs rest E ih =>
    obtain ⟨C, ts', xs, hs, hC, hcode⟩ := ih h
    obtain ⟨C', it, hC', ha⟩ := active_leaf hC (by simpa using hcode)
    cases ha with
    | frame hf hn hb hok =>
      refine ⟨_, _, [], hs, ?_, hb⟩
      exact (hf.ctxWf hs ⟨hs.structsClosed, hs.arraysClosed⟩).withReturn
        (fun t ht => TyOk.of_empty _ (hok t ht))

theorem ContextTyped.fragment {c : Config H} (h : ContextTyped c) : FragmentTyped c := by
  obtain ⟨E, ts, h⟩ := h
  exact E.fragment h

/-- A typed active instruction has at least its required operand arity. This is
independent of numerical semantics and of the ambient label/return context. -/
theorem FragmentTyped.active_arity {s : Store H} {f : Frame} {vs : List Val}
    {a : Admin} {rest : List Admin} {n : Nat}
    (h : FragmentTyped ⟨s, f, vals vs ++ a :: rest⟩)
    (arity : ∀ C it, AdminOk s C a it → n ≤ it.params.length) : n ≤ vs.length := by
  obtain ⟨C, ts, xs, hs, hC, hcode⟩ := h
  obtain ⟨mid, xs₁, _, hp, ht, _⟩ :=
    AdminsOk.split hcode hC (vals vs) (a :: rest) rfl (List.cons_ne_nil _ _)
  obtain ⟨pushed, hv, hsub⟩ := AdminsOk.vals_inv hC.types hp
  have hC' := hC.initLocals xs₁
  obtain ⟨_, _, hsingle⟩ := prefix_typing hC' (body := [a]) (by simpa using ht)
  obtain ⟨framed, it, ha, hsub'⟩ := AdminsOk.single_inv hC'.types hsingle
  have h₁ := hv.length_eq
  have h₂ := hsub.length_eq
  have h₃ := hsub'.1.length_eq
  have h₄ := arity _ _ ha
  simp only [List.nil_append, List.length_append] at h₁ h₂ h₃ h₄
  omega

end Silmaril.Wasm.Execution.Core.Sim
