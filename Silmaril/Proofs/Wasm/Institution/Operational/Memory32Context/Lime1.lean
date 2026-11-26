module

public import Silmaril.Wasm.Institution.Operational.Memory32Context.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Context.Proofs

open Execution.Runtime (Value Frame MemAddr MemInst AdminInstr)
open Wasm.Lime1.Execution
open CallContinuation.Proofs.Lime1 (first first_prefix first_head first_value first_values peel)

private theorem redex_split {stack used : List Value} {op : Admin} {q : Access} {rest : List Admin}
    (eq : values used ++ [op] = values stack ++ q.limeOp :: rest) (nonval : asValue? op = none) :
    stack = used ∧ q.limeOp = op ∧ rest = [] := by
  have qNonval : asValue? q.limeOp = none := by cases q <;> rfl
  obtain ⟨args, cut, split, head, tail⟩ :=
    peel (saved := used) (mid := [op]) (tail := []) ⟨op, List.Mem.head _, nonval⟩
      (by simpa only [List.append_nil] using eq) qNonval
  have length := congrArg List.length head
  simp only [List.length_cons, List.length_nil, List.length_append, values_length] at length
  have hArgs : args = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hCut : cut = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst args cut
  exact ⟨by simpa using split, (List.cons.inj head).1.symm, tail⟩

private theorem lime_front {H : Type} {src dst : Config H} (move : Step CallFrame.limeNoHost src dst)
    (q : Access) {stack : List Value} {rest : List Admin}
    (shape : src.code = values stack ++ q.limeOp :: rest) :
    ∃ kept used mid, stack = kept ++ used ∧ used.length = q.args.length ∧
      Step CallFrame.limeNoHost ⟨src.store, src.frame, values used ++ [q.limeOp]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values kept ++ mid.code ++ rest⟩ := by
  have nonval : asValue? q.limeOp = none := by cases q <;> rfl
  have firstEq : first src.code = some q.limeOp := by rw [shape, first_prefix, first_head rest nonval]
  induction move generalizing stack rest with
  | @context s s' f f' before after move saved tail ih =>
    obtain ⟨args, cut, rfl, source, rfl⟩ := peel move.nonvalue shape nonval
    change before = values args ++ q.limeOp :: cut at source
    have seen : first before = some q.limeOp := by rw [source, first_prefix, first_head cut nonval]
    obtain ⟨kept, used, mid, rfl, length, leaf, eq⟩ := ih source seen
    refine ⟨saved ++ kept, used, mid, (List.append_assoc ..).symm, length, leaf, ?_⟩
    change (⟨s', f', after⟩ : Config H) = _ at eq
    simpa only [values_append, List.append_assoc] using congrArg (fun c : Config H =>
      (⟨c.store, c.frame, values saved ++ c.code ++ tail⟩ : Config H)) eq
  | intLoad s f t packed arg i v a m found read =>
    obtain ⟨rfl, op, rfl⟩ := redex_split (used := [Value.int .i32 i]) shape rfl
    cases q <;> cases op
    exact ⟨[], _, _, rfl, rfl, .intLoad s f _ _ _ _ v a m found read, rfl⟩
  | intLoadTrap s f t packed arg i a m found read =>
    obtain ⟨rfl, op, rfl⟩ := redex_split (used := [Value.int .i32 i]) shape rfl
    cases q <;> cases op
    exact ⟨[], _, _, rfl, rfl, .intLoadTrap s f _ _ _ _ a m found read, rfl⟩
  | intStore s f t packed arg i v a m out found write =>
    obtain ⟨rfl, op, rfl⟩ := redex_split (used := [Value.int .i32 i, Value.int t v]) shape rfl
    cases q <;> cases op
    exact ⟨[], _, _, rfl, rfl, .intStore s f _ _ _ _ _ a m out found write, rfl⟩
  | intStoreTrap s f t packed arg i v a m found write =>
    obtain ⟨rfl, op, rfl⟩ := redex_split (used := [Value.int .i32 i, Value.int t v]) shape rfl
    cases q <;> cases op
    exact ⟨[], _, _, rfl, rfl, .intStoreTrap s f _ _ _ _ _ a m found write, rfl⟩
  | pure s f step =>
    cases step <;> simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at firstEq <;>
      cases q <;> simp [Access.limeOp, first, asValue?] at firstEq
  | invokeHost | invokeHostDiverges => contradiction
  | _ =>
    simp only [first_prefix, first_value] at firstEq
    cases q <;> simp [Access.limeOp, first, asValue?] at firstEq

theorem lime_iff {H : Type} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {q : Access} {saved : List Value} {rest : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step CallFrame.limeNoHost ⟨s, f, values (saved ++ q.args) ++ q.limeOp :: rest⟩ dst ↔
      ∃ out, Edge m.data q out ∧
        dst = ⟨out.limeStore s a m, f, values saved ++ out.code value .trap ++ rest⟩ := by
  constructor
  · intro move
    obtain ⟨kept, used, mid, split, length, head, rfl⟩ := lime_front move q rfl
    obtain ⟨rfl, rfl⟩ := List.append_inj' split length.symm
    cases q with
    | load address =>
      obtain ⟨out, rule, rfl⟩ := MemoryQuery.lime_readback lookup (query := .load address) head
      cases MemoryQuery.invert rule with
      | load => exact ⟨.value _, .load rule, rfl⟩
      | loadTrap => exact ⟨.trap, .loadTrap rule, rfl⟩
    | store address word =>
      obtain ⟨out, rule, rfl⟩ := (MemoryWrite.lime_step_iff (a := .store address word) lookup).mp head
      cases MemoryWrite.invert rule with
      | write => exact ⟨.written _, .store rule, rfl⟩
      | trap => exact ⟨.trap, .storeTrap rule, rfl⟩
  · rintro ⟨out, rule, rfl⟩
    have wrap {q : Access} {out : Outcome} (move : Step CallFrame.limeNoHost
        ⟨s, f, values q.args ++ [q.limeOp]⟩ ⟨out.limeStore s a m, f, out.code value .trap⟩) :
        Step CallFrame.limeNoHost ⟨s, f, values (saved ++ q.args) ++ q.limeOp :: rest⟩
          ⟨out.limeStore s a m, f, values saved ++ out.code value .trap ++ rest⟩ := by
      simpa only [values_append, List.append_assoc, List.singleton_append] using Step.context move saved rest
    cases rule with
    | load e => exact wrap (MemoryQuery.lime_sound lookup e)
    | loadTrap e => exact wrap (MemoryQuery.lime_sound lookup e)
    | store e => exact wrap (MemoryWrite.lime_sound lookup e)
    | storeTrap e => exact wrap (MemoryWrite.lime_sound lookup e)

end Silmaril.Wasm.Institution.Operational.Memory32Context.Proofs
