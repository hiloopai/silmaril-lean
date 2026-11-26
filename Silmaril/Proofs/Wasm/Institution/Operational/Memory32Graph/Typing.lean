module

public import Silmaril.Wasm.Institution.Operational.Memory32Graph.Defs
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs

open Execution.Runtime (Value)
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Computed

theorem split_load {stack : List Value} {saved : List NumType}
    (types : stack.map Value.type = saved ++ [i32]) :
    ∃ keep address, stack = keep ++ [Value.int .i32 address] ∧ keep.map Value.type = saved := by
  obtain ⟨left, right, rfl, eq, typed⟩ := List.map_eq_append_iff.mp types
  rcases right with _ | ⟨⟨t, bits⟩, rest⟩
  · simp at typed
  · simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at typed
    obtain ⟨rfl, rfl⟩ := typed
    exact ⟨left, bits, rfl, eq⟩

theorem split_store {stack : List Value} {saved : List NumType}
    (types : stack.map Value.type = saved ++ [i32, i32]) :
    ∃ keep address word, stack = keep ++ [Value.int .i32 address, Value.int .i32 word] ∧
      keep.map Value.type = saved := by
  rw [show [i32, i32] = [i32] ++ [i32] from rfl, ← List.append_assoc] at types
  obtain ⟨left, word, rfl, leftTypes⟩ := split_load types
  obtain ⟨keep, address, rfl, typed⟩ := split_load leftTypes
  exact ⟨keep, address, word, by simp, typed⟩

theorem locals_typed (decl : Declaration) {args : List Value}
    (typed : args.map Value.type = decl.params) :
    (decl.frame args).locals.map Value.type = decl.params ++ decl.locals := by
  simp only [Declaration.frame, List.map_append, typed, List.map_map]
  congr 1
  exact congrFun List.map_id_fun decl.locals

private theorem numeric_tail {p : Program} {f : Function} {locals stack next : List Value}
    {op : Prefix.Op} {rest : List Op} (typed : locals.map Value.type = f.localTypes)
    (move : Prefix.Reduce locals stack op (.values next))
    (code : Typed p f.decl (stack.map Value.type) (.numeric op :: rest)) :
    Typed p f.decl (next.map Value.type) rest := by
  generalize eq : stack.map Value.type = ts at code
  cases code with
  | numeric check tail =>
    have result := Prefix.checkOp_result move
    rw [typed, Prefix.stackTypes, Prefix.stackTypes, eq, check] at result
    have same := List.reverse_inj.mp (Option.some.inj result)
    exact same ▸ tail

private theorem load_tail {p : Program} {f : Function} {saved : List Value} {address : BitVec 32} {rest : List Op}
    (code : Typed p f.decl ((saved ++ [Value.int .i32 address]).map Value.type) (.load :: rest)) :
    ∀ (bits : BitVec 32), Typed p f.decl ((saved ++ [Value.int .i32 bits]).map Value.type) rest := by
  simp only [List.map_append, List.map_cons, List.map_nil] at code ⊢
  intro bits
  cases code with
  | load shape tail =>
    have eq : saved.map Value.type = _ := List.append_cancel_right shape
    rw [eq]
    exact tail

private theorem store_tail {p : Program} {f : Function} {saved : List Value} {address word : BitVec 32}
    {rest : List Op}
    (code : Typed p f.decl ((saved ++ [Value.int .i32 address, Value.int .i32 word]).map Value.type) (.store :: rest)) :
    Typed p f.decl (saved.map Value.type) rest := by
  simp only [List.map_append, List.map_cons, List.map_nil] at code
  cases code with
  | store shape tail => exact (List.append_cancel_right shape).symm ▸ tail

private theorem call_tail {p : Program} {f : Function} {saved args : List Value} {target : CallTarget}
    {rest : List Op} (typed : args.map Value.type = target.declaration.params)
    (code : Typed p f.decl ((saved ++ args).map Value.type) (.call target :: rest)) :
    ∃ callee, p.lookup target.address = some callee ∧ callee.decl = target.declaration ∧
      Typed p f.decl (saved.map Value.type ++ target.declaration.results) rest := by
  simp only [List.map_append, typed] at code
  cases code with
  | call shape _ found same tail => exact ⟨_, found, same, (List.append_cancel_right shape).symm ▸ tail⟩

theorem frame_or_done {p : Program} {f : Function} {s t : State}
    (move : Step p f s t) (frame : s.phase.Frame) :
    t.phase.Frame ∨ ∃ r, t.phase = .done r := by
  cases move <;> try contradiction
  case numeric _ _ _ _ _ out move => cases out <;> exact Or.inl True.intro
  case load _ _ _ _ _ out move => cases out <;> exact Or.inl True.intro
  case store _ _ _ _ _ _ out move => cases out <;> exact Or.inl True.intro
  case active _ _ _ _ _ _ _ next _ _ =>
    cases next.phase <;> try (left; exact True.intro)
    case done result => cases result <;> exact Or.inl True.intro
  case call | pending | unreachable | discard | complete | trapExit =>
    exact Or.inl True.intro
  case exit => exact .inr ⟨_, rfl⟩

theorem preserve {p : Program} (checked : p.Checked) {f : Function} {addr : Execution.Runtime.FuncAddr}
    (found : p.lookup addr = some f) {s t : State} (move : Step p f s t)
    (ready : Ready p f s.phase) : Ready p f t.phase := by
  induction move generalizing addr with
  | resolve =>
    cases ready with | call typed => exact .invoke typed
  | enter =>
    cases ready with | invoke typed => exact .running (locals_typed _ typed) (checked _ _ found)
  | @numeric f bytes locals stack op rest out move =>
    cases ready with
    | running typed code => cases out with
      | values => exact .running typed (numeric_tail typed move code)
      | trap => exact .trapped
  | load move =>
    cases ready with
    | running typed code => cases move with
      | load => exact .running typed (load_tail code _)
      | loadTrap => exact .trapped
  | store move =>
    cases ready with
    | running typed code => cases move with
      | store => exact .running typed (store_tail code)
      | storeTrap => exact .trapped
  | call args =>
    cases ready with
    | running typed code =>
      obtain ⟨_, link, same, tail⟩ := call_tail args code
      exact .pending typed link same args tail
  | pending foundChild =>
    cases ready with
    | pending typed matched same args rest =>
      rw [foundChild] at matched
      cases matched
      exact .active typed foundChild same True.intro
        (.running (locals_typed _ (same.symm ▸ args)) (checked _ _ foundChild)) rest
  | @active f bytes locals saved target child rest callee nextState foundChild move ih =>
    cases ready with
    | active typed matched same live inside rest =>
      rw [foundChild] at matched
      cases matched
      have next := ih foundChild inside
      rcases frame_or_done move live with liveNext | ⟨res, eq⟩
      · cases h : nextState.phase
        all_goals
          rw [h] at liveNext next
          first | contradiction | exact Ready.active typed foundChild same liveNext next rest
      · rw [eq] at next ⊢
        cases res with
        | trap => exact .trapped
        | values vs =>
          cases next with
          | done result =>
            apply Ready.running typed
            change vs.map Value.type = callee.decl.results at result
            simpa only [List.map_append, result, same] using rest
  | unreachable => exact .trapped
  | discard => exact .trapped
  | @complete f bytes locals stack =>
    cases ready with
    | running _ code =>
      cases code with | done types => exact .exit types
  | trapExit => exact .exit True.intro
  | exit =>
    cases ready with | exit result => exact .done result

theorem bytes_preserved {p : Program} {f : Function} {a b : State}
    (move : Step p f a b) : b.bytes.size = a.bytes.size := by
  induction move
  case load move => cases move <;> rfl
  case store move => cases move with
    | store edge => exact MemoryWrite.closed edge
    | storeTrap => rfl
  all_goals first | assumption | rfl

end Silmaril.Wasm.Institution.Operational.Memory32Graph.Proofs
