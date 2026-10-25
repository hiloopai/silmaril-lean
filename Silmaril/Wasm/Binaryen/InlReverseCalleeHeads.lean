module

public import Silmaril.Wasm.Binaryen.InlReverseCallee
public import Silmaril.Wasm.Binaryen.InlReverseCall
public import Silmaril.Wasm.Binaryen.InlReverseMatch

@[expose] public section

/-! # Chosen relocated-callee head dispatch

A selected target head is matched using its original AI witness. This retains
original local indices and distinguishes an original return, whose relocation
is a blocked branch, from ordinary unchanged computational instructions. Calls
enter the actual selected target function through the original function table,
with their nested activations related by FR. No numerical determinism or
uniqueness of complete outcomes is used.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- Replay the actual selected Wasm call inside a relocated callee. The outer
callee's original locals and caller prefix remain unchanged. -/
theorem reverse_callee_callData (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (selected : CallData t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s F args head originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨values, address, function, params, results, body, rfl,
    callHead, found, expanded, arity, wasm, rfl⟩ := selected
  obtain ⟨original, originalCode, originalFound, sameType, originalWasm, activations⟩ :=
    call_rel_reverse parameters stores found expanded arity wasm
  exact ⟨_, .callRefFunc rfl callHead originalFound (sameType ▸ expanded) arity originalWasm,
    ⟨moduleEq, prefixLength, locals, rfl, .cons (.frame activations) .nil⟩, stores⟩

/-- Replay every unchanged simple nonstructured, nontail callee head,
including actual selected Wasm call entries. -/
theorem reverse_callee_simple_head (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame}
    {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (simple : SimpleE head) (nonstruct : ¬ StructE head) (nontail : ¬ TailE head)
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s F args head originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  rcases head_simple_reverse stores moduleEq.symm simple selected with call |
      ⟨originalNext, actual, originalFrame, transformedFrame, code, related⟩
  · exact reverse_callee_callData parameters moduleEq prefixLength locals stores call
  · rcases head_out selected simple nonstruct with call | out | ⟨tail, _⟩
    · exact reverse_callee_callData parameters moduleEq prefixLength locals stores call
    · refine ⟨originalNext, actual, ⟨?_, prefixLength, ?_, ?_, ?_⟩, related⟩
      · rw [originalFrame]; exact moduleEq
      · rw [originalFrame]; exact locals
      · rw [transformedFrame, originalFrame]
      · rw [code]; exact LI.of_out out
    · exact (nontail tail).elim

/-- Dispatch a relocated original instruction. Original load/store bounds are
retained explicitly, since relocation falls back on an index on overflow and
successful target accesses alone do not imply a valid original local access. -/
theorem reverse_callee_plain_head (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame} {old : Instr}
    (good : InlineTy.retGood d old)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (localBound : ∀ x, (old = .localGet x ∨ old = .localSet x) → x.toNat < F.locals.length)
    {args : List Val} {next : Config H}
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args
      (.plain (InlineTy.xform p.base d old)) next) :
    ∃ originalNext : Config H,
      Det.Head P s F args (.plain old) originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  by_cases localAccess : IsLocalI old = true
  · have localShape : ∃ x, old = .localGet x ∨ old = .localSet x ∨ old = .localTee x := by
      cases old <;> simp_all [IsLocalI]
    obtain ⟨x, rfl | rfl | rfl⟩ := localShape
    · exact reverse_callee_localGet parameters moduleEq prefixLength locals
        (localBound x (.inl rfl)) stores selected
    · exact reverse_callee_localSet parameters moduleEq prefixLength locals
        (localBound x (.inr rfl)) stores selected
    · exact reverse_callee_localTee moduleEq prefixLength locals stores selected
  · by_cases structured : StructE (.plain old)
    · rcases structured with ⟨bt, body, shape⟩ | ⟨bt, body, shape⟩ |
        ⟨bt, yes, no, shape⟩ | ⟨bt, catches, body, shape⟩ <;> cases shape
      · exact reverse_callee_block good moduleEq prefixLength locals stores selected
      · exact reverse_callee_loop good moduleEq prefixLength locals stores selected
      · exact reverse_callee_if good.1 good.2 moduleEq prefixLength locals stores selected
      · exact reverse_callee_tryTable good moduleEq prefixLength locals stores selected
    · have notReturn : old ≠ .return_ := by
        rintro rfl
        exact selected.good.not_blocked (.inl ⟨_, rfl⟩)
      have nonstructural : structuredInstr old = false := by
        cases old <;> simp_all [structuredInstr, StructE]
      rw [xform_flat (by simpa using localAccess) nonstructural notReturn] at selected
      refine reverse_callee_simple_head parameters moduleEq prefixLength locals stores
        (simpleE_plain ?_ ?_ ?_) structured ?_ selected
      · intro x eq; subst eq; simp [IsLocalI] at localAccess
      · intro x eq; subst eq; simp [IsLocalI] at localAccess
      · intro x eq; subst eq; simp [IsLocalI] at localAccess
      · rintro (⟨x, eq⟩ | ⟨x, y, eq⟩) <;> cases eq <;> exact good.elim

/-- Match any selected nonadministrative callee head from its original AI
witness. Runtime labels, handlers and frames are handled by recursive context
rules; structured Wasm instructions and original local accesses are included. -/
theorem reverse_callee_head (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame} {old head : Admin}
    (heads : AI p d old head)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (localBound : ∀ x, (old = .plain (.localGet x) ∨ old = .plain (.localSet x)) →
      x.toNat < F.locals.length)
    {args : List Val} {next : Config H}
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s F args old originalNext ∧
      MR p (.i d L) originalNext next ∧ SR p originalNext.store next.store := by
  cases heads with
  | plain good =>
    exact reverse_callee_plain_head parameters good moduleEq prefixLength locals stores
      (fun x bound => localBound x (bound.imp (congrArg Admin.plain) (congrArg Admin.plain))) selected
  | ref r => exact absurd selected.good.val_none (by simp)
  | callRef dt =>
    exact reverse_callee_simple_head parameters moduleEq prefixLength locals stores
      (simpleE_callRef dt) (not_structE_callRef dt)
      (by rintro (⟨x, eq⟩ | ⟨x, y, eq⟩) <;> cases eq) selected
  | label _ _ => exact (nonlabel _ _ _ rfl).elim
  | handler _ => exact (nonhandler _ _ _ rfl).elim
  | frame _ => exact (nonframe _ _ _ rfl).elim
  | trap => exact (selected.good.ne_trap rfl).elim

/-- Package the chosen callee head as one actual source step and an empty
normalization prefix for recursive reverse context composition. -/
theorem reverse_callee_head_match (parameters : PrmOk p)
    {d : Nat} {L : List (Option Val)} {s t : Store H} {F : Frame} {old head : Admin}
    (heads : AI p d old head)
    (moduleEq : F.module = p.mi) (prefixLength : L.length = p.base)
    (locals : F.locals.length = p.ext) (stores : SR p s t)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (localBound : ∀ x, (old = .plain (.localGet x) ∨ old = .plain (.localSet x)) →
      x.toNat < F.locals.length)
    {args : List Val} {next : Config H}
    (selected : Det.Head P t ⟨L ++ F.locals, p.mi⟩ args head next) :
    ReverseMatch p P (.i d L) ⟨s, F, vals args ++ [old]⟩ next := by
  obtain ⟨originalNext, actual, runtime, related⟩ :=
    reverse_callee_head parameters heads moduleEq prefixLength locals stores
      nonlabel nonhandler nonframe localBound selected
  exact ReverseMatch.of_steps (.single actual.toStep) runtime related

end Silmaril.Wasm.Binaryen.InlR
