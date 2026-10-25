module

public import Silmaril.Wasm.Binaryen.InlReverseCaller
public import Silmaril.Wasm.Binaryen.InlReverseCall
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Binaryen.RemoveUnusedBrsGuardSim

@[expose] public section

/-! # Chosen caller local accesses and Wasm calls

The transformed caller retains the original local prefix followed by its added
callee-local suffix. A reverse load or store must remain inside that original
prefix; a successful target access alone does not establish this bound. These
rules preserve the actual selected local value, frame update or call activation
at every numerical profile, including recursive calls to the changed caller.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- An in-bounds caller load cannot read the added-local suffix. -/
theorem reverse_caller_localGet {s t : Store H} {fo : Frame}
    {E : List (Option Val)} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (bound : x.toNat < fo.locals.length)
    (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.localGet x)) next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args (.plain (.localGet x)) originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨rfl, v, lookup, rfl⟩ := GuardSim.head_localGet selected
  have originalLookup : fo.local? x = some (some v) := by
    simp only [Frame.local?] at lookup ⊢
    rw [List.getElem?_append_left bound] at lookup
    exact lookup
  exact ⟨⟨s, fo, [v.toAdmin]⟩, .variable (.localGet originalLookup),
    ⟨moduleEq, locals, E, extra, rfl, LG.of_out (Out.vals [v])⟩, stores⟩

/-- A caller store updates the original prefix and preserves the entire added
local suffix, including the current state of an active inlined callee. -/
theorem reverse_caller_localSet {s t : Store H} {fo : Frame}
    {E : List (Option Val)} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (bound : x.toNat < fo.locals.length)
    (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.localSet x)) next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args (.plain (.localSet x)) originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨v, rfl, _, rfl⟩ := SimplifyLocalsLite.head_localSet selected
  refine ⟨⟨s, fo.setLocal x v, []⟩, .variable (.localSet bound),
    ⟨?_, ?_, E, extra, ?_, LG.of_out (Out.vals [])⟩, stores⟩
  · simp [Frame.setLocal, moduleEq]
  · simp [Frame.setLocal, locals]
  · simp only [Frame.setLocal]
    rw [List.set_append_left _ _ bound]

/-- The tee expansion does not access the local yet, so its reverse matching
needs no local bound. The subsequent store uses the in-bounds rule above. -/
theorem reverse_caller_localTee {s t : Store H} {fo : Frame}
    {E : List (Option Val)} {x : LocalIdx} {args : List Val} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args (.plain (.localTee x)) next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args (.plain (.localTee x)) originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨v, rfl, rfl⟩ := SimplifyLocalsLite.head_localTee selected
  exact ⟨⟨s, fo, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩, .variable .localTee,
    ⟨moduleEq, locals, E, extra, rfl,
      .val (by simp) (.val (by simp) (.plain (.cons (.flat _) .nil)))⟩, stores⟩

/-- Enter the actual selected transformed Wasm function in the source store.
The inner activations satisfy FR, while the caller's original/added local
slices remain related by the same E. -/
theorem reverse_caller_callData (parameters : PrmOk p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (selected : CallData t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args head originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  obtain ⟨values, address, function, params, results, body, rfl,
    callHead, found, expanded, arity, wasm, rfl⟩ := selected
  obtain ⟨original, originalCode, originalFound, sameType, originalWasm, activations⟩ :=
    call_rel_reverse parameters stores found expanded arity wasm
  exact ⟨_, .callRefFunc rfl callHead originalFound (sameType ▸ expanded) arity originalWasm,
    ⟨moduleEq, locals, E, extra, rfl, .head (.frame activations) .nil⟩, stores⟩

/-- Every unchanged simple nonstructured caller head replays the actual chosen
target outcome. This includes Wasm call entries and ordinary tail-call fetches;
local accesses and structured block/loop/if/try entries use their specific rules. -/
theorem reverse_caller_simple_head (parameters : PrmOk p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (simple : SimpleE head) (nonstruct : ¬ StructE head)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args head originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  rcases head_simple_reverse stores moduleEq.symm simple selected with call |
      ⟨originalNext, actual, originalFrame, transformedFrame, code, related⟩
  · exact reverse_caller_callData parameters moduleEq locals extra stores call
  · rcases head_out selected simple nonstruct with call | out | ⟨_, out⟩
    · exact reverse_caller_callData parameters moduleEq locals extra stores call
    · refine ⟨originalNext, actual, ⟨?_, ?_, E, extra, ?_, ?_⟩, related⟩
      · rw [originalFrame]; exact moduleEq
      · rw [originalFrame]; exact locals
      · rw [transformedFrame, originalFrame]
      · rw [code]; exact LG.of_out out
    · refine ⟨originalNext, actual, ⟨?_, ?_, E, extra, ?_, ?_⟩, related⟩
      · rw [originalFrame]; exact moduleEq
      · rw [originalFrame]; exact locals
      · rw [transformedFrame, originalFrame]
      · rw [code]; exact LG.of_outT out

/-- Dispatch every unchanged nonstructured caller head. Bounds are required
only for loads/stores of original caller locals; tee expansion is independent of
that bound. Runtime labels, handlers and frames have recursive context rules. -/
theorem reverse_caller_flat_head (parameters : PrmOk p)
    {s t : Store H} {fo : Frame} {E : List (Option Val)}
    {args : List Val} {head : Admin} {next : Config H}
    (moduleEq : fo.module = p.mi) (locals : fo.locals.length = p.base)
    (extra : E.length = p.ext) (stores : SR p s t)
    (nonlabel : ∀ n cont body, head ≠ .label n cont body)
    (nonhandler : ∀ n catches body, head ≠ .handler n catches body)
    (nonframe : ∀ n frame body, head ≠ .frame n frame body)
    (nonstruct : ¬ StructE head)
    (localBound : ∀ x, (head = .plain (.localGet x) ∨ head = .plain (.localSet x)) →
      x.toNat < fo.locals.length)
    (selected : Det.Head P t ⟨fo.locals ++ E, p.mi⟩ args head next) :
    ∃ originalNext : Config H,
      Det.Head P s fo args head originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  by_cases simple : SimpleE head
  · exact reverse_caller_simple_head parameters moduleEq locals extra stores simple nonstruct selected
  · have localAccess : ∃ x, head = .plain (.localGet x) ∨ head = .plain (.localSet x) ∨
        head = .plain (.localTee x) := by
      refine Classical.byContradiction fun absent =>
        simple ⟨nonlabel, nonhandler, nonframe, ?_, ?_, ?_⟩
      · intro x eq; exact absent ⟨x, .inl eq⟩
      · intro x eq; exact absent ⟨x, .inr (.inl eq)⟩
      · intro x eq; exact absent ⟨x, .inr (.inr eq)⟩
    obtain ⟨x, rfl | rfl | rfl⟩ := localAccess
    · exact reverse_caller_localGet moduleEq locals extra (localBound x (.inl rfl)) stores selected
    · exact reverse_caller_localSet moduleEq locals extra (localBound x (.inr rfl)) stores selected
    · exact reverse_caller_localTee moduleEq locals extra stores selected

end Silmaril.Wasm.Binaryen.InlR
