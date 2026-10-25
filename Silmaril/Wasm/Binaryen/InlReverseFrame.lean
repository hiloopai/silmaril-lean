module

public import Silmaril.Wasm.Binaryen.InlReverseMatch
public import Silmaril.Wasm.Binaryen.InlReverseCaller

@[expose] public section

/-! # Chosen reverse steps of related activation frames

A selected step inside a frame is exposed with the actual `FR` witness for
recursive generic/caller matching. Terminal frame exits are replayed directly.
In caller mode a trap or throw may have an original unreachable suffix; the
source really bubbles that suffix away before leaving the activation.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

theorem LG.vals_inv_right {E : List (Option Val)} : ∀ {values : List Val} {original : List Admin},
    LG p E original (vals values) → original = vals values
  | [], _, related => by
    cases related with
    | plain tail => cases tail; rfl
  | value :: values, _, related => by
    have related' : LG p E _ (value.toAdmin :: vals values) := related
    generalize valueEq : value.toAdmin = head at related'
    cases related' with
    | val _ tail => rw [LG.vals_inv_right tail, ← valueEq]; rfl
    | head head tail =>
      subst valueEq
      rw [AG.val_inv_right head, LGq.vals_inv_right tail]
      rfl
    | plain tail =>
      exact LGq.vals_inv_right (valueEq ▸ tail)
    | seg _ | trapT | throwT =>
      have value' := congrArg Admin.val? valueEq
      rw [Admin.val?_toAdmin] at value'
      cases value'

theorem FR.modules_eq {oldFrame newFrame : Frame} {oldBody newBody : List Admin}
    (related : FR p oldFrame newFrame oldBody newBody) : newFrame.module = oldFrame.module := by
  cases related with
  | gen => rfl
  | g moduleEq _ _ _ => exact moduleEq.symm

theorem FR.vals_inv_right {oldFrame newFrame : Frame} {oldBody : List Admin} {values : List Val}
    (related : FR p oldFrame newFrame oldBody (vals values)) : oldBody = vals values := by
  cases related with
  | gen code => exact LN.vals_inv_right code
  | g _ _ _ code => exact LG.vals_inv_right code

/-- A return or tail-call instruction is unchanged in the caller relation. -/
theorem AG.eq_of_frameExit_right {E : List (Option Val)} {old head : Admin}
    (exit : head = .plain .return_ ∨ head.IsReturnCallRef) (related : AG p E old head) :
    old = head := by
  rcases exit with rfl | tail
  · obtain ⟨instruction, rfl, translated⟩ := AG.plain_inv_right related
    rw [IR.eq_of_nonstruct_right translated (by simp [StructE])]
  · rcases Det.IsReturnCallRef.cases tail with ⟨index, rfl⟩ | ⟨type, rfl⟩
    · obtain ⟨instruction, rfl, translated⟩ := AG.plain_inv_right related
      rw [IR.eq_of_nonstruct_right translated (by simp [StructE])]
    · cases related; rfl

/-- Recover a return/tail-call prefix from the actual transformed frame body.
The discarded original suffix need not equal its transformed image. -/
theorem FR.frameExit_prefix_right {oldFrame newFrame : Frame} {oldBody rest : List Admin}
    {values : List Val} {head : Admin}
    (exit : head = .plain .return_ ∨ head.IsReturnCallRef)
    (related : FR p oldFrame newFrame oldBody (vals values ++ head :: rest)) :
    ∃ oldRest, oldBody = vals values ++ head :: oldRest := by
  have nonvalue : head.val? = none := by
    rcases exit with rfl | tail
    · rfl
    · exact Det.IsReturnCallRef.val_none tail
  have nonlabel : ∀ n cont body, head ≠ .label n cont body := by
    rintro n cont body rfl
    rcases exit with impossible | impossible
    · cases impossible
    · exact impossible.elim
  have nonhandler : ∀ n catches body, head ≠ .handler n catches body := by
    rintro n catches body rfl
    rcases exit with impossible | impossible
    · cases impossible
    · exact impossible.elim
  have nonframe : ∀ n frame body, head ≠ .frame n frame body := by
    rintro n frame body rfl
    rcases exit with impossible | impossible
    · cases impossible
    · exact impossible.elim
  cases related with
  | gen code =>
    obtain ⟨oldRest, shape, _⟩ := LN.flat_inv_right nonlabel nonhandler nonframe code
    exact ⟨oldRest, shape⟩
  | g _ _ _ code =>
    rcases LG.vals_cons_inv_right nonvalue code with ordinary | pending | trapped | thrown
    · obtain ⟨oldHead, oldRest, shape, headRelated, _⟩ := ordinary
      rw [AG.eq_of_frameExit_right exit headRelated] at shape
      exact ⟨oldRest, shape⟩
    · obtain ⟨rfl, _⟩ := pending
      rcases exit with impossible | impossible
      · cases impossible
      · exact impossible.elim
    · obtain ⟨rfl, _⟩ := trapped
      rcases exit with impossible | impossible
      · cases impossible
      · exact impossible.elim
    · obtain ⟨rfl, _⟩ := thrown
      rcases exit with impossible | impossible
      · cases impossible
      · exact impossible.elim

/-- A transformed trap may retain an arbitrary unreachable original suffix. -/
theorem FR.trap_prefix_right {oldFrame newFrame : Frame} {oldBody : List Admin}
    (related : FR p oldFrame newFrame oldBody [.trap]) :
    ∃ oldRest, oldBody = .trap :: oldRest := by
  cases related with
  | gen code => exact ⟨[], LN.trap_inv_right code⟩
  | g _ _ _ code =>
    rcases LG.vals_cons_inv_right (vs := []) rfl code with ordinary | pending | trapped | thrown
    · obtain ⟨oldHead, oldRest, shape, headRelated, _⟩ := ordinary
      cases headRelated
      exact ⟨oldRest, shape⟩
    · obtain ⟨impossible, _⟩ := pending
      cases impossible
    · obtain ⟨_, oldRest, shape⟩ := trapped
      exact ⟨oldRest, shape⟩
    · obtain ⟨impossible, _⟩ := thrown
      cases impossible

/-- An unchanged exception address and throw prefix precede any unreachable
original suffix retained by `LG.throwT`. -/
theorem FR.throwing_prefix_right {oldFrame newFrame : Frame} {oldBody : List Admin} {a : Nat}
    (related : FR p oldFrame newFrame oldBody (throwing a)) :
    ∃ oldRest, oldBody = throwing a ++ oldRest := by
  cases related with
  | gen code => exact ⟨[], by simpa using LN.throwing_inv_right code⟩
  | g _ _ _ code =>
    rcases LG.vals_cons_inv_right (vs := [.ref (.exn a)]) (x := .plain .throwRef)
        (rest := []) rfl code with ordinary | pending | trapped | thrown
    · obtain ⟨oldHead, oldRest, shape, headRelated, _⟩ := ordinary
      obtain ⟨instruction, rfl, translated⟩ := AG.plain_inv_right headRelated
      rw [IR.eq_of_nonstruct_right translated (by simp [StructE])] at shape
      exact ⟨oldRest, by simpa [vals, Val.toAdmin] using shape⟩
    · obtain ⟨impossible, _⟩ := pending
      cases impossible
    · obtain ⟨impossible, _⟩ := trapped
      cases impossible
    · obtain ⟨_, oldRest, shape⟩ := thrown
      exact ⟨oldRest, by simpa [vals, Val.toAdmin] using shape⟩

/-- The two recursive frame cases are exactly generic or changed-caller mode.
Stores remain explicit so the same witness applies at the actual chosen step. -/
theorem FR.runtime_modes {s t : Store H} {oldFrame newFrame : Frame}
    {oldBody newBody : List Admin} (related : FR p oldFrame newFrame oldBody newBody) :
    MR p .gen ⟨s, oldFrame, oldBody⟩ ⟨t, newFrame, newBody⟩ ∨
      MR p .g ⟨s, oldFrame, oldBody⟩ ⟨t, newFrame, newBody⟩ := by
  cases related with
  | gen code => exact .inl ⟨rfl, code⟩
  | g moduleEq locals extra code => exact .inr ⟨moduleEq, locals, _, extra, rfl, code⟩

/-- A selected target frame step either exposes its actual inner computation,
or exits by a nonempty source run with identical result code. The two outer
frames may differ: activation exits never inspect their locals or module. -/
theorem reverse_frame_core {n : Nat} {s t : Store H}
    {oldOuter newOuter oldFrame newFrame : Frame}
    {oldBody newBody : List Admin} {args : List Val} {next : Config H}
    (stores : SR p s t) (related : FR p oldFrame newFrame oldBody newBody)
    (selected : Det.Head P t newOuter args (.frame n newFrame newBody) next) :
    (∃ bodyNext : Config H, args = [] ∧ FR p oldFrame newFrame oldBody newBody ∧
      Step P Det.noHost ⟨t, newFrame, newBody⟩ bodyNext ∧
      next = ⟨bodyNext.store, newOuter, [.frame n bodyNext.frame bodyNext.code]⟩) ∨
    ∃ code, Relation.TransGen (Step P Det.noHost)
      ⟨s, oldOuter, vals args ++ [.frame n oldFrame oldBody]⟩ ⟨s, oldOuter, code⟩ ∧
      next = ⟨t, newOuter, code⟩ ∧ FlatRes code := by
  have modules := related.modules_eq
  cases selected with
  | ctxtFrame step => exact .inl ⟨_, rfl, related, step, rfl⟩
  | frameVals shape count =>
    rw [shape] at related
    obtain rfl := FR.vals_inv_right related
    exact .inr ⟨_, tg_head (.frameVals rfl count), rfl, .inl ⟨_, rfl⟩⟩
  | returnFrame shape count =>
    rename_i discarded returned rest
    have combined : vals discarded ++ vals returned ++ [Admin.plain .return_] ++ rest =
        vals (discarded ++ returned) ++ .plain .return_ :: rest := by simp
    rw [combined] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := FR.frameExit_prefix_right (.inl rfl) related
    exact .inr ⟨_, tg_head (.returnFrame (by simpa using oldShape) count),
      rfl, .inl ⟨_, rfl⟩⟩
  | returnCallRefFrameNull shape isReturn =>
    rename_i values head rest
    have combined : vals values ++ [Admin.ref .null, head] ++ rest =
        vals (values ++ [.ref .null]) ++ head :: rest := by simp [vals, Val.toAdmin]
    rw [combined] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := FR.frameExit_prefix_right (.inr isReturn) related
    exact .inr ⟨_,
      tg_head (.returnCallRefFrameNull (by simpa [vals, Val.toAdmin] using oldShape) isReturn),
      rfl, .inr (.inl rfl)⟩
  | returnCallRefFrameAddr shape isReturn found expanded count =>
    rename_i discarded returned address head rest function params results
    have combined : vals discarded ++ vals returned ++ [Admin.ref (.func address), head] ++ rest =
        vals (discarded ++ returned ++ [.ref (.func address)]) ++ head :: rest := by
      simp [vals, Val.toAdmin]
    rw [combined] at shape
    rw [shape] at related
    obtain ⟨oldRest, oldShape⟩ := FR.frameExit_prefix_right (.inr isReturn) related
    have types : SameTypes s.funcs t.funcs := by
      rw [stores.ht]
      exact stores.sameTypes.symm
    obtain ⟨originalFunction, originalFound, sameType⟩ := types.get found
    have source : Det.Head P s oldOuter [] (.frame n oldFrame oldBody)
        ⟨s, oldOuter, vals returned ++ [.ref (.func address), head.retToCallIn oldFrame.module]⟩ :=
      .returnCallRefFrameAddr (by simpa [vals, Val.toAdmin] using oldShape) isReturn
        originalFound (by rw [sameType]; exact expanded) count
    exact .inr ⟨_, tg_head source, by rw [modules],
      .inr (.inr (.inr ⟨returned, address, _, rfl, retToCallIn_cases isReturn _⟩))⟩
  | throwRefFrame =>
    rename_i address
    obtain ⟨oldRest, oldShape⟩ := FR.throwing_prefix_right related
    exact .inr ⟨throwing address, (by rw [oldShape]; exact bubble_frame_throw),
      rfl, .inr (.inr (.inl ⟨address, rfl⟩))⟩
  | trapFrame =>
    obtain ⟨oldRest, oldShape⟩ := FR.trap_prefix_right related
    exact .inr ⟨[.trap], (by rw [oldShape]; exact bubble_frame_trap),
      rfl, .inr (.inl rfl)⟩
  | parametric h => fam_dismiss
  | numeric h => fam_dismiss
  | vector h => fam_dismiss
  | «variable» h => fam_dismiss
  | table h => fam_dismiss
  | memory h => fam_dismiss
  | reference h => fam_dismiss
  | aggregate h => fam_dismiss
  | callRefNull hc => exact absurd hc (by simp [Admin.IsCallRef])
  | callRefFunc _ hc => exact absurd hc (by simp [Admin.IsCallRef])

/-- The equal-outer-frame specialization preserves the original generic API. -/
theorem reverse_generic_frame {n : Nat} {s t : Store H} {outer oldFrame newFrame : Frame}
    {oldBody newBody : List Admin} {args : List Val} {next : Config H}
    (stores : SR p s t) (related : FR p oldFrame newFrame oldBody newBody)
    (selected : Det.Head P t outer args (.frame n newFrame newBody) next) :
    (∃ bodyNext : Config H, args = [] ∧ FR p oldFrame newFrame oldBody newBody ∧
      Step P Det.noHost ⟨t, newFrame, newBody⟩ bodyNext ∧
      next = ⟨bodyNext.store, outer, [.frame n bodyNext.frame bodyNext.code]⟩) ∨
    ReverseMatch p P .gen ⟨s, outer, vals args ++ [.frame n oldFrame oldBody]⟩ next := by
  rcases reverse_frame_core (oldOuter := outer) stores related selected with
    contextual | ⟨code, steps, rfl, _⟩
  · exact .inl contextual
  · exact .inr (ReverseMatch.of_steps steps ⟨rfl, LN.refl p _⟩ stores)

end Silmaril.Wasm.Binaryen.InlR
