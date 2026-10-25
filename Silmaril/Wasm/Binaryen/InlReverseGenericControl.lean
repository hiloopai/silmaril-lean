module

public import Silmaril.Wasm.Binaryen.InlReverseContexts

@[expose] public section

/-! # Selected reverse exits from generic labels and handlers

Terminal control rules discard the related suffix and retain the same values,
continuation or exception. The contextual case exposes the actual inner step
for recursive normalization. No uniqueness of numerical results is used.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation Numerics SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Profile}

theorem reverse_generic_label {n : Nat} {cont : List Instr} {body body' : List Admin}
    {s t : Store H} {frame : Frame} {args : List Val} {next : Config H}
    (related : LN p body body') (stores : SR p s t)
    (selected : Det.Head P t frame args (.label n cont body') next) :
    (∃ bodyNext : Config H, args = [] ∧ Step P Det.noHost ⟨t, frame, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.label n cont bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Det.Head P s frame args (.label n cont body) originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  have flatPrefix : ∀ {vs head rest},
      (∀ n cont body, head ≠ Admin.label n cont body) →
      (∀ n catches body, head ≠ .handler n catches body) →
      (∀ n frame body, head ≠ .frame n frame body) →
      body' = vals vs ++ head :: rest → ∃ oldRest, body = vals vs ++ head :: oldRest := by
    intro vs head rest nonlabel nonhandler nonframe shape
    rw [shape] at related
    obtain ⟨oldRest, original, _⟩ := LN.flat_inv_right nonlabel nonhandler nonframe related
    exact ⟨oldRest, original⟩
  cases selected with
  | ctxtLabel step => exact .inl ⟨_, rfl, step, rfl⟩
  | labelVals shape =>
    rw [shape] at related
    exact .inr ⟨_, .labelVals (LN.vals_inv_right related), ⟨rfl, LN.refl p _⟩, stores⟩
  | brLabelZero shape zero count =>
    rename_i discarded results index rest
    have combined : vals discarded ++ vals results ++ [Admin.plain (.br index)] ++ rest =
        vals (discarded ++ results) ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    obtain ⟨oldRest, original⟩ := flatPrefix (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) shape
    exact .inr ⟨_, .brLabelZero (by simpa using original) zero count,
      ⟨rfl, LN.refl p _⟩, stores⟩
  | brLabelSucc shape positive =>
    rename_i values index rest
    obtain ⟨oldRest, original⟩ := flatPrefix (head := .plain (.br index)) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using shape)
    exact .inr ⟨_, .brLabelSucc (by simpa using original) positive,
      ⟨rfl, LN.refl p _⟩, stores⟩
  | returnCallRefLabel shape tail =>
    rename_i values head rest
    obtain ⟨oldRest, original⟩ := flatPrefix (head := head) (fun _ _ _ h => by subst h; exact tail)
      (fun _ _ _ h => by subst h; exact tail) (fun _ _ _ h => by subst h; exact tail)
      (by simpa using shape)
    exact .inr ⟨_, .returnCallRefLabel (by simpa using original) tail,
      ⟨rfl, LN.refl p _⟩, stores⟩
  | returnLabel shape =>
    obtain ⟨oldRest, original⟩ := flatPrefix (head := .plain .return_) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using shape)
    exact .inr ⟨_, .returnLabel (by simpa using original), ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefLabel =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefLabel, ⟨rfl, LN.refl p _⟩, stores⟩
  | trapLabel =>
    rw [LN.trap_inv_right related]
    exact .inr ⟨_, .trapLabel, ⟨rfl, LN.refl p _⟩, stores⟩
  | callRefNull call => exact absurd call (by simp [Admin.IsCallRef])
  | callRefFunc _ call => exact absurd call (by simp [Admin.IsCallRef])
  | parametric step => fam_dismiss
  | numeric step => fam_dismiss
  | vector step => fam_dismiss
  | «variable» step => fam_dismiss
  | table step => fam_dismiss
  | memory step => fam_dismiss
  | reference step => fam_dismiss
  | aggregate step => fam_dismiss

theorem reverse_generic_handler {n : Nat} {catches : List Catch} {body body' : List Admin}
    {s t : Store H} {frame : Frame} {args : List Val} {next : Config H}
    (related : LN p body body') (stores : SR p s t)
    (selected : Det.Head P t frame args (.handler n catches body') next) :
    (∃ bodyNext : Config H, args = [] ∧ Step P Det.noHost ⟨t, frame, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.handler n catches bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Det.Head P s frame args (.handler n catches body) originalNext ∧
      MR p .gen originalNext next ∧ SR p originalNext.store next.store := by
  have flatPrefix : ∀ {vs head rest},
      (∀ n cont body, head ≠ Admin.label n cont body) →
      (∀ n catches body, head ≠ .handler n catches body) →
      (∀ n frame body, head ≠ .frame n frame body) →
      body' = vals vs ++ head :: rest → ∃ oldRest, body = vals vs ++ head :: oldRest := by
    intro vs head rest nonlabel nonhandler nonframe shape
    rw [shape] at related
    obtain ⟨oldRest, original, _⟩ := LN.flat_inv_right nonlabel nonhandler nonframe related
    exact ⟨oldRest, original⟩
  obtain ⟨originalCaller, originalCallee, rfl⟩ := stores
  have stores : SR p s (withFuncs s (newFuncs p s.funcs)) :=
    ⟨originalCaller, originalCallee, rfl⟩
  cases selected with
  | ctxtHandler step => exact .inl ⟨_, rfl, step, rfl⟩
  | brHandler shape =>
    rename_i values index rest
    obtain ⟨oldRest, original⟩ := flatPrefix (head := .plain (.br index)) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using shape)
    exact .inr ⟨_, .brHandler (by simpa using original), ⟨rfl, LN.refl p _⟩, stores⟩
  | returnCallRefHandler shape tail =>
    rename_i values head rest
    obtain ⟨oldRest, original⟩ := flatPrefix (head := head) (fun _ _ _ h => by subst h; exact tail)
      (fun _ _ _ h => by subst h; exact tail) (fun _ _ _ h => by subst h; exact tail)
      (by simpa using shape)
    exact .inr ⟨_, .returnCallRefHandler (by simpa using original) tail,
      ⟨rfl, LN.refl p _⟩, stores⟩
  | returnHandler shape =>
    obtain ⟨oldRest, original⟩ := flatPrefix (head := .plain .return_) (fun _ _ _ h => by cases h)
      (fun _ _ _ h => by cases h) (fun _ _ _ h => by cases h) (by simpa using shape)
    exact .inr ⟨_, .returnHandler (by simpa using original), ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerEmpty =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerEmpty, ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerCatch found tag =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerCatch found tag, ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerCatchRef found tag =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerCatchRef found tag, ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerCatchAll =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerCatchAll, ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerCatchAllRef =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerCatchAllRef, ⟨rfl, LN.refl p _⟩, stores⟩
  | throwRefHandlerNext mismatch =>
    rw [LN.throwing_inv_right related]
    exact .inr ⟨_, .throwRefHandlerNext mismatch, ⟨rfl, LN.refl p _⟩, stores⟩
  | handlerVals shape =>
    rw [shape] at related
    exact .inr ⟨_, .handlerVals (LN.vals_inv_right related), ⟨rfl, LN.refl p _⟩, stores⟩
  | trapHandler =>
    rw [LN.trap_inv_right related]
    exact .inr ⟨_, .trapHandler, ⟨rfl, LN.refl p _⟩, stores⟩
  | callRefNull call => exact absurd call (by simp [Admin.IsCallRef])
  | callRefFunc _ call => exact absurd call (by simp [Admin.IsCallRef])
  | parametric step => fam_dismiss
  | numeric step => fam_dismiss
  | vector step => fam_dismiss
  | «variable» step => fam_dismiss
  | table step => fam_dismiss
  | memory step => fam_dismiss
  | reference step => fam_dismiss
  | aggregate step => fam_dismiss

end Silmaril.Wasm.Binaryen.InlR
