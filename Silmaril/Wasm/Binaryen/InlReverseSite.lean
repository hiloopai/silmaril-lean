module

public import Silmaril.Wasm.Binaryen.InlReverseControl
public import Silmaril.Wasm.Execution.Core.Soundness.PresControl

@[expose] public section

/-! # Reverse exits from the inlined call site

The outer label at the inlined site replaces both the callee's outer label and
its activation frame. On exit, the original therefore takes two administrative
steps. Original typing supplies result arity and excludes escaping branches;
without these invariants the deliberately broad `SiteR` is not reversible.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

theorem reverse_site_values_count {s : Store H} {C : Context} {results : List CValType}
    {values : List Val} (wellFormed : C.Wf)
    (typed : AdminsOk s C (vals values) (.plain [] results)) :
    values.length = results.length := by
  obtain ⟨types, valuesTyped, subtype⟩ := AdminsOk.vals_inv wellFormed.types typed
  have valuesLength := valuesTyped.length_eq
  have typesLength := subtype.length_eq
  simp only [List.length_append, List.length_nil, zero_add] at typesLength
  omega

/-- A typed callee body at its outer level cannot contain an escaping branch. -/
theorem reverse_site_no_branch {s : Store H} {C : Context} {results : List CValType}
    {body : List Admin} (wellFormed : C.Wf) (noLabels : C.labels = [])
    (typed : AdminsOk s C body (.plain [] results)) {values : List Val} {index : LabelIdx}
    {rest : List Admin} (shape : body = vals values ++ .plain (.br index) :: rest) : False := by
  rw [shape] at typed
  have typed' : AdminsOk s C (vals values ++ [.plain (.br index)] ++ rest)
      (.plain [] results) := by simpa using typed
  obtain ⟨_, _, _, _, _, _, _, branch, _⟩ := vals_admin_invCtl wellFormed typed'
  obtain ⟨_, _, lookup, _⟩ := AdminOk.br_invCtl branch
  rw [noLabels] at lookup
  simp at lookup

/-- Reverse a selected exit while the original callee still has its outer
label. The only deferred case is an actual target step inside the label, which
can be matched recursively in callee mode at depth zero. -/
theorem reverse_site_outer_label {n : Nat} {L : List (Option Val)}
    {s t : Store H} {caller callee : Frame} {C : Context} {results : List CValType}
    {args : List Val} {body body' : List Admin} {next : Config H}
    (callerModule : caller.module = p.mi) (callerLocals : caller.locals = L)
    (prefixLength : L.length = p.base) (calleeLocals : callee.locals.length = p.ext)
    (stores : SR p s t)
    (wellFormed : C.Wf) (noLabels : C.labels = []) (arity : results.length = n)
    (typed : AdminsOk s C [.label n [] body] (.plain [] results))
    (bodyRelated : LI p 0 body body')
    (selected : Det.Head P t ⟨L ++ callee.locals, p.mi⟩ args (.label n [] body') next) :
    (∃ bodyNext : Config H, args = [] ∧
      Step P Det.noHost ⟨t, ⟨L ++ callee.locals, p.mi⟩, body'⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.label n [] bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Relation.TransGen (Step P Det.noHost)
        ⟨s, caller, [.frame n callee [.label n [] body]]⟩ originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  have related : ∀ {code : List Admin}, Out code →
      MR p .g ⟨s, caller, code⟩ ⟨t, ⟨L ++ callee.locals, p.mi⟩, code⟩ := by
    intro code output
    exact ⟨callerModule, callerLocals ▸ prefixLength, callee.locals, calleeLocals,
      by rw [callerLocals], LG.of_out output⟩
  cases selected with
  | ctxtLabel step => exact .inl ⟨_, rfl, step, rfl⟩
  | labelVals shape =>
    rw [shape] at bodyRelated
    obtain rfl := LI.vals_reverse bodyRelated
    have count : _ = n := (reverse_site_values_count wellFormed
      (Step.labelVals_presCtl typed)).trans arity
    exact .inr ⟨_, (Relation.TransGen.single (Step.ctxtFrame Step.labelVals)).trans
      (.single (Step.frameVals count)), related (.vals _), stores⟩
  | brLabelZero shape zero count =>
    rename_i discarded returned index rest
    simp only [expression, List.map_nil, List.append_nil]
    have combined : vals discarded ++ vals returned ++ [Admin.plain (.br index)] ++ rest =
        vals (discarded ++ returned) ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨head, oldRest, oldShape, headRelated, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, rfl, _, relocated⟩ := AI.plain_reverse headRelated
    rcases xform_br_reverse relocated with rfl | ⟨rfl, rfl⟩
    · have sourceBranch : Step P Det.noHost ⟨s, callee, [.label n [] body]⟩
          ⟨s, callee, vals returned⟩ := by
        have step := Step.brLabelZero (P := P) (host := Det.noHost) (s := s) (f := callee)
          (vs' := discarded) (vs := returned) (rest := oldRest) (cont := []) zero count
        simpa only [oldShape, vals_append, expression, List.map_nil, List.append_nil,
          List.append_assoc, List.singleton_append] using step
      exact .inr ⟨_, (Relation.TransGen.single (Step.ctxtFrame sourceBranch)).trans
        (.single (Step.frameVals count)), related (.vals _), stores⟩
    · have sourceReturn : Step P Det.noHost ⟨s, callee, [.label n [] body]⟩
          ⟨s, callee, vals (discarded ++ returned) ++ [.plain .return_]⟩ := by
        simpa only [oldShape, List.append_assoc, List.singleton_append] using
          (Step.returnLabel (P := P) (host := Det.noHost) (s := s) (f := callee)
            (vs := discarded ++ returned) (rest := oldRest) (n := n) (cont := []))
      have leave : Step P Det.noHost
          ⟨s, caller, [.frame n callee (vals (discarded ++ returned) ++ [.plain .return_])]⟩
          ⟨s, caller, vals returned⟩ := by
        simpa only [vals_append, List.append_nil] using
          (Step.returnFrame (P := P) (host := Det.noHost) (s := s) (f := caller) (fi := callee)
            (vs' := discarded) (vs := returned) (rest := []) count)
      exact .inr ⟨_, (Relation.TransGen.single (Step.ctxtFrame sourceReturn)).trans
        (.single leave), related (.vals _), stores⟩
  | brLabelSucc shape positive =>
    rename_i returned index rest
    have combined : vals returned ++ [Admin.plain (.br index)] ++ rest =
        vals returned ++ .plain (.br index) :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨head, oldRest, oldShape, headRelated, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, rfl, _, relocated⟩ := AI.plain_reverse headRelated
    rcases xform_br_reverse relocated with rfl | ⟨rfl, rfl⟩
    · have sourceTyped := Step.brLabelSucc_presCtl (by simpa [oldShape] using typed)
        wellFormed positive
      exact (reverse_site_no_branch wellFormed noLabels sourceTyped rfl).elim
    · have zero := InlineTy.xLabel_toNat (d := 0) (by decide)
      omega
  | returnCallRefLabel shape isReturn =>
    rename_i values head rest
    have combined : vals values ++ [head] ++ rest = vals values ++ head :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    exact (related.not_returnCallRef isReturn).elim
  | returnLabel shape =>
    rename_i values rest
    have combined : vals values ++ [Admin.plain .return_] ++ rest =
        vals values ++ .plain .return_ :: rest := by simp
    rw [combined] at shape
    rw [shape] at bodyRelated
    obtain ⟨_, _, _, related, _⟩ := LI.vals_cons_reverse bodyRelated
    obtain ⟨old, _, _, relocated⟩ := AI.plain_reverse related
    exact (xform_ne_return old relocated).elim
  | throwRefLabel =>
    obtain rfl := LI.throwing_reverse bodyRelated
    exact .inr ⟨_, (Relation.TransGen.single (Step.ctxtFrame Step.throwRefLabel)).trans
      (.single Step.throwRefFrame),
      related (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])), stores⟩
  | trapLabel =>
    obtain rfl := LI.trap_reverse bodyRelated
    exact .inr ⟨_, (Relation.TransGen.single (Step.ctxtFrame Step.trapLabel)).trans
      (.single Step.trapFrame), related .trap, stores⟩
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

end Silmaril.Wasm.Binaryen.InlR
