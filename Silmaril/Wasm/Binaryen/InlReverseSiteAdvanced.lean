module

public import Silmaril.Wasm.Binaryen.InlReverseSite
public import Silmaril.Wasm.Execution.Core.Sim.Closure.Label

@[expose] public section

/-! # Reverse matching at every typed inlining-site checkpoint

After the original callee has left its outer label, the target can still be at
that label. Its selected exit must match the original activation's pending
value/return/trap/exception exit. The exact chosen target result is retained;
no numerical determinism assumption is used.
-/

namespace Silmaril.Wasm.Binaryen.InlR

open Execution.Core Execution.Core.Sim Validation SingleThreaded InlS

variable {H : Type} {p : Prm} {P : Numerics.Profile}

/-- An administrative label head consumes no surrounding stack operands. -/
theorem reverse_site_label_args {s : Store H} {f : Frame} {args : List Val} {n : Nat}
    {cont : List Instr} {body : List Admin} {next : Config H}
    (selected : Det.Head P s f args (.label n cont body) next) : args = [] := by
  cases selected with
  | ctxtLabel | labelVals | brLabelZero | brLabelSucc | returnCallRefLabel | returnLabel
      | throwRefLabel | trapLabel => rfl
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

/-- A label around finished values has exactly that administrative result,
even at an arbitrary numerical profile. -/
theorem reverse_site_labelRed_values {s t : Store H} {f g : Frame} {n : Nat}
    {cont : List Instr} {values : List Val} {code : List Admin}
    (selected : Closure.LabelRed P Det.noHost s f n cont (vals values) t g code) :
    t = s ∧ g = f ∧ code = vals values := by
  generalize shape : vals values = body at selected
  cases selected with
  | ctxt step => exact (Det.not_step_vals (shape ▸ step)).elim
  | values chosen =>
    obtain rfl := Det.vals_inj.mp shape
    exact ⟨rfl, rfl, rfl⟩
  | brZero | brSucc | return_ =>
    have allValues := congrArg (fun body : List Admin => body.all Admin.isVal) shape
    simp [List.all_append, Admin.isVal, Admin.val?] at allValues
  | returnCallRef isReturn =>
    have allValues := congrArg (fun body : List Admin => body.all Admin.isVal) shape
    simp [List.all_append, Admin.isVal, Admin.val?_of_isReturnCallRef isReturn] at allValues
  | throwRef address =>
    have member : Admin.plain .throwRef ∈ vals values := by rw [shape]; simp
    exact (Det.mem_vals member rfl).elim
  | trap =>
    have allValues := congrArg (fun body : List Admin => body.all Admin.isVal) shape
    simp [Admin.isVal, Admin.val?] at allValues

/-- A branch to the outer label selects a suffix of exactly its result arity.
Discarded values and unreachable suffix instructions are read from the actual
selected reduction, rather than chosen using a deterministic interpreter. -/
theorem reverse_site_labelRed_brZero {s t : Store H} {f g : Frame} {n : Nat}
    {values : List Val} {index : LabelIdx} {rest code : List Admin}
    (zero : index.toNat = 0)
    (selected : Closure.LabelRed P Det.noHost s f n []
      (vals values ++ .plain (.br index) :: rest) t g code) :
    ∃ discarded returned, values = discarded ++ returned ∧ returned.length = n ∧
      t = s ∧ g = f ∧ code = vals returned := by
  generalize shape : vals values ++ Admin.plain (.br index) :: rest = body at selected
  cases selected with
  | ctxt step =>
    rw [← shape] at step
    exact (Det.not_step_blocked step (W := values) (e := .plain (.br index)) (rest := rest)
      (by simp) (.inl ⟨index, rfl⟩)).elim
  | values chosen => exact (vals_ne_vals_cons rfl shape.symm).elim
  | @brZero discarded returned chosenIndex chosenRest _ count =>
    have combined : vals values ++ Admin.plain (.br index) :: rest =
        vals (discarded ++ returned) ++ .plain (.br chosenIndex) :: chosenRest := by
      simpa using shape
    obtain ⟨stack, _, _⟩ := Det.vals_append_cons_inj combined rfl rfl
    exact ⟨discarded, returned, stack, count, rfl, rfl, by simp [expression]⟩
  | brSucc positive =>
    have combined := shape
    simp only [List.append_assoc, List.singleton_append] at combined
    obtain ⟨_, sameHead, _⟩ := Det.vals_append_cons_inj combined rfl rfl
    cases sameHead
    omega
  | returnCallRef isReturn =>
    have combined := shape
    simp only [List.append_assoc, List.singleton_append] at combined
    obtain ⟨_, sameHead, _⟩ := Det.vals_append_cons_inj combined rfl
      (Det.IsReturnCallRef.val_none isReturn)
    rw [← sameHead] at isReturn
    exact isReturn.elim
  | return_ =>
    have combined := shape
    simp only [List.append_assoc, List.singleton_append] at combined
    obtain ⟨_, sameHead, _⟩ := Det.vals_append_cons_inj combined rfl rfl
    cases sameHead
  | throwRef | trap =>
    have first := congrArg Det.fnv shape
    simp at first

/-- Trap and uncaught-exception kernels leave a label unchanged. -/
theorem reverse_site_labelRed_kernel {s t : Store H} {f g : Frame} {n : Nat}
    {cont : List Instr} {kernel code : List Admin} (isKernel : Det.IsBubble kernel)
    (selected : Closure.LabelRed P Det.noHost s f n cont kernel t g code) :
    t = s ∧ g = f ∧ code = kernel := by
  rcases isKernel with rfl | ⟨address, rfl⟩
  · generalize shape : [Admin.trap] = body at selected
    cases selected with
    | ctxt step => exact (Det.not_step_trap (shape ▸ step)).elim
    | returnCallRef isReturn =>
      have first := congrArg Det.fnv shape
      simp [Det.fnv_cons_of_none (Det.IsReturnCallRef.val_none isReturn)] at first
      obtain ⟨_, head, _⟩ := first
      rw [← head] at isReturn
      exact isReturn.elim
    | trap => exact ⟨rfl, rfl, rfl⟩
    | _ =>
      have first := congrArg Det.fnv shape
      simp at first
  · change Closure.LabelRed P Det.noHost s f n cont
      [Admin.ref (.exn address), .plain .throwRef] t g code at selected
    generalize shape : ([Admin.ref (.exn address), .plain .throwRef] : List Admin) = body at selected
    cases selected with
    | ctxt step => exact (Det.not_step_throwing (shape ▸ step)).elim
    | returnCallRef isReturn =>
      have first := congrArg Det.fnv shape
      simp [Det.fnv_cons_of_none (Det.IsReturnCallRef.val_none isReturn)] at first
      obtain ⟨_, head, _⟩ := first
      rw [← head] at isReturn
      exact isReturn.elim
    | throwRef _ => exact ⟨rfl, rfl, rfl⟩
    | _ =>
      have first := congrArg Det.fnv shape
      simp at first

/-- Selected reverse matching for every typed site checkpoint. The recursive
case carries both the actual target body step and its depth-zero `LI` witness.
Every completed exit returns directly to caller mode at the selected target
successor, so these exits need no further target normalization prefix. -/
theorem reverse_site_selected_head {n : Nat} {L : List (Option Val)}
    {s t : Store H} {caller callee : Frame} {C : Context} {results : List CValType}
    {args : List Val} {original target : List Admin} {next : Config H}
    (callerModule : caller.module = p.mi) (callerLocals : caller.locals = L)
    (prefixLength : L.length = p.base) (calleeLocals : callee.locals.length = p.ext)
    (stores : SR p s t) (wellFormed : C.Wf) (noLabels : C.labels = [])
    (arity : results.length = n) (typed : AdminsOk s C original (.plain [] results))
    (site : SiteR p n original target)
    (selected : Det.Head P t ⟨L ++ callee.locals, p.mi⟩ args (.label n [] target) next) :
    (∃ originalBody bodyNext, original = [.label n [] originalBody] ∧
      LI p 0 originalBody target ∧ args = [] ∧
      Step P Det.noHost ⟨t, ⟨L ++ callee.locals, p.mi⟩, target⟩ bodyNext ∧
      next = ⟨bodyNext.store, bodyNext.frame, [.label n [] bodyNext.code]⟩) ∨
    ∃ originalNext : Config H,
      Relation.TransGen (Step P Det.noHost)
        ⟨s, caller, [.frame n callee original]⟩ originalNext ∧
      MR p .g originalNext next ∧ SR p originalNext.store next.store := by
  obtain rfl := reverse_site_label_args selected
  have related : ∀ {code : List Admin}, Out code →
      MR p .g ⟨s, caller, code⟩ ⟨t, ⟨L ++ callee.locals, p.mi⟩, code⟩ := by
    intro code output
    exact ⟨callerModule, callerLocals ▸ prefixLength, callee.locals, calleeLocals,
      by rw [callerLocals], LG.of_out output⟩
  cases next with
  | mk nextStore nextFrame nextCode =>
    obtain ⟨code, reduction, output⟩ := Closure.Step.label_inv (us := []) selected.toStep
    simp only [Execution.Core.vals_nil', List.nil_append] at output
    subst nextCode
    cases site with
    | a bodyRelated =>
      rcases reverse_site_outer_label callerModule callerLocals prefixLength calleeLocals
          stores wellFormed noLabels arity typed bodyRelated selected with inner | matched
      · obtain ⟨bodyNext, _, step, successor⟩ := inner
        exact .inl ⟨_, bodyNext, rfl, bodyRelated, rfl, step, successor⟩
      · exact .inr matched
    | b values =>
      obtain ⟨rfl, rfl, rfl⟩ := reverse_site_labelRed_values reduction
      have count := (reverse_site_values_count wellFormed typed).trans arity
      exact .inr ⟨_, .single (Step.frameVals count), related (.vals values), stores⟩
    | @c _ values rest =>
      have zero := InlineTy.xLabel_toNat (d := 0) (by decide)
      obtain ⟨discarded, returned, stack, count, rfl, rfl, rfl⟩ :=
        reverse_site_labelRed_brZero zero (by simpa using reduction)
      have leave : Step P Det.noHost
          ⟨s, caller, [.frame n callee (vals values ++ [.plain .return_])]⟩
          ⟨s, caller, vals returned⟩ := by
        simpa only [stack, vals_append, List.append_nil] using
          (Step.returnFrame (P := P) (host := Det.noHost) (s := s) (f := caller) (fi := callee)
            (vs' := discarded) (vs := returned) (rest := []) count)
      exact .inr ⟨_, .single leave, related (.vals _), stores⟩
    | d =>
      obtain ⟨rfl, rfl, rfl⟩ := reverse_site_labelRed_kernel (.inl rfl) reduction
      exact .inr ⟨_, .single Step.trapFrame, related .trap, stores⟩
    | e address =>
      obtain ⟨rfl, rfl, rfl⟩ := reverse_site_labelRed_kernel (.inr ⟨address, rfl⟩) reduction
      exact .inr ⟨_, .single Step.throwRefFrame,
        related (.ok (by simp [okI, structuredInstr, IsLocalI, IsTailI])), stores⟩
    | @f _ returned discarded index rest count zero =>
      obtain ⟨discarded', returned', stack, count', rfl, rfl, rfl⟩ :=
        reverse_site_labelRed_brZero (values := discarded ++ returned) zero
          (by simpa only [vals_append, List.append_assoc, List.singleton_append] using reduction)
      obtain ⟨_, rfl⟩ := List.append_inj' stack (count.trans count'.symm)
      exact .inr ⟨_, .single (Step.frameVals count'), related (.vals _), stores⟩
    | g =>
      rename_i values index rest
      exact (reverse_site_no_branch (values := values) (index := index) (rest := rest)
        wellFormed noLabels typed (by simp)).elim

end Silmaril.Wasm.Binaryen.InlR
