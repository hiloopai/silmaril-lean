module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Refute.Defs

/-!
# Round 6: Core's steps from `ref.r; ref.test rt`

Core's `Step` inverted at the code `[ref r, ref.test rt]`, in any store, frame, profile and host:
it steps only by `ref.test-true` to `i32.const 1` (when `RefOk`) or by `ref.test-false` to
`i32.const 0` (when not) (`step_refTest_inv`). The proof is a case split over `Step` and its
eight family relations; `ctxt-instrs` reduces to the empty code, to a value, or to the single
`ref.test` (`not_step_refTest1`), none of which steps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Refute

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The empty code does not step. -/
theorem not_step_nil {s : Store H} {f : Frame} {c' : Config H} :
    ¬ Step P host ⟨s, f, []⟩ c' := fun h => by
  have := h.not_all_isVal
  simp at this

set_option linter.unusedSimpArgs false in
/-- `ref.test rt` alone (without an operand) does not step. -/
theorem not_step_refTest1 {c c' : Config H} {rt : RefType} (h : Step P host c c')
    (hc : c.code = [.plain (.refTest rt)]) : False := by
  cases h with
  | parametric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | numeric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | vector h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | «variable» h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | table h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | memory h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | reference h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | aggregate h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | ctxtInstrs h hne =>
    simp [vals, List.append_eq_cons_iff] at hc
    rcases hc with ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, rfl⟩⟩ | ⟨⟨a, -, ha⟩, -, -⟩
    · exact not_step_nil h
    · simp at hne
    · rcases a with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at ha
  | _ => simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff, Admin.IsCallRef,
      Admin.IsReturnCallRef]

/-- A non-trivial split of `[ref r, ref.test rt]` has a redex that does not step. -/
theorem not_step_split {s : Store H} {f : Frame} {vs : List Val} {is rest : List Admin}
    {c'' : Config H} {r : Ref} {rt : RefType} (h : Step P host ⟨s, f, is⟩ c'')
    (hc : vals vs ++ is ++ rest = [.ref r, .plain (.refTest rt)]) (hne : vs ≠ [] ∨ rest ≠ []) :
    False :=
  have hl : vs.length + (is.length + rest.length) = 2 := by simpa using congrArg List.length hc
  match is, h, hc, hl with
  | [], h, _, _ => not_step_nil h
  | [a], h, hc, _ =>
    have ha : a ∈ [.ref r, .plain (.refTest rt)] := hc ▸ by simp
    (List.mem_pair.1 ha).elim (fun e => Step.not_vals (vs := [.ref r]) (e ▸ h))
      (fun e => not_step_refTest1 h (congrArg (fun x => [x]) e))
  | [_, _], _, _, hl =>
    have h₁ : vs = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    have h₂ : rest = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    hne.elim (· h₁) (· h₂)
  | _ :: _ :: _ :: _, _, _, hl => by simp at hl; omega

set_option linter.unusedSimpArgs false in
/-- **Core's steps from `ref r; ref.test rt`**: `i32.const 1` if `RefOk`, `i32.const 0` if not. -/
theorem step_refTest_inv {c c' : Config H} {r : Ref} {rt : RefType} (h : Step P host c c')
    (hc : c.code = [.ref r, .plain (.refTest rt)]) :
    (c' = ⟨c.store, c.frame, [constI32 1]⟩ ∧ RefOk c.store r (c.frame.module.instRef rt)) ∨
      (c' = ⟨c.store, c.frame, [constI32 0]⟩ ∧ ¬ RefOk c.store r (c.frame.module.instRef rt)) := by
  cases h with
  | parametric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | numeric h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | vector h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | «variable» h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | table h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | memory h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | reference h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | aggregate h => cases h <;> simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff]
  | ctxtInstrs h hne => exact (not_step_split h hc hne).elim
  | _ => simp_all [List.append_eq_cons_iff, List.cons_eq_append_iff, Admin.IsCallRef,
      Admin.IsReturnCallRef]

end Silmaril.Wasm.SpecTec.Sim.Round6.Refute
