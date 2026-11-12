module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Casts.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Thms

/-!
# Round 6: Core steps from cast redexes

`castStep_rec`: a recursion principle for the Core steps from a configuration whose code is a
cast redex (`castB`). Such a step is one of the eight top-level cast steps (`CastTop`), or one of
the four context rules around a step whose code is again a cast redex. Every other constructor of
`Step` (and of its eight families) has a left-hand side that is not a cast redex, which `simp`
checks constructor by constructor (as `Core.Step.not_all_isVal` does for values).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Casts

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## `castB` -/

/-- A value is not a cast. -/
@[simp] theorem castA_toAdmin (v : Val) : castA v.toAdmin = false := by
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> rfl

/-- A `CALL_REF` is not a cast. -/
theorem castA_of_isCallRef {a : Admin} (h : a.IsCallRef) : castA a = false := by
  rcases Bwd.isCallRef_cases h with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> rfl

/-- A `RETURN_CALL_REF` is not a cast. -/
theorem castA_of_isReturnCallRef {a : Admin} (h : a.IsReturnCallRef) : castA a = false := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · rfl
  · rfl
  · exact h.elim

/-- A value is skipped. -/
@[simp] theorem castB_toAdmin_cons (v : Val) (l : List Admin) :
    castB (v.toAdmin :: l) = castB l := by
  simp [castB]

/-- A prefix of values is skipped. -/
@[simp] theorem castB_vals_append : ∀ (vs : List Val) (l : List Admin),
    castB (vals vs ++ l) = castB l
  | [], _ => rfl
  | v :: vs, l => (castB_toAdmin_cons v (vals vs ++ l)).trans (castB_vals_append vs l)

/-- Values are not a cast redex. -/
@[simp] theorem castB_vals (vs : List Val) : castB (vals vs) = false := by
  have h := castB_vals_append vs []
  rwa [List.append_nil] at h

/-- A label is a cast redex when its body is. -/
@[simp] theorem castB_label (n : Nat) (cont : List Instr) (b l : List Admin) :
    castB (.label n cont b :: l) = castB b := by
  simp [castB, castA, Admin.val?]

/-- A handler is a cast redex when its body is. -/
@[simp] theorem castB_handler (n : Nat) (cs : List Catch) (b l : List Admin) :
    castB (.handler n cs b :: l) = castB b := by
  simp [castB, castA, Admin.val?]

/-- A frame is a cast redex when its body is. -/
@[simp] theorem castB_frame (n : Nat) (fi : Frame) (b l : List Admin) :
    castB (.frame n fi b :: l) = castB b := by
  simp [castB, castA, Admin.val?]

/-- **`castB` holds of every cast redex.** -/
theorem castB_of_castRedex {l : List Admin} (h : Target.CastRedex l) : castB l = true := by
  induction h with
  | skip _ ih => rw [castB_toAdmin_cons, ih]
  | cast hi => simp [castB, castA, hi]
  | label _ ih => rw [castB_label, ih]
  | handler _ ih => rw [castB_handler, ih]
  | frame _ ih => rw [castB_frame, ih]

/-- A cast redex `l ++ r` has its redex in `l` unless `l` is values. -/
theorem castB_append : ∀ {l r : List Admin}, castB (l ++ r) = true →
    (∃ vs, l = vals vs) ∨ castB l = true
  | [], _, _ => .inl ⟨[], rfl⟩
  | a :: l, r, h => by
    have h' : castA a = true ∨ (a.val?.isSome = true ∧ castB (l ++ r) = true) := by
      simpa only [List.cons_append, castB, Bool.or_eq_true, Bool.and_eq_true] using h
    rcases h' with ha | ⟨hv, hl⟩
    · exact .inr (by simp [castB, ha])
    · obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 hv
      obtain rfl := Admin.eq_of_val? hv'
      rcases castB_append hl with ⟨vs, rfl⟩ | hl'
      · exact .inl ⟨v :: vs, rfl⟩
      · exact .inr (by rw [castB_toAdmin_cons, hl'])

/-- **The hole of `ctxt-instrs` at a cast redex is a cast redex**, since values do not step. -/
theorem castB_mid {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hx : castB (vals vs ++ is ++ rest) = true) :
    castB is = true := by
  rw [List.append_assoc, castB_vals_append] at hx
  rcases castB_append hx with ⟨ws, rfl⟩ | h'
  · exact absurd h Step.not_vals
  · exact h'

/-! ## The families -/

/-- The unfolding `simp` uses to evaluate `castB` on a concrete left-hand side. -/
macro "cast_simp" : tactic => `(tactic| simp [castB, castA, Target.castInstr, Admin.val?,
  constI32, Val.i32, vconst, List.append_assoc])

theorem castB_parametric {is is' : List Admin} (h : ParametricStep is is') : castB is = false := by
  cases h <;> cast_simp

theorem castB_numeric {is is' : List Admin} (h : NumericStep P is is') : castB is = false := by
  cases h <;> cast_simp

theorem castB_vector {is is' : List Admin} (h : VectorStep P is is') : castB is = false := by
  cases h <;> cast_simp

theorem castB_variable {c c' : Config H} (h : VariableStep c c') : castB c.code = false := by
  cases h <;> cast_simp

theorem castB_table {c c' : Config H} (h : TableStep P c c') : castB c.code = false := by
  cases h <;> cast_simp

theorem castB_memory {c c' : Config H} (h : MemoryStep P c c') : castB c.code = false := by
  cases h <;> cast_simp

theorem castB_aggregate {c c' : Config H} (h : AggregateStep c c') : castB c.code = false := by
  cases h <;> cast_simp

/-- **The reference steps from a cast redex are the four cast steps.** -/
theorem castTop_of_ref {c c' : Config H} (h : RefStep c c') (hx : castB c.code = true) :
    CastTop c c' := by
  cases h
  case testTrue h => exact .testTrue h
  case testFalse h => exact .testFalse h
  case castSucceed h => exact .castSucceed h
  case castFail h => exact .castFail h
  all_goals (revert hx; cast_simp)

/-! ## The recursion -/

/-- **A recursion principle for the Core steps from a cast redex**: a motive that holds of the
eight top-level cast steps and is carried through the four context rules (each from a step whose
code is again a cast redex) holds of every Core step from a cast redex. -/
theorem castStep_rec {M : Config H → Config H → Prop}
    (top : ∀ {c c' : Config H}, CastTop c c' → M c c')
    (instrs : ∀ {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin},
      Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ → (vs ≠ [] ∨ rest ≠ []) → castB is = true →
      M ⟨s, f, is⟩ ⟨s', f', is'⟩ → M ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩)
    (label : ∀ {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin},
      Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ → castB is = true → M ⟨s, f, is⟩ ⟨s', f', is'⟩ →
      M ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩)
    (handler : ∀ {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch}
      {is is' : List Admin}, Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ → castB is = true →
      M ⟨s, f, is⟩ ⟨s', f', is'⟩ → M ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩)
    (frame : ∀ {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin},
      Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩ → castB is = true → M ⟨s, fi, is⟩ ⟨s', fi', is'⟩ →
      M ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩)
    {c c' : Config H} (h : Step P host c c') : castB c.code = true → M c c' := by
  induction h
  case reference h => exact fun hx => top (castTop_of_ref h hx)
  case ctxtInstrs h hne ih => exact fun hx => instrs h hne (castB_mid h hx) (ih (castB_mid h hx))
  case ctxtLabel h ih =>
    exact fun hx => have hb := (castB_label _ _ _ []).symm.trans hx; label h hb (ih hb)
  case ctxtHandler h ih =>
    exact fun hx => have hb := (castB_handler _ _ _ []).symm.trans hx; handler h hb (ih hb)
  case ctxtFrame h ih =>
    exact fun hx => have hb := (castB_frame _ _ _ []).symm.trans hx; frame h hb (ih hb)
  case brOnCastSucceed h => exact fun _ => top (.brOnCastSucceed h)
  case brOnCastFail h => exact fun _ => top (.brOnCastFail h)
  case brOnCastFailSucceed h => exact fun _ => top (.brOnCastFailSucceed h)
  case brOnCastFailFail h => exact fun _ => top (.brOnCastFailFail h)
  case parametric h => exact fun hx => absurd hx (by rw [castB_parametric h]; decide)
  case numeric h => exact fun hx => absurd hx (by rw [castB_numeric h]; decide)
  case vector h => exact fun hx => absurd hx (by rw [castB_vector h]; decide)
  case «variable» h => exact fun hx => absurd hx (by rw [castB_variable h]; decide)
  case table h => exact fun hx => absurd hx (by rw [castB_table h]; decide)
  case memory h => exact fun hx => absurd hx (by rw [castB_memory h]; decide)
  case aggregate h => exact fun hx => absurd hx (by rw [castB_aggregate h]; decide)
  all_goals first
    | (cast_simp; done)
    | simp [castB, castA, Admin.val?_of_isCallRef (by assumption),
        castA_of_isCallRef (by assumption)]
    | simp [castB, castA, Admin.val?_of_isReturnCallRef (by assumption),
        castA_of_isReturnCallRef (by assumption)]

end Silmaril.Wasm.SpecTec.Sim.Round6.Casts
