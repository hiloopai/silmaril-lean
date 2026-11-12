module

public import Silmaril.Wasm.SpecTec.Sim.Round6.Target.Defs

/-!
# Round 6: cast redexes

`CastRedex` is closed under the context rules in the direction both recursions need: the redex of
a context's hole is the redex of the whole configuration (`castRedex_mid`, `castRedex_label`,
`castRedex_handler`, `castRedex_frame`), and a cast redex `[ref r, cast]` is one
(`castRedex_pair`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.Target

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

/-- A cast redex stays one when code is appended. -/
theorem castRedex_append {a : List Admin} (h : CastRedex a) (b : List Admin) :
    CastRedex (a ++ b) := by
  induction h with
  | skip _ ih => exact .skip ih
  | cast hi => exact .cast hi
  | label hb => exact .label hb
  | handler hb => exact .handler hb
  | frame hb => exact .frame hb

/-- A cast redex stays one under a prefix of values. -/
theorem castRedex_vals {b : List Admin} (h : CastRedex b) : ∀ vs : List Val,
    CastRedex (vals vs ++ b)
  | [] => h
  | _ :: vs => .skip (castRedex_vals h vs)

/-- **The redex of a `ctxt-instrs` hole is the redex of the whole code.** -/
theorem castRedex_mid {b : List Admin} (h : CastRedex b) (vs : List Val) (c : List Admin) :
    CastRedex (vals vs ++ b ++ c) := by
  rw [List.append_assoc]
  exact castRedex_vals (castRedex_append h c) vs

/-- `castRedex_mid`, contrapositive. -/
theorem not_castRedex_mid {vs : List Val} {b c : List Admin}
    (h : ¬ CastRedex (vals vs ++ b ++ c)) : ¬ CastRedex b :=
  fun hb => h (castRedex_mid hb vs c)

/-- The body of a label. -/
theorem not_castRedex_label {n : Nat} {cont : List Instr} {b : List Admin}
    (h : ¬ CastRedex [.label n cont b]) : ¬ CastRedex b :=
  fun hb => h (.label hb)

/-- The body of a handler. -/
theorem not_castRedex_handler {n : Nat} {cs : List Catch} {b : List Admin}
    (h : ¬ CastRedex [.handler n cs b]) : ¬ CastRedex b :=
  fun hb => h (.handler hb)

/-- The body of a frame. -/
theorem not_castRedex_frame {n : Nat} {fi : Frame} {b : List Admin}
    (h : ¬ CastRedex [.frame n fi b]) : ¬ CastRedex b :=
  fun hb => h (.frame hb)

/-- **`[ref r, cast]` is a cast redex.** -/
theorem castRedex_pair {r : Ref} {i : Instr} (hi : castInstr i = true) :
    CastRedex [.ref r, .plain i] :=
  .skip (v := .ref r) (.cast hi)

/-- `ref.test`. -/
theorem castRedex_refTest {r : Ref} {rt : RefType} : CastRedex [.ref r, .plain (.refTest rt)] :=
  castRedex_pair rfl

/-- `ref.cast`. -/
theorem castRedex_refCast {r : Ref} {rt : RefType} : CastRedex [.ref r, .plain (.refCast rt)] :=
  castRedex_pair rfl

/-- `br_on_cast`. -/
theorem castRedex_brOnCast {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} :
    CastRedex [.ref r, .plain (.brOnCast l rt₁ rt₂)] :=
  castRedex_pair rfl

/-- `br_on_cast_fail`. -/
theorem castRedex_brOnCastFail {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType} :
    CastRedex [.ref r, .plain (.brOnCastFail l rt₁ rt₂)] :=
  castRedex_pair rfl

end Silmaril.Wasm.SpecTec.Sim.Round6.Target
