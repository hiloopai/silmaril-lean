module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.PureNumeric

/-!
# Numeric rules of wasm-2.0 `Step_pure` are V2's numeric constructors

Under `NumAgree` (the script's numeric functions agree with V2's numerics at a profile `P`) and
`NumTyped` (the encodings have their IL types), the rules `unop-val`, `binop-val`,
`binop-trap`, `testop` and `relop` of `Scripts.Wasm20.fixed`, at the image of the left-hand side
of each V2 constructor that transcribes them, fire with exactly the images of that
constructor's right-hand sides. Both hypotheses are assumed, not proved.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Pure

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (FiresB)

variable (B : Builtins) {P : Profile}

/-- **`Step_pure/unop-val` is `PureStep.intUnOp`.** -/
theorem intUnOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : IntType}
    {op : IntUnOp} {x : BitVec t.width} (hop : op.valid t) {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 20
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intUnOp t op)]), w]) ↔
      ∃ z, IntUnOpResult t op x z ∧ w = .list (adminsToV [.plain (.intConst t z)]) := by
  obtain ⟨vs, happ, hvs⟩ := A.intUnOp t op x hop
  constructor
  · intro hf
    obtain ⟨c, v, rfl, happ', hm⟩ := unopVal_inv B hf
    have hv : v = .list vs := Applies.unique happ' happ
    obtain ⟨z, hz, rfl⟩ := (hvs c).1 (memValue_list_iff.1 (hv ▸ hm))
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact unopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩) (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.intUnOp t op hop _ ⟨rfl, rfl, rfl⟩ rfl) (T.num (.int t) z "nt" _ ⟨rfl, rfl, rfl⟩ rfl) happ
      (memValue_list_iff.2 ((hvs _).2 ⟨z, hz, rfl⟩))

/-- **`Step_pure/unop-val` is `PureStep.floatUnOp`.** -/
theorem floatUnOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : FloatType}
    {op : FloatUnOp} {x : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 20
        (.tuple [.list (adminsToV [.plain (.floatConst t x), .plain (.floatUnOp t op)]), w]) ↔
      ∃ z, FloatUnOpResult P t op x z ∧ w = .list (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨vs, happ, hvs⟩ := A.floatUnOp t op x
  constructor
  · intro hf
    obtain ⟨c, v, rfl, happ', hm⟩ := unopVal_inv B hf
    have hv : v = .list vs := Applies.unique happ' happ
    obtain ⟨z, hz, rfl⟩ := (hvs c).1 (memValue_list_iff.1 (hv ▸ hm))
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact unopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.float t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.floatUnOp t op _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.num (.float t) z "nt" _ ⟨rfl, rfl, rfl⟩ rfl) happ
      (memValue_list_iff.2 ((hvs _).2 ⟨z, hz, rfl⟩))

/-- **`Step_pure/binop-val` is `PureStep.intBinOp`.** -/
theorem intBinOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : IntType}
    {op : IntBinOp} {x y : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 22
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
          .plain (.intBinOp t op)]), w]) ↔
      ∃ z, IntBinOpResult t op x y z ∧ w = .list (adminsToV [.plain (.intConst t z)]) := by
  obtain ⟨vs, happ, hvs⟩ := A.intBinOp t op x y
  constructor
  · intro hf
    obtain ⟨c, v, rfl, happ', hm⟩ := binopVal_inv B hf
    have hv : v = .list vs := Applies.unique happ' happ
    obtain ⟨z, hz, rfl⟩ := (hvs c).1 (memValue_list_iff.1 (hv ▸ hm))
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact binopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.num (.int t) y "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.intBinOp t op _ ⟨rfl, rfl, rfl⟩ rfl) (T.num (.int t) z "nt" _ ⟨rfl, rfl, rfl⟩ rfl) happ
      (memValue_list_iff.2 ((hvs _).2 ⟨z, hz, rfl⟩))

/-- **`Step_pure/binop-val` is `PureStep.floatBinOp`.** -/
theorem floatBinOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : FloatType} {op : FloatBinOp} {x y : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 22
        (.tuple [.list (adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
          .plain (.floatBinOp t op)]), w]) ↔
      ∃ z, FloatBinOpResult P t op x y z ∧ w = .list (adminsToV [.plain (.floatConst t z)]) := by
  obtain ⟨vs, happ, hvs⟩ := A.floatBinOp t op x y
  constructor
  · intro hf
    obtain ⟨c, v, rfl, happ', hm⟩ := binopVal_inv B hf
    have hv : v = .list vs := Applies.unique happ' happ
    obtain ⟨z, hz, rfl⟩ := (hvs c).1 (memValue_list_iff.1 (hv ▸ hm))
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact binopVal_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.float t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.num (.float t) y "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.floatBinOp t op _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.num (.float t) z "nt" _ ⟨rfl, rfl, rfl⟩ rfl) happ
      (memValue_list_iff.2 ((hvs _).2 ⟨z, hz, rfl⟩))

/-- V2's integer trap condition is the absence of a result. -/
theorem intBinOpTraps_iff {t : IntType} {op : IntBinOp} {x y : BitVec t.width} :
    IntBinOpTraps t op x y ↔ ∀ z, ¬ IntBinOpResult t op x y z := by
  unfold IntBinOpTraps IntBinOpResult
  cases Numerics.intBinOp t op x y <;> simp

/-- **`Step_pure/binop-trap` is `PureStep.intBinOpTrap`.** -/
theorem intBinOpTrap_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 23
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
          .plain (.intBinOp t op)]), w]) ↔
      IntBinOpTraps t op x y ∧ w = .list (adminsToV [.trap]) := by
  obtain ⟨vs, happ, hvs⟩ := A.intBinOp t op x y
  have hnil : vs = [] ↔ IntBinOpTraps t op x y := by
    rw [intBinOpTraps_iff, List.eq_nil_iff_forall_not_mem]
    exact ⟨fun h z hz => h _ ((hvs _).2 ⟨z, hz, rfl⟩), fun h c hc =>
      let ⟨z, hz, _⟩ := (hvs c).1 hc; h z hz⟩
  constructor
  · intro hf
    obtain ⟨rfl, happ'⟩ := binopTrap_inv B hf
    have hv : Value.list [] = .list vs := Applies.unique happ' happ
    exact ⟨hnil.1 (by simpa using hv.symm), rfl⟩
  · rintro ⟨htr, rfl⟩
    have happ' := hnil.2 htr ▸ happ
    exact binopTrap_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.num (.int t) y "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.intBinOp t op _ ⟨rfl, rfl, rfl⟩ rfl) happ'

/-- **`Step_pure/testop` is `PureStep.testOp`.** -/
theorem testOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : IntType}
    {op : IntTestOp} {x : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 24
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intTestOp t op)]), w]) ↔
      w = .list (adminsToV [constI32 (testOp t op x)]) := by
  constructor
  · intro hf
    obtain ⟨c, rfl, happ⟩ := testop_inv B hf
    have hc : c = pctV (testOp t op x).toNat := Applies.unique happ (A.intTestOp t op x)
    rw [hc]
    rfl
  · rintro rfl
    exact testop_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.intTestOp t op _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.i32 _ _ ⟨rfl, rfl, rfl⟩) (A.intTestOp t op x)

/-- **`Step_pure/relop` is `PureStep.intRelOp`.** -/
theorem intRelOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B)) {t : IntType}
    {op : IntRelOp} {x y : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 25
        (.tuple [.list (adminsToV [.plain (.intConst t x), .plain (.intConst t y),
          .plain (.intRelOp t op)]), w]) ↔
      w = .list (adminsToV [constI32 (intRelOp t op x y)]) := by
  constructor
  · intro hf
    obtain ⟨c, rfl, happ⟩ := relop_inv B hf
    have hc : c = pctV (intRelOp t op x y).toNat := Applies.unique happ (A.intRelOp t op x y)
    rw [hc]
    rfl
  · rintro rfl
    exact relop_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.int t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.num (.int t) y "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.intRelOp t op _ ⟨rfl, rfl, rfl⟩ rfl) (T.i32 _ _ ⟨rfl, rfl, rfl⟩) (A.intRelOp t op x y)

/-- **`Step_pure/relop` is `PureStep.floatRelOp`.** -/
theorem floatRelOp_iff (A : NumAgree (simEnv20 B) P) (T : NumTyped (simEnv20 B))
    {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} {w : Value} :
    FiresB (simEnv20 B) "Step_pure" 25
        (.tuple [.list (adminsToV [.plain (.floatConst t x), .plain (.floatConst t y),
          .plain (.floatRelOp t op)]), w]) ↔
      w = .list (adminsToV [constI32 (floatRelOp t op x y)]) := by
  constructor
  · intro hf
    obtain ⟨c, rfl, happ⟩ := relop_inv B hf
    have hc : c = pctV (floatRelOp t op x y).toNat := Applies.unique happ (A.floatRelOp t op x y)
    rw [hc]
    rfl
  · rintro rfl
    exact relop_fires B (T.numtype _ _ ⟨rfl, rfl, rfl⟩)
      (T.num (.float t) x "nt" _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.num (.float t) y "nt" _ ⟨rfl, rfl, rfl⟩ rfl) (T.floatRelOp t op _ ⟨rfl, rfl, rfl⟩ rfl)
      (T.i32 _ _ ⟨rfl, rfl, rfl⟩) (A.floatRelOp t op x y)

end Silmaril.Wasm.SpecTec.Sim20.Pure
