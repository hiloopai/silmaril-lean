module

public import tests.wasm.auto.FrontBench.Defs
public import Silmaril.Wasm.Auto.Front.Thms

/-!
# The front-end benchmark: proved cases

The cases the proving stage settles (first case set), as theorems at **every** profile and for both
front-end relations: `max-select`, `add-swap` and `div10-mulhi` by the tactic `wasm_prove_base`
(function summaries, normal forms, the lemma library), and the reference functions of the
straight-line programs (`max-ref`, `add-ref`, `div10-mulhi-ref`) through
`Silmaril.Wasm.Auto.Bridge.modMeets_of_fnSum` and a short bitvector argument on the summary.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.FrontBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Numerics (Profile bool32)

/-! ## Equivalences -/

/-- `max` by `select` is equivalent to `Max`'s program (by `if`), at every profile. -/
theorem maxSelect_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P maxSelect maxProg 0 := by
  wasm_prove_base

/-- `y + x` is equivalent to `Adder`'s `x + y`, at every profile. -/
theorem addSwap_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P addSwap addProg 0 := by
  wasm_prove_base

/-- The `div10` kernel (multiply-high) is equivalent to `i64.div_u x 10`, at every
profile (one residual goal, discharged by the lemma library). -/
theorem div10Mulhi_equiv (R : Rel) (P : Profile) :
    ModEquiv R.toProp P div10Mulhi div10Ref 0 := by
  wasm_prove_base

/-! ## Typed arguments -/

theorem typedVals_i32_i32 {vs : List Val} (h : TypedVals [.i32, .i32] vs) :
    ∃ x y : BitVec 32, vs = [Val.i32 x, Val.i32 y] := by
  obtain ⟨hl, hi⟩ := h
  match vs, hl with
  | [a, b], _ =>
    obtain ⟨x, hx⟩ := hi 0 (by decide)
    obtain ⟨y, hy⟩ := hi 1 (by decide)
    have ha : a = Val.i32 x := by simpa [Val.i32] using hx
    have hb : b = Val.i32 y := by simpa [Val.i32] using hy
    exact ⟨x, y, by rw [ha, hb]⟩

theorem typedVals_i64 {vs : List Val} (h : TypedVals [.i64] vs) :
    ∃ x : BitVec 64, vs = [Val.i64 x] := by
  obtain ⟨hl, hi⟩ := h
  match vs, hl with
  | [a], _ =>
    obtain ⟨x, hx⟩ := hi 0 (by decide)
    have ha : a = Val.i64 x := by simpa [Val.i64] using hx
    exact ⟨x, by rw [ha]⟩

/-! ## Reference functions -/

/-- The summary of `Adder`'s program. -/
def addSum : FnSum :=
  ⟨[.i32, .i32], [.i32], ⟨[(.i32, .var 0), (.i32, .var 1)], [(.i32, .bin .add (.var 0) (.var 1))]⟩⟩

theorem addSum_eq : fnSum? addProg 0 = some addSum := by decide +kernel

/-- `Adder`'s program meets `x + y`, at every profile. -/
theorem add_meets (R : Rel) (P : Profile) : ModMeets R.toProp P addProg 0 addRef := by
  refine modMeets_of_fnSum (rel_refl R) addSum_eq fun vs htv => Or.inl ?_
  obtain ⟨x, y, rfl⟩ := typedVals_i32_i32 htv
  have h₁ : addRef [Val.i32 x, Val.i32 y] = some (.values [Val.i32 (x + y)]) := rfl
  have h₂ : fnOut addSum [Val.i32 x, Val.i32 y] = [Val.i32 (x + y)] := rfl
  rw [h₁, h₂]

/-- The summary of `Max`'s program: `y + (x - y) * [x >s y]`. -/
def maxSum : FnSum :=
  ⟨[.i32, .i32], [.i32], ⟨[(.i32, .var 0), (.i32, .var 1)],
    [(.i32, selT (.var 0) (.var 1) (.rel .i32 (.gt .signed) (.var 0) (.var 1)))]⟩⟩

theorem maxSum_eq : fnSum? maxProg 0 = some maxSum := by decide +kernel

theorem maxSum_out (x y : BitVec 32) :
    fnOut maxSum [Val.i32 x, Val.i32 y] =
      [if bool32 (decide (x.toInt > y.toInt)) ≠ 0 then Val.i32 x else Val.i32 y] := by
  have h₁ : fnOut maxSum [Val.i32 x, Val.i32 y] = [den (envOfVals [Val.i32 x, Val.i32 y])
      (.i32, selT (.var 0) (.var 1) (.rel .i32 (.gt .signed) (.var 0) (.var 1)))] := rfl
  rw [h₁, den_selT]
  rfl

/-- `Max`'s program meets the signed maximum, at every profile. -/
theorem max_meets (R : Rel) (P : Profile) : ModMeets R.toProp P maxProg 0 maxRef := by
  refine modMeets_of_fnSum (rel_refl R) maxSum_eq fun vs htv => Or.inl ?_
  obtain ⟨x, y, rfl⟩ := typedVals_i32_i32 htv
  have h₁ : maxRef [Val.i32 x, Val.i32 y] =
      some (.values [Val.i32 (Silmaril.WasmSpec.Max.smax x y)]) := rfl
  rw [h₁, maxSum_out]
  by_cases h : y.slt x
  · have hd : decide (x.toInt > y.toInt) = true := by simpa [BitVec.slt] using h
    have hs : Silmaril.WasmSpec.Max.smax x y = x := by simp [Silmaril.WasmSpec.Max.smax, h]
    rw [hd, hs]
    split
    · rfl
    · rename_i hc
      exact absurd hc (by simp [bool32])
  · have hd : decide (x.toInt > y.toInt) = false := by simpa [BitVec.slt] using h
    have hs : Silmaril.WasmSpec.Max.smax x y = y := by simp [Silmaril.WasmSpec.Max.smax, h]
    rw [hd, hs]
    split
    · rename_i hc
      exact absurd hc (by simp [bool32])
    · rfl

/-- The result slot of the `div10` kernel's summary normalises to the library's `div10Lhs`. -/
theorem div10Mulhi_sum :
    ∃ F e, fnSum? div10Mulhi 0 = some F ∧ F.params = [.i64] ∧ F.final.stack = [(.i64, e)] ∧
      norm .i64 e = div10Lhs := by
  cases hF : fnSum? div10Mulhi 0 with
  | none => exact absurd hF (by decide +kernel)
  | some F =>
    have hp : (fnSum? div10Mulhi 0).map FnSum.params = some [.i64] := by decide +kernel
    have hs : (fnSum? div10Mulhi 0).bind (fun F => match F.final.stack with
        | [(.i64, e)] => if norm .i64 e = div10Lhs then some () else none
        | _ => none) = some () := by decide +kernel
    rw [hF] at hp hs
    simp only [Option.map_some, Option.some.injEq, Option.bind_some] at hp hs
    split at hs
    · rename_i e hst
      split at hs
      · rename_i hn
        exact ⟨F, e, rfl, hp, hst, hn⟩
      · cases hs
    · cases hs

/-- The value of the `div10` identity at an environment. -/
theorem ev_div10Lhs (ρ : Env) : ev ρ .i64 div10Lhs = (show BitVec 64 from ρ .i64 0) / 10#64 := by
  have h := Silmaril.Wasm.Auto.Bridge.div10_goal ρ
  have hne : BitVec.ofNat (IntType.width .i64) 10 ≠ 0#(IntType.width .i64) := by decide
  have h' : ev ρ .i64 (.bin (.div .unsigned) (.var 0) (.const 10)) =
      (show BitVec 64 from ρ .i64 0) / 10#64 := by
    simp only [ev, binV_divU hne]
    rfl
  exact h.trans h'

/-- The `div10` kernel meets `x / 10`, at every profile. -/
theorem div10Mulhi_meets (R : Rel) (P : Profile) :
    ModMeets R.toProp P div10Mulhi 0 div10RefFn := by
  obtain ⟨F, e, hF, hp, hst, hn⟩ := div10Mulhi_sum
  refine modMeets_of_fnSum (rel_refl R) hF fun vs htv => Or.inl ?_
  obtain ⟨x, rfl⟩ := typedVals_i64 (hp ▸ htv)
  have hev : ev (envOfVals [Val.i64 x]) .i64 e = x / 10#64 := by
    rw [← ev_norm, hn, ev_div10Lhs]
    rfl
  have hout : fnOut F [Val.i64 x] = [Val.i64 (x / 10#64)] := by
    simp only [fnOut, stackAt, hst, List.map_cons, List.map_nil, List.reverse_cons,
      List.reverse_nil, List.nil_append, den, hev]
    rfl
  rw [hout]
  rfl

end Silmaril.Wasm.Auto.FrontBench
