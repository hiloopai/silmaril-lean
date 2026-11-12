module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# Decoders: the value encoding is injective

`floatV_injective` (every IEEE bit pattern, NaN payloads and signed zeros included, has its own
`fN` value), `refToValue_injective`, `valV_injective`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Typing

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge (refToValue)
open Silmaril.Wasm.SpecTecEnc (floatFraction floatExponent floatSign floatFractionWidth
  floatExponentWidth floatFields_reconstruct floatSign_le_one)

/-- The fraction field is below `2^M`, the exponent field below `2^E`. -/
theorem floatFields_lt (t : FloatType) (b : BitVec t.width) :
    floatFraction t b < 2 ^ floatFractionWidth t ∧ floatExponent t b < 2 ^ floatExponentWidth t :=
  ⟨Nat.mod_lt _ (Nat.two_pow_pos _), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `floatV` determines the three IEEE fields. -/
theorem floatV_fields {t : FloatType} {b b' : BitVec t.width} (h : floatV t b = floatV t b') :
    floatSign t b = floatSign t b' ∧ floatFraction t b = floatFraction t b' ∧
      floatExponent t b = floatExponent t b' := by
  have hs := floatSign_le_one t b
  have hs' := floatSign_le_one t b'
  have hl := floatFields_lt t b
  have hl' := floatFields_lt t b'
  unfold floatV at h
  simp only [Value.case.injEq] at h
  obtain ⟨hsign, hmag⟩ := h
  refine ⟨?_, ?_⟩
  · split_ifs at hsign <;> first | omega | simp at hsign
  · split_ifs at hmag <;>
      simp only [Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
        IL.Num.natN.injEq, IL.Num.intN.injEq, Silmaril.SpecTec.Equiv.Execution.caseNilV,
        and_true, true_and] at hmag <;>
      first
        | (constructor <;> omega)
        | (simp at hmag)

/-- **`floatV` is injective**: distinct bit patterns (NaN payloads and signed zeros included)
have distinct `fN` values. -/
theorem floatV_injective (t : FloatType) : Function.Injective (floatV t) := by
  intro b b' h
  obtain ⟨hs, hf, he⟩ := floatV_fields h
  apply BitVec.eq_of_toNat_eq
  rw [floatFields_reconstruct t b, floatFields_reconstruct t b', hs, hf, he]

/-- `refToValue` is injective. -/
theorem refToValue_injective : Function.Injective refToValue := by
  intro r r' h
  induction r generalizing r' <;> cases r' <;>
    simp only [refToValue, Value.case.injEq, Silmaril.SpecTec.Sem.percentV,
      Silmaril.SpecTec.Sem.caseV, Value.tuple.injEq, List.cons.injEq, Value.num.injEq,
      IL.Num.natN.injEq, and_true, true_and] at h <;>
    first
      | rfl
      | (subst h; rfl)
      | (congr 1; exact BitVec.eq_of_toNat_eq h)
      | (rename_i ih _; exact congrArg Ref.extern (ih h))
      | (simp at h)

/-- `numV` is injective at a fixed type. -/
theorem numV_injective {t : NumType} {b b' : BitVec t.width}
    (h : numV ⟨t, b⟩ = numV ⟨t, b'⟩) : b = b' := by
  rcases t with t | t
  · have hn : b.toNat = b'.toNat := by
      simpa only [numV, Silmaril.SpecTec.Equiv.Execution.pctV, Value.case.injEq, true_and,
        Value.tuple.injEq, List.cons.injEq, and_true, Value.num.injEq, IL.Num.natN.injEq] using h
    exact BitVec.eq_of_toNat_eq hn
  · exact floatV_injective t h

/-- Numeric constants are encoded injectively. -/
theorem valV_num_injective {n n' : NumVal} (h : valV (.num n) = valV (.num n')) : n = n' := by
  obtain ⟨t, b⟩ := n
  obtain ⟨t', b'⟩ := n'
  have h' : Encode.toValue t = Encode.toValue t' ∧ numV ⟨t, b⟩ = numV ⟨t', b'⟩ := by
    simpa only [valV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
      and_true] using h
  obtain rfl := Encode.toValue_injective h'.1
  rw [numV_injective h'.2]

/-- A reference is not encoded as a numeric or vector constant. -/
theorem refToValue_ne_const (r : Ref) (op : MixopS) (w : Value)
    (hop : op = "CONST" ∨ op = "VCONST") : refToValue r ≠ .case op w := by
  rcases hop with rfl | rfl <;> cases r <;> simp [refToValue]

/-- **`valV` is injective.** -/
theorem valV_injective : Function.Injective valV := by
  intro v v' h
  rcases v with n | b | r <;> rcases v' with n' | b' | r'
  case num.num => rw [valV_num_injective h]
  case vec.vec =>
    have hb : b.toNat = b'.toNat := by
      simpa only [valV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, true_and,
        Silmaril.SpecTec.Equiv.Execution.pctV, Value.num.injEq, IL.Num.natN.injEq,
        and_true] using h
    rw [BitVec.eq_of_toNat_eq hb]
  case ref.ref => rw [refToValue_injective h]
  case num.ref => exact absurd h.symm (refToValue_ne_const r' _ _ (.inl rfl))
  case vec.ref => exact absurd h.symm (refToValue_ne_const r' _ _ (.inr rfl))
  case ref.num => exact absurd h (refToValue_ne_const r _ _ (.inl rfl))
  case ref.vec => exact absurd h (refToValue_ne_const r _ _ (.inr rfl))
  all_goals simp [valV] at h

end Silmaril.Wasm.SpecTec.Sim.Typing
