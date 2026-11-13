module

public import Silmaril.Proofs.Wasm.Wasmi.Observed.Run
public import Silmaril.Proofs.Wasm.Wasmi.Observed.Nan
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# The witness store (proofs)

`roundFnB` is an executable check of the facts `RoundFn` collects (the function exists, its body
is `local.get 0; t.op`, its type expands to a function type with one parameter and one
result), and `roundFn_of` reads them back. `round_checks`: the check holds at the eight
addresses of `roundStore` (a kernel evaluation of silmaril-lean's `prepare?` on `roundMod`),
and the module validates. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Wasmi.Observed

variable {H : Type}

/-- The executable form of `RoundFn`. -/
def roundFnB (s : Store H) (a : Nat) (t : FloatType) (op : FloatUnOp) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    (match fi.code with
      | .wasm g =>
        match g.body with
        | [.localGet x, .floatUnOp t' op'] => decide (x = ⟨0⟩ ∧ t' = t ∧ op' = op)
        | _ => false
      | .host _ => false) &&
    (match fi.type.expand? with
      | some (.func ps rs) => ps.length == 1 && rs.length == 1
      | _ => false)
  | none => false

theorem roundFn_of {s : Store H} {a : Nat} {t : FloatType} {op : FloatUnOp}
    (h : roundFnB s a t op = true) : Nonempty (RoundFn s a t op) := by
  unfold roundFnB at h
  split at h
  · rename_i fi hf
    simp only [Bool.and_eq_true] at h
    obtain ⟨h₁, h₂⟩ := h
    split at h₁
    · rename_i g hg
      split at h₁
      · rename_i x t' op' hb
        obtain ⟨rfl, rfl, rfl⟩ := of_decide_eq_true h₁
        split at h₂
        · rename_i ps rs he
          simp only [Bool.and_eq_true, beq_iff_eq] at h₂
          exact ⟨⟨fi, g, ps, rs, hf, hg, hb, Expand.iff.mpr he, h₂.1, h₂.2⟩⟩
        · cases h₂
      · cases h₁
    · cases h₁
  · cases h

/-- **The eight witness functions** are `local.get 0; t.op` with one parameter and one result,
and the module validates with no imports. -/
theorem round_checks :
    ((Validation.validate? roundMod).map fun mt => mt.imports.isEmpty) = some true ∧
      (∀ op ∈ roundOps, roundFnB roundStore (roundAddr .f32 op) .f32 op = true) ∧
      ∀ op ∈ roundOps, roundFnB roundStore (roundAddr .f64 op) .f64 op = true := by
  decide +kernel

theorem roundFn_store {t : FloatType} {op : FloatUnOp} (hop : op ∈ roundOps) :
    Nonempty (RoundFn roundStore (roundAddr t op) t op) := by
  cases t with
  | f32 => exact roundFn_of (round_checks.2.1 op hop)
  | f64 => exact roundFn_of (round_checks.2.2 op hop)

theorem isRound_of_mem {op : FloatUnOp} (hop : op ∈ roundOps) : IsRound op = true := by
  simp only [roundOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;> rfl

end Silmaril.Proofs.Wasm.Wasmi.Observed
