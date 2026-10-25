module

public import Silmaril.Wasm.SingleThreaded.Determinism.Stuck

@[expose] public section

/-! # Profile-independent inversion of host-free instruction heads

These facts concern the active instruction only. Later numerical choices and
host calls remain arbitrary. Binaryen's guard, constant-branch and block-unwrapping
proofs share these lemmas; their original names remain compatibility aliases.
-/

namespace Silmaril.Wasm.SingleThreaded

open Execution.Core Validation

variable {H : Type} {P : Numerics.Profile}

/-- A host-free step at a non-value head which is neither trap nor throw is
a head reduction with an explicit operand-stack split. -/
theorem hostFree_head_inv {s : Store H} {f : Frame} {W : List Val} {e : Admin}
    {rest : List Admin} {c' : Config H} (he : e.val? = none) (htrap : e ≠ .trap)
    (hthrow : e ≠ .plain .throwRef)
    (h : Step P Det.noHost ⟨s, f, vals W ++ e :: rest⟩ c') :
    ∃ vs args c₀, W = vs ++ args ∧ Det.Head P s f args e c₀ ∧
      c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩ := by
  have hf : Det.fnv (vals W ++ e :: rest) = (W, e :: rest) := by
    simp [Det.fnv_cons_of_none he]
  rcases Det.Step.decomp (c := ⟨s, f, vals W ++ e :: rest⟩) h with hd | hb
  · obtain ⟨vs, args, e', rest', c₀, hf', -, hh, rfl⟩ := Det.fnv_headDec hd
    simp only at hf'
    rw [hf] at hf'
    simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    obtain ⟨rfl, rfl, rfl⟩ := hf'
    exact ⟨vs, args, c₀, rfl, hh, rfl⟩
  · exfalso
    obtain ⟨p, q, u, r, -, ⟨hf', -⟩ | ⟨a, hf', -⟩⟩ := Det.fnv_bubble hb <;> simp only at hf' <;>
      rw [hf] at hf' <;> simp only [Prod.mk.injEq, List.cons.injEq] at hf'
    · exact htrap hf'.2.1
    · exact hthrow hf'.2.1

local macro "not_block_family" : tactic => `(tactic| first
  | exact absurd (Det.famOf_of_shape (Det.ParametricStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.NumericStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VectorStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.VariableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.TableStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.MemoryStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.RefStep.shape ‹_›)).2 (by simp [Det.famOf])
  | exact absurd (Det.famOf_of_shape (Det.AggregateStep.shape ‹_›)).2 (by simp [Det.famOf])
  | (exfalso; simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]))

/-- A block head enters the label described by its resolved block type. -/
theorem head_block {s : Store H} {f : Frame} {args : List Val} {bt : BlockType}
    {body : List Instr} {c₀ : Config H}
    (h : Det.Head P s f args (.plain (.block bt body)) c₀) :
    ∃ t₁ t₂, f.module.blockType? bt = some (t₁, t₂) ∧ args.length = t₁.length ∧
      c₀ = ⟨s, f, [.label t₂.length [] (vals args ++ expression body)]⟩ := by
  cases h with
  | block hbt hm => exact ⟨_, _, hbt, hm, rfl⟩
  | _ => not_block_family

end Silmaril.Wasm.SingleThreaded
