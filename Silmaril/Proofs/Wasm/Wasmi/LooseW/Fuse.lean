module

public import Silmaril.Wasm.Wasmi.LooseW.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Store
public import Silmaril.Wasm.Execution.Core.Sim.CodeRel

@[expose] public section

/-!
# The wider select fusion: syntactic facts

As `Silmaril.Proofs.Wasm.Wasmi.Fuse` for `fuse`, now for `fuseW`:

* `fuseWBI`: the base pairs, the translation `g.tgt x t` of a shape against its source
  `g.src x t`;
* `fuseW_rel`: the translation of a sequence is related to it by `InstrsRel fuseWBI`;
* `storeRel_fuseStoreW`: the translated store is related to its source store;
* `invoke_fuseStoreW`: invoking the translated store starts from the same code.

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi.LooseW

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Wasmi Silmaril.Wasm.Wasmi.Fusion Silmaril.Wasm.Wasmi.LooseW

variable {H : Type}

/-- The base pairs of the wider translation: a translated shape (left) against its source
(right). -/
def fuseWBI (x y : List Instr) : Prop := ∃ g i t, x = FuseShape.tgt g i t ∧ y = FuseShape.src g i t

/-- A base pair, as a related sequence. -/
theorem base_rel (g : FuseShape) (x : LocalIdx) (t : Option (List ValType)) {l r : List Instr}
    (h : InstrsRel fuseWBI l r) : InstrsRel fuseWBI (g.tgt x t ++ l) (g.src x t ++ r) :=
  .append (.base ⟨g, x, t, rfl, rfl⟩) h

/-- The motives of `fuseW_rel`, one per syntactic class. -/
abbrev RelI (i : Instr) : Prop := InstrRel fuseWBI (fuseWI i) i
abbrev RelL (l : List Instr) : Prop := InstrsRel fuseWBI (fuseW l) l

theorem relI_block (bt : BlockType) (b : List Instr) (ih : RelL b) : RelI (.block bt b) :=
  .block bt ih
theorem relI_loop (bt : BlockType) (b : List Instr) (ih : RelL b) : RelI (.loop bt b) :=
  .loop bt ih
theorem relI_if (bt : BlockType) (b₁ b₂ : List Instr) (ih₁ : RelL b₁) (ih₂ : RelL b₂) :
    RelI (.if_ bt b₁ b₂) :=
  .if_ bt ih₁ ih₂
theorem relI_try (bt : BlockType) (cs : List Catch) (b : List Instr) (ih : RelL b) :
    RelI (.tryTable bt cs b) :=
  .tryTable bt cs ih

/-- The equations of `fuseW` at a non-zero constant. -/
theorem fuseW_c1 {c : BitVec IntType.i32.width} (hc : c ≠ 0) (x : LocalIdx) (op : IntRelOp)
    (hop : op = .ne ∨ op = .eq) (t : Option (List ValType)) (rest : List Instr) :
    fuseW (.intConst .i32 c :: .localGet x :: .intRelOp .i32 op :: .select t :: rest) =
      .intConst .i32 c :: fuseW (.localGet x :: .intRelOp .i32 op :: .select t :: rest) := by
  rcases hop with rfl | rfl
  · rw [fuseW.eq_2]; simp only [hc, ↓reduceIte]
  · rw [fuseW.eq_4]; simp only [hc, ↓reduceIte]

theorem fuseW_c2 {c : BitVec IntType.i32.width} (hc : c ≠ 0) (x : LocalIdx) (op : IntRelOp)
    (hop : op = .ne ∨ op = .eq) (t : Option (List ValType)) (rest : List Instr) :
    fuseW (.localGet x :: .intConst .i32 c :: .intRelOp .i32 op :: .select t :: rest) =
      .localGet x :: fuseW (.intConst .i32 c :: .intRelOp .i32 op :: .select t :: rest) := by
  rcases hop with rfl | rfl
  · rw [fuseW.eq_3]; simp only [hc, ↓reduceIte]
  · rw [fuseW.eq_5]; simp only [hc, ↓reduceIte]

/-- The fall-through equation: a non-structured head is kept. -/
theorem relL_cons1 {i : Instr} {rest : List Instr} (h : fuseW (i :: rest) = i :: fuseW rest)
    (ih : RelL rest) : RelL (i :: rest) := by
  show InstrsRel fuseWBI (fuseW _) _
  rw [h]; exact .cons (.refl _) ih

/-- **The wider translation of a sequence is related to it.** -/
theorem fuseW_rel (l : List Instr) : InstrsRel fuseWBI (fuseW l) l :=
  fuseW.induct (motive_1 := RelI) (motive_2 := RelL) relI_block relI_loop relI_if relI_try
    (fun i h₁ h₂ h₃ h₄ => by
      show InstrRel fuseWBI (fuseWI i) i
      rw [fuseWI.eq_5 i h₁ h₂ h₃ h₄]; exact .refl i)
    .nil
    (fun x t rest ih => base_rel .ne0 x t ih)
    (fun c x t rest hc ih => relL_cons1 (fuseW_c1 hc x .ne (.inl rfl) t rest) ih)
    (fun x t rest ih => base_rel .neSwap x t ih)
    (fun x c t rest hc ih => relL_cons1 (fuseW_c2 hc x .ne (.inl rfl) t rest) ih)
    (fun x t rest ih => base_rel .eq0 x t ih)
    (fun c x t rest hc ih => relL_cons1 (fuseW_c1 hc x .eq (.inr rfl) t rest) ih)
    (fun x t rest ih => base_rel .eqSwap x t ih)
    (fun x c t rest hc ih => relL_cons1 (fuseW_c2 hc x .eq (.inr rfl) t rest) ih)
    (fun x t rest ih => base_rel .eqz x t ih)
    (fun i rest h₁ h₂ h₃ h₄ h₅ ihi ih => by
      show InstrsRel fuseWBI (fuseW _) _
      rw [fuseW.eq_7 i rest h₁ h₂ h₃ h₄ h₅]; exact .cons ihi ih) l

/-! ## Function instances and stores -/

theorem fuseFuncW_type (fi : FuncInst H) : (fuseFuncW fi).type = fi.type := by
  unfold fuseFuncW; split <;> rfl

/-- **A translated function instance is related to its source.** -/
theorem funcRel_fuseFuncW (fi : FuncInst H) : FuncRel fuseWBI (fuseFuncW fi) fi := by
  obtain ⟨ty, m, code⟩ := fi
  cases code with
  | wasm g => exact ⟨rfl, rfl, rfl, rfl, fuseW_rel g.body⟩
  | host h => exact ⟨rfl, rfl, rfl⟩

/-- **The translated store is related to its source.** -/
theorem storeRel_fuseStoreW (s : Store H) : StoreRel (FuncRel fuseWBI) (fuseStoreW s) s := by
  refine ⟨?_, rfl, ?_⟩
  · simp only [fuseStoreW, List.map_map]
    exact List.map_congr_left fun fi _ => fuseFuncW_type fi
  · simp only [fuseStoreW]
    induction s.funcs with
    | nil => exact .nil
    | cons fi fs ih => exact .cons (funcRel_fuseFuncW fi) ih

/-- Invoking the translated store starts from the same code and frame. -/
theorem invoke_fuseStoreW (s : Store H) (a : Nat) (vs : List Val) :
    invoke (fuseStoreW s) a vs = { invoke s a vs with store := fuseStoreW s } := by
  simp only [invoke, fuseStoreW, List.getElem?_map]
  cases s.funcs[a]? <;> simp [fuseFuncW_type]

end Silmaril.Proofs.Wasm.Wasmi.LooseW
