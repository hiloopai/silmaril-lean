module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Store
public import Silmaril.Wasm.Execution.Core.Sim.CodeRel

@[expose] public section

/-!
# wasmi's select fusion: syntactic facts

* `fuseBI`: the base pairs of the translation, a fused pattern against its source;
* `fuse_rel`: the translation of a sequence is related to the source by the closure
  `InstrsRel fuseBI` of silmaril-lean's code-relation kit;
* `funcRel_fuseFunc`, `storeRel_fuseStore`: the translated store is related to the source
  store (`StoreRel (FuncRel fuseBI)`): same types, modules and locals, related bodies;
* `invoke_fuseStore`: invoking the translated store starts from the same code;
* `fuse_of_patFree`, `fuseStore_of_patFree`: without the pattern, the translation is the
  identity.

New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.Wasmi

variable {H : Type}

/-- The base pairs of wasmi's translation: a fused pattern (left) against its source (right). -/
def fuseBI (x y : List Instr) : Prop := ∃ i t, x = fusedSel i t ∧ y = zeroTestSel i t

/-- The equation of `fuse` at a non-zero constant before the rest of the pattern. -/
theorem fuse_const_ne {c : BitVec IntType.i32.width} (hc : c ≠ 0) (x : LocalIdx)
    (t : Option (List ValType)) (rest : List Instr) :
    fuse (.intConst .i32 c :: .localGet x :: .intRelOp .i32 .ne :: .select t :: rest) =
      .intConst .i32 c :: fuse (.localGet x :: .intRelOp .i32 .ne :: .select t :: rest) := by
  rw [fuse.eq_2]; simp only [hc, ↓reduceIte]

/-- The motives of `fuse_rel`, one per syntactic class. -/
abbrev RelI (i : Instr) : Prop := InstrRel fuseBI (fuseI i) i
abbrev RelL (l : List Instr) : Prop := InstrsRel fuseBI (fuse l) l

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

/-- **The translation of a sequence is related to it.** -/
theorem fuse_rel (l : List Instr) : InstrsRel fuseBI (fuse l) l :=
  fuse.induct (motive_1 := RelI) (motive_2 := RelL) relI_block relI_loop relI_if relI_try
    (fun i h₁ h₂ h₃ h₄ => by
      show InstrRel fuseBI (fuseI i) i
      rw [fuseI.eq_5 i h₁ h₂ h₃ h₄]; exact .refl i)
    .nil
    (fun x t rest ih => .append (.base ⟨x, t, rfl, rfl⟩) ih)
    (fun c x t rest hc ih => by
      show InstrsRel fuseBI (fuse _) _
      rw [fuse_const_ne hc]; exact .cons (.refl _) ih)
    (fun i rest hne ihi ih => by
      show InstrsRel fuseBI (fuse _) _
      rw [fuse.eq_3 i rest hne]; exact .cons ihi ih) l

/-- The translation of an instruction is related to it. -/
theorem fuseI_rel (i : Instr) : InstrRel fuseBI (fuseI i) i :=
  fuseI.induct (motive_1 := RelI) (motive_2 := RelL) relI_block relI_loop relI_if relI_try
    (fun i h₁ h₂ h₃ h₄ => by
      show InstrRel fuseBI (fuseI i) i
      rw [fuseI.eq_5 i h₁ h₂ h₃ h₄]; exact .refl i)
    .nil
    (fun x t rest ih => .append (.base ⟨x, t, rfl, rfl⟩) ih)
    (fun c x t rest hc ih => by
      show InstrsRel fuseBI (fuse _) _
      rw [fuse_const_ne hc]; exact .cons (.refl _) ih)
    (fun i rest hne ihi ih => by
      show InstrsRel fuseBI (fuse _) _
      rw [fuse.eq_3 i rest hne]; exact .cons ihi ih) i

/-- **Without the pattern, the translation is the identity.** -/
theorem fuse_of_patFree (l : List Instr) : patFree l = true → fuse l = l :=
  fuse.induct (motive_1 := fun i => patFreeI i = true → fuseI i = i)
    (motive_2 := fun l => patFree l = true → fuse l = l)
    (fun bt b ih h => by simp only [fuseI, patFreeI] at h ⊢; rw [ih h])
    (fun bt b ih h => by simp only [fuseI, patFreeI] at h ⊢; rw [ih h])
    (fun bt b₁ b₂ ih₁ ih₂ h => by
      simp only [fuseI, patFreeI, Bool.and_eq_true] at h ⊢; rw [ih₁ h.1, ih₂ h.2])
    (fun bt cs b ih h => by simp only [fuseI, patFreeI] at h ⊢; rw [ih h])
    (fun i h₁ h₂ h₃ h₄ _ => fuseI.eq_5 i h₁ h₂ h₃ h₄)
    (fun _ => rfl)
    (fun x t rest _ h => by simp [patFree] at h)
    (fun c x t rest hc ih h => by
      rw [patFree.eq_2, Bool.and_eq_true] at h
      rw [fuse_const_ne hc, ih h.2])
    (fun i rest hne ihi ih h => by
      rw [patFree.eq_3 i rest hne, Bool.and_eq_true] at h
      rw [fuse.eq_3 i rest hne, ihi h.1, ih h.2]) l

/-! ## Function instances and stores -/

theorem fuseFunc_type (fi : FuncInst H) : (fuseFunc fi).type = fi.type := by
  unfold fuseFunc; split <;> rfl

theorem fuseFunc_module (fi : FuncInst H) : (fuseFunc fi).module = fi.module := by
  unfold fuseFunc; split <;> rfl

/-- **A translated function instance is related to its source.** -/
theorem funcRel_fuseFunc (fi : FuncInst H) : FuncRel fuseBI (fuseFunc fi) fi := by
  obtain ⟨ty, m, code⟩ := fi
  cases code with
  | wasm g => exact ⟨rfl, rfl, rfl, rfl, fuse_rel g.body⟩
  | host h => exact ⟨rfl, rfl, rfl⟩

/-- **The translated store is related to its source.** -/
theorem storeRel_fuseStore (s : Store H) : StoreRel (FuncRel fuseBI) (fuseStore s) s := by
  refine ⟨?_, rfl, ?_⟩
  · simp only [fuseStore, List.map_map]
    exact List.map_congr_left fun fi _ => fuseFunc_type fi
  · simp only [fuseStore]
    induction s.funcs with
    | nil => exact .nil
    | cons fi fs ih => exact .cons (funcRel_fuseFunc fi) ih

/-- Invoking the translated store starts from the same code and frame. -/
theorem invoke_fuseStore (s : Store H) (a : Nat) (vs : List Val) :
    invoke (fuseStore s) a vs = { invoke s a vs with store := fuseStore s } := by
  simp only [invoke, fuseStore, List.getElem?_map]
  cases s.funcs[a]? <;> simp [fuseFunc_type]

/-- **Without the pattern, the translated store is the store.** -/
theorem fuseStore_of_patFree {s : Store H} (h : StorePatFree s) : fuseStore s = s := by
  obtain ⟨tags, globals, mems, tables, funcs, datas, elems, structs, arrays, exns⟩ := s
  simp only [fuseStore, Store.mk.injEq, and_true, true_and]
  rw [List.map_congr_left (g := id) ?_, List.map_id]
  intro fi hfi
  obtain ⟨ty, m, code⟩ := fi
  cases code with
  | wasm g =>
    have hb := fuse_of_patFree g.body (h _ hfi g rfl)
    simp only [fuseFunc, hb, id]
  | host _ => rfl

end Silmaril.Proofs.Wasm.Wasmi
