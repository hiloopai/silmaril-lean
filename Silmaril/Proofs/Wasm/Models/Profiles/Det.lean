module

public import Silmaril.Wasm.Models.Profiles.Defs
public import Silmaril.Wasm.Models.Runtime.Thms
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Wasm.Det.Stateless.Defs
public import Silmaril.Wasm.Det.GrowTrap.Defs

/-!
# The determinism subsets in the feature lattice

* `noMem_flat`, `stateless_flat`, `growTrap_flat`: the flat instructions of `Det.NoMem`,
  `Det.Stateless` and `Det.GrowTrap` (other than a typed `select`, whose type annotation may
  mention any value type) are runtime instructions of `noMemS`, `statelessS`, `growTrapS`;
* `noMem_instrB`: conversely, every instruction of a float-free feature set below
  `functionalMutGC` passes `Det.NoMem.instrB` in full mode, so a store of such code passes
  `Det.NoMem.storeB` (`storeB_of_storeIn`) and is deterministic.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.Profiles

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models Silmaril.Wasm.Models.Rt

variable {S : FeatureSet}

theorem noMemS_ref (rt : RefType) : RefType.inFeatB noMemS rt = true := by
  rcases rt with ⟨n, ⟨a⟩ | ⟨x⟩⟩
  · cases a <;> cases n <;> decide
  · cases n <;> simp only [RefType.inFeatB, HeapType.inFeatB] <;> decide

theorem noMemS_heap (ht : HeapType) : HeapType.inFeatB noMemS ht = true := by
  rcases ht with ⟨a⟩ | ⟨x⟩
  · cases a <;> decide
  · simp only [HeapType.inFeatB]; decide

theorem noMem_flat {i : Instr} (h : Silmaril.Wasm.Det.NoMem.flatOk i = true)
    (hs : ∀ ts, i ≠ .select (some ts)) : instrB noMemS i = true := by
  cases i
  case select ts =>
    cases ts
    · decide
    · exact absurd rfl (hs _)
  case intUnOp t op =>
    cases op <;> simp (config := { decide := true }) [instrB, Instr.inFeatB, Instr.headB,
      IntUnOp.inFeatB]
  case convert op =>
    cases op <;> simp (config := { decide := true }) [Silmaril.Wasm.Det.NoMem.flatOk, instrB,
      Instr.inFeatB, Instr.headB, ConvertOp.inFeatB] at h ⊢
  all_goals simp (config := { decide := true }) [Silmaril.Wasm.Det.NoMem.flatOk, instrB,
    Instr.inFeatB, Instr.headB, tblIdxB, noMemS_ref, noMemS_heap] at h ⊢

theorem stateless_flat {A R W : Nat → Bool} {m : ModuleInst} {i : Instr}
    (h : Silmaril.Wasm.Det.Stateless.slInstr A R W m i = true) (hb : i.bodies = [])
    (hs : ∀ ts, i ≠ .select (some ts)) : instrB statelessS i = true := by
  cases i
  case select ts =>
    cases ts
    · decide
    · exact absurd rfl (hs _)
  case intUnOp t op =>
    cases op <;> simp (config := { decide := true }) [instrB, Instr.inFeatB, Instr.headB,
      IntUnOp.inFeatB]
  all_goals simp (config := { decide := true }) [Silmaril.Wasm.Det.Stateless.slInstr, instrB,
    Instr.inFeatB, Instr.headB, Instr.bodies] at h hb ⊢

theorem growTrap_flat {i : Instr} (h : Silmaril.Wasm.Det.GrowTrap.flatOk i = true)
    (hs : ∀ ts, i ≠ .select (some ts)) : instrB growTrapS i = true := by
  cases i
  case select ts =>
    cases ts
    · decide
    · exact absurd rfl (hs _)
  case intUnOp t op =>
    cases op <;> simp (config := { decide := true }) [instrB, Instr.inFeatB, Instr.headB,
      IntUnOp.inFeatB]
  all_goals simp (config := { decide := true }) [Silmaril.Wasm.Det.GrowTrap.flatOk, instrB,
    Instr.inFeatB, Instr.headB, memIdxB] at h ⊢

/-- A capability outside `functionalMutGC` is outside every feature set below it. -/
theorem not_has_of_le_fmg (hS : S ≤ functionalMutGC) {c : Cap}
    (hc : functionalMutGC.has c = false) : S.has c = false := by
  cases h : S.has c
  · rfl
  · exact absurd (has_of_le hS h) (by simp [hc])

open Silmaril.Wasm.Det.NoMem in
theorem noMem_head (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false) {i : Instr}
    {fs : List Nat} (h : Instr.headB S i = true) (hb : i.bodies = []) :
    Silmaril.Wasm.Det.NoMem.instrB (fun _ => true) true fs i = true := by
  have hm : S.has .memory = false := not_has_of_le_fmg hS (by decide)
  have ht : S.has .table = false := not_has_of_le_fmg hS (by decide)
  have hg : S.has .globals = false := not_has_of_le_fmg hS (by decide)
  have hgm : S.has .mutGlobal = false := not_has_of_le_fmg hS (by decide)
  have hv : S.has .simd = false := not_has_of_le_fmg hS (by decide)
  have hci : S.has .callIndirect = false := not_has_of_le_fmg hS (by decide)
  have hbm : S.has .bulkMemory = false := not_has_of_le_fmg hS (by decide)
  have hbo : S.has .bulkMemoryOpt = false := not_has_of_le_fmg hS (by decide)
  have hse : S.has .signExt = false := not_has_of_le_fmg hS (by decide)
  have hsc : S.has .satConv = false := not_has_of_le_fmg hS (by decide)
  cases i
  case call x =>
    simp only [Silmaril.Wasm.Det.NoMem.instrB, callOk]
    cases fs[x.toNat]? <;> rfl
  case returnCall x =>
    simp only [Silmaril.Wasm.Det.NoMem.instrB, callOk]
    cases fs[x.toNat]? <;> rfl
  case intUnOp t op =>
    cases op <;> simp_all [Instr.headB, IntUnOp.inFeatB, Silmaril.Wasm.Det.NoMem.instrB, flatOk]
  case convert op =>
    cases op <;> simp_all [Instr.headB, ConvertOp.inFeatB, Silmaril.Wasm.Det.NoMem.instrB, flatOk]
  all_goals simp_all [Instr.headB, Instr.bodies, Silmaril.Wasm.Det.NoMem.instrB, flatOk,
    memIdxB, tblIdxB, vecB]

/-- Every instruction of a float-free feature set below `functionalMutGC` is in `Det.NoMem`
(full mode: indirect calls allowed, every function may be entered). -/
theorem noMem_instrB (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false) {fs : List Nat}
    (i : Instr) (h : Instr.inFeatB S i = true) :
    Silmaril.Wasm.Det.NoMem.instrB (fun _ => true) true fs i = true := by
  revert h
  induction i using Instr.rec (motive_2 := fun l => Instr.insInFeatB S l = true →
    Silmaril.Wasm.Det.NoMem.instrsB (fun _ => true) true fs l = true)
  all_goals first
    | exact fun h => noMem_head hS hf h rfl
    | simp_all [Instr.inFeatB, Instr.insInFeatB, Silmaril.Wasm.Det.NoMem.instrB,
        Silmaril.Wasm.Det.NoMem.instrsB]

theorem noMem_instrsB (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false) {fs : List Nat}
    (is : List Instr) (h : Instr.insInFeatB S is = true) :
    Silmaril.Wasm.Det.NoMem.instrsB (fun _ => true) true fs is = true := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have h' : Instr.inFeatB S i = true ∧ Instr.insInFeatB S is = true := by
      simpa [Instr.insInFeatB] using h
    simp [Silmaril.Wasm.Det.NoMem.instrsB, noMem_instrB hS hf i h'.1, ih h'.2]

/-- A store all of whose functions are of a float-free feature set below `functionalMutGC`
passes `Det.NoMem.storeB`. -/
theorem storeB_of_storeIn (hS : S ≤ functionalMutGC) (hf : S.has .floatNum = false)
    {s : Store Nat} (hs : StoreIn S s) : Silmaril.Wasm.Det.NoMem.storeB s = true := by
  simp only [Silmaril.Wasm.Det.NoMem.storeB, List.all_eq_true]
  intro fi hfi
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
  unfold Silmaril.Wasm.Det.NoMem.funcB
  split
  · rename_i fn hcode
    exact noMem_instrsB hS hf _ (hs a fi fn ha hcode)
  · rfl

end Silmaril.Proofs.Wasm.Models.Profiles
