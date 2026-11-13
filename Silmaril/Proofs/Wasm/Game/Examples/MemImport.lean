module

public import Silmaril.Wasm.Game.Examples.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Proofs.Wasm.Game.SpecInst.Basic

/-!
# A module importing a memory: proofs

`exMem` imports a memory and a function. Its validation and the spec's
allocation into `exMemStore` are computed by kernel evaluation
(`decide +kernel`), and the typing of the import store is proved by hand
(`exMemStore_ok`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.Examples

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.Examples Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.SpecInst Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- `exMem` validates. -/
theorem exMem_valid_some : (validate? exMem).isSome = true := by decide +kernel
/-- The spec's allocation of `exMem` succeeds. -/
theorem exMem_prep_some : (prepare? evalConst? exMemStore exMem exMemXas).isSome = true := by decide +kernel
/-- Kernel-checked facts about `exMem`: its first import is the memory, it has two imports and
one function import, its configuration holds the segment-initialisation code and the start
call, and its export is the function `1` of type `[] → []`. -/
theorem exMem_i0 : exMemMT.imports.head? = some (.mem memTy) := by decide +kernel
theorem exMem_ilen : exMemMT.imports.length = 2 := by decide +kernel
theorem exMem_fl : (CExternType.funcs exMemMT.imports).length = 1 := by decide +kernel
theorem exMem_cl : exMemPrep.1.code.length = 5 := by decide +kernel
theorem exMem_addrs : exportFuncAddrs exMemPrep.1.frame.module = [1] := by decide +kernel


theorem exMem_last : exMemMT.imports.getLast?.map (fun xt => match xt with | .func _ => true | _ => false) = some true := by decide +kernel
theorem exMem_impT : (CExternType.funcs exMemMT.imports).map FnType.ofDefType? = [some ⟨[], []⟩] := by decide +kernel

/-- The validated type. -/
theorem exMem_valid : validate? exMem = some exMemMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp exMem_valid_some
  show validate? exMem = some ((validate? exMem).getD _)
  rw [hmt]
  rfl

/-- The imports: the memory, then a function. -/
theorem exMem_imports : ∃ d, exMemMT.imports = [.mem memTy, .func d] := by
  obtain ⟨x₀, x₁, hl⟩ := List.length_eq_two.mp exMem_ilen
  have h0' : [x₀, x₁].head? = some (.mem memTy) := hl ▸ exMem_i0
  have h0 : x₀ = .mem memTy := Option.some.inj h0'
  have h1' : [x₀, x₁].getLast?.map (fun xt => match xt with | .func _ => true | _ => false) =
      some true := hl ▸ exMem_last
  have h1 : (match x₁ with | .func _ => true | _ => false) = true := Option.some.inj h1'
  cases x₁ with
  | func d => exact ⟨d, by rw [hl, h0]⟩
  | _ => cases h1

/-- The import store is typed. -/
theorem exMemStore_ok : StoreOk exMemStore := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [exMemStore]; done)
  · intro mi hmi
    have hmi' : mi = ⟨memTy, ByteArray.empty⟩ := by simpa [exMemStore] using hmi
    rw [hmi']
    exact ⟨show memTy.Valid by decide, rfl⟩
  · intro fi hfi
    have hfi' : fi ∈ (importStore (CExternType.funcs exMemMT.imports)).funcs := hfi
    simp only [importStore, List.mem_mapIdx] at hfi'
    obtain ⟨i, hi, rfl⟩ := hfi'
    obtain ⟨hok, ps, rs, he⟩ := funcImport_ok exMem_valid (mem_funcs_of_mem (List.getElem_mem hi))
    exact FuncInstOk.host hok he rfl


theorem exMem_ty1 : (exMemPrep.1.store.funcs[1]?).map (fun fi => FnType.ofDefType? fi.type) = some (some ⟨[], []⟩) := by decide +kernel

/-- The allocation. -/
theorem exMem_prep : prepare? evalConst? exMemStore exMem exMemXas = some exMemPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp exMem_prep_some
  show _ = some ((prepare? evalConst? exMemStore exMem exMemXas).getD _)
  rw [hq]
  rfl

/-- The imported function has scalar type `[] → []`. -/
theorem exMem_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs exMemMT.imports) exMemI.imports := by
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp exMem_fl
  have h' : [d].map FnType.ofDefType? = [some ⟨[], []⟩] := hd ▸ exMem_impT
  have h : FnType.ofDefType? d = some ⟨[], []⟩ := (List.cons.inj h').1
  rw [hd]
  exact .cons h .nil

/-- The import addresses have the import types (the memory exactly). -/
theorem exMem_importsOk : List.Forall₂ (ExternAddrOk exMemStore) exMemXas exMemMT.imports := by
  obtain ⟨d, hd⟩ := exMem_imports
  have hf : CExternType.funcs exMemMT.imports = [d] := by rw [hd]; rfl
  have hfn : exMemStore.funcs[0]? = some { type := d, module := {}, code := .host 0 } := by
    show (importStore (CExternType.funcs exMemMT.imports)).funcs[0]? = _
    rw [hf]
    rfl
  rw [hd]
  exact .cons (ExternAddrOk.mem (mi := ⟨memTy, ByteArray.empty⟩) rfl) (.cons (ExternAddrOk.func hfn) .nil)

/-- The export has scalar type `[] → []`. -/
theorem exMem_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, exMemI.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) exMemI.addrs exMemI.exports := by
  have ha : exMemI.addrs = [1] := exMem_addrs
  obtain ⟨fi, hfi, hty⟩ := Option.map_eq_some_iff.mp exMem_ty1
  rw [ha]
  exact .cons ⟨fi, hfi, hty⟩ .nil

/-- **`exMemI` is the spec instance of `exMem` at `exMemStore`.** -/
theorem exMem_isSpecInstanceAt : IsSpecInstanceAt exMemStore exMemXas exMem exMemMT exMemI exMemC₀ where
  valid := exMem_valid
  storeOk := exMemStore_ok
  importsOk := exMem_importsOk
  hostTyped := importStore_hostTyped exMem_importTypes
  prepared := ⟨exMemPrep.1, exMemPrep.2, exMem_prep, rfl, rfl, rfl⟩
  exportTypes := exMem_exportTypes

end Silmaril.Proofs.Wasm.Game.Examples
