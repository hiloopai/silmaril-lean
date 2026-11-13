module

public import Silmaril.Wasm.Game.Shared.Example.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Proofs.Wasm.Game.SpecInst.Basic

/-!
# The memory-writing example: the instance

`exLog` validates and is allocated by the spec's `prepare?` into `exLogStore`
(kernel evaluation, `decide +kernel`, on Boolean summaries); the import store is
typed by hand (`exLogStore_ok`), so `exLogI` is a spec instance
(`exLog_isSpecInstanceAt`) and well formed at its store (`exLogI_wellFormed`).
Kernel-checked facts about the allocated store give the shape of its two functions.
New proofs, following `Silmaril.Proofs.Wasm.Game.Examples.MemImport`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SharedExample

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Game.SharedExample Silmaril.Proofs.Wasm.Game
  Silmaril.Proofs.Wasm.Game.SpecInst Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

theorem exLog_valid_some : (validate? exLog).isSome = true := by decide +kernel
theorem exLog_prep_some : (prepare? evalConst? exLogStore exLog exLogXas).isSome = true := by
  decide +kernel
theorem exLog_i0 : exLogMT.imports.head? = some (.mem memTy1) := by decide +kernel
theorem exLog_ilen : exLogMT.imports.length = 2 := by decide +kernel
theorem exLog_fl : (CExternType.funcs exLogMT.imports).length = 1 := by decide +kernel
theorem exLog_addrs : exportFuncAddrs exLogPrep.1.frame.module = [1] := by decide +kernel
theorem exLog_last : exLogMT.imports.getLast?.map
    (fun xt => match xt with | .func _ => true | _ => false) = some true := by decide +kernel
theorem exLog_impT : (CExternType.funcs exLogMT.imports).map FnType.ofDefType? =
    [some ⟨[], []⟩] := by decide +kernel

/-- The host function of import `0`. -/
def isHost0 (fi : FuncInst Nat) : Bool := match fi.code with | .host 0 => true | _ => false

/-- A Wasm function without locals whose body is `call 0; i32.const 0; i32.load8_u 0`. -/
def isGetBody (fi : FuncInst Nat) : Bool := match fi.code with
  | .wasm ⟨_, [], [.call x, .intConst .i32 k, .intLoad .i32 (some (.i8, .unsigned)) y arg]⟩ =>
    x.toNat == 0 && k == 0 && y.toNat == 0 && arg == memarg0
  | _ => false

/-- Kernel-checked shape of the allocated store. -/
theorem t_len : exLogPrep.1.store.funcs.length = 2 := by decide +kernel
theorem t_host : exLogPrep.1.store.funcs.map isHost0 = [true, false] := by decide +kernel
theorem t_body : exLogPrep.1.store.funcs.map isGetBody = [false, true] := by decide +kernel
theorem t_ty : exLogPrep.1.store.funcs.map (fun fi => FnType.ofDefType? fi.type) =
    [some ⟨[], []⟩, some ⟨[], [.num (.int .i32)]⟩] := by decide +kernel
theorem t_mod : exLogPrep.1.store.funcs.map (fun fi => fi.module.funcs) = [[], [0, 1]] := by
  decide +kernel
theorem t_mems : exLogPrep.1.store.funcs.map (fun fi => fi.module.mems) = [[], [0]] := by
  decide +kernel
theorem t_memty : exLogPrep.1.store.mems.map MemInst.type = [memTy1] := by decide +kernel

/-- The validated type. -/
theorem exLog_valid : validate? exLog = some exLogMT := by
  obtain ⟨mt, hmt⟩ := Option.isSome_iff_exists.mp exLog_valid_some
  show validate? exLog = some ((validate? exLog).getD _)
  rw [hmt]
  rfl

/-- The allocation. -/
theorem exLog_prep : prepare? evalConst? exLogStore exLog exLogXas = some exLogPrep := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp exLog_prep_some
  show _ = some ((prepare? evalConst? exLogStore exLog exLogXas).getD _)
  rw [hq]
  rfl

/-- The imports: the memory, then a function. -/
theorem exLog_imports : ∃ d, exLogMT.imports = [.mem memTy1, .func d] := by
  obtain ⟨x₀, x₁, hl⟩ := List.length_eq_two.mp exLog_ilen
  have h0' : [x₀, x₁].head? = some (.mem memTy1) := hl ▸ exLog_i0
  have h0 : x₀ = .mem memTy1 := Option.some.inj h0'
  have h1' : [x₀, x₁].getLast?.map (fun xt => match xt with | .func _ => true | _ => false) =
      some true := hl ▸ exLog_last
  have h1 : (match x₁ with | .func _ => true | _ => false) = true := Option.some.inj h1'
  cases x₁ with
  | func d => exact ⟨d, by rw [hl, h0]⟩
  | _ => cases h1

theorem zeroPage_size : zeroPage.size = memTy1.limits.min.val * Silmaril.Wasm.Execution.Memory.pageSize := by
  simp [zeroPage, memTy1, Silmaril.Wasm.Execution.Memory.pageSize, ByteArray.size]

/-- The import store is typed. -/
theorem exLogStore_ok : StoreOk exLogStore := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [exLogStore]; done)
  · intro mi hmi
    have hmi' : mi = ⟨memTy1, zeroPage⟩ := by simpa [exLogStore] using hmi
    rw [hmi']
    exact ⟨show memTy1.Valid by decide, zeroPage_size⟩
  · intro fi hfi
    have hfi' : fi ∈ (importStore (CExternType.funcs exLogMT.imports)).funcs := hfi
    simp only [importStore, List.mem_mapIdx] at hfi'
    obtain ⟨i, hi, rfl⟩ := hfi'
    obtain ⟨hok, ps, rs, he⟩ := funcImport_ok exLog_valid (mem_funcs_of_mem (List.getElem_mem hi))
    exact FuncInstOk.host hok he rfl

/-- The imported function has scalar type `[] → []`. -/
theorem exLog_importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs exLogMT.imports) exLogI.imports := by
  obtain ⟨d, hd⟩ := List.length_eq_one_iff.mp exLog_fl
  have h' : [d].map FnType.ofDefType? = [some ⟨[], []⟩] := hd ▸ exLog_impT
  have h : FnType.ofDefType? d = some ⟨[], []⟩ := (List.cons.inj h').1
  rw [hd]
  exact .cons h .nil

/-- The import addresses have the import types. -/
theorem exLog_importsOk : List.Forall₂ (ExternAddrOk exLogStore) exLogXas exLogMT.imports := by
  obtain ⟨d, hd⟩ := exLog_imports
  have hf : CExternType.funcs exLogMT.imports = [d] := by rw [hd]; rfl
  have hfn : exLogStore.funcs[0]? = some { type := d, module := {}, code := .host 0 } := by
    show (importStore (CExternType.funcs exLogMT.imports)).funcs[0]? = _
    rw [hf]
    rfl
  rw [hd]
  exact .cons (ExternAddrOk.mem (mi := ⟨memTy1, zeroPage⟩) rfl)
    (.cons (ExternAddrOk.func hfn) .nil)

/-- The two functions of the allocated store. -/
theorem exFuncs : ∃ fi₀ fi₁ : FuncInst Nat, exLogPrep.1.store.funcs = [fi₀, fi₁] :=
  List.length_eq_two.mp t_len

/-- The export has scalar type `[] → [i32]`. -/
theorem exLog_exportTypes : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat,
      exLogI.store.funcs[a]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
    exLogI.addrs exLogI.exports := by
  have ha : exLogI.addrs = [1] := exLog_addrs
  obtain ⟨fi₀, fi₁, hf⟩ := exFuncs
  have hty : FnType.ofDefType? fi₁.type = some ⟨[], [.num (.int .i32)]⟩ := by
    have h := t_ty
    rw [hf] at h
    exact (List.cons.inj (List.cons.inj h).2).1
  rw [ha]
  exact .cons ⟨fi₁, by show exLogPrep.1.store.funcs[1]? = _; rw [hf]; rfl, hty⟩ .nil

/-- **`exLogI` is the spec instance of `exLog` at `exLogStore`.** -/
theorem exLog_isSpecInstanceAt :
    IsSpecInstanceAt exLogStore exLogXas exLog exLogMT exLogI exLogC₀ where
  valid := exLog_valid
  storeOk := exLogStore_ok
  importsOk := exLog_importsOk
  hostTyped := importStore_hostTyped exLog_importTypes
  prepared := ⟨exLogPrep.1, exLogPrep.2, exLog_prep, rfl, rfl, rfl⟩
  exportTypes := exLog_exportTypes

/-- The instance is well formed at its store. -/
theorem exLogI_wellFormed : exLogI.WellFormed exLogI.store := by
  have h := exLog_isSpecInstanceAt.ok.2
  rwa [exLog_isSpecInstanceAt.store_eq] at h

end Silmaril.Proofs.Wasm.Game.SharedExample
