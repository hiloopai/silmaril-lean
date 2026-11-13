module

public import Silmaril.Wasm.Models.FunInst.Defs
public import Silmaril.Wasm.Models.FunCompile.Thms
public import Silmaril.Wasm.Models.FunRefCompile.Thms
public import Silmaril.Wasm.Execution.Core.Exec.PrepareDirect
public import Silmaril.Proofs.Wasm.Models.FunInst.Main

/-!
# Instantiating the compiled FunLang and FunRef modules

For both compilers, silmaril's executable direct instantiation of `moduleOf p` in the empty
store, without imports, returns `storeX p`. This is `storeOf p` with the export of `main`
recorded in the module instance (`instantiate_funCompile`, `instantiate_funRefCompile`). For
an accepted program the prepared configuration is an `Instantiate` configuration of silmaril's
relational `$instantiate`, which runs to `storeX p` (`instantiate_funCompile_spec`,
`instantiate_funRefCompile_spec`).

The behaviours of `main` in the instantiated store are those of `behaviours_compile`
(`behaviours_funCompileX`, `behaviours_funRefCompileX`). Exactly one behaviour returns the
program's word, at every profile and for every host.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunInst

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

/-! ## FunLang -/

theorem allocTypes_fun : allocTypes FunCompile.recTypes = FunCompile.modTypes := by decide

/-- **Instantiating the compiled FunLang module yields `storeX p`**: `main` at address `0` with
the instance `instX`, and no start function. -/
theorem instantiate_funCompile (p : FunLang.Prog) :
    instantiateDirect? ({} : Store Nat) (FunCompile.moduleOf p) [] =
      some (FunCompile.storeX p, { module := FunCompile.instX }, none) := by
  simp [instantiateDirect?, prepareDirect?, prepare?, FunCompile.moduleOf, evalGlobals?,
    evalExprs?, evalExprss?, allocModule?, allocTypes_fun, initSegments?, initElem?, initData?,
    allocMany, allocFunc, allocExport?, FunCompile.instX, FunCompile.instOf,
    FunCompile.modTypes, ModuleInst.initial, FunCompile.funcOf, Idx.toNat, ExternAddr.funcs,
    ExternAddr.tags, ExternAddr.globals, ExternAddr.mems, ExternAddr.tables, initElemList?,
    initDataList?, FunCompile.storeX, FunCompile.mainInstX]

/-- Instantiation of the compiled FunLang module on the specification side. -/
theorem instantiate_funCompile_spec (P : Profile) (host : HostSemantics Nat) {p : FunLang.Prog}
    (hp : p.Ok) :
    ∃ c, prepare? evalConst? ({} : Store Nat) (FunCompile.moduleOf p) [] = some (c, none) ∧
      Instantiate P host {} (FunCompile.moduleOf p) [] (c.withStart none) ∧
      Steps P host (c.withStart none)
        ⟨FunCompile.storeX p, { module := FunCompile.instX }, startCode none⟩ := by
  obtain ⟨mt, hok⟩ := (FunCompile.moduleOf_valid hp).1
  have hxt : mt.imports = [] := by
    cases hok with
    | mk htypes himports => cases himports; rfl
  obtain ⟨c, hc, -, hi, hs⟩ := instantiateDirect?_sound (P := P) (host := host)
    (instantiate_funCompile p) ⟨mt.exports, [], hxt ▸ hok, .nil⟩
  exact ⟨c, hc, hi, hs⟩

/-- **The behaviours of the instantiated FunLang module**: exactly one, returning the program's
word, at every profile and for every host. -/
theorem behaviours_funCompileX (P : Profile) (host : HostSemantics Nat) {p : FunLang.Prog}
    (hp : p.Ok) (n : BitVec 31) :
    behaviours P host (FunCompile.storeX p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunInst.behaviours_mainX P host hp.1 hp.2 n

/-! ## FunRef -/

theorem allocTypes_funRef : allocTypes FunRefCompile.recTypes = FunRefCompile.modTypes := by
  decide

/-- **Instantiating the compiled FunRef module yields `storeX p`.** -/
theorem instantiate_funRefCompile (p : FunRef.Prog) :
    instantiateDirect? ({} : Store Nat) (FunRefCompile.moduleOf p) [] =
      some (FunRefCompile.storeX p, { module := FunRefCompile.instX }, none) := by
  simp [instantiateDirect?, prepareDirect?, prepare?, FunRefCompile.moduleOf, evalGlobals?,
    evalExprs?, evalExprss?, allocModule?, allocTypes_funRef, initSegments?, initElem?,
    initData?, allocMany, allocFunc, allocExport?, FunRefCompile.instX, FunRefCompile.instOf,
    FunRefCompile.modTypes, ModuleInst.initial, FunRefCompile.funcOf, Idx.toNat,
    ExternAddr.funcs, ExternAddr.tags, ExternAddr.globals, ExternAddr.mems, ExternAddr.tables,
    initElemList?, initDataList?, FunRefCompile.storeX, FunRefCompile.mainInstX]

/-- Instantiation of the compiled FunRef module on the specification side. -/
theorem instantiate_funRefCompile_spec (P : Profile) (host : HostSemantics Nat)
    {p : FunRef.Prog} (hp : p.Ok) :
    ∃ c, prepare? evalConst? ({} : Store Nat) (FunRefCompile.moduleOf p) [] = some (c, none) ∧
      Instantiate P host {} (FunRefCompile.moduleOf p) [] (c.withStart none) ∧
      Steps P host (c.withStart none)
        ⟨FunRefCompile.storeX p, { module := FunRefCompile.instX }, startCode none⟩ := by
  obtain ⟨mt, hok⟩ := (FunRefCompile.moduleOf_valid hp).1
  have hxt : mt.imports = [] := by
    cases hok with
    | mk htypes himports => cases himports; rfl
  obtain ⟨c, hc, -, hi, hs⟩ := instantiateDirect?_sound (P := P) (host := host)
    (instantiate_funRefCompile p) ⟨mt.exports, [], hxt ▸ hok, .nil⟩
  exact ⟨c, hc, hi, hs⟩

/-- **The behaviours of the instantiated FunRef module.** -/
theorem behaviours_funRefCompileX (P : Profile) (host : HostSemantics Nat) {p : FunRef.Prog}
    (hp : p.Ok) (n : BitVec 31) :
    behaviours P host (FunRefCompile.storeX p) 0 [.i32 (n.setWidth 32)] =
      {.returns [.i32 ((p.word n).setWidth 32)]} :=
  Silmaril.Proofs.Wasm.Models.FunInst.behaviours_mainRX P host hp.1 hp.2 n

end Silmaril.Wasm.Models.FunInst
