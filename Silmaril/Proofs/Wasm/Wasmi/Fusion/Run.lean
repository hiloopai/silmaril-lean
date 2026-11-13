module

public import Silmaril.Wasm.Wasmi.Fusion.Defs
public import Silmaril.Wasm.Wasmi.Thms

/-!
# Runs of the probe's variants of the reproducer (proofs)

`behaviours_of`: the behaviours of `f 5 1` in `storeOf body` are a single behaviour `b`, at
every profile, from kernel evaluations of the validation, allocation, native-profile and arity
checks and of one native run (`Silmaril.Wasm.Interp.native_adequacy`, as for the reproducer in
`Silmaril.Proofs.Wasm.Wasmi.Repro`). The checks of the three variants and of their wider
translations are `decide +kernel`; the translated stores are the stores of the translated
modules by `rfl`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Fusion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Wasmi
open Silmaril.Wasm.Wasmi.Fusion
open Silmaril.Proofs.Wasm.Wasmi (storeOk_of invokeOk_of nbeh_eq_singleton)

/-- The checks of a variant store that give its behaviours on `f 5 1`. -/
structure Checks (body : List Instr) (b : Behaviour Val) : Prop where
  valid : ((Validation.validate? (modOf body)).map fun mt => mt.imports.isEmpty) = some true
  isSome : (prepare? evalConst? ({} : Store Empty) (modOf body) []).isSome = true
  start : (prepOf body).2.isNone = true
  native : nativeFuncsB (storeOf body).funcs = true ∧ storeChkB (storeOf body).funcs = true
  type : ((storeOf body).funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)])
  run : ((Binaryen.invokeRun 20 (storeOf body) 0 [Val.i32 5, Val.i32 1]).bind
    fun r => Binaryen.flowBeh r.2) = some b

/-- **The behaviours of `f 5 1`** in a checked variant store, at every profile. -/
theorem behaviours_of {body : List Instr} {b : Behaviour Val} (h : Checks body b)
    (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (storeOf body) 0 [Val.i32 5, Val.i32 1] = {b} := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h.isSome
  have hprep : prepare? evalConst? ({} : Store Empty) (modOf body) [] = some (prepOf body) := by
    simp [prepOf, hp]
  have hok : StoreOk (storeOf body) :=
    storeOk_of h.valid hprep (Option.isNone_iff_eq_none.mp h.start)
  rw [native_adequacy hok (nativeFuncsOk_of_check h.native.1) (storeChk_of_check h.native.2)
    (invokeOk_of h.type 5 1)]
  exact nbeh_eq_singleton h.run

theorem swap_checks : Checks swapBody (.returns [Val.i32 7]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
theorem eq_checks : Checks eqBody (.returns [Val.i32 5]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
theorem eqz_checks : Checks eqzBody (.returns [Val.i32 5]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
theorem swapW_checks : Checks (fuseW swapBody) (.returns [Val.i32 5]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
theorem eqW_checks : Checks (fuseW eqBody) (.returns [Val.i32 7]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩
theorem eqzW_checks : Checks (fuseW eqzBody) (.returns [Val.i32 7]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- The wider translation of a variant store is the store of the translated module. -/
theorem fuseStoreW_swap : fuseStoreW (storeOf swapBody) = storeOf (fuseW swapBody) := rfl
theorem fuseStoreW_eq : fuseStoreW (storeOf eqBody) = storeOf (fuseW eqBody) := rfl
theorem fuseStoreW_eqz : fuseStoreW (storeOf eqzBody) = storeOf (fuseW eqzBody) := rfl
/-- On the reproducer the wider translation is `fuse`. -/
theorem fuseStoreW_repro : fuseStoreW reproStore = reproStoreW := rfl

/-- The variants have no `fuse` shape, so the model of `Silmaril.Wasm.Wasmi` leaves them alone. -/
theorem swap_patFree : StorePatFree (storeOf swapBody) := by
  intro fi hfi g hg
  have hf : (storeOf swapBody).funcs.all (fun fi => match fi.code with
      | .wasm g => patFree g.body | .host _ => true) = true := by decide +kernel
  have := List.all_eq_true.mp hf fi hfi
  simpa [hg] using this
theorem eq_patFree : StorePatFree (storeOf eqBody) := by
  intro fi hfi g hg
  have hf : (storeOf eqBody).funcs.all (fun fi => match fi.code with
      | .wasm g => patFree g.body | .host _ => true) = true := by decide +kernel
  have := List.all_eq_true.mp hf fi hfi
  simpa [hg] using this
theorem eqz_patFree : StorePatFree (storeOf eqzBody) := by
  intro fi hfi g hg
  have hf : (storeOf eqzBody).funcs.all (fun fi => match fi.code with
      | .wasm g => patFree g.body | .host _ => true) = true := by decide +kernel
  have := List.all_eq_true.mp hf fi hfi
  simpa [hg] using this

end Silmaril.Proofs.Wasm.Wasmi.Fusion
