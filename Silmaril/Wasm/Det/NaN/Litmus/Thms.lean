module

public import Silmaril.Wasm.Det.NaN.Litmus.Defs
public import Silmaril.Wasm.Det.NaN.Thms
public import Silmaril.Proofs.Wasm.Det.NaN.Litmus

/-!
# Litmus tests for determinism up to NaN payloads: theorems

For `nanMod` (`raw`: the sum of two `f32`s; `guard`: the sum, or `0` if it is a NaN; `cmp`:
`sum < 1`), allocated into `nanStore`:

* `nanStore_check`, `nanDet_module`: the store passes the fragment check, so every function is
  deterministic up to NaN payloads at every profile (tactic `nan_det`); `bits_rejected`: a
  function returning `i32.reinterpret_f32` of the sum is rejected by the check;
* `raw_not_det`, `not_detModule`: at every profile with the specification's NaN semantics
  (`P.nan = .spec`), `raw` on two canonical NaNs returns both `+nan` and `-nan`, so neither
  `raw` nor the module is deterministic modulo traps and imports: the counterexample is two
  explicit Core runs;
* `guard_det`, `cmp_det`: at **every** profile and every call state of the module, `guard`
  and `cmp` are deterministic modulo traps and imports (`DetFn`): the NaN check of `guard`
  and the comparison of `cmp` keep NaN payloads away from the output. The verification
  condition `NaNFreeOut` is discharged by one explicit run at the deterministic profile
  (`nanFreeOut_of_canonical`).

So `guard` and `cmp` are per-function litmus tests: deterministic where the module is not.

Proofs: `Silmaril.Proofs.Wasm.Det.NaN.Litmus`. New.
-/

@[expose] public section

namespace Silmaril.Wasm.Det.NaN.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Det.Core
  Silmaril.Wasm.Det.NaN
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Det.NaN.Litmus (shape_spec shape0 shape1 shape2 rawB_eq guardB_eq cmpB_eq
  expand_of_funcType? args_f32 steps_invoke guard_body cmp_body raw_body nanP_allowed
  nanN_allowed)

/-- `nanStore` passes the fragment check (no `global.set`). -/
theorem nanStore_check : nanCheck false nanStore = true := by decide +kernel

/-- `nan_det` on a single function. -/
example (P : Profile) : NaNDetFn P nanStore 0 := by nan_det

/-- **Every function of the module is deterministic up to NaN payloads**, at every profile. -/
theorem nanDet_module (P : Profile) : NaNDetModule P nanEntry nanStore := by nan_det

/-- **A bit sink is rejected**: reinterpreting the sum as an `i32` is not in the fragment. -/
theorem bits_rejected : nanInstrs true bitsBody = false := by decide

/-- The call states of the module are its initial store. -/
theorem nanReach_eq {P : Profile} {s : Store Nat} (h : CallReach P nanEntry nanStore s) :
    s = nanStore :=
  callReach_eq nanStore_check h

/-- An invocation of a function with two `f32` parameters whose body runs at the deterministic
profile to a NaN-free value has NaN-free outputs at every profile. -/
theorem nanFreeOut_of_body {P : Profile} {i : Nat} {body : List Instr → Bool}
    {locals : List ValType} {rs' : List Validation.CValType}
    (hsh : nanStore.funcs[i]?.map (shapeOk body locals ([.num (.float .f32), .num (.float .f32)],
      rs')) = some true) (hrs : rs'.length = 1) {x y : BitVec 32}
    (hbody : ∀ fi fn, nanStore.funcs[i]? = some fi → fi.code = .wasm fn → body fn.body = true →
      fn.locals = locals → ∃ v f', Steps (profile neverFail) Det.noHost
        ⟨nanStore, Frame.forCall fi.module [f32v x, f32v y] fn.locals, expression fn.body⟩
        ⟨nanStore, f', vals [v]⟩ ∧ nanVal v = false) :
    NaNFreeOut P (invoke nanStore i [f32v x, f32v y]) := by
  obtain ⟨fi, fn, hfi, hcode, hb, hloc, hty⟩ := shape_spec hsh
  obtain ⟨ps, rs, he, hps, hrs'⟩ := expand_of_funcType? hty
  obtain ⟨v, f', hrun, hv⟩ := hbody fi fn hfi hcode hb hloc
  have hpl : [f32v x, f32v y].length = ps.length := by
    show 2 = ps.toList.length
    rw [hps]
    rfl
  have hout : [v].length = rs.length := by
    show 1 = rs.toList.length
    rw [hrs', hrs]
  have hinv : Steps (profile neverFail) Det.noHost (invoke nanStore i [f32v x, f32v y])
      ⟨nanStore, {}, vals [v]⟩ := steps_invoke hfi he hpl hcode hrun hout
  have hc : NCfg false (invoke nanStore i [f32v x, f32v y]) :=
    Silmaril.Proofs.Wasm.Det.NaN.nCfg_invoke (nFuncs_of_nanCheck nanStore_check) i _
  refine nanFreeOut_of_canonical hc hinv (r := .values [v]) (.ret (by simp) rfl) ?_
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact hv

/-- **`guard` is deterministic modulo traps and imports**, at every profile, at every call
state of the module. -/
theorem guard_det (P : Profile) {s : Store Nat} (hs : CallReach P nanEntry nanStore s) :
    DetFn P s 1 := by
  rw [nanReach_eq hs]
  refine detFn_of_nanCheck nanStore_check fun vs hok => ?_
  obtain ⟨fi, fn, hfi, -, -, -, hty⟩ := shape_spec shape1
  obtain ⟨x, y, rfl⟩ := args_f32 hfi hty hok
  refine nanFreeOut_of_body shape1 rfl fun fi' fn' _ _ hb hloc => ?_
  rw [guardB_eq hb, hloc]
  exact guard_body nanStore fi'.module x y

/-- **`cmp` is deterministic modulo traps and imports**, at every profile, at every call
state of the module. -/
theorem cmp_det (P : Profile) {s : Store Nat} (hs : CallReach P nanEntry nanStore s) :
    DetFn P s 2 := by
  rw [nanReach_eq hs]
  refine detFn_of_nanCheck nanStore_check fun vs hok => ?_
  obtain ⟨fi, fn, hfi, -, -, -, hty⟩ := shape_spec shape2
  obtain ⟨x, y, rfl⟩ := args_f32 hfi hty hok
  refine nanFreeOut_of_body shape2 rfl fun fi' fn' _ _ hb hloc => ?_
  rw [cmpB_eq hb, hloc]
  exact cmp_body nanStore fi'.module x y

/-- `raw` on two canonical NaNs returns every sum the profile allows. -/
theorem raw_run {P : Profile} (hP : P.nan = .spec) {z : BitVec 32}
    (hz : Numerics.floatBinOpRel .f32 .add nanP nanP z) :
    Steps P Det.noHost (invoke nanStore 0 [f32v nanP, f32v nanP]) ⟨nanStore, {}, vals [f32v z]⟩ := by
  obtain ⟨fi, fn, hfi, hcode, hb, hloc, hty⟩ := shape_spec shape0
  obtain ⟨ps, rs, he, hps, hrs⟩ := expand_of_funcType? hty
  have hpl : [f32v nanP, f32v nanP].length = ps.length := by
    show 2 = ps.toList.length
    rw [hps]
    rfl
  have hout : [f32v z].length = rs.length := by
    show 1 = rs.toList.length
    rw [hrs]
    rfl
  have hrun : Steps P Det.noHost
      ⟨nanStore, Frame.forCall fi.module [f32v nanP, f32v nanP] fn.locals, expression fn.body⟩
      ⟨nanStore, Frame.forCall fi.module [f32v nanP, f32v nanP] fn.locals, vals [f32v z]⟩ := by
    rw [rawB_eq hb, hloc]
    exact raw_body hP nanStore fi.module hz
  exact steps_invoke hfi he hpl hcode hrun hout

/-- `raw` accepts two `f32` arguments. -/
theorem raw_invokeOk : InvokeOk nanStore 0 [f32v nanP, f32v nanP] := by
  obtain ⟨fi, -, hfi, -, -, -, hty⟩ := shape_spec shape0
  obtain ⟨ps, rs, he, hps, -⟩ := expand_of_funcType? hty
  refine ⟨fi, ps, rs, hfi, he, ?_⟩
  rw [hps]
  exact .cons (.num _) (.cons (.num _) .nil)

/-- **`raw` is not deterministic** at a profile with the specification's NaN semantics: it
returns `+nan` and `-nan` for `nan + nan`. -/
theorem raw_not_det {P : Profile} (hP : P.nan = .spec) :
    ¬ DetCall P nanStore 0 [f32v nanP, f32v nanP] := by
  intro hD
  have h := hD [] _ _ _ _ (.stop (raw_run hP nanP_allowed)) (.stop (raw_run hP nanN_allowed))
    (.ret (r := .values [f32v nanP]) (by simp) rfl)
    (.ret (r := .values [f32v nanN]) (by simp) rfl)
  have h₁ : Out.ret (.values [f32v nanP]) = Out.ret (.values [f32v nanN]) := h.1
  have h₂ : (⟨.float .f32, nanP⟩ : NumVal) = ⟨.float .f32, nanN⟩ := by
    simpa only [Out.ret.injEq, Result.values.injEq, List.cons.injEq, and_true, f32v,
      Val.num.injEq] using h₁
  have h₃ : nanP.toNat = nanN.toNat := congrArg (fun v : NumVal => v.bits.toNat) h₂
  exact absurd h₃ (by decide)

/-- **The module is not deterministic** at a profile with the specification's NaN semantics,
although `guard` and `cmp` are (`guard_det`, `cmp_det`). -/
theorem not_detModule {P : Profile} (hP : P.nan = .spec) : ¬ DetModule P nanEntry nanStore :=
  fun hD => raw_not_det hP (hD nanStore .init 0 (show 0 < 3 by decide) _ raw_invokeOk)

end Silmaril.Wasm.Det.NaN.Litmus
