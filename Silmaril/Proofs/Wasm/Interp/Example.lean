module

public import Silmaril.Wasm.Interp.Example.Defs
public import Silmaril.Proofs.Wasm.Interp.Check
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# A closed module for native adequacy (proofs)

The validation, the allocation and the store of `exMod` are computed by kernel evaluation of
silmaril-lean's `validate?` and `prepare?` (`decide +kernel` on Boolean summaries; no
compiled evaluation), and so are the executable checks `nativeFuncsB` and `storeChkB` and two runs
of the native interpreter. The typing of the store comes from silmaril-lean's
`prepare?_sound` and `Instantiate.ok`. New proofs.
-/

namespace Silmaril.Proofs.Wasm.Interp.Example

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Interp.Example

/-- `exMod` validates, without imports. -/
theorem exMod_valid : ((Validation.validate? exMod).map fun mt => mt.imports.isEmpty) = some true :=
  by decide +kernel
/-- The allocation succeeds. -/
theorem exPrep_some : (prepare? evalConst? ({} : Store Empty) exMod []).isSome = true :=
  by decide +kernel
/-- No segment code and no start function. -/
theorem exPrep_shape : exPrep.1.code.isEmpty = true ∧ exPrep.2.isNone = true := by decide +kernel
/-- The executable native-profile check. -/
theorem exStore_native : nativeFuncsB exStore.funcs = true := by decide +kernel
/-- The executable arity check. -/
theorem exStore_chk : storeChkB exStore.funcs = true := by decide +kernel
/-- The type of function `0`. -/
theorem exStore_type : (exStore.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by decide +kernel
/-- Two native runs. -/
theorem exRun_07 : ((Binaryen.invokeRun 20 exStore 0 [Val.i32 0, Val.i32 7]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 7]) := by decide +kernel
theorem exRun_37 : ((Binaryen.invokeRun 20 exStore 0 [Val.i32 3, Val.i32 7]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 3]) := by decide +kernel

/-- The allocation, as an equation. -/
theorem exPrep_eq : prepare? evalConst? ({} : Store Empty) exMod [] = some exPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp exPrep_some
  simp [exPrep, hp]

/-- **`exMod` instantiates to `exPrep.1`**, at every profile and host. -/
theorem ex_instantiate (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) exMod [] exPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? exMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? exMod with _ | mt
    · have hm := exMod_valid
      simp [h] at hm
    · have hm := exMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk exMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have hst : exPrep.2 = none := Option.isNone_iff_eq_none.mp exPrep_shape.2
  have h : Instantiate P host ({} : Store Empty) exMod [] (exPrep.1.withStart exPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := exPrep.1) (st := exPrep.2) evalConst?_evalSound
      exPrep_eq hvalid).2
  have hw : exPrep.1.withStart exPrep.2 = exPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem exStore_ok : StoreOk exStore := by
  have hc : ConfigOk exPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (ex_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- **Two `i32` arguments are a typed invocation of function `0`.** -/
theorem ex_invokeOk (x y : BitVec 32) : InvokeOk exStore 0 [Val.i32 x, Val.i32 y] := by
  obtain ⟨fi, hfi, hty⟩ : ∃ fi, exStore.funcs[0]? = some fi ∧
      Validation.DefType.funcType? fi.type =
        some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by
    rcases h : exStore.funcs[0]? with _ | fi
    · have ht := exStore_type
      simp [h] at ht
    · exact ⟨fi, rfl, by simpa [h] using exStore_type⟩
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at hty
    refine ⟨fi, ps, rs, hfi, Validation.Expand.iff.mpr he, ?_⟩
    rw [hty.1]
    exact .cons (ValOk.num _) (.cons (ValOk.num _) .nil)
  · cases hty

/-! ## Native behaviours of a terminating invocation -/

/-- More fuel never changes a result of `invokeRun`. -/
theorem invokeRun_mono {H : Type} {n n' : Nat} (hle : n ≤ n') {s : Store H} {a : Nat}
    {vs : List Val} {r : Store H × Binaryen.Flow} (h : Binaryen.invokeRun n s a vs = some r) :
    Binaryen.invokeRun n' s a vs = some r := by
  unfold Binaryen.invokeRun at h ⊢
  split at h
  · split at h
    · rename_i fn _ rs _ _
      rcases hr : Binaryen.run n s _ [] (Binaryen.liftInstrs fn.body) with _ | x
      · rw [hr] at h
        cases h
      · rw [hr] at h
        rw [Binaryen.run_mono hle hr]
        exact h
    · cases h
  · cases h

/-- **The native behaviours of a terminating invocation** are its single result. -/
theorem nbeh_eq_singleton {H : Type} {s : Store H} {a : Nat} {vs : List Val} {n : Nat}
    {b : Behaviour Val} (h : ((Binaryen.invokeRun n s a vs).bind fun r => Binaryen.flowBeh r.2) =
      some b) : Binaryen.nbeh s a vs = {b} := by
  obtain ⟨⟨s₀, fl₀⟩, h₀, hb₀⟩ := Option.bind_eq_some_iff.mp h
  ext b'
  constructor
  · rintro (⟨m, s₁, fl₁, h₁, hb₁⟩ | ⟨-, hdiv⟩)
    · have e₀ : Binaryen.invokeRun (max n m) s a vs = some (s₀, fl₀) :=
        invokeRun_mono (Nat.le_max_left n m) h₀
      have e₁ : Binaryen.invokeRun (max n m) s a vs = some (s₁, fl₁) :=
        invokeRun_mono (Nat.le_max_right n m) h₁
      have hfl : fl₁ = fl₀ := by
        rw [e₀] at e₁
        exact (Prod.mk.inj (Option.some.inj e₁)).2.symm
      have hb : some b' = some b := by rw [← hb₁, ← hb₀, hfl]
      exact Option.some.inj hb
    · rw [hdiv n] at h₀
      cases h₀
  · rintro rfl
    exact .inl ⟨n, s₀, fl₀, h₀, hb₀⟩

end Silmaril.Proofs.Wasm.Interp.Example
