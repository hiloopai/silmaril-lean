module

public import Silmaril.Wasm.Wasmi.Defs
public import Silmaril.Wasm.Interp.Thms
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# The reproducer of wasmi issue #2046 (proofs)

The behaviours of `f 5 1` in the reproducer store and in its translation, at every profile,
by `Silmaril.Wasm.Interp.native_adequacy`: the validation, allocation, native-profile and arity
checks and two native runs are kernel evaluations (`decide +kernel`, no native evaluation); the
typing of the stores comes from silmaril-lean's `prepare?_sound` and `Instantiate.ok`. The
translation of the store is the store of the translated module, by `rfl`.

`instantiate_of`, `invokeRun_mono` and `nbeh_eq_singleton` follow the proofs of
`Silmaril.Proofs.Wasm.Interp.Example` (another topic, whose proof modules are not imported here),
generalised to any closed module. New proofs.
-/

namespace Silmaril.Proofs.Wasm.Wasmi

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp Silmaril.Wasm.Wasmi

/-! ## Closed modules -/

/-- A closed module that validates and allocates without segments or start function
instantiates to its allocation, at every profile and host. -/
theorem instantiate_of {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none)
    (P : Numerics.Profile) (host : HostSemantics Empty) :
    Instantiate P host ({} : Store Empty) m [] p.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? m = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? m with _ | mt
    · simp [h] at hv
    · simp only [h, Option.map_some, Option.some.injEq] at hv
      exact ⟨mt, rfl, hv⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk m ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Empty)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  have h : Instantiate P host ({} : Store Empty) m [] (p.1.withStart p.2) :=
    (prepare?_sound (P := P) (host := host) (c := p.1) (st := p.2) evalConst?_evalSound
      hp hvalid).2
  have hw : p.1.withStart p.2 = p.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- The store of such an instance is typed. -/
theorem storeOk_of {m : Module} {p : Config Empty × Option FuncIdx}
    (hv : ((Validation.validate? m).map fun mt => mt.imports.isEmpty) = some true)
    (hp : prepare? evalConst? ({} : Store Empty) m [] = some p) (hst : p.2 = none) :
    StoreOk p.1.store := by
  have hc : ConfigOk p.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (instantiate_of hv hp hst (SingleThreaded.profile fun _ _ _ _ => false)
        SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

/-- Two `i32` arguments are a typed invocation of a function of type `[i32 i32] → [i32]`. -/
theorem invokeOk_of {s : Store Empty}
    (ht : (s.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
      some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)])) (x y : BitVec 32) :
    InvokeOk s 0 [Val.i32 x, Val.i32 y] := by
  obtain ⟨fi, hfi, hty⟩ : ∃ fi, s.funcs[0]? = some fi ∧
      Validation.DefType.funcType? fi.type =
        some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by
    rcases h : s.funcs[0]? with _ | fi
    · simp [h] at ht
    · exact ⟨fi, rfl, by simpa [h] using ht⟩
  unfold Validation.DefType.funcType? at hty
  split at hty
  · rename_i ps rs he
    simp only [Option.some.injEq, Prod.mk.injEq] at hty
    refine ⟨fi, ps, rs, hfi, Validation.Expand.iff.mpr he, ?_⟩
    rw [hty.1]
    exact .cons (ValOk.num _) (.cons (ValOk.num _) .nil)
  · cases hty

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

/-- The native behaviours of a terminating invocation are its single result. -/
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

/-! ## The reproducer and its translation -/

theorem repro_valid :
    ((Validation.validate? reproMod).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel
theorem reproW_valid :
    ((Validation.validate? reproModW).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel
theorem repro_some : (prepare? evalConst? ({} : Store Empty) reproMod []).isSome = true := by
  decide +kernel
theorem reproW_some : (prepare? evalConst? ({} : Store Empty) reproModW []).isSome = true := by
  decide +kernel
theorem repro_start : reproPrep.2.isNone = true := by decide +kernel
theorem reproW_start : reproPrepW.2.isNone = true := by decide +kernel
theorem repro_checks : nativeFuncsB reproStore.funcs = true ∧ storeChkB reproStore.funcs = true := by
  decide +kernel
theorem reproW_checks :
    nativeFuncsB reproStoreW.funcs = true ∧ storeChkB reproStoreW.funcs = true := by
  decide +kernel
theorem repro_type : (reproStore.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by decide +kernel
theorem reproW_type : (reproStoreW.funcs[0]?.bind fun fi => Validation.DefType.funcType? fi.type) =
    some ([.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]) := by decide +kernel

/-- The native run of `f 5 1` in the reproducer store: `7`. -/
theorem repro_run : ((Binaryen.invokeRun 20 reproStore 0 [Val.i32 5, Val.i32 1]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 7]) := by decide +kernel
/-- The native run of `f 5 1` in the translated store: `5`. -/
theorem reproW_run : ((Binaryen.invokeRun 20 reproStoreW 0 [Val.i32 5, Val.i32 1]).bind
    fun r => Binaryen.flowBeh r.2) = some (.returns [Val.i32 5]) := by decide +kernel

/-- **The translation of the reproducer store is the store of the translated module.** -/
theorem fuseStore_repro : fuseStore reproStore = reproStoreW := rfl

theorem repro_prep : prepare? evalConst? ({} : Store Empty) reproMod [] = some reproPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp repro_some
  simp [reproPrep, hp]

theorem reproW_prep : prepare? evalConst? ({} : Store Empty) reproModW [] = some reproPrepW := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp reproW_some
  simp [reproPrepW, hp]

theorem repro_storeOk : StoreOk reproStore :=
  storeOk_of repro_valid repro_prep (Option.isNone_iff_eq_none.mp repro_start)

theorem reproW_storeOk : StoreOk reproStoreW :=
  storeOk_of reproW_valid reproW_prep (Option.isNone_iff_eq_none.mp reproW_start)

/-- **The reproducer at every profile**: `f 5 1` returns `7` and does nothing else. -/
theorem core_f (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost reproStore 0 [Val.i32 5, Val.i32 1] =
      {.returns [Val.i32 7]} := by
  rw [native_adequacy repro_storeOk (nativeFuncsOk_of_check repro_checks.1)
    (storeChk_of_check repro_checks.2) (invokeOk_of repro_type 5 1)]
  exact nbeh_eq_singleton repro_run

/-- **The translated reproducer at every profile**: `f 5 1` returns `5` and does nothing
else. -/
theorem wasmi_f (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (fuseStore reproStore) 0 [Val.i32 5, Val.i32 1] =
      {.returns [Val.i32 5]} := by
  rw [fuseStore_repro, native_adequacy reproW_storeOk (nativeFuncsOk_of_check reproW_checks.1)
    (storeChk_of_check reproW_checks.2) (invokeOk_of reproW_type 5 1)]
  exact nbeh_eq_singleton reproW_run

end Silmaril.Proofs.Wasm.Wasmi
