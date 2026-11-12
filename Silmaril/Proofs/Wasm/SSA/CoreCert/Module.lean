module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Func
public import Silmaril.Wasm.Binaryen.AdequacyModule
public import Silmaril.Wasm.Binaryen.Uniform
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-!
# The run-time certificate of a closed module (proofs)

`prepare_code`: in the store that silmaril's executable instantiation `prepare?` allocates for a
validated module without imports, the function at address `g` has the code of the module's
function `g` (silmaril's `alloc_funcs`); `prepare_storeOk`: that store is typed
(`prepare?_sound`, `Instantiate.ok`). `coreChecked_spec`: when `optimizeFuncCoreChecked m g`
returns `bf'`, the allocated stores of `m` and of `m.setFunc g bf'` satisfy every hypothesis of
`invoke_replace` at address `g`, so invocations of function `g` have the same Core 3.0
behaviours in both, at every profile. New proofs.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SSA

variable {H : Type}

/-- A closed validated module: its type, without imports. -/
theorem closed_type {M : Module}
    (hv : ((Validation.validate? M).map fun mt => mt.imports.isEmpty) = some true) :
    ∃ mt, Validation.validate? M = some mt ∧ mt.imports = [] := by
  rcases h : Validation.validate? M with _ | mt
  · rw [h] at hv
    cases hv
  · rw [h, Option.map_some, Option.some.injEq] at hv
    exact ⟨mt, rfl, List.isEmpty_iff.mp hv⟩

/-- `prepare?` of a closed validated module is a Core 3.0 instantiation. -/
theorem prepare_instantiate {M : Module} {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? ({} : Store H) M [] = some (c, st))
    (hv : ((Validation.validate? M).map fun mt => mt.imports.isEmpty) = some true)
    (P : Numerics.Profile) (host : HostSemantics H) :
    Instantiate P host ({} : Store H) M [] (c.withStart st) := by
  obtain ⟨mt, hmt, himp⟩ := closed_type hv
  have hvalid : ∃ xtE xtI, Validation.ModuleOk M ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store H)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt, by rw [himp]; exact .nil⟩
  exact (prepare?_sound (P := P) (host := host) evalConst?_evalSound hp hvalid).2

theorem withStart_store (c : Config H) (st : Option FuncIdx) : (c.withStart st).store = c.store := by
  cases st <;> rfl

/-- **The allocated store of a closed validated module is typed.** -/
theorem prepare_storeOk {M : Module} {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? ({} : Store H) M [] = some (c, st))
    (hv : ((Validation.validate? M).map fun mt => mt.imports.isEmpty) = some true) :
    StoreOk c.store := by
  have hc : ConfigOk (c.withStart st) [] :=
    Instantiate.ok SingleThreaded.divHost_ok storeOk_empty
      (prepare_instantiate hp hv (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  rw [← withStart_store c st]
  exact SingleThreaded.ConfigOk.storeOk hc

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) : ∀ {i : Nat} {x : α}, l₁[i]? = some x → ∃ y, l₂[i]? = some y := by
  induction h with
  | nil => intro i x hx; simp at hx
  | cons _ _ ih =>
    intro i x hx
    rcases i with _ | i
    · exact ⟨_, rfl⟩
    · exact ih hx

/-- **The allocated store holds the module's functions at their indices.** -/
theorem prepare_code {M : Module} {c : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? ({} : Store H) M [] = some (c, st))
    (hv : ((Validation.validate? M).map fun mt => mt.imports.isEmpty) = some true)
    {g : Nat} {fn : Func} (hg : M.funcs[g]? = some fn) :
    ∃ fi, c.store.funcs[g]? = some fi ∧ fi.code = .wasm fn := by
  have hi := prepare_instantiate hp hv (SingleThreaded.profile fun _ _ _ _ => false)
    SingleThreaded.divHost
  obtain ⟨_, _, hm, hxas⟩ := hi.valid
  obtain ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi', hg', ht, he, ha, hc⟩ := hi.run
  have hstore : c.store = s₄ := by rw [← withStart_store c st, hc]
  cases hm with
  | mk htypes himports hC' hC htags hglobals _ htables hfuncs _ helems _ _ _ =>
  have hF := alloc_funcs htypes himports hC' hC htags hglobals htables hfuncs helems hxas
    hg' ht he ha
  rw [hstore, hF]
  obtain ⟨d, hd⟩ := forall₂_getElem? hfuncs hg
  exact ⟨⟨d, mi', .wasm fn⟩, by simp [List.getElem?_zip_eq_some, hd, hg], rfl⟩

/-! ## The certificate -/

theorem lower_funcs {m : BModule} {g : Nat} {bf : BFunc} (h : m.funcs[g]? = some bf) :
    m.lower.funcs[g]? = some (coreFunc bf) := by
  simp [BModule.lower, h]

theorem setFunc_lower_funcs {m : BModule} {g : Nat} {bf bf' : BFunc} (h : m.funcs[g]? = some bf) :
    (m.setFunc g bf').lower.funcs[g]? = some (coreFunc bf') := by
  simp [BModule.lower, BModule.setFunc, BodyReplacement.getElem?_modifyAt, h]

theorem allocStore?_inv {m : BModule} {s : Store Empty} (h : allocStore? m = some s) :
    ∃ c st, prepare? evalConst? ({} : Store Empty) m.lower [] = some (c, st) ∧ c.store = s := by
  obtain ⟨⟨c, st⟩, hp, hs⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c, st, hp, hs⟩

theorem typeAt_inv {s : Store H} {a : Nat} {ft : FuncType} (h : typeAt s a ft = true) :
    ∃ fi, s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type =
      some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal) := by
  unfold typeAt at h
  split at h
  · rename_i fi hfi
    exact ⟨fi, hfi, beq_iff_eq.mp h⟩
  · cases h

/-- **The allocated store of a closed validated module is that of a Core 3.0 instantiation**, at
every profile and host. -/
theorem allocStore?_instantiate {m : BModule} {s : Store Empty} (hs : allocStore? m = some s)
    (hv : closedValid m = true) :
    ∃ c : Config Empty, c.store = s ∧ ∀ (P : Numerics.Profile) (host : HostSemantics Empty),
      Instantiate P host ({} : Store Empty) m.lower [] c := by
  obtain ⟨c, st, hp, rfl⟩ := allocStore?_inv hs
  exact ⟨c.withStart st, withStart_store c st,
    fun P host => prepare_instantiate hp (beq_iff_eq.mp hv) P host⟩

/-- What `storeReady` checked. -/
theorem storeReady_inv {s : Store H} {a : Nat} {ft : FuncType} (h : storeReady s a ft = true) :
    Silmaril.Wasm.Interp.StoreChk s.funcs ∧ NativeFuncsOk s.funcs ∧ ∃ fi, s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type =
        some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal) := by
  simp only [storeReady, Bool.and_eq_true] at h
  exact ⟨Silmaril.Wasm.Interp.storeChk_of_check h.1.1, Silmaril.Wasm.Interp.nativeFuncsOk_of_check h.1.2,
    typeAt_inv h.2⟩

/-- A store allocated for a checked closed module, with its function `g`. -/
theorem checked_store {m : BModule} {g : Nat} {bf : BFunc} {ft : FuncType} {s : Store Empty}
    (hbf : m.lower.funcs[g]? = some (coreFunc bf)) (hs : allocStore? m = some s)
    (hv : closedValid m = true) (hr : storeReady s g ft = true) :
    StoreOk s ∧ Silmaril.Wasm.Interp.StoreChk s.funcs ∧ NativeFuncsOk s.funcs ∧
      ∃ fi, s.funcs[g]? = some fi ∧ fi.code = .wasm (coreFunc bf) ∧
        Validation.DefType.funcType? fi.type =
          some (ft.params.map Validation.liftVal, ft.results.map Validation.liftVal) := by
  obtain ⟨c, st, hp, rfl⟩ := allocStore?_inv hs
  have hv' : ((Validation.validate? m.lower).map fun mt => mt.imports.isEmpty) = some true :=
    beq_iff_eq.mp hv
  obtain ⟨hS, hF, fi, hfi, hty⟩ := storeReady_inv hr
  obtain ⟨fi', hfi', hcode⟩ := prepare_code hp hv' hbf
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  exact ⟨prepare_storeOk hp hv', hS, hF, fi', hfi, hcode, hty⟩

/-- What `optimizeFuncCoreChecked` checked. -/
theorem optimizeFuncCoreChecked_inv {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    ∃ bf ft s s', m.funcs[g]? = some bf ∧ m.funcType? bf.type = some ft ∧
      optimizeFuncCore? ft bf = some bf' ∧ allocStore? m = some s ∧
      allocStore? (m.setFunc g bf') = some s' ∧ closedValid m = true ∧
      closedValid (m.setFunc g bf') = true ∧ storeReady s g ft = true ∧
      storeReady s' g ft = true := by
  simp only [optimizeFuncCoreChecked, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨bf, hbf, ft, hft, bf'', ho, s, hs, s', hs', hif⟩ := h
  split at hif
  · rename_i hc
    obtain rfl : bf'' = bf' := Option.some.inj hif
    simp only [Bool.and_eq_true] at hc
    exact ⟨bf, ft, s, s', hbf, hft, ho, hs, hs', hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
  · cases hif

/-- **The run-time certificate is sound**: invocations of function `g` have the same Core 3.0
behaviours in the allocated stores of the module and of the module with the replacement, at
every profile, divergence included. -/
theorem coreChecked_spec {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') :
    ∃ s s' : Store Empty, allocStore? m = some s ∧ allocStore? (m.setFunc g bf') = some s' ∧
      ∀ (P : Numerics.Profile) (vs : List Val), InvokeOk s g vs →
        behaviours P closedHost s g vs = behaviours P closedHost s' g vs := by
  obtain ⟨bf, ft, s, s', hbf, -, ho, hs, hs', hv, hv', hr, hr'⟩ := optimizeFuncCoreChecked_inv h
  obtain ⟨hok, hS, hF, fi, hfi, hcode, hty⟩ := checked_store (lower_funcs hbf) hs hv hr
  obtain ⟨hok', hS', hF', fi', hfi', hcode', hty'⟩ :=
    checked_store (setFunc_lower_funcs hbf) hs' hv' hr'
  exact ⟨s, s', hs, hs', fun P vs hinv =>
    invoke_replace hok hF hS hok' hF' hS' hfi hcode hty hfi' hcode' hty' ho hinv P⟩

/-- **The certificate against any module holding the replacement**: if `m'` is closed, valid,
holds `bf'` as function `g` and its allocated store passes the executable checks at `g`, then
invocations of `g` have the same Core 3.0 behaviours in the allocated stores of `m` and `m'`. -/
theorem coreChecked_replace {m : BModule} {g : Nat} {bf' : BFunc}
    (h : optimizeFuncCoreChecked m g = some bf') {m' : BModule} {s' : Store Empty}
    (hv' : closedValid m' = true) (hs' : allocStore? m' = some s')
    (hcode' : m'.funcs[g]? = some bf')
    (hr' : ∀ bf ft, m.funcs[g]? = some bf → m.funcType? bf.type = some ft →
      storeReady s' g ft = true) :
    ∃ s : Store Empty, allocStore? m = some s ∧ ∀ (P : Numerics.Profile) (vs : List Val),
      InvokeOk s g vs → behaviours P closedHost s g vs = behaviours P closedHost s' g vs := by
  obtain ⟨bf, ft, s, -, hbf, hft, ho, hs, -, hv, -, hr, -⟩ := optimizeFuncCoreChecked_inv h
  obtain ⟨hok, hS, hF, fi, hfi, hcode, hty⟩ := checked_store (lower_funcs hbf) hs hv hr
  obtain ⟨hok', hS', hF', fi', hfi', hc', hty'⟩ :=
    checked_store (lower_funcs hcode') hs' hv' (hr' bf ft hbf hft)
  exact ⟨s, hs, fun P vs hinv =>
    invoke_replace hok hF hS hok' hF' hS' hfi hcode hty hfi' hc' hty' ho hinv P⟩

/-! ## Lambda-SSA functions compiled to Core -/

/-- What `compileCore?` checked. -/
theorem compileCore?_inv {f : SFunc} {s : Store Empty} (h : compileCore? f = some s) :
    ∃ g bf, decompileFunc f = some g ∧ toBFunc? ⟨0⟩ g = some bf ∧ g.native = true ∧
      coreReady (sigType g.params g.result) bf = true ∧
      closedValid (soloModule (sigType g.params g.result) bf) = true ∧
      allocStore? (soloModule (sigType g.params g.result) bf) = some s ∧
      storeReady s 0 (sigType g.params g.result) = true := by
  simp only [compileCore?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨g, hg, bf, hbf, hif⟩ := h
  split at hif
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨s', hs', hif'⟩ := Option.bind_eq_some_iff.mp hif
    split at hif'
    · obtain rfl : s' = s := Option.some.inj hif'
      exact ⟨g, bf, hg, hbf, hc.1.1, hc.1.2, hc.2, hs', ‹_›⟩
    · cases hif'
  · cases hif

/-- **The Core 3.0 behaviours of a lambda-SSA function compiled by `compileCore?`**, at every
profile: the behaviours of a typed invocation are its SSA outcomes, and divergence exactly when
it has none. -/
theorem compileCore?_spec {f : SFunc} {s : Store Empty} (h : compileCore? f = some s)
    (P : Numerics.Profile) {vs : List Val} (hok : InvokeOk s 0 vs) :
    ∃ args : List WVal, vs = args.map WVal.toVal ∧ args.map WVal.type = f.params ∧
      behaviours P closedHost s 0 vs =
        {b | (∃ o, f.Run args o ∧ b = outBeh (some o)) ∨ (b = .diverges ∧ ∀ o, ¬ f.Run args o)} := by
  obtain ⟨g, bf, hg, hbf, hn, hr, hv, hs, hready⟩ := compileCore?_inv h
  have hof : ofBFunc? (sigType g.params g.result) bf = some g := ofBFunc?_toBFunc? hbf rfl rfl
  have hlow : (soloModule (sigType g.params g.result) bf).lower.funcs[0]? = some (coreFunc bf) :=
    lower_funcs rfl
  obtain ⟨hs', hS, hF, fi, hfi, hcode, hty⟩ := checked_store hlow hs hv hready
  obtain ⟨args, rfl, hargs, hbeh⟩ :=
    behaviours_eq_run hs' hF hS hfi hcode hty hof hn (coreReady_inv hr).1 hok P
  have hrun : ∀ o, g.Run args o ↔ f.Run args o := fun o => decompileFunc_iff hg
  refine ⟨args, rfl, hargs.trans (decompileFunc_params hg).1, ?_⟩
  rw [hbeh]
  ext b
  simp only [Set.mem_ofPred_eq, hrun]

/-- Integer arguments of the parameter types are a typed invocation of the compiled function. -/
theorem compileCore?_invokeOk {f : SFunc} {s : Store Empty} (h : compileCore? f = some s)
    {args : List WVal} (hargs : args.map WVal.type = f.params) :
    InvokeOk s 0 (args.map WVal.toVal) := by
  obtain ⟨g, bf, hg, -, -, -, -, -, hready⟩ := compileCore?_inv h
  obtain ⟨-, -, fi, hfi, hty⟩ := storeReady_inv hready
  have hty' : Validation.DefType.funcType? fi.type = some
      (g.params.map fun t => Validation.liftVal (.num (.int t)),
        (resultTypes g.result).map Validation.liftVal) := by
    rw [hty]
    simp only [sigType, List.map_map]
    rfl
  exact invokeOk_of_type hfi hty' (hargs.trans (decompileFunc_params hg).1.symm)

end Silmaril.Proofs.Wasm.SSA.CoreCert
