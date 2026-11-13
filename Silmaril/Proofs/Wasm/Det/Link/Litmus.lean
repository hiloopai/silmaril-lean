module

public import Silmaril.Wasm.Det.Link.Litmus.Defs
public import Silmaril.Wasm.Game.Linking.Thms
public import Silmaril.Wasm.Det.NoMem.Defs
public import Silmaril.Wasm.Det.Stateless.Defs
public import Silmaril.Wasm.Det.Game.Instance.Defs

/-!
# A concrete static link (litmus): the setup

Kernel evaluation of the linker, of `instantiateOnce?` and of the checks of the subsets on the
concrete link `linkP`/`linkC` of `Silmaril.Wasm.Det.Link.Litmus`, and the `Setup` built from them by
`Silmaril.Wasm.Game.Linking.exists_scalar_setup` (`exists_setup`). The consumer store of that setup
is pinned to `linkScs` (`Assembly.imports` is determined by the linker's import resolution,
`assembly_imports`), so the executable checks run on the stores of the setup itself.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Link.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Link
  Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Link.Litmus

/-! ### Kernel-checked facts -/

theorem link_some : (link? "p" linkP linkC).isSome = true := by decide +kernel
theorem provInst_some : (instantiateOnce? linkBase linkP (Preparation.imports [])).isSome = true := by
  decide +kernel
theorem linkedInst_some :
    (instantiateOnce? linkBase linkL (Preparation.imports [])).isSome = true := by decide +kernel
theorem stubInst_some : (instantiateOnce? (stubOut linkBase.funcs.length linkStubs linkSp) linkC
    (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat))).isSome =
      true := by decide +kernel
theorem sharedInst_some : (instantiateOnce? linkSp linkC
    (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat))).isSome =
      true := by decide +kernel
theorem closB_sc : Silmaril.Wasm.Det.NoMem.closB linkSc linkAddrs = true := by decide +kernel
theorem closB_scs : Silmaril.Wasm.Det.NoMem.closB linkScs linkAddrs = true := by decide +kernel
theorem checkSet_sc : Silmaril.Wasm.Det.Stateless.checkSet linkSc linkAddrs (fun _ => false)
    (fun _ => false) = true := by decide +kernel
theorem checkSet_scs : Silmaril.Wasm.Det.Stateless.checkSet linkScs linkAddrs (fun _ => false)
    (fun _ => false) = true := by decide +kernel
theorem storeB_sp : Silmaril.Wasm.Det.NoMem.storeB linkSp = true := by decide +kernel
theorem storeB_scs : Silmaril.Wasm.Det.NoMem.storeB linkScs = true := by decide +kernel
theorem storeB_sl : Silmaril.Wasm.Det.NoMem.storeB linkSl = true := by decide +kernel
theorem stateless_sp : Silmaril.Wasm.Det.Stateless.moduleStatelessCheck linkSp = true := by
  decide +kernel
theorem stateless_scs : Silmaril.Wasm.Det.Stateless.moduleStatelessCheck linkScs = true := by
  decide +kernel
theorem stateless_sl : Silmaril.Wasm.Det.Stateless.moduleStatelessCheck linkSl = true := by
  decide +kernel
theorem export_addrs : exportFuncAddrs linkLI.2.1.module = [0, 1] := by decide +kernel
theorem stubs_eq : canonicalStubs [⟨0⟩] linkBase.funcs.length linkP.funcs.length [0, 1] =
    linkStubs := by decide +kernel
theorem sp_type : (linkSp.funcs[linkBase.funcs.length + 0]?.bind fun fi =>
    FnType.ofDefType? fi.type) = some i32Fn := by decide +kernel
theorem sl_type₀ : (linkSl.funcs[0]?.bind fun fi => FnType.ofDefType? fi.type) = some i32Fn := by
  decide +kernel
theorem sl_type₁ : (linkSl.funcs[1]?.bind fun fi => FnType.ofDefType? fi.type) = some i32Fn := by
  decide +kernel
theorem resolve_eq : ((validate? linkP).bind fun pt => (validate? linkC).bind fun ct =>
    resolveImports? "p" linkP linkC pt ct) = some [⟨0⟩] := by decide +kernel

/-! ### Rewriting the computed values -/

theorem eq_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o
  · cases h
  · rfl

theorem eta3 {α β γ : Type} {o : Option (α × β × γ)} {x : α × β × γ} (h : o = some x) :
    o = some (x.1, x.2.1, x.2.2) := h

theorem link_eq : link? "p" linkP linkC = some linkL := eq_getD linkP link_some

theorem fnType_of_bind {o : Option (FuncInst Nat)} {ft : FnType}
    (h : (o.bind fun fi => FnType.ofDefType? fi.type) = some ft) :
    ∃ fi : FuncInst Nat, o = some fi ∧ FnType.ofDefType? fi.type = some ft :=
  Option.bind_eq_some_iff.1 h

/-- The imports of every assembly of the link are the provider's function `0`. -/
theorem assembly_imports {ns : String} {p c l : Module} (w : Recipe.Assembly ns p c l)
    (hns : ns = "p") (hp : p = linkP) (hc : c = linkC) : w.imports = [⟨0⟩] := by
  subst hns hp hc
  have h := resolve_eq
  rw [w.providerValidation, w.consumerValidation] at h
  simp only [Option.bind_some] at h
  rw [w.resolved] at h
  exact Option.some.inj h

/-- **The concrete link is a setup of the scalar fragment**, with the stores computed above. -/
theorem exists_setup : ∃ S : Setup, S.namespaceName = "p" ∧ S.provider = linkP ∧
    S.consumer = linkC ∧ S.linked = linkL ∧ S.sp = linkSp ∧ S.scs = linkScs ∧ S.sl = linkSl ∧
    S.stubTypes = [i32Fn] ∧ S.exportTypes = [i32Fn, i32Fn] ∧ S.Scalar := by
  have w := Classical.choice (link?_recipe link_eq)
  have hw := assembly_imports w rfl rfl rfl
  have hbase : ∀ fi ∈ linkBase.funcs, ∃ f, fi.code = .wasm f := by
    intro fi hfi
    cases hfi
  have hok : StoreOk linkBase := by
    constructor <;> intro x hx <;> cases hx
  obtain ⟨fi₀, h₀, t₀⟩ := fnType_of_bind sp_type
  obtain ⟨fl₀, hl₀, tl₀⟩ := fnType_of_bind sl_type₀
  obtain ⟨fl₁, hl₁, tl₁⟩ := fnType_of_bind sl_type₁
  have hstub : List.Forall₂ (fun k ft => ∃ fi : FuncInst Nat,
      linkPI.1.funcs[linkBase.funcs.length + k]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
      (canonicalStubs w.imports linkBase.funcs.length linkP.funcs.length
        (exportFuncAddrs linkLI.2.1.module)) [i32Fn] := by
    rw [hw, export_addrs, stubs_eq]
    exact .cons ⟨fi₀, h₀, t₀⟩ .nil
  have hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, linkLI.1.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) (exportFuncAddrs linkLI.2.1.module) [i32Fn, i32Fn] := by
    rw [export_addrs]
    exact .cons ⟨fl₀, hl₀, tl₀⟩ (.cons ⟨fl₁, hl₁, tl₁⟩ .nil)
  have hpI : instantiateOnce? linkBase linkP (Preparation.imports []) = some linkPI :=
    eq_getD noInst provInst_some
  have hlI : instantiateOnce? linkBase linkL (Preparation.imports []) = some linkLI :=
    eq_getD noInst linkedInst_some
  obtain ⟨S, hns, hp, hc, hl, hb, hsp, hsl, hfl, hst, hsT, heT, hS⟩ :=
    exists_scalar_setup w link_eq hbase hok (eta3 hpI) (eta3 hlI) hstub hexp
  have hsp : S.sp = linkSp := hsp
  refine ⟨S, hns, hp, hc, hl, hsp, ?_, hsl, hsT, heT, hS⟩
  have hi := S.stubInst
  rw [assembly_imports S.assembly hns hp hc, hst, hw, export_addrs, stubs_eq, hb, hsp, hc] at hi
  have hi' : instantiateOnce? (stubOut linkBase.funcs.length linkStubs linkSp) linkC
      (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat)) =
        some (S.scs, S.fcs, none) := hi
  simp only [linkScs, linkCI, hi', Option.getD_some]

/-- Every export address of an instance whose addresses lie in `linkAddrs` lies in `linkAddrs`
(the default address `0` included). -/
theorem entry_mem {I : ScalarInstance} (h : ∀ x ∈ I.addrs, x ∈ linkAddrs) {a : Nat}
    (ha : Silmaril.Wasm.Det.Game.entry I a) : a ∈ linkAddrs := by
  obtain ⟨j, rfl⟩ := ha
  show I.addrs.getD j 0 ∈ linkAddrs
  rw [List.getD_eq_getElem?_getD]
  cases hx : I.addrs[(j : Nat)]? with
  | none => simp [linkAddrs]
  | some x => exact h x (List.mem_of_getElem? hx)

/-- **The concrete link is a setup of the scalar fragment with its shared store pinned**: the
shared store is `linkSc` and the export addresses of the provider and the consumer lie in
`linkAddrs`. -/
theorem exists_setup_sc : ∃ S : Setup, S.provider = linkP ∧ S.consumer = linkC ∧
    S.sc = linkSc ∧ S.scs = linkScs ∧ S.sl = linkSl ∧ S.Scalar ∧
    (∀ a, Silmaril.Wasm.Det.Game.entry S.providerI a → a ∈ linkAddrs) ∧
    (∀ a, Silmaril.Wasm.Det.Game.entry S.consumerI a → a ∈ linkAddrs) := by
  have w := Classical.choice (link?_recipe link_eq)
  have hw := assembly_imports w rfl rfl rfl
  have hbase : ∀ fi ∈ linkBase.funcs, ∃ f, fi.code = .wasm f := by
    intro fi hfi
    cases hfi
  have hok : StoreOk linkBase := by
    constructor <;> intro x hx <;> cases hx
  obtain ⟨fi₀, h₀, t₀⟩ := fnType_of_bind sp_type
  obtain ⟨fl₀, hl₀, tl₀⟩ := fnType_of_bind sl_type₀
  obtain ⟨fl₁, hl₁, tl₁⟩ := fnType_of_bind sl_type₁
  have hstub : List.Forall₂ (fun k ft => ∃ fi : FuncInst Nat,
      linkPI.1.funcs[linkBase.funcs.length + k]? = some fi ∧ FnType.ofDefType? fi.type = some ft)
      (canonicalStubs w.imports linkBase.funcs.length linkP.funcs.length
        (exportFuncAddrs linkLI.2.1.module)) [i32Fn] := by
    rw [hw, export_addrs, stubs_eq]
    exact .cons ⟨fi₀, h₀, t₀⟩ .nil
  have hexp : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, linkLI.1.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) (exportFuncAddrs linkLI.2.1.module) [i32Fn, i32Fn] := by
    rw [export_addrs]
    exact .cons ⟨fl₀, hl₀, tl₀⟩ (.cons ⟨fl₁, hl₁, tl₁⟩ .nil)
  have hpI : instantiateOnce? linkBase linkP (Preparation.imports []) = some linkPI :=
    eq_getD noInst provInst_some
  have hlI : instantiateOnce? linkBase linkL (Preparation.imports []) = some linkLI :=
    eq_getD noInst linkedInst_some
  obtain ⟨S, hns, hp, hc, -, hb, hsp, hsl, hfl, hst, -, -, hS⟩ :=
    exists_scalar_setup w link_eq hbase hok (eta3 hpI) (eta3 hlI) hstub hexp
  have hsp : S.sp = linkSp := hsp
  have hstubs : S.stubs = linkStubs := by rw [hst, hw, export_addrs, stubs_eq]
  have hexpS : exportFuncAddrs S.fl.module = [0, 1] := by rw [hfl]; exact export_addrs
  have himp := assembly_imports S.assembly hns hp hc
  have hscs : S.scs = linkScs := by
    have hi := S.stubInst
    rw [himp, hstubs, hb, hsp, hc] at hi
    have hi' : instantiateOnce? (stubOut linkBase.funcs.length linkStubs linkSp) linkC
        (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat)) =
          some (S.scs, S.fcs, none) := hi
    simp only [linkScs, linkCI, hi', Option.getD_some]
  have hsc : S.sc = linkSc := by
    have hi := S.sharedInst
    rw [himp, hb, hsp, hc] at hi
    have hi' : instantiateOnce? linkSp linkC
        (Preparation.imports ([(⟨0⟩ : FuncIdx)].map fun f => linkBase.funcs.length + f.toNat)) =
          some (S.sc, S.fc, none) := hi
    simp only [linkSc, linkShI, hi', Option.getD_some]
  refine ⟨S, hp, hc, hsc, hscs, hsl, hS, fun a ha => entry_mem ?_ ha, fun a ha => entry_mem ?_ ha⟩
  · intro x hx
    have hx' : x ∈ S.stubs.map (S.base.funcs.length + ·) := hx
    have hm : linkStubs.map (linkBase.funcs.length + ·) = [0] := rfl
    rw [hstubs, hb, hm, List.mem_singleton] at hx'
    rw [hx']
    decide
  · intro x hx
    have hx' : x ∈ exportFuncAddrs S.fl.module := hx
    rw [hexpS] at hx'
    exact hx'

end Silmaril.Proofs.Wasm.Det.Link.Litmus
