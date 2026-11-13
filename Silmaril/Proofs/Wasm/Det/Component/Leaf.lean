module

public import Silmaril.Proofs.Wasm.Det.Component.Session
public import Silmaril.Proofs.Wasm.Det.Component.Ref
public import Silmaril.Wasm.Det.Core.Litmus.Thms

/-!
# Sessions and export calls from core per-function facts: proofs

* statelessness of a session export from output agreement of its core functions
  (`sStatelessAt_of_obsAgree`), and from the executable leaf check (`sStatelessAt_of_abiLeafCheck`);
* determinism of a session export from determinism of its core functions at every store with the
  session's function instances (`sDetAt_of_detCalls`), and from the leaf check
  (`sDetAt_of_abiLeafCheck`);
* `CoreDet` of a simple component from the leaf check of the instantiated module
  (`coreDet_of_instLeafCheck`).

The leaf facts are `Silmaril.Proofs.Wasm.Det.Core.Leaf.{leafCheck_spec, obsAgree_leaf, detCall_leaf}`,
reached through the public imports of the header `Silmaril.Wasm.Det.Core.Litmus.Thms`. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Det.Component

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Component
open Silmaril.Wasm.Det.Core.Litmus (leafCheck)

variable {P : Profile}

/-! ## Leaf functions -/

/-- A leaf function agrees with itself across stores holding the same function instances. -/
theorem obsAgree_of_leaf {s₀ t₁ t₂ : Store Nat} {a : Nat} (h : leafCheck s₀ a = true)
    (h₁ : t₁.funcs = s₀.funcs) (h₂ : t₂.funcs = s₀.funcs) {vs : List Val} (hn : Nums vs) :
    ObsAgree P (invoke t₁ a vs) (invoke t₂ a vs) := by
  obtain ⟨fi, fn, hfi, hcode, hleaf, hnat, -⟩ := Silmaril.Proofs.Wasm.Det.Core.Leaf.leafCheck_spec h
  exact Silmaril.Proofs.Wasm.Det.Core.Leaf.obsAgree_leaf (by rw [h₁]; exact hfi)
    (by rw [h₂]; exact hfi) hcode hleaf hnat hn

/-- A leaf function is deterministic in every store holding the same function instances. -/
theorem detCall_of_leaf {s₀ t : Store Nat} {a : Nat} (h : leafCheck s₀ a = true)
    (ht : t.funcs = s₀.funcs) {vs : List Val} (hn : Nums vs) : DetCall P t a vs := by
  obtain ⟨fi, fn, hfi, hcode, hleaf, hnat, -⟩ := Silmaril.Proofs.Wasm.Det.Core.Leaf.leafCheck_spec h
  exact Silmaril.Proofs.Wasm.Det.Core.Leaf.detCall_leaf (by rw [ht]; exact hfi) hcode hleaf hnat hn

theorem nums_reallocArgs (n : Nat) : Nums (reallocArgs n) := by
  intro v hv
  simp only [reallocArgs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

theorem nums_ofFlat (xs : List Silmaril.Wasm.Component.Flat) : Nums (xs.map ofFlat) := by
  intro v hv
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hv
  exact ⟨_, rfl⟩

/-- A configuration returning values is a non-trapping stop. -/
theorem outAt_vals {d : Config Nat} {ws : List Val} (h : d.code = vals ws) :
    OutAt d (.ret (.values ws)) :=
  .ret (by simp) h

theorem out_vals_inj {ws₁ ws₂ : List Val} (h : Out.ret (.values ws₁) = Out.ret (.values ws₂)) :
    ws₁ = ws₂ := by
  injection h with h'
  injection h'

/-! ## Statelessness -/

/-- The `realloc` VC from output agreement of `realloc` across stores with the functions `F`. -/
theorem reallocVC_obsAgree {F : List (FuncInst Nat)} {ra : Nat}
    (hA : ∀ t₁ t₂ n, FuncsAt F t₁ t₂ →
      ObsAgree P (invoke t₁ ra (reallocArgs n)) (invoke t₂ ra (reallocArgs n))) :
    ReallocVC P (FuncsAt F) (FuncsAt F) ra := by
  intro s₁ s₂ n d₁ d₂ p₁ p₂ ho h₁ h₂ hd₁ hd₂
  have he : Out.ret (.values [Val.i32 p₁]) = Out.ret (.values [Val.i32 p₂]) :=
    hA s₁ s₂ n ho [] d₁ d₂ _ _ (.stop h₁) (.stop h₂) (outAt_vals hd₁) (outAt_vals hd₂)
  have hp : p₁ = p₂ := i32_inj (List.cons.inj (out_vals_inj he)).1
  exact ⟨hp, (runs_invoke_funcs (.stop h₁)).symm.trans ho.1,
    (runs_invoke_funcs (.stop h₂)).symm.trans ho.2⟩

/-- Writes keep `FuncsAt`. -/
theorem writeVC_funcsAt (F : List (FuncInst Nat)) (m : Nat) : WriteVC (FuncsAt F) (FuncsAt F) m :=
  fun _ _ _ _ _ _ ho h₁ h₂ => ⟨(memWrite_funcs h₁).trans ho.1, (memWrite_funcs h₂).trans ho.2⟩

/-- The core VC of a flat-result export from output agreement of its core function. -/
theorem coreVC_obsAgree {F : List (FuncInst Nat)} {x : AbiFn} (hres : x.resBuf = none)
    (hA : ∀ t₁ t₂ args, FuncsAt F t₁ t₂ → Nums args →
      ObsAgree P (invoke t₁ x.fn args) (invoke t₂ x.fn args)) : CoreVC P (FuncsAt F) x := by
  intro t₁ t₂ args tr d₁ d₂ ws₁ ws₂ ho hn h₁ h₂ hd₁ hd₂
  have hw : ws₁ = ws₂ :=
    out_vals_inj (hA t₁ t₂ args ho hn tr d₁ d₂ _ _ h₁ h₂ (outAt_vals hd₁) (outAt_vals hd₂))
  refine ⟨hw, ?_⟩
  simp only [liftRes, hres, hw]

/-- **Statelessness of a flat-result export from its core functions**: if `realloc` (for a
`list<u8>` parameter) and the core function have equal non-trapping outputs in any two stores
holding the session's function instances, the export is stateless. -/
theorem sStatelessAt_of_obsAgree {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (hres : (X i).resBuf = none)
    (hR : ∀ ra m, (X i).argBuf = some (ra, m) → ∀ t₁ t₂ n, FuncsAt s₀.funcs t₁ t₂ →
      ObsAgree P (invoke t₁ ra (reallocArgs n)) (invoke t₂ ra (reallocArgs n)))
    (hC : ∀ t₁ t₂ args, FuncsAt s₀.funcs t₁ t₂ → Nums args →
      ObsAgree P (invoke t₁ (X i).fn args) (invoke t₂ (X i).fn args)) :
    SStatelessAt (abiSem P X) s₀ i :=
  sStatelessAt_of_obs (isPER_funcsAt s₀.funcs) ⟨rfl, rfl⟩ confined_funcsAt
    (abi_obsDetermines (Mid := FuncsAt s₀.funcs) (Arg := FuncsAt s₀.funcs) X i
      (fun _ _ _ h => h)
      (fun ra m hx => ⟨reallocVC_obsAgree (hR ra m hx), writeVC_funcsAt _ m⟩)
      (coreVC_obsAgree hres hC))

/-- What `abiLeafCheck` establishes. -/
theorem abiLeafCheck_spec {s₀ : Store Nat} {x : AbiFn} (h : abiLeafCheck s₀ x = true) :
    x.resBuf = none ∧ leafCheck s₀ x.fn = true ∧
      ∀ ra m, x.argBuf = some (ra, m) → leafCheck s₀ ra = true := by
  unfold abiLeafCheck at h
  rcases hb : x.argBuf with _ | ⟨ra, m⟩
  · have h' : x.resBuf.isNone = true ∧ leafCheck s₀ x.fn = true := by
      simpa only [hb, Bool.and_true, Bool.and_eq_true] using h
    refine ⟨Option.isNone_iff_eq_none.mp h'.1, h'.2, fun ra m hx => ?_⟩
    cases hx
  · have h' : (x.resBuf.isNone = true ∧ leafCheck s₀ x.fn = true) ∧ leafCheck s₀ ra = true := by
      simpa only [hb, Bool.and_eq_true] using h
    refine ⟨Option.isNone_iff_eq_none.mp h'.1.1, h'.1.2, fun ra' m' hx => ?_⟩
    have he : (ra, m) = (ra', m') := Option.some.inj hx
    rw [← (Prod.mk.inj he).1]
    exact h'.2

/-- **The leaf check gives statelessness**, at every profile. -/
theorem sStatelessAt_of_abiLeafCheck {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (h : abiLeafCheck s₀ (X i) = true) : SStatelessAt (abiSem P X) s₀ i := by
  obtain ⟨hres, hfn, hra⟩ := abiLeafCheck_spec h
  exact sStatelessAt_of_obsAgree hres
    (fun ra m hx _ _ n ho => obsAgree_of_leaf (hra ra m hx) ho.1 ho.2 (nums_reallocArgs n))
    (fun _ _ _ ho hn => obsAgree_of_leaf hfn ho.1 ho.2 hn)

/-! ## Determinism -/

section Det

variable {x : AbiFn}

/-- Deterministic lowering. -/
theorem lower_det {s t₁ t₂ : Store Nat} {v : AVal} {a₁ a₂ : List Val}
    (hR : ∀ ra m, x.argBuf = some (ra, m) → ∀ n, DetCall P s ra (reallocArgs n))
    (h₁ : Lower P x s v t₁ a₁) (h₂ : Lower P x s v t₂ a₂) : t₁ = t₂ ∧ a₁ = a₂ := by
  cases h₁ with
  | flat _ =>
    cases h₂ with
    | flat _ => exact ⟨rfl, rfl⟩
  | buf hx hs hd hw =>
    cases h₂ with
    | buf hx' hs' hd' hw' =>
      show _ ∧ _
      obtain ⟨hra, hm⟩ := Prod.mk.inj (Option.some.inj (hx.symm.trans hx'))
      have hs'' := hra ▸ hs'
      obtain ⟨ho, hst⟩ := hR _ _ hx _ [] _ _ _ _ (.stop hs) (.stop hs'') (outAt_vals hd)
        (outAt_vals hd')
      have hp := i32_inj (List.cons.inj (out_vals_inj ho)).1
      have hw'' := hm ▸ hp ▸ hst ▸ hw'
      exact ⟨Option.some.inj (hw.symm.trans hw''), by rw [hp]⟩

/-- Deterministic post-return. -/
theorem postRet_det {s s₁ s₂ : Store Nat} {ws : List Val} {ok₁ ok₂ : Bool}
    (hp : ∀ pr, x.post = some pr → DetCall P s pr ws) (h₁ : PostRet P x s ws s₁ ok₁)
    (h₂ : PostRet P x s ws s₂ ok₂) (e₁ : ok₁ = true) (e₂ : ok₂ = true) : s₁ = s₂ := by
  cases h₁ with
  | none hx =>
    cases h₂ with
    | none _ => rfl
    | run hx' _ _ => cases hx.symm.trans hx'
  | run hx hs he =>
    cases h₂ with
    | none hx' => cases hx.symm.trans hx'
    | run hx' hs' he' =>
      show _ = _
      have hpr := Option.some.inj (hx.symm.trans hx')
      have hs'' := hpr ▸ hs'
      have hr₁ := of_decide_eq_true e₁
      have hr₂ := of_decide_eq_true e₂
      exact (hp _ hx [] _ _ _ _ (.stop hs) (.stop hs'') (outAt_vals (hr₁ ▸ he))
        (outAt_vals (hr₂ ▸ he'))).2

/-- The returning case of `abiCall_det`. -/
theorem abiCall_det_ret {s s₁ s₂ t₁ t₂ : Store Nat} {v : AVal} {tr : List Call}
    {a₁ a₂ ws₁ ws₂ : List Val} {d₁ d₂ : Config Nat} {ok₁ ok₂ : Bool} {w₁ w₂ : AVal}
    (hR : ∀ ra m, x.argBuf = some (ra, m) → ∀ n, DetCall P s ra (reallocArgs n))
    (hC : ∀ t args, t.funcs = s.funcs → Nums args → DetCall P t x.fn args)
    (hp : ∀ pr, x.post = some pr → ∀ t ws, t.funcs = s.funcs → DetCall P t pr ws)
    (hl₁ : Lower P x s v s₁ a₁) (hr₁ : Runs P (invoke s₁ x.fn a₁) tr d₁) (hd₁ : d₁.code = vals ws₁)
    (hp₁ : PostRet P x d₁.store ws₁ t₁ ok₁)
    (hl₂ : Lower P x s v s₂ a₂) (hr₂ : Runs P (invoke s₂ x.fn a₂) tr d₂) (hd₂ : d₂.code = vals ws₂)
    (hp₂ : PostRet P x d₂.store ws₂ t₂ ok₂)
    (e₁ : (if ok₁ then liftRes x d₁.store ws₁ else none) = some w₁)
    (e₂ : (if ok₂ then liftRes x d₂.store ws₂ else none) = some w₂) : w₁ = w₂ ∧ t₁ = t₂ := by
  obtain ⟨hst, ha⟩ : s₁ = s₂ ∧ a₁ = a₂ := lower_det hR hl₁ hl₂
  have hr₂' : Runs P (invoke s₁ x.fn a₁) tr d₂ := ha ▸ hst ▸ hr₂
  have hf₁ : s₁.funcs = s.funcs :=
    (lower_obs isPER_funcsEq (fun _ => rfl) (confVC_funcs x) hl₁).symm
  have hD : DetCall P s₁ x.fn a₁ := hC _ _ hf₁ (lower_nums hl₁)
  obtain ⟨ho, hds⟩ : Out.ret (.values ws₁) = Out.ret (.values ws₂) ∧ d₁.store = d₂.store :=
    hD _ _ _ _ _ hr₁ hr₂' (outAt_vals hd₁) (outAt_vals hd₂)
  have hws : ws₁ = ws₂ := out_vals_inj ho
  have hp₂' : PostRet P x d₁.store ws₁ t₂ ok₂ := hws ▸ hds ▸ hp₂
  have hfd : d₁.store.funcs = s.funcs := (runs_invoke_funcs hr₁).symm.trans hf₁
  have ht : t₁ = t₂ := postRet_det (fun pr hx => hp pr hx _ _ hfd) hp₁ hp₂' (ite_some e₁).1
    (ite_some e₂).1
  have he₂ : liftRes x d₁.store ws₁ = some w₂ := hws ▸ hds ▸ (ite_some e₂).2
  have hl : some w₁ = some w₂ := (ite_some e₁).2.symm.trans he₂
  exact ⟨Option.some.inj hl, ht⟩

/-- **Two canonical-ABI calls from one store** with the same argument and answers that both
return: equal outputs and equal final stores. -/
theorem abiCall_det {s t₁ t₂ : Store Nat} {v : AVal} {tr : List Call} {o₁ o₂ : Option AVal}
    {w₁ w₂ : AVal}
    (hR : ∀ ra m, x.argBuf = some (ra, m) → ∀ n, DetCall P s ra (reallocArgs n))
    (hC : ∀ t args, t.funcs = s.funcs → Nums args → DetCall P t x.fn args)
    (hp : ∀ pr, x.post = some pr → ∀ t ws, t.funcs = s.funcs → DetCall P t pr ws)
    (h₁ : AbiCall P x s v tr t₁ o₁) (h₂ : AbiCall P x s v tr t₂ o₂) (e₁ : o₁ = some w₁)
    (e₂ : o₂ = some w₂) : w₁ = w₂ ∧ t₁ = t₂ := by
  cases h₁ with
  | lowerFails _ => cases e₁
  | coreFails _ _ _ _ => cases e₁
  | ret hl₁ hr₁ hd₁ hp₁ =>
    cases h₂ with
    | lowerFails _ => cases e₂
    | coreFails _ _ _ _ => cases e₂
    | ret hl₂ hr₂ hd₂ hp₂ => exact abiCall_det_ret hR hC hp hl₁ hr₁ hd₁ hp₁ hl₂ hr₂ hd₂ hp₂ e₁ e₂

end Det

/-- **Determinism of a session export from its core functions**: if `realloc`, the core
function and `post-return` are deterministic in every store holding the session's function
instances, the export is deterministic. -/
theorem sDetAt_of_detCalls {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (hR : ∀ ra m, (X i).argBuf = some (ra, m) → ∀ t n, t.funcs = s₀.funcs →
      DetCall P t ra (reallocArgs n))
    (hC : ∀ t args, t.funcs = s₀.funcs → Nums args → DetCall P t (X i).fn args)
    (hp : ∀ pr, (X i).post = some pr → ∀ t ws, t.funcs = s₀.funcs → DetCall P t pr ws) :
    SDetAt (abiSem P X) s₀ i := by
  intro s hs v tr s₁ s₂ w₁ w₂ h₁ h₂
  have hf : s.funcs = s₀.funcs := sReach_funcs hs
  exact abiCall_det (fun ra m hx n => hR ra m hx s n hf)
    (fun t args ht hn => hC t args (ht.trans hf) hn)
    (fun pr hx t ws ht => hp pr hx t ws (ht.trans hf)) h₁ h₂ rfl rfl

/-- **The leaf check gives determinism** (without `post-return`), at every profile. -/
theorem sDetAt_of_abiLeafCheck {ι : Type} {X : ι → AbiFn} {s₀ : Store Nat} {i : ι}
    (h : abiLeafCheck s₀ (X i) = true) (hpost : (X i).post = none) :
    SDetAt (abiSem P X) s₀ i := by
  obtain ⟨-, hfn, hra⟩ := abiLeafCheck_spec h
  refine sDetAt_of_detCalls
    (fun ra m hx t n ht => detCall_of_leaf (hra ra m hx) ht (nums_reallocArgs n))
    (fun t args ht hn => detCall_of_leaf hfn ht hn) ?_
  intro pr hx
  rw [hpost] at hx
  cases hx

/-! ## One export call on the reference machine -/

open Silmaril.Wasm.Component.Reference (Simple SimpleExport NumModule) in
/-- The leaf check of the instantiated module applies to the instance. -/
theorem leafCheck_of_inst {m : NumModule} {k : Nat} (h : instLeafCheck m.mod k = true)
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) :
    leafCheck I.store (I.addrs.getD k 0) = true := by
  obtain ⟨⟨mt, hmt⟩, -, -⟩ := hI
  obtain ⟨f, hinst, haddrs⟩ := hmt.instantiated
  have h' : leafCheck I.store ((Silmaril.Wasm.Game.exportFuncAddrs f.module).getD k 0) = true := by
    simpa only [instLeafCheck, hmt.valid, hinst] using h
  rw [← haddrs]
  exact h'

open Silmaril.Wasm.Component.Reference (Simple SimpleExport) in
/-- **`CoreDet` from the leaf check** of the instantiated core module. -/
theorem coreDet_of_instLeafCheck {c : Simple} {x : SimpleExport}
    (h : instLeafCheck c.mod.mod x.core = true) : CoreDet P c x :=
  fun _ hI xs => detCall_of_leaf (leafCheck_of_inst h hI) rfl (nums_ofFlat xs)

end Silmaril.Proofs.Wasm.Det.Component
