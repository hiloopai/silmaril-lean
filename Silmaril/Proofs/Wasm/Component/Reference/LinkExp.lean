module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkSplit
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSegs
public import Silmaril.Proofs.Wasm.Component.Reference.MultiCall

/-!
# The exporter's nested runs in the shared core store

Inside a linked call, the exporter's core activation runs in the shared core store `σ` (host
code `CanonHost`). Renamed to `Nat` host codes by any `g` (`Store.mapH g σ`), the shared store
relates the exporter's own store `π` (provider) and the importer's relocated store `κ`
(consumer) by `Linking.Split.Rel4`. The exporter is the part with the empty prefix (`s₀ = {}`,
`reloc_empty`): its invocation in the shared store is the image of its invocation in `π`
(`linkSt_invoke`), and every shared run maps back (`reach_link_back`).

* `exp_run`: a shared run of the invocation of export `x` of the exporter's instance `Ie`
  (well formed at `π`) on the lowered arguments `vs` never stops at a callout; when it returns
  flat values `zs`, they have the flat result types, `some zs` is a core outcome of `coreAt` at
  `π`, and every IR lift `ws` of them is a returned call `RetAt … π ws π'`, `Ie` well formed at
  `π'`; when it traps, `none` is a core outcome of `coreAt` at `π`. In every case, `Rel4` holds
  again with the exporter's store `π'` at the end of the run (`Rel4.after_p`), the importer's
  part unchanged.
* `exp_trap_spec`: the trap case as a `specAt` outcome.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

section Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren)

/-! ## Values and exceptions of images -/

/-- Values whose image under a code map are flat are their own image. -/
theorem map_val_flat (M : CMap) :
    ∀ {vs : List Silmaril.Wasm.Component.Reference.Val} {zs : List Silmaril.Wasm.Execution.Runtime.Value},
      (vs.map M.val).mapM toFlat? = some zs → vs.map M.val = vs
  | [], _, _ => rfl
  | v :: vs, zs, h => by
    rw [List.map_cons, List.mapM_cons] at h
    cases hv : toFlat? (M.val v) with
    | none => simp [hv] at h
    | some z =>
      cases hm : (vs.map M.val).mapM toFlat? with
      | none => simp [hv, hm] at h
      | some zs' =>
        have hvv : M.val v = v := by
          cases v with
          | ref r => cases hv
          | num n => rfl
          | vec b => rfl
        rw [List.map_cons, hvv, map_val_flat M hm]

/-- The values of a list never end with `THROW_REF`. -/
theorem vals_ne_throwing' (vs : List Silmaril.Wasm.Component.Reference.Val) (a : Nat) : vals vs ≠ throwing a := by
  intro h
  have h' : (vals vs).map Admin.val? = (throwing a).map Admin.val? := congrArg _ h
  have hl : (vals vs).map Admin.val? = vs.map some := by
    simp only [vals, List.map_map, Function.comp_def, Admin.val?_toAdmin]
  have hr : (throwing a).map Admin.val? = [some (.ref (.exn a)), none] := rfl
  rw [hl, hr] at h'
  have hn : none ∈ vs.map some := by rw [h']; simp
  simp at hn

theorem decompose?_throwing' {H : Type} (s : Store H) (a : Nat) :
    decompose? s (throwing a) = none :=
  SingleThreaded.decompose?_vals_cons_none (vs := [.ref (.exn a)]) (r := []) rfl
    fun _ _ => SingleThreaded.decompHead_plain rfl

variable {H : Type} {s₀ : Store H} {ρ : Ren} {O : Own}
  {x y : Store H × Thread} {ts : List CValType}

/-- No image of a typed part throws. -/
theorem throwing_back (P : Silmaril.Wasm.Numerics.Profile) (hL : LinkSt s₀ ρ O x y) (hs : StoreOk x.1) (ht : ThreadOk x.1 x.2 ts)
    {a : Nat} (h : (y.2.config y.1).code = throwing a) : False := by
  rcases part_cases (P := P) hL hs ht with ⟨vs, hv⟩ | htr | ⟨E, a', hh, args, hd⟩ | ⟨x₁, hx⟩
  · exact vals_ne_throwing' _ a ((link_values hL hv).symm.trans h)
  · have h' := (link_trap hL htr).symm.trans h
    simp [throwing] at h'
  · have hd' := link_callout hL hd
    rw [h, decompose?_throwing'] at hd'
    cases hd'
  · obtain ⟨y₁, -, -, hy₁, -, -, -⟩ := internal_link hL hx
    obtain ⟨f', code', -, hst⟩ := hy₁
    exact Step.not_quiet hst (by rw [h]; exact quiet_throwing a)

end Core

/-! ## The exporter's run -/

section Run

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Execution.Core (Store Config)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch Rel4)

variable {P : Profile} {c : Simple} {Ie : Silmaril.Wasm.Game.ScalarInstance} {x : SimpleExport}
  {vs : List Silmaril.Wasm.Component.Val}

/-- **The invocation of the exporter's function in the shared store** is the image of its
invocation in the exporter's store (the empty prefix). -/
theorem exp_invoke {π τ : Store Nat} {ρ : Ren} {O : Own} (hR : PartRel ρ O π τ)
    (hF : FnPre ({} : Store Nat) τ π) {a : Nat} (hO : O.fn a) (xs : List Flat) :
    LinkSt ({} : Store Nat) ρ O (π, .pending a (xs.map Silmaril.Wasm.SingleThreaded.ofFlat))
      (τ, .pending a (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)) := by
  obtain ⟨fi, hfi, -⟩ := hR.fn a hO
  have ha : a < π.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have hvs : ∀ v ∈ xs.map Silmaril.Wasm.SingleThreaded.ofFlat, ∀ r, v ≠ .ref r := by
    intro v hv r
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv
    exact nofun
  have hcode : O.CodeGood (Silmaril.Wasm.Execution.Core.invoke π a
      (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)).code := by
    simp only [Silmaril.Wasm.Execution.Core.invoke, hfi, Option.map_some, Option.getD_some]
    exact O.codeGood_append.mpr ⟨codeGood_scalar hvs,
      Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.cons_ref hO (by simp [Own.CodeGood])⟩
  have hgood : SplitGood (Silmaril.Wasm.Execution.Core.invoke π a
      (xs.map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    ⟨ρ, O, τ, hR, ⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩, hcode⟩
  have hrp : PartRel ρ O (reloc ({} : Store Nat) π) τ := (reloc_empty π).symm ▸ hR
  have hO' : O.fn (({} : Store Nat).funcs.length + a) := (Nat.zero_add a).symm ▸ hO
  have hL := linkSt_invoke hrp hF ha hO' hvs hgood
  have h0 : ({} : Store Nat).funcs.length + a = a := Nat.zero_add a
  rwa [h0] at hL

/-- **A run of the exporter mapped back from the shared store**: from the invocation of export
`x` of `Ie` (well formed at `π`) on the lowered `vs`, a host-free run to `(π', t')`, whose image
is the shared thread `y`, typed. -/
structure ExpBack (P : Profile) (c : Simple) (Ie : Silmaril.Wasm.Game.ScalarInstance)
    (x : SimpleExport) (vs : List Silmaril.Wasm.Component.Val) (π π' : Store Nat)
    (t' : Silmaril.Wasm.SingleThreaded.Thread) (y : Store Nat × Silmaril.Wasm.SingleThreaded.Thread) :
    Prop where
  inst : c.mod.IsInst Ie
  core : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)
  typed : ValTy.checkList x.ty.params vs = true
  wf : Ie.WellFormed π
  run : Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P)
    (π, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
      (lowerArgs x.ty.params vs)) (π', t')
  link : ∃ ρ O, LinkSt ({} : Store Nat) ρ O (π', t') y
  storeOk : Silmaril.Wasm.Execution.Core.StoreOk π'
  threadOk : ∃ ts, Silmaril.Wasm.SingleThreaded.ThreadOk π' t' ts

/-- The lowered arguments have the core export's parameter types. -/
theorem exp_hxs {nm : String} (h : c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (typed : ValTy.checkList x.ty.params vs = true) (hk : x.core < c.mod.exports.length) :
    (lowerArgs x.ty.params vs).map (·.type) = (c.mod.exports[x.core]'hk).2.params := by
  have hget : c.mod.exports[x.core]'hk = (nm, x.ty.flat) := (List.getElem?_eq_some_iff.mp h).2
  rw [hget]
  exact lowerList_types _ _ typed

namespace ExpBack

variable {π π' : Store Nat} {t' : Silmaril.Wasm.SingleThreaded.Thread}
  {y : Store Nat × Silmaril.Wasm.SingleThreaded.Thread}

theorem hk (B : ExpBack P c Ie x vs π π' t' y) : x.core < c.mod.exports.length := by
  obtain ⟨nm, h⟩ := B.core
  exact (List.getElem?_eq_some_iff.mp h).1

theorem hxs (B : ExpBack P c Ie x vs π π' t' y) :
    (lowerArgs x.ty.params vs).map (·.type) = (c.mod.exports[x.core]'B.hk).2.params := by
  obtain ⟨nm, h⟩ := B.core
  exact exp_hxs h B.typed B.hk

theorem steps (B : ExpBack P c Ie x vs π π' t' y) :
    Silmaril.Wasm.Execution.Core.Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      (Silmaril.Wasm.Execution.Core.invoke π (Ie.addrs.getD x.core 0)
        ((lowerArgs x.ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat))
      (t'.config π') :=
  internalP_steps B.run

/-- The image never stops at a host call. -/
theorem no_callout (B : ExpBack P c Ie x vs π π' t' y) {E : Silmaril.Wasm.SingleThreaded.Ctx}
    {a : Nat} {h : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hd : Silmaril.Wasm.SingleThreaded.decompose? y.1 (y.2.config y.1).code =
      some (E, a, h, args)) : False := by
  obtain ⟨ρ, O, hL⟩ := B.link
  obtain ⟨ts, ht⟩ := B.threadOk
  obtain ⟨E₁, a₁, args₁, hdx, -⟩ := callout_back P hL B.storeOk ht hd
  have hn : Silmaril.Wasm.SingleThreaded.decompose? (t'.config π').store (t'.config π').code =
      none := run_no_callout_at B.inst B.wf B.hk B.hxs B.steps
  have hs : (t'.config π').store = π' := Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
  rw [hs] at hn
  exact absurd (hdx.symm.trans hn) (by simp)

/-- A finished image: typed flat results, a `coreAt` outcome, a returned call. -/
theorem values (B : ExpBack P c Ie x vs π π' t' y) {cvs : List Silmaril.Wasm.Execution.Core.Val}
    (hc : (y.2.config y.1).code = Silmaril.Wasm.Execution.Core.vals cvs) {zs : List FlatValue}
    (hm : cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs) :
    zs.map (·.type) = ValTy.flatList x.ty.results ∧
      some zs ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π ∧
      ∀ ws, liftArgs x.ty.results zs = some ws → RetAt P c Ie x vs π ws π' ∧ Ie.WellFormed π' := by
  obtain ⟨ρ, O, hL⟩ := B.link
  obtain ⟨ts, ht⟩ := B.threadOk
  obtain ⟨vs', hv', hmap⟩ := values_back P hL B.storeOk ht hc
  have hvv : vs'.map (linkMap ({} : Store Nat) ρ).val = vs' :=
    map_val_flat _ (show (vs'.map (linkMap ({} : Store Nat) ρ).val).mapM
      Silmaril.Wasm.SingleThreaded.toFlat? = some zs by rw [hmap]; exact hm)
  have hcv : vs' = cvs := hvv.symm.trans hmap
  have hcode : (t'.config π').code = Silmaril.Wasm.Execution.Core.vals cvs := hcv ▸ hv'
  obtain ⟨nm, hcx⟩ := B.core
  have hty : zs.map (·.type) = (c.mod.exports[x.core]'B.hk).2.results :=
    run_typed_at B.inst B.wf B.hk B.hxs B.steps hcode hm
  have hget : c.mod.exports[x.core]'B.hk = (nm, x.ty.flat) :=
    (List.getElem?_eq_some_iff.mp hcx).2
  have hret : ∀ ws, liftArgs x.ty.results zs = some ws → RetAt P c Ie x vs π ws π' :=
    fun ws hws => ⟨B.typed, t', cvs, zs, B.run, hcode, hm, hws⟩
  refine ⟨by rw [hty, hget]; rfl, ⟨_, .values cvs, B.steps, hcode, hm.symm⟩,
    fun ws hws => ⟨hret ws hws, ?_⟩⟩
  exact RetAt.wellFormed B.inst ⟨nm, hcx⟩ B.wf (hret ws hws)

/-- A trapped image: the `coreAt` outcome `none`. -/
theorem trap (B : ExpBack P c Ie x vs π π' t' y)
    (hc : (y.2.config y.1).code = [.trap] ∨
      ∃ b, (y.2.config y.1).code = Silmaril.Wasm.Execution.Core.throwing b) :
    none ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π := by
  obtain ⟨ρ, O, hL⟩ := B.link
  obtain ⟨ts, ht⟩ := B.threadOk
  rcases hc with hc | ⟨b, hc⟩
  · exact ⟨_, .trap, B.steps, trap_back P hL B.storeOk ht hc, rfl⟩
  · exact (throwing_back P hL B.storeOk ht hc).elim

end ExpBack

/-- **The exporter's run in the shared store.** A shared run, renamed by `g`, of the invocation
of export `x` of the exporter's instance `Ie` on the lowered arguments `vs`, where the shared
store relates the exporter's store `π` and the importer's `κ` (`Rel4`, the exporter's function
owned): the run never stops at a callout; a returned run has flat values of the result types,
is a `coreAt` outcome at `π` and a returned call `RetAt` whenever its lift succeeds, `Ie` well
formed after it; a trapped run is the `coreAt` outcome `none`. The relation holds again at the
end, for a new exporter store `π'` (`Rel4.after_p`), with `FnPre`. -/
theorem exp_run (hI : c.mod.IsInst Ie) (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    (typed : ValTy.checkList x.ty.params vs = true) {π κ : Store Nat} (hw : Ie.WellFormed π)
    {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own} (g : CanonHost (E3 P) → Nat)
    {σ : (E3 P).Store (CanonHost (E3 P))}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g σ) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0))
    {e : CoreSt (E3 P)}
    (he : Relation.ReflTransGen (CoreStep (E3 P))
      (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) e) :
    ∃ (π' : Store Nat) (ρp' : Ren) (Op' : Own),
      Rel4 Op₀ Oc₀ ρp' Op' ρc Oc (Store.mapH g e.1) π' κ ∧
      FnPre ({} : Store Nat) (Store.mapH g e.1) π' ∧
      (∀ h ys, (E3 P).status e.1 e.2 ≠ .callout h ys) ∧
      (∀ zs, (E3 P).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList x.ty.results ∧
        some zs ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π ∧
        ∀ ws, liftArgs x.ty.results zs = some ws → RetAt P c Ie x vs π ws π' ∧ Ie.WellFormed π') ∧
      ((E3 P).status e.1 e.2 = .returned .trap →
        none ∈ coreAt P Ie x.core (lowerArgs x.ty.params vs) π) := by
  obtain ⟨nm, hcx⟩ := hcore
  have hk : x.core < c.mod.exports.length := (List.getElem?_eq_some_iff.mp hcx).1
  have hO' : Op.fn (Ie.addrs.getD x.core 0) := hR.fnp ▸ hO
  have hL₀ := exp_invoke hR.rp hF hO' (lowerArgs x.ty.params vs)
  obtain ⟨ts, htyped, -⟩ := Silmaril.Wasm.Game.ScalarInstance.invoke_typed hw
    (opAt hI hk (exp_hxs hcx typed hk))
  have hrun : Silmaril.Wasm.Game.Reach P (Store.mapH g σ,
      Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
        (lowerArgs x.ty.params vs)) (Store.mapH g e.1, e.2) :=
    reach_mapH g (coreSteps_internalP he)
  obtain ⟨⟨π', t'⟩, ρp', Op', prun, hL, hgr, htc, hs', ht'⟩ :=
    reach_link_back hrun hL₀ hw.storeOk htyped
  have B : ExpBack P c Ie x vs π π' t' (Store.mapH g e.1, e.2) :=
    ⟨hI, ⟨nm, hcx⟩, typed, hw, prun, ⟨ρp', Op', hL⟩, hs', ⟨ts, ht'⟩⟩
  have hcode : ((e.2).config (Store.mapH g e.1)).code = ((e.2).config e.1).code :=
    config_code_mapH g e.1 e.2
  have hrel : PartRel ρp' Op' π' (Store.mapH g e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  refine ⟨π', ρp', Op', Rel4.after_p hR hrel hgr htc, hL.fn, ?_, ?_, ?_⟩
  · intro h ys hst
    obtain ⟨E, a', h', args', hd⟩ := status_callout hst
    obtain ⟨E', hd'⟩ := decompose?_mapH g hd
    exact B.no_callout (hcode ▸ hd')
  · intro zs hst
    obtain ⟨cvs, hc, hm⟩ := status_values hst
    exact B.values (hcode ▸ hc) hm
  · intro hst
    exact B.trap (hcode ▸ status_trap hst)

/-- **The exporter's half of a link site**: from any shared store related as in `exp_run`, the
exporter's runs on the lowering of lifted arguments never call out and return values of the flat
result types. -/
theorem exp_site_run (hI : c.mod.IsInst Ie)
    (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat)) {π κ : Store Nat}
    (hw : Ie.WellFormed π) {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    (g : CanonHost (E3 P) → Nat) {σ : (E3 P).Store (CanonHost (E3 P))}
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g σ) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0))
    {ys : List Flat} :
    ∀ ws, liftArgs x.ty.params ys = some ws → ∀ e,
      Relation.ReflTransGen (CoreStep (E3 P))
        (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat (Ie.addrs.getD x.core 0)
          (lowerArgs x.ty.params ws)) e →
      (∀ h' ys', (E3 P).status e.1 e.2 ≠ .callout h' ys') ∧
      ∀ zs, (E3 P).status e.1 e.2 = .returned (.values zs) →
        zs.map (·.type) = ValTy.flatList x.ty.results := by
  intro ws hws e he
  have typed : ValTy.checkList x.ty.params ws = true :=
    Silmaril.Wasm.Component.checkList_of_liftArgs hws
  obtain ⟨π', ρp', Op', -, -, hco, hval, -⟩ :=
    exp_run (vs := ws) hI hcore typed hw g hR hF hO he
  exact ⟨hco, fun zs hz => (hval zs hz).1⟩

/-- **A link site from the exporter's facts**: a callout of the importer to the trampoline of
the exporter's lifted export `x` (core address `Ie.addrs.getD x.core 0`), at IR types within
the flat arities, from a shared store related as in `exp_run`. -/
theorem linkSite_exp {σ' : Type} {B : Machine.Config (E3 P) σ'} {y : CoreSt (E3 P)}
    {f : FuncId} {ys : List Flat}
    (hf : ArenaField.funcs.get? B.store f =
      some (.lifted (Ie.addrs.getD x.core 0) (witFt x.ty) {} ⟨1⟩))
    (hpf : floatFreeList x.ty.params = true) (hys : ys.map (·.type) = ValTy.flatList x.ty.params)
    (hmaxp : (ValTy.flatList x.ty.params).length ≤ 16) (hres : x.ty.results.length ≤ 1)
    (hrf : floatFreeList x.ty.results = true) (hmaxr : (ValTy.flatList x.ty.results).length ≤ 1)
    (hI : c.mod.IsInst Ie) (hcore : ∃ nm, c.mod.exports[x.core]? = some (nm, x.ty.flat))
    {π κ : Store Nat} (hw : Ie.WellFormed π) {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    (g : CanonHost (E3 P) → Nat)
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g y.1) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g y.1) π) (hO : Op₀.fn (Ie.addrs.getD x.core 0)) :
    LinkSite B y (.lowered f (witFt x.ty) {} ⟨2⟩) ys :=
  ⟨⟨f, Ie.addrs.getD x.core 0, x.ty, rfl, hf, hpf, hys, hmaxp, hres, hrf, hmaxr,
    exp_site_run hI hcore hw g hR hF hO⟩⟩

end Run

end Silmaril.Proofs.Wasm.Component.Reference
