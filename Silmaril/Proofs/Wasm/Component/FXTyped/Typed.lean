module

public import Silmaril.Proofs.Wasm.Component.FXTyped.Arity
public import Silmaril.Proofs.Wasm.Component.FXTyped.CoreSplit
public import Silmaril.Proofs.Wasm.Component.FXRefV.Run
public import Silmaril.Wasm.Component.FXTyped.Defs

/-!
# `SimpleFX.Typed` on the typed fragment

For `c : SimpleFX` with `c.Inst`, the `fxEV P` engine instance `J` of `c`'s module has the store
`csOf c f' cs₁`: the Core instance's store `cs₁` followed by the FX functions (`allocFX_ext`,
`allocFX_func`).

* **Core exports** (`typedAt_core`): a Core thread never enters an FX function
  (`core_stays`), because its renamed run is a run of the Core instance in the extended store,
  which never reaches a host-call redex (`core_ext_run`, split fragment). Its returned values are
  then typed by the same lemma.
* **FX exports** (`arityAt_fx`): a returned call of FX function `d` returns
  `|d.type.results| = |flatList x.ty.results|` values (`fx_results_length`). With no flat
  results, this is typing (`typedAt_fx`).
* **`typed_of_frag`**: `c.Typed P` on the fragment `SimpleFX.Frag`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (decompose? Thread toFlat?)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Component.FXTyped
open Silmaril.Proofs.Wasm.Component.FXRefV (csOf ciOf addrOf HostFree hostFree_cs instOf_fxV SM_id)
open Silmaril.Proofs.Wasm.Component.Reference (inst_once Store.mapH FuncInst.mapH StoreGood
  storeGood_inst lowerList_types status_values decompose?_mapH)
open Silmaril.Wasm.Component.Engine.CoreEngine (Steps)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-! ## FX function allocation -/

theorem ext_ext (s : Store H) (L L' : List (FuncInst H)) : ext (ext s L) L' = ext s (L ++ L') := by
  simp [ext]

theorem allocHost_ext (s : Store H) (ft : V1.FuncType) (h : H) :
    (SingleThreaded.allocHost s ft h).1 = ext s [⟨SingleThreaded.ofFlatType ft, {}, .host h⟩] := rfl

/-- **`allocFX` appends functions.** -/
theorem allocFX_ext (inst : ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl), ∃ L, (allocFX inst s ds).1 = ext s L
  | s, [] => ⟨[], by simp [allocFX, ext]⟩
  | s, d :: ds => by
    obtain ⟨L, hL⟩ := allocFX_ext inst (SingleThreaded.allocHost s d.type (.fx (d.func inst))).1 ds
    refine ⟨[⟨SingleThreaded.ofFlatType d.type, {}, .host (.fx (d.func inst))⟩] ++ L, ?_⟩
    simp only [allocFX]
    rw [hL, allocHost_ext, ext_ext]

/-- **FX function `j` of `allocFX` at address `|s.funcs| + j`.** -/
theorem allocFX_func (inst : ModuleInst) :
    ∀ (s : Store (FXCode H)) (ds : List FXDecl) {j : Nat} {d : FXDecl}, ds[j]? = some d →
      (allocFX inst s ds).1.funcs[s.funcs.length + j]? =
        some ⟨SingleThreaded.ofFlatType d.type, {}, .host (.fx (d.func inst))⟩
  | _, [], _, _, h => by simp at h
  | s, d₀ :: ds, j, d, h => by
    simp only [allocFX]
    cases j with
    | zero =>
      cases Option.some.inj h
      obtain ⟨L, hL⟩ := allocFX_ext inst
        (SingleThreaded.allocHost s d₀.type (.fx (d₀.func inst))).1 ds
      rw [hL, Nat.add_zero]
      exact ext_funcs_getElem? (by simp [SingleThreaded.allocHost, allocFunc])
    | succ j =>
      have hl : (SingleThreaded.allocHost s d₀.type (FXCode.fx (d₀.func inst))).1.funcs.length =
          s.funcs.length + 1 := by simp [SingleThreaded.allocHost, allocFunc]
      have e := allocFX_func inst (SingleThreaded.allocHost s d₀.type (.fx (d₀.func inst))).1 ds
        (j := j) (d := d) (by simpa using h)
      rw [hl] at e
      rw [show s.funcs.length + (j + 1) = s.funcs.length + 1 + j by omega]
      exact e

theorem mapH_ext {H' : Type} (g : H → H') (s : Store H) (L : List (FuncInst H)) :
    Store.mapH g (ext s L) = ext (Store.mapH g s) (L.map (FuncInst.mapH g)) := by
  simp [Store.mapH, ext]

/-! ## The engine instance -/

/-- The data of the engine instance `J` of a `SimpleFX.Inst` component (host type `Nat`). -/
theorem inst_data {c : SimpleFX} (hi : c.Inst) {J : EInstance (fxEV P)}
    (hJ : instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J) :
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (cs₁ : Store (FXCode Nat)) (f' : Frame),
      c.core.IsInst I ∧
      instantiateOnce? ({} : Store (FXCode Nat)) c.core.mod [] = some (cs₁, f', none) ∧
      Store.mapH (fun _ => (0 : Nat)) cs₁ = I.store ∧ J.store = csOf c f' cs₁ ∧
      ∀ (k : Nat) (p : String × CoreFuncTy), c.mod.exports[k]? = some p →
        J.addrs[k]? = some (addrOf c I.addrs cs₁.funcs.length k) := by
  obtain ⟨I, mt, cs₁, f', hI, hv, hmt, ho, hs, ha⟩ :=
    inst_once (H := FXCode Nat) (fun _ => (0 : Nat)) hi.core
  obtain ⟨J', hJ', hJs, hJa⟩ := instOf_fxV (P := P) hi id hv hmt ho ha
  obtain rfl : J = J' := Option.some.inj (hJ.symm.trans hJ')
  refine ⟨I, cs₁, f', hI, ho, hs, ?_, hJa⟩
  rw [hJs, SM_id]

/-! ## Core exports -/

/-- **A Core thread whose renamed runs reach no host-call redex stays a Core thread.** -/
theorem core_stays (g : FXCode H → Nat) {σ : Store (FXCode H)} {t₀ : Thread}
    (hok : ∀ y, Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (Store.mapH g σ, t₀) y →
      decompose? y.1 (y.2.config y.1).code = none)
    {y : Store (FXCode H) × ThreadV H} (run : Steps (fxEV P) (σ, .core t₀) y) :
    ∃ t, y.2 = .core t ∧ Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P) (σ, t₀) (y.1, t) := by
  induction run with
  | refl => exact ⟨t₀, rfl, .refl⟩
  | @tail y z _ hstep ih =>
    obtain ⟨t, hy, hr⟩ := ih
    obtain ⟨s, t'⟩ := y
    dsimp only at hy hr
    subst hy
    rcases (hstep : InternalV P (s, .core t) z) with ⟨t₂, hz, hP⟩ | ⟨⟨F, args, hst⟩, -⟩
    · exact ⟨t₂, hz, hr.tail hP⟩
    · exfalso
      obtain ⟨E, a, hd⟩ := Silmaril.Proofs.Wasm.Component.FXEngineV.decompose?_of_statusP_callout hst
      obtain ⟨E', hd'⟩ := decompose?_mapH g hd
      have hc : (t.config (Store.mapH g s)).code = (t.config s).code := by
        rw [Silmaril.Proofs.Wasm.Component.FXEngine.config_mapH']
        rfl
      have hn := hok (Store.mapH g s, t) (Silmaril.Proofs.Wasm.Component.Reference.reach_mapH g hr)
      dsimp only at hn
      rw [hc, hd'] at hn
      cases hn

/-- A returned Core thread of `fxEV P` has flat returned Core status. -/
theorem core_returned {s : Store (FXCode H)} {t : Thread} {ys : List Flat}
    (h : statusV P s (.core t) = .returned (.values ys)) :
    flatStatus (Silmaril.Wasm.Game.statusP P s t) = .returned (.values ys) := by
  have hn : ∀ F args, Silmaril.Wasm.Game.statusP P s t ≠ .callout (.fx F) args := by
    intro F args e
    simp only [statusV, e, liftR] at h
    cases h
  have h' : liftR (Silmaril.Wasm.Game.statusP P s t) = .returned (.values ys) := h
  rw [Silmaril.Proofs.Wasm.Component.FXEngineV.liftR_eq hn] at h'
  exact Silmaril.Proofs.Wasm.Component.FXRefE.mapHostS_returned h'

/-- The address of a Core export in the engine instance. -/
theorem core_addr {c : SimpleFX} {I : Silmaril.Wasm.Game.ScalarInstance} {n : Nat} {k : Nat}
    {J : EInstance (fxEV P)} {a : Nat} (hk : k < c.core.exports.length)
    (hJa' : J.addrs[k]? = some (addrOf c I.addrs n k)) (hJa : J.addrs[k]? = some a) :
    a = I.addrs.getD k 0 := by
  have e : some (addrOf c I.addrs n k) = some a := hJa'.symm.trans hJa
  have e' : addrOf c I.addrs n k = I.addrs.getD k 0 := by simp only [addrOf, hk, ↓reduceIte]
  exact (Option.some.inj e).symm.trans e'

/-- The address of an FX export in the engine instance. -/
theorem fx_addr {c : SimpleFX} {I : Silmaril.Wasm.Game.ScalarInstance} {n : Nat} {k : Nat}
    {J : EInstance (fxEV P)} {a : Nat} (hk : c.core.exports.length ≤ k)
    (hJa' : J.addrs[k]? = some (addrOf c I.addrs n k)) (hJa : J.addrs[k]? = some a) :
    a = n + (k - c.core.exports.length) := by
  have e : some (addrOf c I.addrs n k) = some a := hJa'.symm.trans hJa
  have e' : addrOf c I.addrs n k = n + (k - c.core.exports.length) := by
    simp only [addrOf, show ¬ k < c.core.exports.length by omega, ↓reduceIte]
  exact (Option.some.inj e).symm.trans e'

/-- The engine instance's store, renamed, is the Core instance's store extended. -/
theorem store_ext {c : SimpleFX} {I : Silmaril.Wasm.Game.ScalarInstance} {cs₁ : Store (FXCode Nat)}
    {f' : Frame} {J : EInstance (fxEV P)} (hs : Store.mapH (fun _ => (0 : Nat)) cs₁ = I.store)
    (hJs : J.store = csOf c f' cs₁) :
    ∃ L, Store.mapH (fun _ => (0 : Nat)) (J.store : Store (FXCode Nat)) = ext I.store L := by
  obtain ⟨L, hL⟩ := allocFX_ext (fxInst f'.module cs₁.funcs.length c.fxs.length) cs₁ c.fxs
  refine ⟨L.map (FuncInst.mapH fun _ => (0 : Nat)), ?_⟩
  rw [hJs, show csOf c f' cs₁ = _ from hL, mapH_ext, hs]

/-- Returned values of a Core thread whose renamed runs are typed. -/
theorem core_values {s' : Store (FXCode Nat)} {t : Thread} {ys : List Flat} {rts : List NumType}
    (hst : statusV P s' (.core t) = .returned (.values ys))
    (hok : ∀ (cvs : List Silmaril.Wasm.Execution.Core.Val) (zs : List Flat),
      (t.config (Store.mapH (fun _ => (0 : Nat)) s')).code = vals cvs →
      cvs.mapM toFlat? = some zs → zs.map (·.type) = rts) : ys.map (·.type) = rts := by
  obtain ⟨cvs, hcv, hm⟩ := status_values (core_returned hst)
  have hc' : (t.config (Store.mapH (fun _ => (0 : Nat)) s')).code = (t.config s').code :=
    congrArg Config.code (Silmaril.Proofs.Wasm.Component.FXEngine.config_mapH'
      (fun _ : FXCode Nat => (0 : Nat)) s' t)
  exact hok cvs ys (hc'.trans hcv) hm

/-- **`Typed` at a Core export of a Core part in the split fragment.** -/
theorem typedAt_core {c : SimpleFX} (hi : c.Inst) (hsplit : Linked2.ModSplitOk c.core.mod)
    (hc : c.toSimple.Good) {x : SimpleExport} (hx : x ∈ c.exports)
    (hk : x.core < c.core.exports.length) : SimpleFX.TypedAt P c x := by
  intro J hJ vs hvs ys ⟨a, s', t', hJa, run, hres⟩
  obtain ⟨I, cs₁, f', hI, ho, hs, hJs, hJa'⟩ := inst_data (P := P) hi hJ
  obtain ⟨nm, hn⟩ := hc.core x hx
  have hget : c.core.exports[x.core] = (nm, x.ty.flat) :=
    (List.getElem?_eq_some_iff.mp ((List.getElem?_append_left hk).symm.trans hn)).2
  have hxs : (lowerArgs x.ty.params vs).map (·.type) = c.core.exports[x.core].2.params :=
    hget ▸ lowerList_types _ _ hvs
  have ha : a = I.addrs.getD x.core 0 := core_addr hk (hJa' x.core _ hn) hJa
  obtain ⟨L, hσ⟩ := store_ext hs hJs
  have hok : ∀ y, Relation.ReflTransGen (Silmaril.Wasm.Game.InternalP P)
      (Store.mapH (fun _ => (0 : Nat)) J.store, Thread.invokeFlat a (lowerArgs x.ty.params vs)) y →
      decompose? y.1 (y.2.config y.1).code = none ∧
        ∀ (cvs : List Silmaril.Wasm.Execution.Core.Val) (zs : List Flat),
          (y.2.config y.1).code = vals cvs → cvs.mapM toFlat? = some zs →
            zs.map (·.type) = c.core.exports[x.core].2.results :=
    fun y hy => core_ext_run (P := P) hI (storeGood_inst hsplit hI.1.choose_spec) hk hxs L
      (by rw [← hσ, ← ha]; exact hy)
  obtain ⟨t, ht, hr⟩ := core_stays (P := P) (fun _ => (0 : Nat)) (fun y hy => (hok y hy).1) run
  rcases hres with ⟨ys', hst, e⟩ | ⟨-, e⟩
  · show ys.map (·.type) = ValTy.flatList x.ty.results
    have hst' : statusV P s' (.core t) = .returned (.values ys) := by
      rw [Option.some.inj e, ← hst, show t' = .core t from ht]; rfl
    have hty := core_values hst' ((hok _ (Silmaril.Proofs.Wasm.Component.Reference.reach_mapH _ hr)).2)
    rw [hty, hget]
    rfl
  · cases e

/-! ## FX exports -/

/-- The FX declaration of an FX export of a `Good` component. -/
theorem fx_decl {c : SimpleFX} (hc : c.toSimple.Good) {x : SimpleExport} (hx : x ∈ c.exports)
    (hk : c.core.exports.length ≤ x.core) :
    ∃ nm d, c.mod.exports[x.core]? = some (nm, x.ty.flat) ∧
      c.fxs[x.core - c.core.exports.length]? = some d ∧
      ValTy.flatList x.ty.params = d.type.params ∧ ValTy.flatList x.ty.results = d.type.results := by
  obtain ⟨nm, hn⟩ := hc.core x hx
  have hfx : (fxIface c.fxs)[x.core - c.core.exports.length]? = some (nm, x.ty.flat) :=
    (List.getElem?_append_right hk).symm.trans hn
  obtain ⟨d, hd, hdp⟩ : ∃ d, c.fxs[x.core - c.core.exports.length]? = some d ∧
      (d.name, (⟨d.type.params, d.type.results⟩ : CoreFuncTy)) = (nm, x.ty.flat) := by
    simpa only [fxIface, List.getElem?_map, Option.map_eq_some_iff] using hfx
  have hty : (⟨d.type.params, d.type.results⟩ : CoreFuncTy) = x.ty.flat := (Prod.mk.inj hdp).2
  exact ⟨nm, d, hn, hd, (congrArg CoreFuncTy.params hty).symm,
    (congrArg CoreFuncTy.results hty).symm⟩

/-- **Arity at an FX export.** -/
theorem arityAt_fx {c : SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good) {x : SimpleExport}
    (hx : x ∈ c.exports) (hk : c.core.exports.length ≤ x.core) : SimpleFX.ArityAt P c x := by
  intro J hJ vs hvs ys ⟨a, s', t', hJa, run, hres⟩
  obtain ⟨I, cs₁, f', hI, ho, hs, hJs, hJa'⟩ := inst_data (P := P) hi hJ
  obtain ⟨nm, d, hn, hd, hpar, hres'⟩ := fx_decl hc hx hk
  have ha : a = cs₁.funcs.length + (x.core - c.core.exports.length) :=
    fx_addr hk (hJa' x.core _ hn) hJa
  have hA : FXAt J.store a (d.func (fxInst f'.module cs₁.funcs.length c.fxs.length)) d.type :=
    ⟨by rw [hJs, ha]; exact allocFX_func _ cs₁ c.fxs hd, rfl⟩
  have hxs : (lowerArgs x.ty.params vs).length = d.type.params.length := by
    have hl : (lowerArgs x.ty.params vs).map (·.type) = ValTy.flatList x.ty.params :=
      lowerList_types _ _ hvs
    rw [← hpar, ← hl, List.length_map]
  have hsF : HostFree J.store := hJs ▸ hostFree_cs ho
  rcases hres with ⟨ys', hst, e⟩ | ⟨-, e⟩
  · show ys.length = (ValTy.flatList x.ty.results).length
    rw [Option.some.inj e, fx_results_length hsF hA hxs run hst, hres']
    rfl
  · cases e

/-- **`Typed` at an FX export without flat results.** -/
theorem typedAt_fx {c : SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good) {x : SimpleExport}
    (hx : x ∈ c.exports) (hk : c.core.exports.length ≤ x.core)
    (h0 : ValTy.flatList x.ty.results = []) : SimpleFX.TypedAt P c x := by
  intro J hJ vs hvs ys hys
  have hl := arityAt_fx (P := P) hi hc hx hk J hJ vs hvs ys hys
  rw [h0] at hl ⊢
  rw [List.length_eq_zero_iff.mp hl]
  rfl

/-! ## The fragment -/

/-- **`SimpleFX.Typed` on the typed fragment.** -/
theorem typed_of_frag {c : SimpleFX} (hi : c.Inst) (hc : c.toSimple.Good)
    (hF : SimpleFX.Frag c) : c.Typed P := by
  intro J hJ x hx vs hvs ys hys
  by_cases hk : x.core < c.core.exports.length
  · exact typedAt_core hi (hF.core x hx hk) hc hx hk J hJ vs hvs ys hys
  · exact typedAt_fx hi hc hx (by omega) (hF.fx x hx (by omega)) J hJ vs hvs ys hys

end Silmaril.Proofs.Wasm.Component.FXTyped
