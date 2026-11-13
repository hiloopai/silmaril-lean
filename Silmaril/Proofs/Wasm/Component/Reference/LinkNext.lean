module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkPlay

/-!
# The invariant between linked calls

After a linked call the shared core store is no longer the exporter's store followed by the
importer's: both parts allocated into it, interleaved. Between calls it is related to the
exporter's store `π` and the importer's `u` as along a call (`LReady`): `Rel4` for the
ownerships of `rel4_init` (fixed by the stores `s₀`, `u₀` after instantiation), the functions of
both parts functions of the shared store, both instances well formed, the shared functions `F₀`,
and the importer's store in the split fragment for the functions of `u₀` (`SGoodSt`).

* `SGood`, `sgood_ssteps`: a configuration in the split fragment whose ownership has the
  functions `Fn` stays so along runs of the part against `valEnv` (`step_sim`; answers are
  typed values);
* `linv_ready`: `LInv` at the importer's export call from `LReady` (`linkSt_invoke`), the start
  `linv_init` generalised;
* `lready_init`: `LReady` after instantiation (`rel4_init`);
* `lready_after`: `LInv` at any point gives `LReady` at the shared store and the part's store
  (`good_ssteps`, `wellFormed_of_funcs'`, `sgood_ssteps`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst Config)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4)

variable {P : Profile}

/-! ## The split fragment with fixed functions -/

/-- The store `u` is related to some store for an ownership with the functions `Fn`. -/
def SGoodSt (Fn : Nat → Prop) (u : Store Nat) : Prop :=
  ∃ (ρ : Ren) (O : Own) (σ : Store Nat), PartRel ρ O u σ ∧ O.fn = Fn

/-- The configuration `c` is in the split fragment for an ownership with the functions `Fn`. -/
def SGood (Fn : Nat → Prop) (c : Config Nat) : Prop :=
  ∃ (ρ : Ren) (O : Own) (σ : Store Nat), PartRel ρ O c.store σ ∧ O.FrameGood c.frame ∧
    O.CodeGood c.code ∧ O.fn = Fn

theorem SGood.st {Fn : Nat → Prop} {c : Config Nat} (h : SGood Fn c) : SGoodSt Fn c.store := by
  obtain ⟨ρ, O, σ, hR, -, -, hfn⟩ := h
  exact ⟨ρ, O, σ, hR, hfn⟩

theorem SGood.splitGood {Fn : Nat → Prop} {c : Config Nat} (h : SGood Fn c) : SplitGood c := by
  obtain ⟨ρ, O, σ, hR, hf, hc, -⟩ := h
  exact ⟨ρ, O, σ, hR, hf, hc⟩

theorem SGood.step {Fn : Nat → Prop} {c c' : Config Nat}
    (h : Silmaril.Wasm.Execution.Core.Step P (fun _ _ _ _ => False) c c') (hg : SGood Fn c) :
    SGood Fn c' := by
  obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := hg
  obtain ⟨ρ', O', σ', -, hR', hf', hc', hgr, -⟩ :=
    Silmaril.Proofs.Wasm.Game.Linking.Split.step_sim h hR hf hc
  exact ⟨ρ', O', σ', hR', hf', hc', hgr.fn.trans hfn⟩

/-- Values of scalar types are good for every ownership. -/
theorem goodVal_of_hasVal {O : Own} :
    ∀ {ts : List Silmaril.Wasm.Game.ScalarType} {vs : List Silmaril.Wasm.Execution.Core.Val},
      List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal ts vs → ∀ v ∈ vs, O.GoodVal v
  | [], [], .nil => fun _ h => absurd h List.not_mem_nil
  | t :: ts, w :: vs, .cons hw hr => by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · cases t with
      | num t => obtain ⟨b, rfl⟩ := hw; trivial
      | v128 => obtain ⟨b, rfl⟩ := hw; trivial
      | i31 n =>
        rcases hw with ⟨b, rfl⟩ | ⟨-, rfl⟩
        · exact (O.goodVal_ref _).mpr (O.goodRef_i31 b)
        · exact (O.goodVal_ref _).mpr O.goodRef_null
    · exact goodVal_of_hasVal hr v hv

/-- **Runs of the part against `valEnv` stay in the split fragment** for the functions `Fn`. -/
theorem sgood_ssteps {I : Silmaril.Wasm.Game.ScalarInstance} {Fn : Nat → Prop}
    {x y : Config Nat × (valEnv I).S}
    (h : Silmaril.Wasm.Game.SSteps P (valEnv I) x y) (hg : SGood Fn x.1) : SGood Fn y.1 := by
  induction h with
  | refl => exact hg
  | tail _ hst ih =>
    cases hst with
    | internal h0 => exact ih.step h0
    | @answer c E a h args e w q q' hd op ans =>
      obtain ⟨v, rfl⟩ := ans
      obtain ⟨ρ, O, σ, hR, hf, hc, hfn⟩ := ih
      obtain ⟨fi, yy, ps, rs, -, -, -, -, -, hcode⟩ :=
        Silmaril.Wasm.SingleThreaded.decompose?_sound hd
      have hc' : O.CodeGood
          (E.fill (Silmaril.Wasm.Execution.Core.vals args ++ [.ref (.func a), yy])) :=
        hcode ▸ hc
      exact ⟨ρ, O, σ, hR, hf, hc'.fill E (O.codeGood_vals.mpr (goodVal_of_hasVal v.2)), hfn⟩
    | silent => exact ih

/-- The invocation of an owned function of a store in the split fragment. -/
theorem sgood_invoke {Fn : Nat → Prop} {u : Store Nat} (hu : SGoodSt Fn u) {a : Nat} (ha : Fn a)
    {vs : List Silmaril.Wasm.Execution.Core.Val} (hvs : ∀ (O : Own), ∀ v ∈ vs, O.GoodVal v) :
    SGood Fn (Silmaril.Wasm.Execution.Core.invoke u a vs) := by
  obtain ⟨ρ, O, σ, hR, hfn⟩ := hu
  have hO : O.fn a := hfn ▸ ha
  obtain ⟨fi, hfi, -⟩ := hR.fn a hO
  have hcode : O.CodeGood (Silmaril.Wasm.Execution.Core.invoke u a vs).code := by
    simp only [Silmaril.Wasm.Execution.Core.invoke, hfi, Option.map_some, Option.getD_some]
    exact O.codeGood_append.mpr ⟨O.codeGood_vals.mpr (hvs O),
      Silmaril.Proofs.Wasm.Game.Linking.Split.Own.CodeGood.cons_ref hO (by simp [Own.CodeGood])⟩
  exact ⟨ρ, O, σ, hR, ⟨⟨rfl, rfl, rfl, rfl, rfl, nofun, nofun⟩, nofun⟩, hcode, hfn⟩

theorem sgoodSt_of_storeGood {u : Store Nat} (hg : StoreGood u) : SGoodSt (ownOf u).fn u :=
  ⟨Ren.id, ownOf u, u, hg.partRel, rfl⟩

/-- Well-formedness transfers to a well-typed store with the same functions. -/
theorem wellFormed_of_funcs' {I : Silmaril.Wasm.Game.ScalarInstance} {s s' : Store Nat}
    (hw : I.WellFormed s) (hs' : Silmaril.Wasm.Execution.Core.StoreOk s')
    (hf : s'.funcs = s.funcs) : I.WellFormed s' := by
  refine ⟨hs', hw.addrs_length, fun j => ?_, fun a fi h ha hc => hw.host_type a fi h (hf ▸ ha) hc⟩
  rw [hf]
  exact hw.export_type j

/-! ## The invariant between calls -/

/-- **The invariant between linked calls** at the shared core store `cs`, the importer's store
`u` and the exporter's `π`: the ownerships are those of `rel4_init` at the stores `s₀`, `u₀`
after instantiation. -/
structure LReady (P : Profile) (l : Linked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance)
    (s₀ u₀ : Store Nat) (F₀ : List (FuncInst (CanonHost (E3 P))))
    (cs : Store (CanonHost (E3 P))) (u π : Store Nat) : Prop where
  rel : ∃ ρp Op ρc Oc, Rel4 (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) ρp Op ρc Oc
    (Store.mapH (gL P l) cs) π (reloc s₀ u)
  fnE : FnPre ({} : Store Nat) (Store.mapH (gL P l) cs) π
  fnC : FnPre s₀ (Store.mapH (gL P l) cs) u
  wfE : Ie.WellFormed π
  wfI : Ii.WellFormed u
  funcs : cs.funcs = F₀
  ufuncs : u.funcs = u₀.funcs
  good : SGoodSt (ownOf u₀).fn u

section Ready

variable {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {s₀ u₀ u π : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))}

/-- **The invariant at the importer's export call**, from the invariant between calls: the
shared thread invokes the relocated address of the export question `f` on flat arguments. -/
theorem linv_ready {y : CoreSt (E3 P)} (hR : LReady P l Ie Ii s₀ u₀ F₀ y.1 u π) {f : Ii.F.Op}
    {xs : List Flat} (hxs : f.2.1 = xs.map Silmaril.Wasm.SingleThreaded.ofFlat)
    (hth : y.2 = Silmaril.Wasm.SingleThreaded.Thread.invokeFlat
      (s₀.funcs.length + Ii.addr f.1) xs) :
    LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y (u, Ii.initThread f) π := by
  obtain ⟨ρp, Op, ρc, Oc, hR4⟩ := hR.rel
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
  have ha₀ : Ii.addr f.1 < u₀.funcs.length := hR.ufuncs ▸ ha
  have hvs : ∀ v ∈ f.2.1, ∀ r, v ≠ .ref r := hxs ▸ ofFlat_scalar xs
  have hO : Oc.fn (s₀.funcs.length + Ii.addr f.1) := by
    rw [hR4.fnc]
    exact ⟨Nat.le_add_right _ _, by simpa [ownOf] using ha₀⟩
  have hg : SplitGood (Silmaril.Wasm.Execution.Core.invoke u (Ii.addr f.1) f.2.1) :=
    (sgood_invoke hR.good (show (ownOf u₀).fn (Ii.addr f.1) from ha₀)
      (fun _ => goodVal_of_hasVal f.2.2)).splitGood
  have hL := linkSt_invoke hR4.rc hR.fnC ha hO hvs hg
  have hshared : (Store.mapH (gL P l) y.1, y.2) = (Store.mapH (gL P l) y.1,
      Silmaril.Wasm.SingleThreaded.Thread.pending (s₀.funcs.length + Ii.addr f.1) f.2.1) := by
    rw [hth, hxs]
    rfl
  exact ⟨⟨_, _, _, _, hshared ▸ hL, hR4⟩, hR.fnE, hR.wfE, hR.funcs, .refl⟩

/-- **The invariant after instantiation**: the shared core store renames under `gL` to the
exporter's store `s₀` followed by the importer's `u₀`, relocated, both good. -/
theorem lready_init {cs : Store (CanonHost (E3 P))} (hg₀ : StoreGood s₀) (hgu : StoreGood u₀)
    (hy : Store.mapH (gL P l) cs = reloc s₀ u₀) (hF : cs.funcs = F₀) (hwe : Ie.WellFormed s₀)
    (hwi : Ii.WellFormed u₀) : LReady P l Ie Ii s₀ u₀ F₀ cs u₀ s₀ where
  rel := by
    rw [hy]
    exact ⟨_, _, _, _, rel4_init hg₀ hgu⟩
  fnE := hy ▸ fnPre_prefix s₀ u₀
  fnC := hy ▸ fnPre_refl s₀ u₀
  wfE := hwe
  wfI := hwi
  funcs := hF
  ufuncs := rfl
  good := sgoodSt_of_storeGood hgu

/-- **The invariant between calls from the invariant along a call**: at any point of a call
started from `LReady` at the part's store `u`, the shared store, the part's store and the
exporter's store satisfy `LReady`. -/
theorem lready_after {cs : Store (CanonHost (E3 P))} (hR : LReady P l Ie Ii s₀ u₀ F₀ cs u π)
    {f : Ii.F.Op} {y : CoreSt (E3 P)}
    {x : Store Nat × Silmaril.Wasm.SingleThreaded.Thread} {π' : Store Nat}
    (hI : LInv P l Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f y x π') :
    LReady P l Ie Ii s₀ u₀ F₀ y.1 x.1 π' := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR4⟩ := hI.rel
  have hx1 : (x.2.config x.1).store = x.1 := Silmaril.Wasm.SingleThreaded.Thread.config_store _ _
  obtain ⟨ts, hg₀⟩ := SEnvTyping.good_invoke hR.wfI f
  have hg := SEnvTyping.good_ssteps (P := P) hR.wfI (valEnv_throwsBelow Ii _)
    (x := (_, ())) (y := (x.2.config x.1, ())) hg₀ hI.run
  have hs : Silmaril.Wasm.Execution.Core.StoreOk x.1 := by
    have h := Silmaril.Wasm.SingleThreaded.ConfigOk.storeOk hg.ok
    rwa [hx1] at h
  have hfx : x.1.funcs = u.funcs := hx1 ▸ hg.inv.funcs
  obtain ⟨fi, hfi, -⟩ := hR.wfI.export_type f.1
  have ha₀ : (ownOf u₀).fn (Ii.addr f.1) := by
    have ha : Ii.addr f.1 < u.funcs.length := (List.getElem?_eq_some_iff.mp hfi).1
    show Ii.addr f.1 < u₀.funcs.length
    exact hR.ufuncs ▸ ha
  have hsg := sgood_ssteps (P := P) (x := (_, ())) (y := (x.2.config x.1, ())) hI.run
    (sgood_invoke hR.good ha₀ (fun _ => goodVal_of_hasVal f.2.2))
  refine ⟨⟨ρp, Op, ρc, Oc, hR4⟩, hI.fnE, hL.fn, hI.wf, wellFormed_of_funcs' hR.wfI hs hfx,
    hI.funcs, hfx.trans hR.ufuncs, hx1 ▸ hsg.st⟩

end Ready

end Silmaril.Proofs.Wasm.Component.Reference
