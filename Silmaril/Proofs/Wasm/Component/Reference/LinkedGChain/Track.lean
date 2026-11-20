module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Rounds

/-!
# A round of a linked component, with its footprint tracked

A linked component used as an exporter (`LinkedG.toExp`) has, as its footprint, the union of
its exporter's footprint `F` and the image `img ρc Oc` of its importer's ownership. R2 and R3
(`RefData.Ends`, `RefData.BwdF`) ask that its core activation change the core store only inside
that footprint and by allocation (`CoreFoot.Within`), its footprint growing by fresh addresses
(`CoreFoot.Grows`). `RoundEndB` of `LinkedGRound` does not record either. Here the round is
followed with the footprint at its start tracked:

* `CoreFoot` algebra: `union`, `Under Fc σ₀ F` (`F` inside `Fc` or above the allocation of
  `σ₀`, its globals in `Fc`), reflexivity, monotonicity and the composition of `Within` along
  runs whose footprints stay `Under` the starting one (`within_trans`);
* `RelT … Fc σ₀ F y x`: the importer's relation of `LInvG` **at a witness** `ρc, Oc`, with the
  core store changed since `σ₀` only inside `Fc` and by allocation, and the combined footprint
  `F ∪ img ρc Oc` `Under Fc σ₀`. `RelT.reach`, `RelT.resume`: it survives the importer's runs
  (`reach_link_fwd`'s `Touch` and `Grow`) and the exporter's returns (`Within`, `Grows` of R2);
* `TrapT`: the same at a trapped core store (with the exporter's relation there);
* `rounds_fwdT`: `rounds_fwdB` with `RelT` along the round: its ends (`RoundEndT`) carry
  `RelT` at the importer's result, or `TrapT` at the trapped core store.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload sigN)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

/-! ## Footprint algebra -/

section Foot

variable {H : Type}

/-- The union of two footprints. -/
def footUnion (F G : CoreFoot) : CoreFoot :=
  ⟨fun a => F.gl a ∨ G.gl a, fun a => F.st a ∨ G.st a, fun a => F.ar a ∨ G.ar a⟩

/-- **`F` lies under `Fc` at `σ₀`**: its globals are `Fc`'s, its structs and arrays are `Fc`'s or
not yet allocated in `σ₀`. -/
structure Under (Fc : CoreFoot) (σ₀ : Store H) (F : CoreFoot) : Prop where
  gl : ∀ a, F.gl a → Fc.gl a
  st : ∀ a, F.st a → Fc.st a ∨ σ₀.structs.length ≤ a
  ar : ∀ a, F.ar a → Fc.ar a ∨ σ₀.arrays.length ≤ a

theorem under_refl (F : CoreFoot) (σ : Store H) : Under F σ F :=
  ⟨fun _ h => h, fun _ h => .inl h, fun _ h => .inl h⟩

theorem within_refl (F : CoreFoot) (σ : Store H) : F.Within σ σ :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, le_refl _, le_refl _⟩

theorem grows_refl (F : CoreFoot) (σ : Store H) : F.Grows F σ :=
  ⟨fun _ => Iff.rfl, fun _ h => h, fun _ h => h, fun _ h => .inl h, fun _ h => .inl h⟩

theorem within_union_left {F G : CoreFoot} {σ σ' : Store H} (h : F.Within σ σ') :
    (footUnion F G).Within σ σ' where
  funcs := h.funcs
  globals a ha := h.globals a (fun h' => ha (.inl h'))
  structs a ha := h.structs a (fun h' => ha (.inl h'))
  arrays a ha := h.arrays a (fun h' => ha (.inl h'))
  structs_len := h.structs_len
  arrays_len := h.arrays_len

theorem within_union_right {F G : CoreFoot} {σ σ' : Store H} (h : G.Within σ σ') :
    (footUnion F G).Within σ σ' where
  funcs := h.funcs
  globals a ha := h.globals a (fun h' => ha (.inr h'))
  structs a ha := h.structs a (fun h' => ha (.inr h'))
  arrays a ha := h.arrays a (fun h' => ha (.inr h'))
  structs_len := h.structs_len
  arrays_len := h.arrays_len

/-- **Changes compose**: changes since `σ₀` inside `Fc`, then changes inside a footprint under
`Fc` at `σ₀`, are changes since `σ₀` inside `Fc`. -/
theorem within_trans {Fc F : CoreFoot} {σ₀ σ σ' : Store H} (h₀ : Fc.Within σ₀ σ)
    (hU : Under Fc σ₀ F) (h : F.Within σ σ') : Fc.Within σ₀ σ' where
  funcs := h.funcs.trans h₀.funcs
  globals a ha := (h.globals a (fun hF => ha (hU.gl a hF))).trans (h₀.globals a ha)
  structs a ha hl := by
    have hn : ¬ F.st a := fun hF => (hU.st a hF).elim ha (fun h' => by omega)
    exact (h.structs a hn (lt_of_lt_of_le hl h₀.structs_len)).trans (h₀.structs a ha hl)
  arrays a ha hl := by
    have hn : ¬ F.ar a := fun hF => (hU.ar a hF).elim ha (fun h' => by omega)
    exact (h.arrays a hn (lt_of_lt_of_le hl h₀.arrays_len)).trans (h₀.arrays a ha hl)
  structs_len := h₀.structs_len.trans h.structs_len
  arrays_len := h₀.arrays_len.trans h.arrays_len

theorem under_grows {Fc F F' : CoreFoot} {σ₀ σ : Store H} (hU : Under Fc σ₀ F)
    (hg : F.Grows F' σ) (hs : σ₀.structs.length ≤ σ.structs.length)
    (ha : σ₀.arrays.length ≤ σ.arrays.length) : Under Fc σ₀ F' where
  gl a h := hU.gl a ((hg.gl a).mp h)
  st a h := (hg.stNew a h).elim (hU.st a) (fun h' => .inr (le_trans hs h'))
  ar a h := (hg.arNew a h).elim (hU.ar a) (fun h' => .inr (le_trans ha h'))

theorem grows_union {F F' G G' : CoreFoot} {σ : Store H} (hF : F.Grows F' σ)
    (hG : G.Grows G' σ) : (footUnion F G).Grows (footUnion F' G') σ where
  gl a := or_congr (hF.gl a) (hG.gl a)
  st a := Or.imp (hF.st a) (hG.st a)
  ar a := Or.imp (hF.ar a) (hG.ar a)
  stNew a h := h.elim (fun h => (hF.stNew a h).imp_left .inl) (fun h => (hG.stNew a h).imp_left .inr)
  arNew a h := h.elim (fun h => (hF.arNew a h).imp_left .inl) (fun h => (hG.arNew a h).imp_left .inr)

/-- A touch of a part, read on the shared store under a host-code renaming. -/
theorem within_of_touchH (g : H → Nat) {ρ : Ren} {O : Own} {σ σ' : Store H}
    (h : Touch ρ O (Store.mapH g σ) (Store.mapH g σ')) (hf : σ'.funcs = σ.funcs) :
    (img ρ O).Within σ σ' where
  funcs := hf
  globals a ha := h.globals a ha
  structs a ha hl := h.structs a (fun b hb e => ha ⟨b, hb, e⟩) hl
  arrays a ha hl := h.arrays a (fun b hb e => ha ⟨b, hb, e⟩) hl
  structs_len := h.structs_len
  arrays_len := h.arrays_len

theorem grows_of_growH (g : H → Nat) {ρ ρ' : Ren} {O O' : Own} {σ : Store H}
    (h : Grow ρ O ρ' O' (Store.mapH g σ)) : (img ρ O).Grows (img ρ' O') σ :=
  have h' := grows_of_grow h
  ⟨h'.gl, h'.st, h'.ar, h'.stNew, h'.arNew⟩

end Foot

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}

/-! ## The tracked relation -/

/-- **The importer's relation at a witness, tracked**: `LInvG.rel` at `ρc, Oc` (the importer's
part at `x` related to the shared thread `y`, its image disjoint from the exporter's footprint
`F`), the core store changed since `σ₀` only inside `Fc` and by allocation, and the combined
footprint `F ∪ img ρc Oc` under `Fc` at `σ₀`. -/
def RelT (s₀ : Store Nat) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own) (Fc : CoreFoot)
    (σ₀ : Store (CanonHost (E3 P))) (F : CoreFoot) (y : CoreSt (E3 P)) (x : Store Nat × STh) :
    Prop :=
  ∃ (ρc : Ren) (Oc : Own), LinkSt s₀ ρc Oc x (Store.mapH g y.1, y.2) ∧ Oc.fn = Oc₀.fn ∧
    Oc.gl = Oc₀.gl ∧ FootDisj F ρc Oc y.1 ∧ Fc.Within σ₀ y.1 ∧
    Under Fc σ₀ (footUnion F (img ρc Oc))

/-- **The tracked relation at a trapped core store `c`**: the exporter's relation at a store
with the core store `c` and the functions of `S₀`, the importer's store `u` related to `c` at a
witness disjointly from it, `c` changed since `σ₀` only inside `Fc` and by allocation, the
combined footprint under `Fc` at `σ₀`. -/
def TrapT {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (s₀ : Store Nat)
    (g : CanonHost (E3 P) → Nat) (Oc₀ : Own) (Fc : CoreFoot) (σ₀ : Store (CanonHost (E3 P)))
    (S₀ : CStore (E3 P)) (s : e.St) (c : (E3 P).Store (CanonHost (E3 P))) (u : Store Nat) :
    Prop :=
  ∃ (S' : RefStore (E3 P)) (F' : CoreFoot) (ρc : Ren) (Oc : Own), S'.core = c ∧
    S'.funcs = S₀.funcs ∧ d.Hold pl s S' F' ∧ PartRel ρc Oc (reloc s₀ u) (Store.mapH g c) ∧
    Oc.fn = Oc₀.fn ∧ Oc.gl = Oc₀.gl ∧ FootDisj F' ρc Oc c ∧ Fc.Within σ₀ c ∧
    Under Fc σ₀ (footUnion F' (img ρc Oc))

section Track

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl} {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))}

/-- **The tracked relation at the start**: `LInvG.rel` at a witness, with the starting store and
the combined footprint. -/
theorem relT_start {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh} {ρc : Ren} {Oc : Own}
    (hL : LinkSt s₀ ρc Oc x (Store.mapH g y.1, y.2)) (hfn : Oc.fn = Oc₀.fn) (hgl : Oc.gl = Oc₀.gl)
    (hD : FootDisj F ρc Oc y.1) :
    RelT s₀ g Oc₀ (footUnion F (img ρc Oc)) y.1 F y x :=
  ⟨ρc, Oc, hL, hfn, hgl, hD, within_refl _ _, under_refl _ _⟩

/-- **A run of the importer's part, tracked**: `LInvG.reach_fwd` keeping `RelT`. -/
theorem RelT.reach (SI : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) {s : e.St}
    {M : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) (hT : RelT s₀ g Oc₀ Fc σ₀ F y x)
    {x' : Store Nat × STh} (hx : Silmaril.Wasm.Game.Reach P x x') :
    ∃ y', Relation.ReflTransGen (CoreStep (E3 P)) y y' ∧
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s { M with core := y'.1 } F y' x' ∧
      RelT s₀ g Oc₀ Fc σ₀ F y' x' := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  obtain ⟨y', ρc', Oc', hrun, hL', hgr, htc, hfy⟩ :=
    reach_link_fwd g tr hx (SI.hostsSat hI.funcs) hL
  have hag : F.Agree (M.core : Store (CanonHost (E3 P))) y'.1 := by
    rw [hI.core]
    exact agree_of_touch hD htc hfy
  have hD' : FootDisj F ρc' Oc' y'.1 := hD.after_part hgr htc
  have hWi : (footUnion F (img ρc Oc)).Within y.1 y'.1 :=
    within_union_right (within_of_touchH g htc hfy)
  refine ⟨y', hrun, ⟨⟨ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD'⟩,
    hFr.agree pl s M _ F hI.hold hag (List.prefix_refl _) (fun _ _ => rfl), rfl,
    hfy.trans hI.funcs, hI.run.trans (reach_ssteps hx)⟩,
    ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD', within_trans hW hU hWi,
    under_grows hU (grows_union (grows_refl F _) (grows_of_growH g hgr)) hW.structs_len
      hW.arrays_len⟩

/-- **The exporter returned, tracked**: `LInvG.resume_fwd` keeping `RelT` at the exporter's
grown footprint. -/
theorem RelT.resume {s : e.St} {M : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)}
    {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x)
    (hT : RelT s₀ g Oc₀ Fc σ₀ F y x) {k : Nat} {p : FuncTy}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {args : List Silmaril.Wasm.Execution.Core.Val}
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (us : List IVal) {M' : RefStore (E3 P)} {F' : CoreFoot}
    (hw : F.Within (M.core : Store (CanonHost (E3 P))) M'.core)
    (hgF : F.Grows F' (M.core : Store (CanonHost (E3 P))))
    (hB : F'.Bounded (M'.core : Store (CanonHost (E3 P)))) :
    RelT s₀ g Oc₀ Fc σ₀ F'
      (M'.core, (E3 P).resume M'.core y.2 (.values (lowerArgs p.results us)))
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  rw [hI.core] at hw hgF
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  have hrc : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g M'.core) := partRel_within hR0 hD hw
  have hfm : (Store.mapH g M'.core).funcs = (Store.mapH g y.1).funcs := mapH_funcs_eq g hw.funcs
  have hL1 : LinkSt s₀ ρc Oc x (Store.mapH g M'.core, y.2) := linkSt_transport hL hfm hrc
  have hL2 := link_resume hL1 hdx (ofFlat_scalar (lowerArgs p.results us))
  have hres : (E3 P).resume M'.core y.2 (.values (lowerArgs p.results us)) =
      Silmaril.Wasm.SingleThreaded.resumeResult (Store.mapH g M'.core) y.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)) :=
    (resume_values M'.core y.2 _).trans (resumeResult_mapH g M'.core y.2 _).symm
  exact ⟨ρc, Oc, hres ▸ hL2, hfn, hgl, hD.after_owner hR0 hgF hB,
    within_trans hW hU (within_union_left hw),
    under_grows hU (grows_union hgF (grows_refl _ _)) hW.structs_len hW.arrays_len⟩

/-- **The importer stopped, tracked**: `trapAt_of_linv` with `TrapT`. -/
theorem trapT_of_linv {s : e.St} {S : RefStore (E3 P)} {S₀ : CStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)}
    {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y x)
    (hT : RelT s₀ g Oc₀ Fc σ₀ F y x) (hf : S.funcs = S₀.funcs) :
    TrapT d pl s₀ g Oc₀ Fc σ₀ S₀ s y.1 x.1 := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  exact ⟨S, F, ρc, Oc, hI.core, hf, hI.hold, hR0, hfn, hgl, hD, hW, hU⟩

/-- **The exporter trapped, tracked**: `trapAt_of_within` with `TrapT`. -/
theorem trapT_of_within {s s' : e.St} {S S' : RefStore (E3 P)} {S₀ : CStore (E3 P)} {F F' : CoreFoot}
    {y : CoreSt (E3 P)} {x : Store Nat × STh} (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s S F y x)
    (hT : RelT s₀ g Oc₀ Fc σ₀ F y x) (hH : d.Hold pl s' S' F') (hf : S'.funcs = S₀.funcs)
    (hw : F.Within (S.core : Store (CanonHost (E3 P))) S'.core)
    (hgF : F.Grows F' (S.core : Store (CanonHost (E3 P))))
    (hB : F'.Bounded (S'.core : Store (CanonHost (E3 P)))) :
    TrapT d pl s₀ g Oc₀ Fc σ₀ S₀ s' S'.core x.1 := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD, hW, hU⟩ := hT
  rw [hI.core] at hw hgF
  have hR0 : PartRel ρc Oc (reloc s₀ x.1) (Store.mapH g y.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  exact ⟨S', F', ρc, Oc, rfl, hf, hH, partRel_within hR0 hD hw, hfn, hgl,
    hD.after_owner hR0 hgF hB, within_trans hW hU (within_union_left hw),
    under_grows hU (grows_union hgF (grows_refl _ _)) hW.structs_len hW.arrays_len⟩

theorem TrapT.funcs_congr {S₀ S₁ : CStore (E3 P)} {s : e.St}
    {c : (E3 P).Store (CanonHost (E3 P))} {u : Store Nat}
    (h : TrapT d pl s₀ g Oc₀ Fc σ₀ S₀ s c u) (hf : S₀.funcs = S₁.funcs) :
    TrapT d pl s₀ g Oc₀ Fc σ₀ S₁ s c u := by
  obtain ⟨S', F', ρc, Oc, h₁, h₂, h₃⟩ := h
  exact ⟨S', F', ρc, Oc, h₁, h₂.trans hf, h₃⟩

end Track

/-! ## A round, tracked -/

/-- **`RoundEndB` with the footprint tracked**: at the importer's result, `RelT` at the
importer's part there; at a trapped end, `TrapT` at the trapped core store. -/
def RoundEndT (prof : ProfileKind) (P : Profile) (impl : HostImpl (E3 P) σ) {e : ExpSpec}
    (d : e.RefData P) (pl : d.Pl) (ii : Nat) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (Fc : CoreFoot) (σ₀ : Store (CanonHost (E3 P)))
    (f : Ii.F.Op) (M : Machine.Config (E3 P) σ) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) (y : CoreSt (E3 P)) (s₁ : e.St) (u₁ : Store Nat)
    (w : Ii.F.Ar f) : Prop :=
  (∃ (trc : List (Label (E3 P) σ)) (C' : List (Option (Activation (E3 P) σ)))
      (S'' : RefStore (E3 P)) (F' : CoreFoot) (yc : CoreSt (E3 P)) (t' : STh)
      (r : Silmaril.Wasm.Execution.Core.Result),
    Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) trc
      (coreCfg { M with conts := C', store := S''.toCStore } th K segs rest yc) ∧ NoHI trc ∧
    LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s₁ S'' F' yc (u₁, t') ∧
    RelT s₀ g Oc₀ Fc σ₀ F' yc (u₁, t') ∧
    Silmaril.Wasm.Game.ResultAt u₁ t' r ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) r = some w ∧
    FrameG d pl ii th S'' ∧ CallExt d pl M.ref S'') ∨
  (∃ c, TrapEnd prof P impl (coreCfg M th K segs rest y) c ∧
    TrapAtG d pl Ii s₀ u₀ F₀ g Oc₀ f M.store s₁ c u₁ ∧
    TrapT d pl s₀ g Oc₀ Fc σ₀ M.store s₁ c u₁ ∧
    Silmaril.Wasm.Game.Answer.ofResult? (Ii.exports.get f.1) .trap = some w)

section Round

variable {lg : LinkedG} {Ii : SInst} {u₀ s₀ : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {g : CanonHost (E3 P) → Nat}
  {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op} {d : lg.exp.RefData P} {pl : d.Pl}
  {ii : Nat} {Fc : CoreFoot} {σ₀ : Store (CanonHost (E3 P))}

/-- **A round of the importer against the exporter, tracked**: `rounds_fwdB` keeping `RelT`. -/
theorem rounds_fwdT (SI : ImpStatG P lg.imp Ii u₀ F₀ g tr) (W : WireG lg d pl tr ii)
    (hFr : d.Frame) (hFw : d.Fwd) (hB : d.Bounded) (th : Option ThreadId)
    (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))) (segs : List (Seg (E3 P) σ))
    (rest : List (Activation (E3 P) σ)) {w : Ii.F.Ar f} :
    ∀ (rs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN lg.imp.imports.length).Op, Option Payload)))
      (M : Machine.Config (E3 P) σ) (s s₁ : lg.exp.St) (F : CoreFoot) (y : CoreSt (E3 P))
      (x : Store Nat × STh) (u₁ : Store Nat),
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M.ref F y x → RelT s₀ g Oc₀ Fc σ₀ F y x →
      FrameG d pl ii th M.store →
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss →
      LinkedG.ExpRun P lg s dss.flatten s₁ →
      Ii.Path P (.running f x.1 x.2) (callMoves rs ++ [.inr (.ans f w)]) (.idle u₁) →
      RoundEndT prof P impl d pl ii Ii s₀ u₀ F₀ g Oc₀ Fc σ₀ f M th K segs rest y s₁ u₁ w
  | [], dss, M, s, s₁, F, y, x, u₁, hI, hT, hFG, hrel, hexp, hpath => by
    cases hrel
    cases hexp
    obtain ⟨s', t', r, run, final, hw, hq⟩ := path_ret_inv (by simpa [callMoves] using hpath)
    cases hq
    obtain ⟨yc, hy, hIc, hTc⟩ := RelT.reach SI hFr hI hT run
    obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy
    exact .inl ⟨tr₀, M.conts, { M.store with core := yc.1 }, F, yc, t', r, r₀,
      NoHI.of_core htr₀, hIc, hTc, final, hw, hFG.core _, callExt_refl _⟩
  | ⟨eq, v⟩ :: rs, dss₀, M, s, s₁, F, y, x, u₁, hI, hT, hFG, hrel, hexp, hpath => by
    obtain ⟨ds, dss, hd, hrel', rfl⟩ : ∃ ds dss,
        Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii ⟨eq, v⟩ ds ∧
        List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel lg.imp Ii) rs dss ∧
        dss₀ = ds :: dss := by
      cases hrel with
      | cons h₁ h₂ => exact ⟨_, _, h₁, h₂, rfl⟩
    obtain ⟨s', t', k, args, run, co, op, hpath'⟩ := path_round_inv (rest := callMoves rs ++
      [.inr (.ans f w)]) (by simpa [callMoves] using hpath)
    obtain ⟨y₁, hy₁, hI₁, hT₁⟩ := RelT.reach SI hFr hI hT run
    let M₁ : Machine.Config (E3 P) σ := { M with core := y₁.1 }
    have hFG₁ : FrameG d pl ii th M₁.store := hFG
    obtain ⟨tr₀, htr₀, r₀⟩ := Adequacy.coreCfg_steps_of (prof := prof) (hr := fun _ _ => false)
      (dispatch := DI P impl) (B := M) (th := th) (K := K) (segs := segs) (rest := rest) hy₁
    have r₀' : Machine.Steps prof (fun _ _ => false) (DI P impl) (coreCfg M th K segs rest y) tr₀
        (coreCfg M₁ th K segs rest y₁) := r₀
    have hX₁ : CallExt d pl M.ref M₁.ref := callExt_refl _
    obtain ⟨nm, p, ys, E, a, hk, hdx, hys, hst, hyty⟩ := hI₁.callout_fwd SI co op
    obtain ⟨wi, xe, hwire, hxe, hty, htr⟩ := W.site k nm p hk
    have hek := ifaceOp?_some op
    obtain ⟨nm', ft, A, hk', hA, hm⟩ := hd
    have hA' : payloadAnswer (Ii.imports.get eq.1) A = v := hA
    have hft : ft = p := by
      rw [hek.1, hk] at hk'
      simp only [Option.some.injEq, Prod.mk.injEq] at hk'
      exact hk'.2.symm
    subst hft
    have hfilt : eq.2.1.filterMap Silmaril.Wasm.SingleThreaded.toFlat? = ys :=
      hek.2 ▸ filterMap_of_mapM hys
    have hmi : (nm, ft) ∈ lg.imp.imports := List.mem_of_getElem? hk
    obtain ⟨hmaxp, hmaxr, hres⟩ := W.arity.2 _ hmi
    obtain ⟨hpf, hrf⟩ := W.floats.2 _ hmi
    rw [hfilt] at hm
    split at hm
    · -- the arguments do not lift
      next hws =>
      obtain ⟨rfl, rfl⟩ := hm
      have hv : v = .trap := hA.symm
      subst hv
      obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
      cases hrel'
      cases hexp
      obtain ⟨ιi, hi, hleave⟩ := hFG₁.imp
      obtain ⟨ιe, hie, hth⟩ := hFG₁.exp wi ⟨xe, hxe⟩
      obtain ⟨hf, -⟩ := hFr.lifted pl s M₁.ref F wi xe hI₁.hold hxe
      rw [hty] at hf
      rw [htr] at hst
      have hT := (nest_trap_argsG (prof := prof) (impl := impl) (d.inst pl wi) ii M₁ hFG₁.lock ιe
        _ th K segs rest y₁ ⟨d.fid pl wi⟩ (d.addr pl wi) ft ys ιi hst (hFG₁.entry _ _ _) hi
        hleave hf hie (addThread?_ok hth _) hpf hyty hmaxp hws).toS.trapEnd
      exact .inr ⟨y₁.1, TrapEnd.steps r₀' (Quiet.of_core htr₀) hT, trapAt_of_linv hI₁ rfl,
        trapT_of_linv hI₁ hT₁ rfl, hw'⟩
    · next ws hws =>
      obtain ⟨hkl, R, rfl, hAR⟩ := hm
      have hexp' : LinkedG.ExpRun P lg s
          (⟨(⟨eq.1.val, hkl⟩, .vals ws), R⟩ :: dss.flatten) s₁ := by
        simpa only [List.flatten_cons, List.singleton_append] using hexp
      cases hexp' with
      | @step _ s₂ _ _ _ _ _ w₂ hwire' hstep hrest =>
        have hw₂ : w₂.val = wi := by
          rw [hek.1, hwire] at hwire'
          exact (Option.some.inj hwire').symm
        rw [hw₂] at hstep
        rcases call_stepB' (prof := prof) (impl := impl) SI hFr hFw hI₁ th hFG₁ co op hk hxe
            hty htr K segs rest hpf hmaxp hres hrf hmaxr hys hws hstep with
          ⟨us, rfl, hck, trc, C', S'', F', hrun, hnh, hni, hH, hwi, hgr, hFG₂, hX, -⟩ |
          ⟨rfl, c, hTE, S', F', hc', hfS, hH, hwi, hgr⟩
        · have hv : Silmaril.Wasm.Game.Answer.toResult v =
              .values ((lowerArgs ft.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
            rw [← hA', hAR]
            have hup : (some (Payload.vals us)).bind (Silmaril.Wasm.Component.Adapter.lower ft).up =
                some (.flat (lowerArgs ft.results us)) := by
              simp only [Option.bind_some, Silmaril.Wasm.Component.Adapter.up,
                Silmaril.Wasm.Component.checkLower, hck, ite_true, Option.map_some]
            rw [hup, payloadAnswer_flat (w := .values ⟨_, SI.resAnswer hk hek.1 hck⟩) rfl]
            rfl
          rw [hv] at hpath'
          have hBH := hB pl _ S'' F' hH
          have hI₂ := LInvG.resume_fwd SI hI₁ hk hdx op hck hH hwi hgr hBH
          have hT₂ := RelT.resume (p := ft) hI₁ hT₁ hdx us hwi hgr hBH
          have hX₂ : CallExt d pl M.ref S'' := callExt_trans hX₁ hX
          rcases rounds_fwdT SI W hFr hFw hB th K segs rest rs dss
              { M₁ with conts := C', store := S''.toCStore, core := S''.core } s₂ s₁ F' _ _ u₁ hI₂ hT₂ hFG₂ hrel' hrest
              hpath' with
            ⟨trc', C'', S''', F'', yc, t'', r, hrun', hq', hIc, hTc, final, hw'', hFG', hX'⟩ |
            ⟨c, hTE, hTA, hTT, hw''⟩
          · exact .inl ⟨tr₀ ++ (trc ++ trc'), C'', S''', F'', yc, t'', r,
              Adequacy.steps_append r₀' (Adequacy.steps_append hrun hrun'),
              (NoHI.of_core htr₀).append ((show NoHI trc from ⟨hnh, hni⟩).append hq'), hIc, hTc,
              final, hw'', hFG', callExt_trans hX₂ hX'⟩
          · exact .inr ⟨c, TrapEnd.stepsI (Adequacy.steps_append r₀' hrun)
              ((NoHI.of_core htr₀).append ⟨hnh, hni⟩) hTE, hTA.funcs_congr (callExt_funcs hX₂),
              hTT.funcs_congr (callExt_funcs hX₂), hw''⟩
        · have hv : v = .trap := by
            rw [← hA', hAR]
            rfl
          subst hv
          obtain ⟨rfl, rfl, hw'⟩ := path_doomed co hpath'
          cases hrel'
          cases hrest
          subst hc'
          have hBH := hB pl _ S' F' hH
          exact .inr ⟨S'.core, TrapEnd.steps r₀' (Quiet.of_core htr₀) hTE,
            (trapAt_of_within hI₁ hH hfS hwi hgr hBH).funcs_congr rfl,
            (trapT_of_within hI₁ hT₁ hH hfS hwi hgr hBH).funcs_congr rfl, hw'⟩

end Round

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
