module

public import Silmaril.Wasm.Component.Reference.LinkedGImp.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef.SimpleInit

/-!
# The importer's invariant against an abstract exporter

`LInv` of `LinkSeg` carries the exporter of a `Linked2` as the provider half of `Rel4` (its
store `π` embedded along a renaming). Here the exporter is an abstract `RefData` `d` at a
placement `pl`: its part of the shared store is `d.Hold pl s S F` (state `s`, component store
`S`, footprint `F`), and the importer's part is related as in `LInv` (`LinkSt`), with its image
disjoint from `F` and `F` allocated (`FootDisj`).

* `ImpStatG`: the importer's static facts: `Good`, its core instance, and the host code of the
  shared functions `F₀`: every host function is the trampoline `tr k` of an import `k`, and the
  renaming `g` of host codes sends `tr k` to `k` (for `Linked2`, `tr k` is
  `.lowered (wireFid k) (witFt p) {} ⟨2⟩` and `g = trampIdxL`);
* `LInvG d pl … s S F y x`: the invariant at the shared core thread `y`, the importer's part
  thread `x`, the exporter's state `s`, the component store `S` (whose core store is `y.1`) and
  the footprint `F`;
* `LInvG.reach_fwd`: a run of the importer's part is a core run of the shared thread, keeping
  `LInvG` at the same exporter state and footprint (R1 for the importer's changes);
* `LInvG.callout_fwd`: a callout of the part to import `k` is a callout of the shared thread to
  the trampoline `tr k`, on flat arguments of the import's parameter types;
* `LInvG.resume_fwd`: after the exporter's core activation changed the component store to `S'`
  inside its footprint and by fresh addresses (`CoreFoot.Within`, `CoreFoot.Grows`), holding a
  new state `s'` with an allocated footprint `F'`, both threads resumed with the lowering of
  results `us` satisfy `LInvG` at `s'`, `S'`, `F'`. These are the importer-side facts of R2's
  return (`ExpSpec.RefData.Ends`), with R6 (`Bounded`) for the allocation of `F'`;
* `simple_bounded`: a simple exporter's data meets R6.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat FuncTy Payload)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "IVal" => Silmaril.Wasm.Component.Val

variable {P : Profile}

/-! ## Footprints disjoint from a part -/

section Foot

variable {H : Type}

/-- **The footprint `F` is disjoint from the image of a part** (renaming `ρ`, ownership `O`) and
allocated in `σ`. -/
structure FootDisj (F : CoreFoot) (ρ : Ren) (O : Own) (σ : Store H) : Prop where
  gl : ∀ a, O.gl a → ¬ F.gl a
  st : ∀ a b, F.st a → O.st b → ρ.st b ≠ a
  ar : ∀ a b, F.ar a → O.ar b → ρ.ar b ≠ a
  bound : F.Bounded σ

/-- The identity renaming. -/
def renId : Ren := ⟨fun a => a, fun a => a⟩

/-- The ownership of a footprint (no functions). -/
def ownOfFoot (F : CoreFoot) : Own := ⟨F.st, F.ar, fun _ => False, F.gl⟩

/-- A change inside a footprint is a touch of its ownership. -/
theorem touch_of_within (g : H → Nat) {F : CoreFoot} {σ σ' : Store H} (hw : F.Within σ σ') :
    Touch renId (ownOfFoot F) (Store.mapH g σ) (Store.mapH g σ') where
  funcs := mapH_funcs_eq g hw.funcs
  globals a ha := hw.globals a ha
  structs a ha hl := hw.structs a (fun h => ha a h rfl) hl
  arrays a ha hl := hw.arrays a (fun h => ha a h rfl) hl
  structs_len := hw.structs_len
  arrays_len := hw.arrays_len

/-- **A touch of a part disjoint from an allocated footprint agrees on the footprint.** -/
theorem agree_of_touch {g : H → Nat} {F : CoreFoot} {ρ : Ren} {O : Own} {σ σ' : Store H}
    (hD : FootDisj F ρ O σ) (ht : Touch ρ O (Store.mapH g σ) (Store.mapH g σ'))
    (hf : σ'.funcs = σ.funcs) : F.Agree σ σ' where
  funcs := by rw [hf]
  globals a ha := ht.globals a (fun hO => hD.gl a hO ha)
  structs a ha := ht.structs a (fun b hb => hD.st a b ha hb) (hD.bound.st a ha)
  arrays a ha := ht.arrays a (fun b hb => hD.ar a b ha hb) (hD.bound.ar a ha)

/-- **The part moved**: the footprint stays disjoint from its grown image, and allocated. -/
theorem FootDisj.after_part {g : H → Nat} {F : CoreFoot} {ρ ρ' : Ren} {O O' : Own}
    {σ σ' : Store H} (hD : FootDisj F ρ O σ) (hg : Grow ρ O ρ' O' (Store.mapH g σ))
    (ht : Touch ρ O (Store.mapH g σ) (Store.mapH g σ')) : FootDisj F ρ' O' σ' where
  gl a ha := by
    rw [hg.gl] at ha
    exact hD.gl a ha
  st a b ha hb e := by
    rcases hg.stNew b hb with hb' | hb'
    · exact hD.st a b ha hb' ((hg.st b hb').2.symm.trans e)
    · change σ.structs.length ≤ ρ'.st b at hb'
      have := hD.bound.st a ha
      omega
  ar a b ha hb e := by
    rcases hg.arNew b hb with hb' | hb'
    · exact hD.ar a b ha hb' ((hg.ar b hb').2.symm.trans e)
    · change σ.arrays.length ≤ ρ'.ar b at hb'
      have := hD.bound.ar a ha
      omega
  bound := ⟨fun a ha => lt_of_lt_of_le (hD.bound.st a ha) ht.structs_len,
    fun a ha => lt_of_lt_of_le (hD.bound.ar a ha) ht.arrays_len⟩

/-- **The footprint's owner moved**: the part's relation survives. -/
theorem partRel_within {g : H → Nat} {F : CoreFoot} {ρ : Ren} {O : Own} {p : Store Nat}
    {σ σ' : Store H} (hR : PartRel ρ O p (Store.mapH g σ)) (hD : FootDisj F ρ O σ)
    (hw : F.Within σ σ') : PartRel ρ O p (Store.mapH g σ') :=
  hR.touch (touch_of_within g hw) hD.gl (fun a b ha hb e => hD.st b a hb ha e.symm)
    (fun a b ha hb e => hD.ar b a hb ha e.symm)

/-- **The footprint's owner moved**: its grown footprint stays disjoint from the part's image. -/
theorem FootDisj.after_owner {g : H → Nat} {F F' : CoreFoot} {ρ : Ren} {O : Own}
    {p : Store Nat} {σ σ' : Store H} (hD : FootDisj F ρ O σ)
    (hR : PartRel ρ O p (Store.mapH g σ)) (hgF : F.Grows F' σ) (hB : F'.Bounded σ') :
    FootDisj F' ρ O σ' where
  gl a ha h := hD.gl a ha ((hgF.gl a).mp h)
  st a b ha hb e := by
    rcases hgF.stNew a ha with ha' | ha'
    · exact hD.st a b ha' hb e
    · have := (hR.st_lt hb).2
      change ρ.st b < σ.structs.length at this
      omega
  ar a b ha hb e := by
    rcases hgF.arNew a ha with ha' | ha'
    · exact hD.ar a b ha' hb e
    · have := (hR.ar_lt hb).2
      change ρ.ar b < σ.arrays.length at this
      omega
  bound := hB

end Foot

/-! ## The static facts and the invariant -/

/-- **The importer's static facts**: `Good`, its core instance `Ii` at the store `u₀`, and the
host code of the shared functions `F₀`: `tr` inverts the renaming `g` on every host function
(the importer's trampolines and any host code of the exporter's part), and `g` renames the
trampoline `tr k` of import `k` to `k`. -/
structure ImpStatG (P : Profile) (b : SimpleI) (Ii : SInst) (u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat)
    (tr : Nat → CanonHost (E3 P)) : Prop where
  good : b.Good
  inst : b.mod.IsInst Ii
  wf : Ii.WellFormed u₀
  tramp : ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
    F₀[A]? = some fi → fi.code = .host h → tr (g h) = h
  inv : ∀ k, k < b.imports.length → g (tr k) = k

/-- **The importer's invariant against the exporter's data `d` at placement `pl`**, at the
exporter's state `s`, the component store `S` (with core store `y.1`), the exporter's footprint
`F`, the shared thread `y` and the importer's part thread `x`. -/
structure LInvG {e : ExpSpec} (d : e.RefData P) (pl : d.Pl) (Ii : SInst) (s₀ u₀ : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (g : CanonHost (E3 P) → Nat) (Oc₀ : Own)
    (f : Ii.F.Op) (s : e.St) (S : RefStore (E3 P)) (F : CoreFoot) (y : CoreSt (E3 P))
    (x : Store Nat × STh) : Prop where
  rel : ∃ ρc Oc, LinkSt s₀ ρc Oc x (Store.mapH g y.1, y.2) ∧ Oc.fn = Oc₀.fn ∧ Oc.gl = Oc₀.gl ∧
    FootDisj F ρc Oc y.1
  hold : d.Hold pl s S F
  core : S.core = y.1
  funcs : y.1.funcs = F₀
  run : Silmaril.Wasm.Game.SSteps P (valEnv Ii)
    (Silmaril.Wasm.Execution.Core.invoke u₀ (Ii.addr f.1) f.2.1, ()) (x.2.config x.1, ())

section Inv

variable {b : SimpleI} {Ii : SInst} {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))}
  {g : CanonHost (E3 P) → Nat} {tr : Nat → CanonHost (E3 P)} {Oc₀ : Own} {f : Ii.F.Op}
  {e : ExpSpec} {d : e.RefData P} {pl : d.Pl}

/-- The shared store has only trampolines as host code, which `tr` recovers from `g`. -/
theorem ImpStatG.hostsSat (S : ImpStatG P b Ii u₀ F₀ g tr) {σ : Store (CanonHost (E3 P))}
    (hs : σ.funcs = F₀) : HostsSat (fun h => tr (g h) = h) σ := by
  intro A fi h hA hc
  exact S.tramp A fi h (hs ▸ hA) hc

/-- **A run of the importer's part is a core run of the shared thread**, `LInvG` holding at its
end with the same exporter state and footprint (R1). -/
theorem LInvG.reach_fwd (S : ImpStatG P b Ii u₀ F₀ g tr) (hFr : d.Frame) {s : e.St}
    {M : RefStore (E3 P)} {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) {x' : Store Nat × STh}
    (hx : Silmaril.Wasm.Game.Reach P x x') :
    ∃ y', Relation.ReflTransGen (CoreStep (E3 P)) y y' ∧
      LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s { M with core := y'.1 } F y' x' := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
  obtain ⟨y', ρc', Oc', hrun, hL', hgr, htc, hfy⟩ :=
    reach_link_fwd g tr hx (S.hostsSat hI.funcs) hL
  have hag : F.Agree (M.core : Store (CanonHost (E3 P))) y'.1 := by
    rw [hI.core]
    exact agree_of_touch hD htc hfy
  exact ⟨y', hrun, ⟨⟨ρc', Oc', hL', hgr.fn.trans hfn, hgr.gl.trans hgl, hD.after_part hgr htc⟩,
    hFr.agree pl s M _ F hI.hold hag (List.prefix_refl _) (fun _ _ => rfl), rfl,
    hfy.trans hI.funcs, hI.run.trans (reach_ssteps hx)⟩⟩

/-- **A callout of the importer's part is a callout of the shared thread** to the trampoline
`tr k` of the import `k` (type `p`), on the flat arguments of the part's, of the flat parameter
types. -/
theorem LInvG.callout_fwd (S : ImpStatG P b Ii u₀ F₀ g tr) {s : e.St} {M : RefStore (E3 P)}
    {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) {k : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val}
    (hc : Silmaril.Wasm.Game.CalloutAt x.1 x.2 k args) {q : Ii.E.Op}
    (he : Ii.importOp? k args = some q) :
    ∃ (nm : String) (p : FuncTy) (ys : List Flat) (E : Silmaril.Wasm.SingleThreaded.Ctx)
      (a : Nat),
      b.imports[k]? = some (nm, p) ∧
      Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args) ∧
      args.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some ys ∧
      (E3 P).status y.1 y.2 = .callout (tr k) ys ∧
      ys.map (·.type) = ValTy.flatList p.params := by
  obtain ⟨E, a, hdx⟩ := hc
  obtain ⟨ρc, Oc, hL, -⟩ := hI.rel
  have hdy := (decompose?_config_mapH g y.1 y.2).symm.trans (link_callout hL hdx)
  obtain ⟨⟨E', A, h, args'⟩, hd, hq⟩ := Option.map_eq_some_iff.mp hdy
  simp only [mapR, Prod.mk.injEq] at hq
  obtain ⟨-, -, hgh, hargs⟩ := hq
  obtain ⟨fi, -, -, -, hf, hcode, -⟩ := Silmaril.Wasm.SingleThreaded.decompose?_sound hd
  rw [hI.funcs] at hf
  have htr := S.tramp A fi _ hf hcode
  rw [hgh] at htr
  subst htr
  have hek := ifaceOp?_some he
  have hk' : k < b.imports.length := by
    have hl : Ii.imports.length = b.imports.length := by
      rw [S.inst.2.1, S.good.imports, List.length_map, List.length_map]
    rw [← hl, ← hek.1]
    exact q.1.isLt
  obtain ⟨⟨nm, p⟩, hk⟩ : ∃ r, b.imports[k]? = some r := ⟨_, List.getElem?_eq_getElem hk'⟩
  have h2 : List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get q.1).params args :=
    hek.2 ▸ q.2.2
  rw [imports_get S.good S.inst q k hk' hek.1, (List.getElem?_eq_some_iff.mp hk).2] at h2
  obtain ⟨ys, hys⟩ := Silmaril.Proofs.Wasm.Component.Core3G.toFlat?_isSome h2
  have hargs' : args' = args := by
    rw [hargs]
    exact map_val_of_flat _ hys
  subst hargs'
  refine ⟨nm, p, ys, E, a, hk, hdx, hys, ?_, flat_types_of_hasVal h2 hys⟩
  show flatStatus (Silmaril.Wasm.Game.statusP P y.1 y.2) = _
  rw [statusP_of_decomp hd]
  simp only [flatStatus, hys]

/-- The typed values answer of the import question `q` of `Ii` from the lowering of results `us`
of the import's type. -/
theorem ImpStatG.resAnswer (S : ImpStatG P b Ii u₀ F₀ g tr) {q : Ii.E.Op} {k : Nat}
    {nm : String} {p : FuncTy} (hk : b.imports[k]? = some (nm, p)) (he : q.1.val = k)
    {us : List IVal} (hus : ValTy.checkList p.results us = true) :
    List.Forall₂ Silmaril.Wasm.Game.ScalarType.HasVal (Ii.imports.get q.1).results
      ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat) := by
  obtain ⟨hk', hpk⟩ := List.getElem?_eq_some_iff.mp hk
  have hty : (lowerArgs p.results us).map (·.type) = ValTy.flatList p.results :=
    lowerList_types _ _ hus
  have heq : (Silmaril.Wasm.Component.Reference.fnOf b.imports[k].2.flat).results =
      (lowerArgs p.results us).map (fun x => Silmaril.Wasm.Game.ScalarType.num x.type) := by
    rw [hpk]
    show (ValTy.flatList p.results).map _ = _
    rw [← hty, List.map_map]
    rfl
  rw [imports_get S.good S.inst q k hk' he, heq]
  exact forall₂_hasVal_ofFlat _

/-- **After the exporter's core activation the invariant holds again**: the exporter changed the
component store from `M` to `M'` inside its footprint `F` and by fresh addresses, holding the
state `s'` with footprint `F'` grown from `F` and allocated; the shared thread resumed with the
lowering of `us` (results of the import's type) and the part resumed with the same values
satisfy `LInvG` at `s'`, `M'`, `F'`. -/
theorem LInvG.resume_fwd (S : ImpStatG P b Ii u₀ F₀ g tr) {s : e.St} {M : RefStore (E3 P)}
    {F : CoreFoot} {y : CoreSt (E3 P)} {x : Store Nat × STh}
    (hI : LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s M F y x) {k : Nat} {nm : String} {p : FuncTy}
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} {q : Ii.E.Op}
    (hk : b.imports[k]? = some (nm, p))
    (hdx : Silmaril.Wasm.SingleThreaded.decompose? x.1 (x.2.config x.1).code = some (E, a, k, args))
    (he : Ii.importOp? k args = some q) {us : List IVal}
    (hus : ValTy.checkList p.results us = true) {s' : e.St} {M' : RefStore (E3 P)}
    {F' : CoreFoot} (hH : d.Hold pl s' M' F')
    (hw : F.Within (M.core : Store (CanonHost (E3 P))) M'.core)
    (hgF : F.Grows F' (M.core : Store (CanonHost (E3 P))))
    (hB : F'.Bounded (M'.core : Store (CanonHost (E3 P)))) :
    LInvG d pl Ii s₀ u₀ F₀ g Oc₀ f s' M' F'
      (M'.core, (E3 P).resume M'.core y.2 (.values (lowerArgs p.results us)))
      (x.1, Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2
        (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))) := by
  obtain ⟨ρc, Oc, hL, hfn, hgl, hD⟩ := hI.rel
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
  have hek : q.1.val = k ∧ q.2.1 = args := ifaceOp?_some he
  have hdx' : Silmaril.Wasm.SingleThreaded.decompose? (x.2.config x.1).store
      (x.2.config x.1).code = some (E, a, k, args) :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store x.1 x.2).symm ▸ hdx
  have hstep : Silmaril.Wasm.Game.SStep P (valEnv Ii) (x.2.config x.1, ())
      (⟨(x.2.config x.1).store, (x.2.config x.1).frame,
        E.fill (Silmaril.Wasm.Execution.Core.Result.values
          ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat)).toAdmin⟩, ()) :=
    Silmaril.Wasm.Game.SStep.answer (P := P) (L := valEnv Ii) (q := ()) (q' := ())
      (w := .values ⟨_, S.resAnswer hk hek.1 hus⟩) hdx' he ⟨_, rfl⟩
  have hcfg := resumeResult_config hdx'
    (.values ((lowerArgs p.results us).map Silmaril.Wasm.SingleThreaded.ofFlat))
  refine ⟨⟨ρc, Oc, hres ▸ hL2, hfn, hgl, hD.after_owner hR0 hgF hB⟩, hH, rfl,
    hw.funcs.trans hI.funcs, ?_⟩
  show Silmaril.Wasm.Game.SSteps P (valEnv Ii) _ (Silmaril.Wasm.SingleThreaded.Thread.config x.1
    (Silmaril.Wasm.SingleThreaded.resumeResult x.1 x.2 _), ())
  rw [hcfg]
  exact hI.run.tail hstep

end Inv

/-! ## R6 for a simple exporter -/

/-- **A simple exporter's footprints are allocated** (R6). -/
theorem simple_bounded (c : Simple) (I : SInst) : (simpleData P c I).Bounded := by
  intro pl s S F h
  obtain ⟨ρ, O, hR, -, rfl⟩ := h.rel
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (hR.st_lt ha).2
  · rintro _ ⟨a, ha, rfl⟩
    exact (hR.ar_lt ha).2

/-- **A simple exporter meets R1–R6.** -/
theorem simple_refAdeqB (P : Profile) {c : Simple} (hc : c.Good) (hi : c.Inst) {I : SInst}
    (hI : c.mod.IsInst I) (hS : Linked2.ModSplitOk c.mod.mod)
    (hN : ∀ x ∈ c.exports, ∀ n, x.name ≠ tag "t" n) : (Simple.expSpec c I).RefAdeqB P :=
  ⟨simpleData P c I, simple_frame c I, simple_fwd hc hI, simple_bwd hc hI,
    simple_init hc hi hI hS hN, simple_resume c I, simple_bounded c I⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
