module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.InitRun
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain.Fwd
public import Silmaril.Wasm.Component.Reference.LinkedGChain.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Ready

/-!
# R4 for a linked component as an exporter

`toExpData_initUX`: the data `toExpData lg d Ii` meets R4 with the read-back and any host code
(`RefData.InitUX`) when the exporter's data `d` meets R1, R4 (`InitUX`) and R6 and the link meets
`LinkOk`. The nested instantiation of `lg.toRef` is a live run (`instCallG_reach` of
`InitRun`) to the importer's instantiation after R4's configuration `m₁`; there:

* the placement (`initPl`): the exporter at R4's placement, the importer at the next instance
  `m₁.store.insts.length`, relocated after R4's core store renamed by `gX` (`s0G`), owning its
  relocated store (`shOwn`), its exports from the function id `m₁.store.funcs.length`;
* `holdX_init`: `HoldX` at the importer's instance store and the exporter's initial state, the
  footprint the exporter's and the importer's relocated ownership (`statB_init` and the proof of
  `readyB_init` of `LinkedGInit`, at the configuration of the nested instantiation);
* the rest of `InitAtX`: new instances, the parent's export map, the call records, nesting
  depth and waiting threads unchanged, globals allocated, distinct function ids.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGImp
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
open Silmaril.Proofs.Wasm.Component.Reference.LinkedGInst
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Instantiate
open Silmaril.Wasm.Execution.Core (Store FuncInst FuncCode)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)

local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

variable {P : Profile} {σ : Type} {lg : LinkedG} {d : lg.exp.RefData P} {Ii : SInst}

theorem toComp_exports_name {w : Nat} {x : Export} (h : lg.toComp.exports[w]? = some x) :
    ∃ hw : w < lg.imp.exports.length, x.name = lg.imp.exports[w].name := by
  change (List.mapIdx _ lg.imp.exports)[w]? = some x at h
  rw [List.getElem?_mapIdx] at h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hw, rfl⟩ := List.getElem?_eq_some_iff.mp hy
  exact ⟨hw, rfl⟩

theorem arenasExtend_trans {s₁ s₂ s₃ : CStore (core3P P)} (h₁ : ArenasExtend s₁ s₂)
    (h₂ : ArenasExtend s₂ s₃) : ArenasExtend s₁ s₃ := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, h₁', i₁, j₁, k₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, h₂', i₂, j₂, k₂⟩ := h₂
  exact ⟨a₁.trans a₂, b₁.trans b₂, c₁.trans c₂, d₁.trans d₂, e₁.trans e₂, f₁.trans f₂,
    g₁.trans g₂, h₁'.trans h₂', i₁.trans i₂, j₁.trans j₂, k₁.trans k₂⟩

theorem arenasExtend_alloc (s : CStore (core3P P)) :
    ArenasExtend s (ArenaOps.allocSt ArenaField.insts {} s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, ArenaField.insts]

theorem arenasExtend_impStore (s : CStore (core3P P)) (c : Store (CanonHost (core3P P)))
    (r : Store (CanonHost (core3P P) × Nat)) :
    ArenasExtend s (impStore lg Ii s c r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [impStore, nestStoreI, liftStore, ArenaOps.allocSt,
      ArenaField.alloc, Arena.alloc, ArenaField.insts]

theorem impStore_insts (s : CStore (core3P P)) (c : Store (CanonHost (core3P P)))
    (r : Store (CanonHost (core3P P) × Nat)) :
    (impStore lg Ii s c r).insts = s.insts ++ [({} : InstState)] := by
  simp [impStore, nestStoreI, liftStore, ArenaOps.allocSt,
    ArenaField.alloc, Arena.alloc, ArenaField.insts]

theorem impStore_funcs (s : CStore (core3P P)) (c : Store (CanonHost (core3P P)))
    (r : Store (CanonHost (core3P P) × Nat)) :
    s.funcs <+: (impStore lg Ii s c r).funcs := by
  simp [impStore, nestStoreI, liftStore, ArenaOps.allocSt,
    ArenaField.alloc, Arena.alloc, ArenaField.insts]

theorem impStore_lockdown (s : CStore (core3P P)) (c : Store (CanonHost (core3P P)))
    (r : Store (CanonHost (core3P P) × Nat)) :
    (impStore lg Ii s c r).lockdown = s.lockdown := by
  simp [impStore, nestStoreI, liftStore, ArenaOps.allocSt,
    ArenaField.alloc, Arena.alloc, ArenaField.insts]

theorem impStore_nest (s : CStore (core3P P)) (c : Store (CanonHost (core3P P)))
    (r : Store (CanonHost (core3P P) × Nat)) :
    (impStore lg Ii s c r).nestingDepth = s.nestingDepth := by
  simp [impStore, nestStoreI, liftStore, ArenaOps.allocSt,
    ArenaField.alloc, Arena.alloc, ArenaField.insts]

/-- The component store and the shared core store after the importer's nested instantiation
from `m₁` (`impCfg`). -/
def impRef (lg : LinkedG) (Ii : SInst) {σ : Type} (m₁ : Machine.Config (core3P P) σ)
    (r : Store (CanonHost (core3P P) × Nat)) : RefStore (core3P P) :=
  ⟨impStore lg Ii m₁.store m₁.core r, impCore m₁.core r⟩

theorem impCfg_ref {σ : Type} (m₁ : Machine.Config (core3P P) σ)
    (r : Store (CanonHost (core3P P) × Nat)) : (impCfg lg Ii m₁ r).ref = impRef lg Ii m₁ r := rfl

/-- **The placement after the nested instantiation.** -/
def initPl (d : lg.exp.RefData P) (Ii : SInst) {σ : Type} (pl : d.Pl)
    (m₁ : Machine.Config (core3P P) σ) : ExpPl lg d :=
  ⟨pl, m₁.store.insts.length, s0G d pl m₁, Ii.store, shOwn (sh (s0G d pl m₁)) (ownOf Ii.store),
    m₁.store.funcs.length⟩

/-- **`HoldX` after the nested instantiation**, at the importer's instance store and the
exporter's initial state (`statB_init`, and `readyB_init`'s invariant at the witness). -/
theorem holdX_init (hFr : d.Frame) (hB : d.Bounded) (hl : lg.LinkOk) (hI : lg.imp.mod.IsInst Ii)
    {pl : d.Pl} {F : CoreFoot} {es : List (String × ItemVal (core3P P))}
    {M m₁ : Machine.Config (core3P P) σ} {r : Store (CanonHost (core3P P) × Nat)}
    (hA : d.InitAtX pl F es M m₁) (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : TrampsOf lg (fidG d pl) (nextInst m₁.store) r) :
    HoldX lg d Ii (initPl d Ii pl m₁) (Ii.store, lg.exp.init) (impRef lg Ii m₁ r)
      (footUnion F (img Ren.id (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store)))) := by
  have hgu : StoreGood Ii.store := storeGood_inst hl.split hI.1.choose_spec
  have hB₁ := hB pl lg.exp.init m₁.ref F hA.hold
  have hgl : ∀ a, F.gl a → a < (cseG m₁).globals.length := hA.globals
  have hst : ∀ a, F.st a → a < (cseG m₁).structs.length := hB₁.st
  have har : ∀ a, F.ar a → a < (cseG m₁).arrays.length := hB₁.ar
  have hag : F.Agree (cseG m₁) (coreG m₁ r) := by
    refine ⟨?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [coreG, reloc_funcs]
      exact List.prefix_append _ _
    · rw [coreG, reloc_globals, List.getElem?_append_left (hgl a ha)]
    · rw [coreG, reloc_structs, List.getElem?_append_left (hst a ha)]
    · rw [coreG, reloc_arrays, List.getElem?_append_left (har a ha)]
  have hH : d.Hold pl lg.exp.init (impRef lg Ii m₁ r) F := by
    refine hFr.agree pl _ m₁.ref _ F hA.hold hag (impStore_funcs m₁.store m₁.core r) fun i hi => ?_
    show (impStore lg Ii m₁.store m₁.core r).insts[i]? = _
    rw [impStore_insts m₁.store m₁.core r, List.getElem?_append_left (hA.block i hi).2]
    rfl
  have hmap := mapH_coreG hl.wireTy hl.nodup hA hrs hh
  have ST : StatB P lg d pl m₁.store.insts.length Ii (s0G d pl m₁) Ii.store (coreG m₁ r).funcs
      (gX d pl m₁.store.insts.length (cseG m₁).funcs)
      (trX d pl m₁.store.insts.length (cseG m₁).funcs)
      (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store)) (impStore lg Ii m₁.store m₁.core r).funcs
      (fun j => m₁.store.funcs.length + j) :=
    statB_init hl.wireTy hl.nodup hl.good hl.arity hl.floats hI hA hh
  have hcore : (impRef lg Ii m₁ r).core = coreG m₁ r := rfl
  have hD : FootDisj F Ren.id (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store))
      (impRef lg Ii m₁ r).core := by
    refine ⟨fun a ha hF => ?_, fun a b ha hb e => ?_, fun a b ha hb e => ?_,
      hB _ _ _ F hH⟩
    · have h₁ := hgl a hF
      have h₂ : (s0G d pl m₁).globals.length ≤ a := ha.1
      simp only [s0G, cseG, Store.mapH] at h₂ h₁
      omega
    · have h₁ := hst a ha
      have h₂ : (s0G d pl m₁).structs.length ≤ b := hb.1
      simp only [s0G, Store.mapH] at h₂
      have e' : b = a := e
      omega
    · have h₁ := har a ha
      have h₂ : (s0G d pl m₁).arrays.length ≤ b := hb.1
      simp only [s0G, Store.mapH] at h₂
      have e' : b = a := e
      omega
  have hR : PartRel Ren.id (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store)) (reloc (s0G d pl m₁) Ii.store)
      (Store.mapH (gX d pl m₁.store.insts.length (cseG m₁).funcs)
        (impRef lg Ii m₁ r).core) := by
    rw [hcore, hmap]
    exact partRel_reloc (s₀ := s0G d pl m₁) hgu
  have hfC : FnPre (s0G d pl m₁) (Store.mapH (gX d pl m₁.store.insts.length (cseG m₁).funcs)
      (impRef lg Ii m₁ r).core) Ii.store := by
    rw [hcore, hmap]
    exact fnPre_refl _ _
  have hRW : LReadyW d pl Ii (s0G d pl m₁) Ii.store (coreG m₁ r).funcs
      (gX d pl m₁.store.insts.length (cseG m₁).funcs) (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store))
      (impRef lg Ii m₁ r) lg.exp.init Ii.store F Ren.id
      (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store)) :=
    ⟨hR, rfl, rfl, hD, hH, hfC, hI.1.choose_spec.ok, rfl, rfl, sgoodSt_of_storeGood hgu⟩
  refine ⟨⟨_, _, _, F, Ren.id, _, ST, hRW, ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩⟩,
    real_bounded hD hR, ⟨{}, ?_, rfl⟩, ?_⟩
  · show (impStore lg Ii m₁.store m₁.core r).insts[m₁.store.insts.length]? = _
    rw [impStore_insts m₁.store m₁.core r]
    exact List.getElem?_concat_length
  · rintro w ⟨xe, hxe⟩
    obtain ⟨-, ι, hι, ht⟩ := hA.exports w xe hxe
    refine ⟨ι, ?_, .inl ht⟩
    show (impStore lg Ii m₁.store m₁.core r).insts[d.inst pl w]? = some ι
    rw [impStore_insts m₁.store m₁.core r, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hι).1]
    exact hι

/-- **R4 for a linked component**: `toExpData lg d Ii` meets `RefData.InitUX`, from R1, R4 and
R6 of the exporter's data `d`, for a link meeting `LinkOk` at an instance `Ii` of the importer's
core module. -/
theorem toExpData_initUX (hInit : d.InitUX) (hFr : d.Frame) (hB : d.Bounded) (hl : lg.LinkOk)
    (hI : lg.imp.mod.IsInst Ii) : (toExpData lg d Ii).InitUX := by
  intro σ prof impl M th outer k segs rest hcore hlock
  have hseg : lg.imp.mod.mod.data = [] ∧ lg.imp.mod.mod.elems = [] :=
    ⟨hl.split.data, hl.split.elems⟩
  obtain ⟨tr, a, m', hrun, hh, ht, hl', ho, xs, rfl, m₁, pl, F, es, r, hW, hrs, htr, hxs, rfl⟩ :=
    instCallG_reach (prof := prof) (impl := impl) hInit hFr hl.wireTy hl.good hl.inst hl.arity
      hseg hl.names hI th outer M hcore hlock k segs rest
  have hA := hW.toInitAtX
  have hlen₁ : ({ M with store := ArenaOps.allocSt ArenaField.insts ({} : InstState) M.store } :
      Machine.Config (core3P P) σ).store.insts.length = M.store.insts.length + 1 := by
    simp [ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, ArenaField.insts]
  refine ⟨tr, _, initPl d Ii pl m₁,
    footUnion F (img Ren.id (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store))), _, lrun_liveDet hrun,
    hh, ht, ho, rfl, ⟨hl', ?_, holdX_init hFr hB hl hI hA hrs htr, ?_, ?_, hA.pending,
      hA.results, ?_, ?_, ?_⟩, hW.waiting⟩
  · exact arenasExtend_trans (arenasExtend_trans (arenasExtend_alloc _) hA.ext)
      (arenasExtend_impStore m₁.store m₁.core r)
  · intro i hi
    have hl₂ : (impStore lg Ii m₁.store m₁.core r).insts.length = m₁.store.insts.length + 1 := by
      rw [impStore_insts m₁.store m₁.core r, List.length_append, List.length_singleton]
    show M.store.insts.length ≤ i ∧ i < (impStore lg Ii m₁.store m₁.core r).insts.length
    rw [hl₂]
    rcases hi with hi | hi
    · have := hA.block i hi
      omega
    · have e : i = m₁.store.insts.length := hi
      have := (hA.ext.1).length_le
      rw [e]
      omega
  · intro w x hx
    obtain ⟨hw, hname⟩ := toComp_exports_name hx
    refine ⟨?_, {}, ?_, rfl⟩
    · rw [hxs, hname]
      exact lookup_mapIdx_val (·.name) (fun k => (ItemVal.func ⟨k⟩ : ItemVal (core3P P)))
        m₁.store.funcs.length lg.imp.exports w hw hl.good.names
    · show (impStore lg Ii m₁.store m₁.core r).insts[m₁.store.insts.length]? = _
      rw [impStore_insts m₁.store m₁.core r]
      exact List.getElem?_concat_length
  · show (impStore lg Ii m₁.store m₁.core r).nestingDepth = M.store.nestingDepth
    rw [impStore_nest m₁.store m₁.core r, hA.nest]
    simp [ArenaOps.allocSt, ArenaField.alloc, Arena.alloc, ArenaField.insts]
  · rintro a (ha | ha)
    · have h₁ := hA.globals a ha
      show a < (coreG m₁ r).globals.length
      rw [coreG, reloc_globals, List.length_append]
      exact Nat.lt_of_lt_of_le h₁ (Nat.le_add_right _ _)
    · obtain ⟨h₁, h₂⟩ := ha
      have h₂' : a - (s0G d pl m₁).globals.length < Ii.store.globals.length := h₂
      have hg : (Store.mapH Prod.fst r).globals.length = Ii.store.globals.length := by
        rw [← hrs]
        rfl
      show a < (coreG m₁ r).globals.length
      rw [coreG, reloc_globals, List.length_append, List.length_map, hg]
      have h₁' : (s0G d pl m₁).globals.length ≤ a := h₁
      simp only [s0G, cseG, Store.mapH] at h₁' h₂' ⊢
      omega
  · intro w w' x x' _ _ e
    have e' : m₁.store.funcs.length + w = m₁.store.funcs.length + w' := e
    omega

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGChain
