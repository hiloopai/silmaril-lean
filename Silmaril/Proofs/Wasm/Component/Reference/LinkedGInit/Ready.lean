module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit.Run
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedGRound.Sess
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSound
public import Silmaril.Proofs.Wasm.Component.Reference.LinkSoundSeq

/-!
# Between calls after the instantiation of `LinkedG.toRef`

At `afterG` (the configuration after instantiating `lg.toRef`, `Run`), with the exporter at R4's
placement `pl`, the importer at instance `ii` (the first after R4's instances) and its store
`Ii.store` relocated after R4's core store `cse`:

* `trG`, `gG`: the trampoline of import `k` (lowering the wired export's function id from
  instance `ii`) and the host-code renaming back to `k` (`gG_trG`, from distinct function ids of
  distinct exports and an injective wiring);
* `trX`, `gX`: `trG`, `gG` extended to the host code of the exporter's core store (any host
  functions, e.g. a linked exporter's own trampolines), sent above the importer's imports
  (`trX_gX`); these are the renaming of `StatB`;
* `statB_init`: the static facts `StatB` of `LinkedGRound`, with `s₀ = cse` renamed;
* `readyB_init`: `ReadyB` at `afterG`, call id `0`, the exporter's state `e.init` (R4's `Hold`
  moved along the importer's instantiation by R1) and the importer's store `Ii.store` (the
  `Rel4` consumer half of `rel4_init`, disjoint from the footprint: R6 and `InitAt.globals`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit

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
open Silmaril.Wasm.Component (FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel)

variable {P : Profile} {σ : Type}

/-! ## Trampolines -/

section Tramp

variable {lg : LinkedG} (d : lg.exp.RefData P) (pl : d.Pl)

/-- The trampoline of import `k`, lowering the wired export's function from instance `ii`. -/
def trG (ii k : Nat) : CanonHost (core3P P) :=
  .lowered (fidG d pl k) (witFt ((lg.imp.imports[k]?).elim (⟨[], []⟩ : FuncTy) (·.2))) {} ⟨ii⟩

open Classical in
/-- Host code to the import whose trampoline it is. -/
def gG (ii : Nat) (h : CanonHost (core3P P)) : Nat :=
  if hh : ∃ k, k < lg.imp.imports.length ∧ trG d pl ii k = h then Classical.choose hh else 0

variable {d pl}

theorem trG_eq {ii k : Nat} (hk : k < lg.imp.imports.length) :
    trG d pl ii k = .lowered (fidG d pl k) (witFt lg.imp.imports[k].2) {} ⟨ii⟩ := by
  simp [trG, List.getElem?_eq_getElem hk]

/-- **Trampolines of distinct imports differ**, for an injective wiring to exports with distinct
function ids. -/
theorem trG_inj (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hinj : ∀ (w w' : Nat) (x x' : Export), lg.exp.comp.exports[w]? = some x →
      lg.exp.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w')
    {ii k k' : Nat} (hk : k < lg.imp.imports.length) (hk' : k' < lg.imp.imports.length)
    (e : trG d pl ii k = trG d pl ii k') : k = k' := by
  rw [trG_eq hk, trG_eq hk'] at e
  have hf : fidG d pl k = fidG d pl k' := (CanonHost.lowered.inj e).1
  have hkw : k < lg.wire.length := hW.length ▸ hk
  have hkw' : k' < lg.wire.length := hW.length ▸ hk'
  obtain ⟨x, hx, -⟩ := hW.ty k lg.wire[k] (List.getElem?_eq_getElem hkw)
  obtain ⟨x', hx', -⟩ := hW.ty k' lg.wire[k'] (List.getElem?_eq_getElem hkw')
  have hfe : d.fid pl lg.wire[k] = d.fid pl lg.wire[k'] := by
    have h' : d.fid pl (lg.wire.getD k 0) = d.fid pl (lg.wire.getD k' 0) := congrArg FuncId.idx hf
    rwa [getD_lt hkw, getD_lt hkw'] at h'
  have hw := hinj _ _ x x' hx hx' hfe
  exact (List.Nodup.getElem_inj_iff hn).1 hw

theorem gG_trG (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hinj : ∀ (w w' : Nat) (x x' : Export), lg.exp.comp.exports[w]? = some x →
      lg.exp.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w')
    {ii k : Nat} (hk : k < lg.imp.imports.length) : gG d pl ii (trG d pl ii k) = k := by
  have hh : ∃ k', k' < lg.imp.imports.length ∧ trG d pl ii k' = trG d pl ii k := ⟨k, hk, rfl⟩
  unfold gG
  split
  · rename_i h'
    exact trG_inj hW hn hinj (Classical.choose_spec h').1 hk (Classical.choose_spec h').2
  · exact absurd hh ‹_›

/-! ### Host code of the exporter's part

The exporter's core store may have host functions of its own (a linked exporter has its
importer's trampolines). The renaming `gX` sends the importer's trampolines to their imports, as
`gG` does, and any other host code `h` of the functions `L` (the exporter's) to
`len + A` for an address `A` of `L` with host code `h`; `trX` inverts it there. -/

/-- The host code of the function at address `A` of `L`, if it is a host function. -/
def hostAt (L : List (FuncInst (CanonHost (core3P P)))) (A : Nat) : Option (CanonHost (core3P P)) :=
  (L[A]?).bind fun fi => match fi.code with
    | .host h => some h
    | .wasm _ => none

variable (d pl) in
/-- The trampoline of import `k` below the importer's import count; the host code of the
function at address `k - len` of `L` above it. -/
def trX (ii : Nat) (L : List (FuncInst (CanonHost (core3P P)))) (k : Nat) :
    CanonHost (core3P P) :=
  if k < lg.imp.imports.length then trG d pl ii k
  else (hostAt L (k - lg.imp.imports.length)).getD (trG d pl ii k)

open Classical in
variable (d pl) in
/-- Host code to the import whose trampoline it is, and other host code of `L` above the
importer's import count. -/
def gX (ii : Nat) (L : List (FuncInst (CanonHost (core3P P)))) (h : CanonHost (core3P P)) :
    Nat :=
  if ∃ k, k < lg.imp.imports.length ∧ trG d pl ii k = h then gG d pl ii h
  else if hh : ∃ A, hostAt L A = some h then lg.imp.imports.length + Classical.choose hh else 0

theorem trX_lt {ii k : Nat} {L : List (FuncInst (CanonHost (core3P P)))}
    (hk : k < lg.imp.imports.length) : trX d pl ii L k = trG d pl ii k := by
  simp [trX, hk]

theorem gX_trG (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hinj : ∀ (w w' : Nat) (x x' : Export), lg.exp.comp.exports[w]? = some x →
      lg.exp.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w')
    {ii k : Nat} {L : List (FuncInst (CanonHost (core3P P)))} (hk : k < lg.imp.imports.length) :
    gX d pl ii L (trG d pl ii k) = k := by
  have hh : ∃ k', k' < lg.imp.imports.length ∧ trG d pl ii k' = trG d pl ii k := ⟨k, hk, rfl⟩
  simp only [gX, hh, ↓reduceIte]
  exact gG_trG hW hn hinj hk

theorem gX_trX (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hinj : ∀ (w w' : Nat) (x x' : Export), lg.exp.comp.exports[w]? = some x →
      lg.exp.comp.exports[w']? = some x' → d.fid pl w = d.fid pl w' → w = w')
    {ii k : Nat} {L : List (FuncInst (CanonHost (core3P P)))} (hk : k < lg.imp.imports.length) :
    gX d pl ii L (trX d pl ii L k) = k := by
  rw [trX_lt hk]
  exact gX_trG hW hn hinj hk

/-- **`trX` inverts `gX` on the importer's trampolines and on the host code of `L`.** -/
theorem trX_gX {ii : Nat} {L : List (FuncInst (CanonHost (core3P P)))} {h : CanonHost (core3P P)}
    (hh : (∃ k, k < lg.imp.imports.length ∧ trG d pl ii k = h) ∨ ∃ A, hostAt L A = some h) :
    trX d pl ii L (gX d pl ii L h) = h := by
  by_cases ht : ∃ k, k < lg.imp.imports.length ∧ trG d pl ii k = h
  · have hc := Classical.choose_spec ht
    have e : gX d pl ii L h = Classical.choose ht := by
      simp only [gX, gG, ht, ↓reduceIte, ↓reduceDIte]
    rw [e, trX_lt hc.1]
    exact hc.2
  · have hA : ∃ A, hostAt L A = some h := hh.resolve_left ht
    have e : gX d pl ii L h = lg.imp.imports.length + Classical.choose hA := by
      simp only [gX, ht, hA, ↓reduceIte, ↓reduceDIte]
    have hn : ¬ lg.imp.imports.length + Classical.choose hA < lg.imp.imports.length := by omega
    simp only [e, trX, hn, ↓reduceIte, Nat.add_sub_cancel_left, Classical.choose_spec hA,
      Option.getD_some]

theorem hostAt_of {L : List (FuncInst (CanonHost (core3P P)))} {A : Nat}
    {fi : FuncInst (CanonHost (core3P P))} {h : CanonHost (core3P P)} (hA : L[A]? = some fi)
    (hc : fi.code = .host h) : hostAt L A = some h := by
  simp [hostAt, hA, hc]

end Tramp

/-! ## The static facts and the configuration between calls -/

section Init

variable {lg : LinkedG} {d : lg.exp.RefData P} {pl : d.Pl} {F : CoreFoot}
  {es : List (String × Instantiate.ItemVal (core3P P))} {M m₁ : Machine.Config (core3P P) σ}
  {r : Store (CanonHost (core3P P) × Nat)} {Ii : Silmaril.Wasm.Game.ScalarInstance}

/-- R4's core store, as a store. -/
def cseG (m₁ : Machine.Config (core3P P) σ) : Store (CanonHost (core3P P)) := m₁.core

/-- The exporter's core store after R4, renamed. -/
def s0G (d : lg.exp.RefData P) (pl : d.Pl) (m₁ : Machine.Config (core3P P) σ) : Store Nat :=
  Store.mapH (gX d pl m₁.store.insts.length (cseG m₁).funcs) (cseG m₁)

/-- The shared core store after the importer's instantiation. -/
def coreG (m₁ : Machine.Config (core3P P) σ) (r : Store (CanonHost (core3P P) × Nat)) :
    Store (CanonHost (core3P P)) :=
  reloc (cseG m₁) (Store.mapH Prod.fst r)

theorem afterG_core : (afterG lg Ii m₁ r).core = coreG m₁ r := rfl

theorem afterG_funcs : (afterG lg Ii m₁ r).store.funcs = m₁.store.funcs ++
    liftedList (addrL (cseG m₁).funcs.length Ii) ⟨m₁.store.insts.length⟩ lg.imp.exports := rfl

theorem afterG_insts : (afterG lg Ii m₁ r).store.insts = m₁.store.insts ++ [({} : InstState)] := by
  simp [afterG, impStore, nestStoreI, liftStore, ArenaOps.allocSt,
    ArenaField.alloc, Arena.alloc, ArenaField.insts, DispatchSt.decNestingSt]

theorem s0G_funcs_length : (s0G d pl m₁).funcs.length = (cseG m₁).funcs.length := by
  simp [s0G, Store.mapH]

/-- **The importer's static facts after instantiation**. -/
theorem impStat_init (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hI : lg.imp.mod.IsInst Ii) (hA : d.InitAtX pl F es M m₁)
    (hh : TrampsOf lg (fidG d pl) (nextInst m₁.store) r) :
    ImpStatG P lg.imp Ii Ii.store (coreG m₁ r).funcs
      (gX d pl m₁.store.insts.length (cseG m₁).funcs)
      (trX d pl m₁.store.insts.length (cseG m₁).funcs) where
  good := hIg
  inst := hI
  wf := hI.1.choose_spec.ok
  tramp := by
    intro A fi h hA' hc
    refine trX_gX ?_
    rcases Nat.lt_or_ge A (cseG m₁).funcs.length with hlt | hge
    · have h₁ : (cseG m₁).funcs[A]? = some fi := by
        rw [coreG, reloc_funcs, List.getElem?_append_left hlt] at hA'
        exact hA'
      exact .inr ⟨A, hostAt_of h₁ hc⟩
    obtain ⟨fr, hfr, hfe⟩ := reloc_suffix_get hge hA'
    have hcf : (FuncInst.mapH Prod.fst fr).code = .host h := by
      rw [← hc, ← hfe]
      rfl
    obtain ⟨hk, hcode, hh'⟩ := mapH_fst_host hcf
    obtain ⟨k, hkl, hke⟩ := hh _ fr hk hfr hcode
    refine .inl ⟨k, hkl, Eq.symm ?_⟩
    rw [← hh', hke, trG_eq hkl]
    rfl
  inv k hk := gX_trX hW hn hA.fidInj hk

/-- The renamed shared core store is the exporter's, then the importer's relocated. -/
theorem mapH_coreG (hW : lg.WireTy) (hn : lg.wire.Nodup) (hA : d.InitAtX pl F es M m₁)
    (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : TrampsOf lg (fidG d pl) (nextInst m₁.store) r) :
    Store.mapH (gX d pl m₁.store.insts.length (cseG m₁).funcs) (coreG m₁ r) =
      reloc (s0G d pl m₁) Ii.store := by
  rw [coreG, mapH_reloc, mapH_mapH, ← hrs]
  congr 1
  refine mapH_congr_hosts hh ?_
  rintro _ ⟨k, hk, rfl⟩
  show gX d pl m₁.store.insts.length (cseG m₁).funcs (.lowered (fidG d pl k)
    (witFt lg.imp.imports[k].2) {} (nextInst m₁.store)) = k
  have e : (.lowered (fidG d pl k) (witFt lg.imp.imports[k].2) {} (nextInst m₁.store) :
      CanonHost (core3P P)) = trG d pl m₁.store.insts.length k := by
    rw [trG_eq hk]
    rfl
  rw [e]
  exact gX_trG hW hn hA.fidInj hk

/-- **The static facts of `LinkedGRound` after instantiating `lg.toRef`.** -/
theorem statB_init (hW : lg.WireTy) (hn : lg.wire.Nodup) (hIg : lg.imp.Good)
    (hIa : lg.imp.Arity) (hff : lg.imp.FloatFree) (hI : lg.imp.mod.IsInst Ii)
    (hA : d.InitAtX pl F es M m₁) (hh : TrampsOf lg (fidG d pl) (nextInst m₁.store) r) :
    StatB P lg d pl m₁.store.insts.length Ii (s0G d pl m₁) Ii.store (coreG m₁ r).funcs
      (gX d pl m₁.store.insts.length (cseG m₁).funcs)
      (trX d pl m₁.store.insts.length (cseG m₁).funcs)
      (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store)) (afterG lg Ii m₁ r).store.funcs
      (fun j => m₁.store.funcs.length + j) where
  imp := impStat_init hW hn hIg hI hA hh
  wire := by
    refine ⟨fun k nm p hk => ?_, hIa, hff⟩
    have hkl : k < lg.imp.imports.length := (List.getElem?_eq_some_iff.1 hk).1
    have hkw : k < lg.wire.length := hW.length ▸ hkl
    obtain ⟨x, hx, hty⟩ := hW.ty k lg.wire[k] (List.getElem?_eq_getElem hkw)
    have hp : lg.imp.imports[k] = (nm, p) := (List.getElem?_eq_some_iff.1 hk).2
    have hxp : x.ty = p := by
      rw [hk] at hty
      exact (Option.some.inj hty).symm
    refine ⟨lg.wire[k], x, List.getElem?_eq_getElem hkw, hx, hxp, ?_⟩
    rw [trX_lt hkl, trG_eq hkl, hp]
    show CanonHost.lowered ⟨d.fid pl (lg.wire.getD k 0)⟩ _ _ _ = _
    rw [getD_lt hkw]
  out := fun hb => by
    have := (hA.block _ hb).2
    omega
  own := fun a ha => ⟨Nat.le_add_right _ _, by simpa [ownOf] using ha⟩
  lifted := by
    intro j
    obtain ⟨nm, hcore⟩ := hIg.core _ (List.getElem_mem j.isLt)
    have hk : lg.imp.exports[j].core < lg.imp.mod.exports.length :=
      (List.getElem?_eq_some_iff.mp hcore).1
    have hlen : lg.imp.exports[j].core < Ii.addrs.length := by
      rw [hI.1.choose_spec.ok.addrs_length, hI.2.2, List.length_map]
      exact hk
    rw [afterG_funcs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    simp only [liftedList, List.getElem?_map, List.getElem?_eq_getElem j.isLt, Option.map_some]
    have hlen' : lg.imp.exports[j.val].core < Ii.addrs.length := hlen
    rw [addrL_eq _ hlen', s0G_funcs_length]
    rfl

/-- **Between calls after instantiating `lg.toRef`**, from R4's configuration `m₁` reached from
a configuration `M` without calls, at nesting depth `1`. -/
theorem readyB_init (hFr : d.Frame) (hB : d.Bounded) (hW : lg.WireTy) (hn : lg.wire.Nodup)
    (hI : lg.imp.mod.IsInst Ii) (hS : Linked2.ModSplitOk lg.imp.mod.mod)
    (hA : d.InitAtX pl F es M m₁) (hp : M.pending = []) (hr : M.results = [])
    (hnest : M.store.nestingDepth = 1) (hrs : Store.mapH Prod.snd r = Ii.store)
    (hh : TrampsOf lg (fidG d pl) (nextInst m₁.store) r) :
    ReadyB d pl m₁.store.insts.length Ii (s0G d pl m₁) Ii.store (coreG m₁ r).funcs
      (gX d pl m₁.store.insts.length (cseG m₁).funcs) (shOwn (sh (s0G d pl m₁)) (ownOf Ii.store))
      (afterG lg Ii m₁ r).store.funcs (afterG lg Ii m₁ r) lg.exp.init Ii.store 0 := by
  have hgu : StoreGood Ii.store := storeGood_inst hS hI.1.choose_spec
  -- the exporter's relation moves along the importer's instantiation (R1)
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
  have hH : d.Hold pl lg.exp.init (afterG lg Ii m₁ r).ref F := by
    refine hFr.agree pl _ m₁.ref _ F hA.hold hag ?_ fun i hi => ?_
    · show m₁.store.funcs <+: (afterG lg Ii m₁ r).store.funcs
      rw [afterG_funcs]
      exact List.prefix_append _ _
    · show (afterG lg Ii m₁ r).store.insts[i]? = m₁.store.insts[i]?
      rw [afterG_insts, List.getElem?_append_left (hA.block i hi).2]
  have hmap := mapH_coreG hW hn hA hrs hh
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [afterG, impStore, nestStoreI, liftStore, ArenaOps.allocSt,
      ArenaField.alloc, Arena.alloc, ArenaField.insts, DispatchSt.decNestingSt, hA.lock]
  · have hn₁ := hA.nest
    simp [afterG, impStore, nestStoreI, liftStore, ArenaOps.allocSt,
      ArenaField.alloc, Arena.alloc, ArenaField.insts, DispatchSt.decNestingSt, hn₁, hnest]
  · refine ⟨{}, ?_, threadsOk_empty, rfl⟩
    rw [afterG_insts]
    exact List.getElem?_concat_length
  · rintro w ⟨xe, hxe⟩
    obtain ⟨-, ι, hι, ht⟩ := (hA.exports w xe hxe)
    refine ⟨ι, ?_, .inl ht⟩
    rw [afterG_insts, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hι).1]
    exact hι
  · intro x hx
    have : x ∈ M.pending := by
      have e := hA.pending
      simp only [afterG] at hx
      rw [e] at hx
      exact hx
    rw [hp] at this
    cases this
  · intro x hx
    have : x ∈ M.results := by
      have e := hA.results
      simp only [afterG] at hx
      rw [e] at hx
      exact hx
    rw [hr] at this
    cases this
  · refine ⟨⟨F, Ren.id, shOwn (sh (s0G d pl m₁)) (ownOf Ii.store), ?_, rfl, rfl, ?_, hH⟩, ?_,
      hI.1.choose_spec.ok, rfl, rfl, sgoodSt_of_storeGood hgu⟩
    · rw [Machine.Config.ref_core, afterG_core, hmap]
      exact partRel_reloc (s₀ := s0G d pl m₁) hgu
    · refine ⟨fun a ha hF => ?_, fun a b ha hb e => ?_, fun a b ha hb e => ?_,
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
    · rw [Machine.Config.ref_core, afterG_core, hmap]
      exact fnPre_refl _ _

end Init

end Silmaril.Proofs.Wasm.Component.Reference.LinkedGInit
