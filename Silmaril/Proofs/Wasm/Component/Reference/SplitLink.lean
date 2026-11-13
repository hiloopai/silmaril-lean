module

public import Silmaril.Proofs.Wasm.Component.Reference.SplitInit
public import Silmaril.Proofs.Wasm.Component.Reference.InstLinkCore

/-!
# The importer's part in the shared store: relocation, then renaming

The importer of a `Linked2` runs, in the reference machine, in the core store `reloc s₀ u`
(the exporter's store `s₀` followed by the importer's store `u`, relocated) and, after calls,
in a shared store `σ` into which the relocated store embeds along a renaming of GC addresses
(`Linking.Split.PartRel`). This file composes the two simulations:

* `shOwn δ O`: ownership `O` shifted by `δ`; goodness of references, values, module instances,
  frames and code is shifted along (`goodRef_shift`, …, `codeGood_shift`;
  `codeRefs_shift`, `codeFrames_shift`);
* `partRel_reloc`: a good store `u`, relocated past `s₀`, is related to itself for the shifted
  ownership of everything in `u`; `partRel_prefix`: a good store `s₀` is related to
  `reloc s₀ u` for the ownership of everything in `s₀` (the exporter's part); the two
  ownerships are disjoint (`shOwn_ownOf_disjoint`);
* `ImpRel s₀ ρ O σ c`: the importer configuration `c` (in its own store) is in the split
  fragment and its relocation is related to `σ` along `ρ` for `O`; `step_link`: one host-free
  step of `c` is one host-free step of its image in `σ`, the relation re-established for a grown
  ownership, `σ` touched only at what the importer owns (so the exporter's relation survives,
  `PartRel.touch`); `impRel_init`: the initial relation, with `σ = reloc s₀ u` and the identity
  renaming.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Grow Touch noHost step_sim)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-! ## Shifted ownership -/

/-- The ownership `O` shifted by `δ`. -/
def shOwn (δ : Shift) (O : Own) : Own :=
  ⟨fun a => δ.st ≤ a ∧ O.st (a - δ.st), fun a => δ.ar ≤ a ∧ O.ar (a - δ.ar),
    fun a => δ.fn ≤ a ∧ O.fn (a - δ.fn), fun a => δ.gl ≤ a ∧ O.gl (a - δ.gl)⟩

section ShOwn

variable (δ : Shift) {O : Own}

theorem goodRef_shift : ∀ {r : Ref}, O.GoodRef r → (shOwn δ O).GoodRef (δ.ref r)
  | .i31 _, _ => trivial
  | .null, _ => trivial
  | .struct a, h => ⟨Nat.le_add_right _ _, by simpa using h⟩
  | .array a, h => ⟨Nat.le_add_right _ _, by simpa using h⟩
  | .func a, h => ⟨Nat.le_add_right _ _, by simpa using h⟩
  | .exn _, h => h.elim
  | .host _, h => h.elim
  | .extern r, h => goodRef_shift (r := r) h

theorem goodVal_shift {v : Val} (h : O.GoodVal v) : (shOwn δ O).GoodVal (δ.val v) := by
  cases v with
  | ref r => exact goodRef_shift δ h
  | num => trivial
  | vec => trivial

theorem goodFV_shift {v : FieldVal} (h : O.GoodFV v) : (shOwn δ O).GoodFV (δ.fval v) := by
  cases v with
  | val v => exact goodVal_shift δ h
  | pack => trivial

theorem modGood_shift {m : ModuleInst} (h : O.ModGood m) : (shOwn δ O).ModGood (δ.minst m) where
  tags := by simp [Shift.minst, h.tags]
  mems := by simp [Shift.minst, h.mems]
  tables := by simp [Shift.minst, h.tables]
  elems := by simp [Shift.minst, h.elems]
  datas := by simp [Shift.minst, h.datas]
  globals g hg := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
    exact ⟨Nat.le_add_right _ _, by simpa using h.globals b hb⟩
  funcs a ha := by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ⟨Nat.le_add_right _ _, by simpa using h.funcs b hb⟩

theorem frameGood_shift {f : Frame} (h : O.FrameGood f) : (shOwn δ O).FrameGood (δ.frame f) := by
  refine ⟨modGood_shift δ h.1, fun v hv => ?_⟩
  obtain ⟨w, hw, hwv⟩ : ∃ w, w ∈ f.locals ∧ Option.map δ.val w = some v :=
    List.mem_map.mp (by simpa [Shift.frame] using hv)
  obtain ⟨u, rfl, rfl⟩ : ∃ u, w = some u ∧ δ.val u = v := Option.map_eq_some_iff.mp hwv
  exact goodVal_shift δ (h.2 u hw)

theorem codeRefs_shift : ∀ l : List Admin, codeRefs (δ.code l) = (codeRefs l).map δ.ref
  | [] => by simp
  | .ref r :: l => by simp [codeRefs_shift l]
  | .label n c b :: l => by simp [codeRefs_shift b, codeRefs_shift l]
  | .handler n cs b :: l => by simp [codeRefs_shift b, codeRefs_shift l]
  | .frame n f b :: l => by simp [codeRefs_shift b, codeRefs_shift l]
  | .plain i :: l => by simp [codeRefs_shift l]
  | .callRefType d :: l => by simp [codeRefs_shift l]
  | .returnCallRefType d :: l => by simp [codeRefs_shift l]
  | .trap :: l => by simp [codeRefs_shift l]

theorem codeFrames_shift : ∀ l : List Admin, codeFrames (δ.code l) = (codeFrames l).map δ.frame
  | [] => by simp
  | .ref r :: l => by simp [codeFrames_shift l]
  | .label n c b :: l => by simp [codeFrames_shift b, codeFrames_shift l]
  | .handler n cs b :: l => by simp [codeFrames_shift b, codeFrames_shift l]
  | .frame n f b :: l => by simp [codeFrames_shift b, codeFrames_shift l]
  | .plain i :: l => by simp [codeFrames_shift l]
  | .callRefType d :: l => by simp [codeFrames_shift l]
  | .returnCallRefType d :: l => by simp [codeFrames_shift l]
  | .trap :: l => by simp [codeFrames_shift l]

theorem codeGood_shift {l : List Admin} (h : O.CodeGood l) : (shOwn δ O).CodeGood (δ.code l) := by
  refine ⟨fun r hr => ?_, fun fr hfr => ?_⟩
  · obtain ⟨r₀, h₀, rfl⟩ : ∃ r₀, r₀ ∈ codeRefs l ∧ δ.ref r₀ = r :=
      List.mem_map.mp (codeRefs_shift δ l ▸ hr)
    exact goodRef_shift δ (h.1 r₀ h₀)
  · obtain ⟨f₀, h₀, rfl⟩ : ∃ f₀, f₀ ∈ codeFrames l ∧ δ.frame f₀ = fr :=
      List.mem_map.mp (codeFrames_shift δ l ▸ hfr)
    exact frameGood_shift δ (h.2 f₀ h₀)

end ShOwn

/-! ## The initial relations -/

section Init

variable (s₀ : Store H)

theorem globals_reloc_of {t : Store H} {a : Nat} {g : GlobalInst} (h : t.globals[a]? = some g) :
    (reloc s₀ t).globals[s₀.globals.length + a]? = some ((sh s₀).ginst g) := by
  rw [reloc_globals, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, h, Option.map_some]

/-- **The importer's part right after instantiation**: a good store `u`, relocated past `s₀`,
is related to itself for the shifted ownership of everything in `u`. -/
theorem partRel_reloc {u : Store H} (hg : StoreGood u) :
    PartRel Ren.id (shOwn (sh s₀) (ownOf u)) (reloc s₀ u) (reloc s₀ u) where
  fn a ha := by
    obtain ⟨k, rfl⟩ : ∃ k, a = s₀.funcs.length + k := ⟨a - s₀.funcs.length, by have h1 : s₀.funcs.length ≤ a := ha.1; omega⟩
    obtain ⟨fi, hfi⟩ : ∃ fi, u.funcs[k]? = some fi := getElem?_of_lt' (by simpa [ownOf] using ha.2)
    refine ⟨_, funcs_reloc_of s₀ hfi, _, funcs_reloc_of s₀ hfi, rfl, fun c hc => ⟨rfl, ?_⟩⟩
    exact modGood_shift (sh s₀) (hg.fn k fi hfi c hc)
  gl a ha := by
    obtain ⟨k, rfl⟩ : ∃ k, a = s₀.globals.length + k :=
      ⟨a - s₀.globals.length, by have h1 : s₀.globals.length ≤ a := ha.1; omega⟩
    obtain ⟨g, hga⟩ : ∃ g, u.globals[k]? = some g := getElem?_of_lt' (by simpa [ownOf] using ha.2)
    exact ⟨_, globals_reloc_of s₀ hga, by simpa using globals_reloc_of s₀ hga,
      goodVal_shift (sh s₀) (hg.gl k g hga)⟩
  st a ha := by
    obtain ⟨k, rfl⟩ : ∃ k, a = s₀.structs.length + k :=
      ⟨a - s₀.structs.length, by have h1 : s₀.structs.length ≤ a := ha.1; omega⟩
    obtain ⟨si, hsi⟩ : ∃ si, u.structs[k]? = some si :=
      getElem?_of_lt' (by simpa [ownOf] using ha.2)
    refine ⟨_, structs_reloc_of s₀ hsi, by simpa using structs_reloc_of s₀ hsi, fun fv hfv => ?_⟩
    obtain ⟨fv₀, h₀, rfl⟩ : ∃ fv₀, fv₀ ∈ si.fields ∧ (sh s₀).fval fv₀ = fv :=
      List.mem_map.mp (by simpa [Shift.sinst] using hfv)
    exact goodFV_shift (sh s₀) (hg.st k si hsi fv₀ h₀)
  ar a ha := by
    obtain ⟨k, rfl⟩ : ∃ k, a = s₀.arrays.length + k :=
      ⟨a - s₀.arrays.length, by have h1 : s₀.arrays.length ≤ a := ha.1; omega⟩
    obtain ⟨ai, hai⟩ : ∃ ai, u.arrays[k]? = some ai :=
      getElem?_of_lt' (by simpa [ownOf] using ha.2)
    refine ⟨_, arrays_reloc_of s₀ hai, by simpa using arrays_reloc_of s₀ hai, fun fv hfv => ?_⟩
    obtain ⟨fv₀, h₀, rfl⟩ : ∃ fv₀, fv₀ ∈ ai.fields ∧ (sh s₀).fval fv₀ = fv :=
      List.mem_map.mp (by simpa [Shift.ainst] using hfv)
    exact goodFV_shift (sh s₀) (hg.ar k ai hai fv₀ h₀)
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

/-- **The exporter's part right after instantiation**: a good store `s₀` is related to the
store `reloc s₀ u` that extends it, for the ownership of everything in `s₀`. -/
theorem partRel_prefix (hg : StoreGood s₀) (u : Store H) :
    PartRel Ren.id (ownOf s₀) s₀ (reloc s₀ u) where
  fn a ha := by
    obtain ⟨fi, hfi⟩ : ∃ fi, s₀.funcs[a]? = some fi := getElem?_of_lt' ha
    have h' : (reloc s₀ u).funcs[a]? = some fi := by
      rw [reloc_funcs, List.getElem?_append_left ha, hfi]
    exact ⟨fi, hfi, fi, h', rfl, fun c hc => ⟨rfl, hg.fn a fi hfi c hc⟩⟩
  gl a ha := by
    obtain ⟨g, hga⟩ : ∃ g, s₀.globals[a]? = some g := getElem?_of_lt' ha
    have h' : (reloc s₀ u).globals[a]? = some g := by
      rw [reloc_globals, List.getElem?_append_left ha, hga]
    exact ⟨g, hga, by simpa using h', hg.gl a g hga⟩
  st a ha := by
    obtain ⟨si, hsi⟩ : ∃ si, s₀.structs[a]? = some si := getElem?_of_lt' ha
    have h' : (reloc s₀ u).structs[a]? = some si := by
      rw [reloc_structs, List.getElem?_append_left ha, hsi]
    exact ⟨si, hsi, by simpa using h', hg.st a si hsi⟩
  ar a ha := by
    obtain ⟨ai, hai⟩ : ∃ ai, s₀.arrays[a]? = some ai := getElem?_of_lt' ha
    have h' : (reloc s₀ u).arrays[a]? = some ai := by
      rw [reloc_arrays, List.getElem?_append_left ha, hai]
    exact ⟨ai, hai, by simpa using h', hg.ar a ai hai⟩
  stInj _ _ _ _ h := h
  arInj _ _ _ _ h := h

/-- **The two parts own disjoint addresses.** -/
theorem shOwn_ownOf_disjoint (u : Store H) :
    (∀ a, (ownOf s₀).st a → ¬ (shOwn (sh s₀) (ownOf u)).st a) ∧
    (∀ a, (ownOf s₀).ar a → ¬ (shOwn (sh s₀) (ownOf u)).ar a) ∧
    (∀ a, (ownOf s₀).fn a → ¬ (shOwn (sh s₀) (ownOf u)).fn a) ∧
    (∀ a, (ownOf s₀).gl a → ¬ (shOwn (sh s₀) (ownOf u)).gl a) := by
  refine ⟨fun a h h' => ?_, fun a h h' => ?_, fun a h h' => ?_, fun a h h' => ?_⟩ <;>
    simp only [ownOf, shOwn, sh_st, sh_ar, sh_fn, sh_gl] at h h' <;> omega

end Init

/-! ## The importer's steps in the shared store -/

section Link

variable (s₀ : Store H)

/-- **The importer's relation**: the configuration `c` of the importer (in its own store) is in
the split fragment, and its relocation past `s₀` is related to the shared store `σ` along `ρ`
for `O`, with good shifted frame and code. -/
structure ImpRel (ρ : Ren) (O : Own) (σ : Store H) (c : Config H) : Prop where
  good : SplitGood c
  rel : PartRel ρ O (reloc s₀ c.store) σ
  frame : O.FrameGood ((sh s₀).frame c.frame)
  code : O.CodeGood ((sh s₀).code c.code)

/-- The image in the shared store of an importer configuration. -/
def linkC (ρ : Ren) (σ : Store H) (c : Config H) : Config H :=
  ⟨σ, ρ.frame ((sh s₀).frame c.frame), ρ.code ((sh s₀).code c.code)⟩

/-- **One host-free step of the importer is one host-free step in the shared store.** -/
theorem step_link {P : Profile} {c c' : Config H} (h : Step P noHost c c') {ρ : Ren} {O : Own}
    {σ : Store H} (hR : ImpRel s₀ ρ O σ c) :
    ∃ ρ' O' σ', Step P noHost (linkC s₀ ρ σ c) (linkC s₀ ρ' σ' c') ∧ ImpRel s₀ ρ' O' σ' c' ∧
      Grow ρ O ρ' O' σ ∧ Touch ρ O σ σ' := by
  obtain ⟨ρ₀, O₀, σ₀, hR₀, hf₀, hc₀⟩ := hR.good
  have hsh : Step P noHost (shC s₀ c) (shC s₀ c') := step_shift s₀ h hf₀ hc₀
  obtain ⟨ρ', O', σ', hst, hR', hf', hc', hg, ht⟩ := step_sim hsh hR.rel hR.frame hR.code
  exact ⟨ρ', O', σ', hst, ⟨SplitGood.step h hR.good, hR', hf', hc'⟩, hg, ht⟩

/-- **The initial importer relation**: a thread of a good store `u` in the split fragment for
the ownership of everything in `u`, related to `reloc s₀ u` by the identity. -/
theorem impRel_init {u : Store H} (hg : StoreGood u) {f : Frame} {l : List Admin}
    (hf : (ownOf u).FrameGood f) (hc : (ownOf u).CodeGood l) :
    ImpRel s₀ Ren.id (shOwn (sh s₀) (ownOf u)) (reloc s₀ u) ⟨u, f, l⟩ where
  good := ⟨Ren.id, ownOf u, u, hg.partRel, hf, hc⟩
  rel := partRel_reloc s₀ hg
  frame := frameGood_shift (sh s₀) hf
  code := codeGood_shift (sh s₀) hc

end Link

/-! ## The stores of `instBehavioursL_inst` -/

section Linked

open Silmaril.Wasm.Component.Reference (Linked2 core3P)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {Pf : Profile}

/-- **The exporter's core store is good** (`CoreFacts` of `instBehavioursL_inst`). -/
theorem storeGood_cse {l : Linked2} (hS : l.SplitOk) {Ie : Silmaril.Wasm.Game.ScalarInstance}
    {cse : (core3P Pf).Store (CanonHost (core3P Pf))} {cie : (core3P Pf).Inst}
    (hF : CoreFacts l.exp Ie cse cie) : StoreGood (cse : Store (CanonHost (core3P Pf))) := by
  obtain ⟨⟨mt, hI⟩, -, -⟩ := hF.isInst
  have h : StoreGood (Store.mapH (fun _ => 0) (cse : Store (CanonHost (core3P Pf)))) :=
    hF.store ▸ storeGood_inst hS.exp hI
  exact (storeGood_mapH_iff _ _).mp h

/-- **The importer's core store is good**: the first projection of the store `r` of
`instBehavioursL_inst`, whose second projection is the game instance's store. -/
theorem storeGood_fst {l : Linked2} (hS : l.SplitOk) {Ii : Silmaril.Wasm.Game.ScalarInstance}
    (hI : l.imp.mod.IsInst Ii) {r : Store (CanonHost (core3P Pf) × Nat)}
    (hr : Store.mapH Prod.snd r = Ii.store) : StoreGood (Store.mapH Prod.fst r) := by
  obtain ⟨⟨mt, hIs⟩, -, -⟩ := hI
  have h : StoreGood (Store.mapH Prod.snd r) := hr ▸ storeGood_inst hS.imp hIs
  exact (storeGood_mapH_iff _ _).mpr ((storeGood_mapH_iff _ _).mp h)

/-- The segment condition of `instBehavioursL_inst` holds in the split fragment. -/
theorem SplitOk.noSeg {l : Linked2} (hS : l.SplitOk) :
    l.imp.mod.mod.data = [] ∧ l.imp.mod.mod.elems = [] := ⟨hS.imp.data, hS.imp.elems⟩

end Linked

end Silmaril.Proofs.Wasm.Component.Reference
