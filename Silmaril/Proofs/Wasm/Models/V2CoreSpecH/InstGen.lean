module

public import Silmaril.Proofs.Wasm.Models.V2CoreSpecH.Inst

/-!
# Spec preparation against single allocation, with segments and global imports

**Copied** from `Silmaril.Proofs.Wasm.Game.SpecGlobals.InstGen`, with `Store Nat`,
`Config Nat` and `FuncInst Nat` replaced by
`Store H`, `Config H` and `FuncInst H` (`variable {H : Type}`), in this topic's namespace; the
proofs are unchanged. The original is stated at `Nat` only; nothing in it uses `Nat`. The
copy is what lets `V2CoreSpecH.Main` state the spec-inclusion at every host type.

Generalises `Silmaril.Proofs.Wasm.Game.SpecGlobals.Inst` (`prepare_once`) to modules **with data
and element segments** and **with global imports**:

* `prepare_residue_emb`: the specification's `prepare? evalConst? t m (xas.map (external ι))`
  (globals allocated twice) against the preparation `prepare? evalConst? s₁ m.globalResidue …`
  of the global-free residue that `instantiateOnce?` runs after `$evalglobals`: the same segment
  code (`segCode m`), frames related by `frame ι'`, stores by `Emb ι'`, with `ι'` extending `ι`.
  The imported global addresses are renamed by `ι` (`external`).
* `prepare_once_gen`: hence, from `instantiateOnce? s m xas = some (s', f', st)`, the spec
  configuration is the renamed residue configuration `c₁`, whose segment code silmaril-lean's
  `initSegments?` runs directly to `(s', f')`.
* `forall₂_externAddrOk_map`: import typing transports to the renamed addresses.

Proofs as in the original, reusing the closed forms of `Inst`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.V2CoreSpecH

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Proofs.Wasm.Game.SpecGlobals

variable {H : Type}

/-! ## Renamed external addresses -/

theorem globals_map_external (ι : Nat → Nat) :
    ∀ xas : List ExternAddr,
      ExternAddr.globals (xas.map (external ι)) = (ExternAddr.globals xas).map ι
  | [] => rfl
  | x :: xas => by
    cases x <;> simp only [List.map_cons, external, ExternAddr.globals, List.map_cons,
      globals_map_external ι xas]

theorem tags_map_external (ι : Nat → Nat) :
    ∀ xas : List ExternAddr, ExternAddr.tags (xas.map (external ι)) = ExternAddr.tags xas
  | [] => rfl
  | x :: xas => by
    cases x <;> simp only [List.map_cons, external, ExternAddr.tags, tags_map_external ι xas]

theorem mems_map_external (ι : Nat → Nat) :
    ∀ xas : List ExternAddr, ExternAddr.mems (xas.map (external ι)) = ExternAddr.mems xas
  | [] => rfl
  | x :: xas => by
    cases x <;> simp only [List.map_cons, external, ExternAddr.mems, mems_map_external ι xas]

theorem tables_map_external (ι : Nat → Nat) :
    ∀ xas : List ExternAddr, ExternAddr.tables (xas.map (external ι)) = ExternAddr.tables xas
  | [] => rfl
  | x :: xas => by
    cases x <;> simp only [List.map_cons, external, ExternAddr.tables, tables_map_external ι xas]

theorem funcs_map_external (ι : Nat → Nat) :
    ∀ xas : List ExternAddr, ExternAddr.funcs (xas.map (external ι)) = ExternAddr.funcs xas
  | [] => rfl
  | x :: xas => by
    cases x <;> simp only [List.map_cons, external, ExternAddr.funcs, funcs_map_external ι xas]

/-- Typing of a renamed external address. -/
theorem externAddrOk_external {ι : Nat → Nat} {s t : Store H} (hst : Emb ι Univ s t)
    {xa : ExternAddr} {xt : CExternType} (h : ExternAddrOk s xa xt) :
    ExternAddrOk t (external ι xa) xt := by
  induction h with
  | tag hl => exact .tag (hst.tags ▸ hl)
  | global hl =>
    have hl' : t.globals[ι _]? = some _ := (hst.globals _ trivial).trans hl
    exact .global hl'
  | mem hl => exact .mem (hst.mems ▸ hl)
  | table hl => exact .table (hst.tables ▸ hl)
  | func hl => exact .func (fi := function ι _) (hst.func_lookup hl)
  | sub _ hok hs ih => exact .sub ih hok hs

/-- **Import typing transports to the renamed addresses.** -/
theorem forall₂_externAddrOk_map {ι : Nat → Nat} {s t : Store H} (hst : Emb ι Univ s t)
    {xas : List ExternAddr} {xts : List CExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas xts) :
    List.Forall₂ (ExternAddrOk t) (xas.map (external ι)) xts := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons (externAddrOk_external hst hh) ih

/-- Imported global addresses of well-typed imports exist. -/
theorem imports_globals_lt {s : Store H} {xas : List ExternAddr} {xts : List CExternType}
    (h : List.Forall₂ (ExternAddrOk s) xas xts) :
    ∀ a ∈ ExternAddr.globals xas, a < s.globals.length := by
  induction h with
  | nil => intro a ha; cases ha
  | @cons xa xt xas xts hh _ ih =>
    intro a ha
    cases xa with
    | global b =>
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact externAddrOk_global_lt hh a rfl
      · exact ih a ha'
    | _ => exact ih a ha

/-! ## Provisional and allocated instances -/

variable {ι : Nat → Nat}

theorem map_globals_congr {xas : List ExternAddr} {n N c : Nat}
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < n) :
    (ExternAddr.globals xas).map (shiftMap ι n N c) = ExternAddr.globals (xas.map (external ι)) := by
  rw [globals_map_external]
  exact List.map_congr_left fun a ha => shiftMap_lt (hxb a ha)

theorem frame_initial' {ρ : Nat → Nat} {s t : Store H} {D : Nat → Prop} (hst : Emb ρ D s t)
    {m : Module} {xas : List ExternAddr} (hρ : (ExternAddr.globals xas).map ρ =
      ExternAddr.globals (xas.map (external ι))) :
    frame ρ ⟨[], ModuleInst.initial s m xas⟩ =
      ⟨[], ModuleInst.initial t m (xas.map (external ι))⟩ := by
  simp only [frame, moduleView, ModuleInst.initial, hρ, funcs_map_external, List.map_nil,
    hst.funcs_length]

theorem exportsInst_twice' {ρ : Nat → Nat} {s₂ t₂ : Store H} (hs2 : Emb ρ Univ s₂ t₂)
    {m : Module} {xas : List ExternAddr} {n N : Nat} (hxb : ∀ a ∈ ExternAddr.globals xas, a < n)
    (ht2 : t₂.globals.length = N + m.globals.length) (nt : Nat) (tagTypes : List DefType) :
    exportsInst t₂ m (xas.map (external ι)) m.globals.length nt tagTypes =
      moduleView (shiftMap ι n N m.globals.length)
        (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt tagTypes) := by
  have hglob : ((ExternAddr.globals (xas ++ globalAddrs n m.globals.length)) ++
      List.range' s₂.globals.length 0).map (shiftMap ι n N m.globals.length) =
      ExternAddr.globals (xas.map (external ι)) ++ List.range' t₂.globals.length m.globals.length := by
    rw [ExternAddr.globals_append, ExternAddr.globals_globalAddrs, ht2, List.range'_zero,
      List.append_nil, List.map_append, map_globals_congr hxb, globals_shift]
  simp only [exportsInst, moduleView, hglob, ExternAddr.tags_append, ExternAddr.tags_globalAddrs,
    ExternAddr.mems_append, ExternAddr.mems_globalAddrs, ExternAddr.tables_append,
    ExternAddr.tables_globalAddrs, ExternAddr.funcs_append, ExternAddr.funcs_globalAddrs,
    List.append_nil, hs2.tags, hs2.mems, hs2.tables, hs2.funcs_length, List.map_nil,
    Module.globalResidue, tags_map_external, mems_map_external, tables_map_external,
    funcs_map_external]

theorem allocInst_twice' {ρ : Nat → Nat} {s₂ t₂ : Store H} (hs2 : Emb ρ Univ s₂ t₂)
    {m : Module} {xas : List ExternAddr} {n N : Nat} (hxb : ∀ a ∈ ExternAddr.globals xas, a < n)
    (ht2 : t₂.globals.length = N + m.globals.length) (nt ne : Nat) (tagTypes : List DefType)
    (xi : List ExportInst) :
    allocInst t₂ m (xas.map (external ι)) m.globals.length nt ne tagTypes
        (xi.map (exportView (shiftMap ι n N m.globals.length))) =
      moduleView (shiftMap ι n N m.globals.length)
        (allocInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt ne tagTypes
          xi) := by
  have hEI := exportsInst_twice' (ι := ι) hs2 hxb ht2 nt tagTypes
  unfold allocInst
  rw [hEI]
  simp only [moduleView, hs2.datas, hs2.elems, Module.globalResidue]
  rfl

theorem allocStore_globals' {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) {m : Module} {vs : List Val} {rT : List Ref}
    {rE : List (List Ref)}
    (hG : ((m.globals.map fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
        vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G)
    (tagTypes funcTypes : List DefType) (mi mi' : ModuleInst) (a : Nat) :
    (allocStore t₂ m vs rT rE tagTypes funcTypes mi').globals[shiftMap ι s.globals.length
        t.globals.length G.length a]? =
      (allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes mi).globals[a]? := by
  have hs4 : (allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes mi).globals =
      s.globals ++ G := by
    simp only [allocStore, hs2g, List.zip_nil_right, List.map_nil, List.append_nil]
  have ht4 : (allocStore t₂ m vs rT rE tagTypes funcTypes mi').globals = t.globals ++ G ++ G := by
    simp only [allocStore, ht2g, hG]
  rw [hs4, ht4]
  exact globals_twice (fun b => hst.globals b trivial) a

theorem allocStore_funcs' {ρ : Nat → Nat} {s t s₂ t₂ : Store H}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    (hs2f : s₂.funcs = s.funcs) {m : Module} {vs : List Val} {rT : List Ref}
    {rE : List (List Ref)} (c : Nat) (tagTypes funcTypes : List DefType) (mi : ModuleInst) :
    (allocStore t₂ m vs rT rE tagTypes funcTypes
        (moduleView (shiftMap ι s.globals.length t.globals.length c) mi)).funcs =
      (allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes mi).funcs.map
        (function (shiftMap ι s.globals.length t.globals.length c)) := by
  have hold : t₂.funcs = s.funcs.map (function (shiftMap ι s.globals.length t.globals.length c)) := by
    rw [hs2.funcs, hs2f]
    refine map_function_congr hb fun a ha => ?_
    rw [hρ a ha, shiftMap_lt ha]
  simp only [allocStore, hold, hs2f, List.map_append, List.map_map]
  rfl

theorem allocStore_emb' {ρ : Nat → Nat} {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    (hinj : Function.Injective ι) (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) (hs2f : s₂.funcs = s.funcs)
    {m : Module} {vs : List Val} {rT : List Ref} {rE : List (List Ref)}
    (hG : ((m.globals.map fun g => (⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
        vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G)
    (tagTypes funcTypes : List DefType) (mi : ModuleInst) :
    Emb (shiftMap ι s.globals.length t.globals.length G.length) Univ
      (allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes mi)
      (allocStore t₂ m vs rT rE tagTypes funcTypes
        (moduleView (shiftMap ι s.globals.length t.globals.length G.length) mi)) :=
  { globals := fun a _ => allocStore_globals' hst hs2g ht2g hG tagTypes funcTypes mi _ a
    inj := fun _ _ _ _ h => shiftMap_injective G.length hinj (lt_of_emb hst) h
    funcs := allocStore_funcs' hb hs2 hρ hs2f G.length tagTypes funcTypes mi
    fdom := fun fi _ => modDom_univ fi.module
    tags := by simp only [allocStore, hs2.tags]
    mems := by simp only [allocStore, hs2.mems, Module.globalResidue]
    tables := by simp only [allocStore, hs2.tables, Module.globalResidue]
    datas := by simp only [allocStore, hs2.datas, Module.globalResidue]
    elems := by simp only [allocStore, hs2.elems, Module.globalResidue]
    structs := hs2.structs
    arrays := hs2.arrays
    exns := hs2.exns }

theorem allocInst_dom' {s₂ : Store H} {m : Module} {xas : List ExternAddr} {n nt ne : Nat}
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < n) {tagTypes : List DefType}
    {xi : List ExportInst}
    (hX : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs n m.globals.length) 0 nt tagTypes)) = some xi) :
    ModDom (· < n + m.globals.length)
      (allocInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt ne tagTypes
        xi) := by
  have hg : (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt
      tagTypes).globals = ExternAddr.globals xas ++ (List.range m.globals.length).map (n + ·) := by
    simp only [exportsInst, ExternAddr.globals_append, ExternAddr.globals_globalAddrs,
      List.range'_zero, List.append_nil]
  have hlt : ∀ a ∈ (exportsInst s₂ m.globalResidue (xas ++ globalAddrs n m.globals.length) 0 nt
      tagTypes).globals, a < n + m.globals.length := by
    intro a ha
    rw [hg, List.mem_append] at ha
    rcases ha with ha | ha
    · have := hxb a ha
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
      have := List.mem_range.1 hi
      omega
  refine ⟨hlt, fun e he a ha => ?_⟩
  obtain ⟨x, -, hx⟩ := mapM_mem hX e he
  exact hlt a (allocExport?_global hx ha)

/-- The renamed exports of the residue's provisional instance are the spec's. -/
theorem exports_twice' {ρ : Nat → Nat} {s t s₂ t₂ : Store H} (hs2 : Emb ρ Univ s₂ t₂)
    {m : Module} {xas : List ExternAddr} (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (ht2l : t₂.globals.length = t.globals.length + m.globals.length) {vs : List Val}
    (hk : min m.globals.length vs.length = m.globals.length) {nt : Nat} {tagTypes : List DefType}
    {xi : List ExportInst}
    (hX : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) 0 nt tagTypes)) = some xi) :
    m.exports.mapM (allocExport? (exportsInst t₂ m (xas.map (external ι))
      (min m.globals.length vs.length) nt tagTypes)) =
      some (xi.map (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length))) := by
  have hv : allocExport? (moduleView (shiftMap ι s.globals.length t.globals.length
      m.globals.length) (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) 0 nt tagTypes)) =
      fun e => (allocExport? (exportsInst s₂ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) 0 nt tagTypes) e).map
        (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length)) :=
    funext fun e => allocExport?_view _ _ e rfl
  rw [hk, exportsInst_twice' (ι := ι) (n := s.globals.length) hs2 hxb ht2l, hv,
    mapM_option_map, hX]
  rfl

theorem allocStore_dom {s s₂ s₄ : Store H} {m : Module} {xas : List ExternAddr}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G) (hs2f : s₂.funcs = s.funcs)
    (hGl : G.length = m.globals.length) {rT : List Ref} {rE : List (List Ref)}
    {tagTypes funcTypes : List DefType} {xi : List ExportInst} {nt ne : Nat}
    (hX : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) 0 nt tagTypes)) = some xi)
    (hs4 : s₄ = allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes
      (allocInst s₂ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length) 0 nt ne
        tagTypes xi)) :
    ∀ fi ∈ s₄.funcs, ModDom (· < s₄.globals.length) fi.module := by
  have hdom := allocInst_dom' (ne := ne) hxb hX
  have hlen : s₄.globals.length = s.globals.length + m.globals.length := by
    rw [hs4]
    simp only [allocStore, hs2g, List.zip_nil_right, List.map_nil, List.append_nil,
      List.length_append, hGl]
  intro fi hfi
  rw [hlen]
  have hfi' : fi ∈ s.funcs ∨ ∃ p ∈ funcTypes.zip m.globalResidue.funcs,
      (⟨p.1, allocInst s₂ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)
        0 nt ne tagTypes xi, .wasm p.2⟩ : FuncInst H) = fi := by
    rw [hs4] at hfi
    simpa only [allocStore, hs2f, List.mem_append, List.mem_map] using hfi
  rcases hfi' with hold | ⟨p, -, hp⟩
  · exact modDom_mono (hb fi hold) fun a ha => by omega
  · rw [← hp]
    exact hdom

/-- **`$allocmodule` twice against once**, with element references and global imports. -/
theorem allocModule?_twice' {ρ : Nat → Nat} {s t s₂ t₂ : Store H} (hst : Emb ι Univ s t)
    (hinj : Function.Injective ι) (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    (hs2 : Emb ρ Univ s₂ t₂) (hρ : ∀ a, a < s.globals.length → ρ a = ι a)
    {G : List GlobalInst} (hs2g : s₂.globals = s.globals ++ G)
    (ht2g : t₂.globals = t.globals ++ G) (hs2f : s₂.funcs = s.funcs)
    {m : Module} {xas : List ExternAddr} (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {vs : List Val} {rT : List Ref} {rE : List (List Ref)} (hvs : vs.length = m.globals.length)
    (hG : List.zipWith GlobalInst.mk (Module.closedGlobalTypes m) vs = G)
    {s₄ : Store H} {mi : ModuleInst}
    (hres : allocModule? s₂ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)
      [] rT rE = some (s₄, mi)) :
    ∃ t₄, allocModule? t₂ m (xas.map (external ι)) vs rT rE =
        some (t₄, moduleView (shiftMap ι s.globals.length t.globals.length m.globals.length) mi) ∧
      Emb (shiftMap ι s.globals.length t.globals.length m.globals.length) Univ s₄ t₄ ∧
      ∀ fi ∈ s₄.funcs, ModDom (· < s₄.globals.length) fi.module := by
  obtain ⟨tagTypes, funcTypes, xi, hT, hF, hX, hmi, hs4⟩ := allocModule?_inv' hres
  have hG' : ((m.globals.map fun g => (⟨g.type.mutability,
      (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩ : CGlobalType)).zip
      vs).map (fun p => (⟨p.1, p.2⟩ : GlobalInst)) = G := by
    rw [zip_map_mk]; exact hG
  have hGl : G.length = m.globals.length := by
    rw [← hG, List.length_zipWith, Module.closedGlobalTypes, List.length_map, hvs, Nat.min_self]
  have hk : min m.globals.length vs.length = m.globals.length := by rw [hvs, Nat.min_self]
  have ht2l : t₂.globals.length = t.globals.length + m.globals.length := by
    rw [ht2g, List.length_append, hGl]
  have hX0 : m.exports.mapM (allocExport? (exportsInst s₂ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) 0
      (min m.tables.length rT.length) tagTypes)) = some xi := hX
  have hX' := exports_twice' (ι := ι) hs2 hxb ht2l hk hX0
  have hmi' : allocInst t₂ m (xas.map (external ι)) (min m.globals.length vs.length)
      (min m.tables.length rT.length) (min m.elems.length rE.length) tagTypes
      (xi.map (exportView (shiftMap ι s.globals.length t.globals.length m.globals.length))) =
      moduleView (shiftMap ι s.globals.length t.globals.length m.globals.length) mi := by
    rw [hmi, hk, allocInst_twice' (ι := ι) (n := s.globals.length) hs2 hxb ht2l]
    rfl
  have hT' : m.tags.mapM (fun x => (allocTypes m.types)[x.toNat]?) = some tagTypes := hT
  have hF' : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes := hF
  have he : Emb (shiftMap ι s.globals.length t.globals.length m.globals.length) Univ s₄
      (allocStore t₂ m vs rT rE tagTypes funcTypes
        (moduleView (shiftMap ι s.globals.length t.globals.length m.globals.length) mi)) := by
    have he₀ := allocStore_emb' (rT := rT) (rE := rE) hst hinj hb hs2 hρ hs2g ht2g hs2f hG'
      tagTypes funcTypes mi
    rw [hGl] at he₀
    rw [hs4]
    exact he₀
  refine ⟨_, by rw [allocModule?_of hT' hF' hX', hmi'], he, ?_⟩
  exact allocStore_dom (ne := min m.elems.length rE.length) hb hxb hs2g hs2f hGl hX0
    (hs4.trans (congrArg (allocStore s₂ m.globalResidue [] rT rE tagTypes funcTypes) hmi))

/-! ## `prepare?` with segments -/

/-- The segment-initialisation code of `$instantiate`. -/
def segCode (m : Module) : List Admin :=
  expression ((List.range m.elems.length).zip m.elems |>.flatMap fun (i, e) => runElem i e) ++
    expression ((List.range m.data.length).zip m.data |>.flatMap fun (i, d) => runData i d)

/-- The size guard of `prepare?`. -/
def SegGuard (m : Module) : Prop :=
  m.elems.length ≤ 2 ^ 32 ∧ m.data.length ≤ 2 ^ 32 ∧
    (∀ d ∈ m.data, d.bytes.size < 2 ^ 32) ∧ (∀ e ∈ m.elems, e.init.length < 2 ^ 32)

theorem prepare?_residue' {m : Module} {s₁ : Store H} {xas : List ExternAddr} {c : Config H}
    {st : Option FuncIdx} (h : prepare? evalConst? s₁ m.globalResidue xas = some (c, st)) :
    ∃ s₂ f₂ rT s₃ f₃ rE s₄ mi,
      evalExprs? evalConst? s₁ ⟨[], ModuleInst.initial s₁ m.globalResidue xas⟩
        (m.tables.map Table.init) = some (s₂, f₂, rT) ∧
      evalExprss? evalConst? s₂ f₂ (m.elems.map Elem.init) = some (s₃, f₃, rE) ∧
      allocModule? s₃ m.globalResidue xas [] rT rE = some (s₄, mi) ∧
      c = ⟨s₄, { module := mi }, segCode m⟩ ∧ st = m.start ∧ SegGuard m := by
  have hst := prepare?_start h
  unfold prepare? at h
  split at h
  · rename_i hguard
    simp only [Module.globalResidue_globals, List.map_nil, evalGlobals?] at h
    split at h
    · cases h
    · rename_i s₂ f₂ rT hT
      split at h
      · cases h
      · rename_i s₃ f₃ rE hE
        split at h
        · cases h
        · rename_i s₄ mi hM
          cases h
          exact ⟨s₂, f₂, rT, s₃, f₃, rE, s₄, mi, hT, hE, hM, rfl, hst, hguard⟩
  · cases h

theorem prepare?_of' {t : Store H} {m : Module} {xas : List ExternAddr} (hguard : SegGuard m)
    {t₁ t₂ t₃ t₄ : Store H} {g₁ g₂ g₃ : Frame} {vs : List Val} {rT : List Ref}
    {rE : List (List Ref)} {mi : ModuleInst}
    (h1 : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (t₁, g₁, vs))
    (h2 : evalExprs? evalConst? t₁ g₁ (m.tables.map Table.init) = some (t₂, g₂, rT))
    (h3 : evalExprss? evalConst? t₂ g₂ (m.elems.map Elem.init) = some (t₃, g₃, rE))
    (h4 : allocModule? t₃ m xas vs rT rE = some (t₄, mi)) :
    prepare? evalConst? t m xas = some (⟨t₄, { module := mi }, segCode m⟩, m.start) := by
  have h1' : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m xas⟩
      (m.globals.map fun g => ⟨g.type.mutability,
        (liftVal g.type.value).substAll ((allocTypes m.types).map .dt)⟩)
      (m.globals.map Global.init) = some (t₁, g₁, vs) := h1
  unfold prepare?
  split
  · simp only [h1', h2, h3, h4, segCode]
  · exact absurd hguard ‹_›

/-! ## The comparison -/

/-- Spec preparation against the residue preparation that `instantiateOnce?` runs. -/
theorem prepare_residue_emb {s t : Store H} {ι : Nat → Nat}
    (hst : Emb ι Univ s t) (hinj : Function.Injective ι)
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr}
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {s₁ : Store H} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config H} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    ∃ (c : Config H) (ι' : Nat → Nat),
      prepare? evalConst? t m (xas.map (external ι)) = some (c, st) ∧
      c.code = c₁.code ∧ c.frame = frame ι' c₁.frame ∧ Function.Injective ι' ∧
      Emb ι' Univ c₁.store c.store ∧ (∀ a, a < s.globals.length → ι' a = ι a) ∧
      ∀ fi ∈ c₁.store.funcs, ModDom (· < c₁.store.globals.length) fi.module := by
  obtain ⟨s₂, f₂, rT, s₃, f₃, rE, s₄, mi, hT, hE, hM, hc₁, hst₀, hguard⟩ := prepare?_residue' hp
  have hf₁ : f₁ = ⟨[], ModuleInst.initial s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length)⟩ := evalGlobals?_initial hg
  have hT₁ : evalExprs? evalConst? s₁ f₁ (m.tables.map Table.init) = some (s₂, f₂, rT) := by
    rw [hf₁]; exact hT
  have hρ : Emb (shiftMap ι s.globals.length t.globals.length 0) Univ s t :=
    emb_shift hst hinj hb 0
  have hl : ∀ a, s.globals.length ≤ a → shiftMap ι s.globals.length t.globals.length 0 a =
      t.globals.length + (a - s.globals.length) := fun a ha => by
    rw [shiftMap_ge ha, Nat.add_zero]
  obtain ⟨t₁, ht₁, hst₁⟩ := evalGlobals?_emb _ _ hρ hl hg
  obtain ⟨t₂, ht₂, hst₂⟩ := evalExprs?_emb _ hst₁ hT₁
  obtain ⟨t₃, ht₃, hst₃⟩ := evalExprss?_emb _ hst₂ hE
  have ht₁' : evalGlobals? evalConst? t ⟨[], ModuleInst.initial t m (xas.map (external ι))⟩
      (Module.closedGlobalTypes m) (m.globals.map Global.init) =
      some (t₁, frame (shiftMap ι s.globals.length t.globals.length 0) f₁, vs) := by
    rw [← frame_initial' hρ (map_globals_congr hxb)]; exact ht₁
  obtain ⟨hs1g, hs1f, -⟩ := evalGlobals?_shape hg
  obtain ⟨ht1g, -, -⟩ := evalGlobals?_shape ht₁'
  obtain ⟨hs2g, hs2f, -⟩ := evalExprs?_shape hT₁
  obtain ⟨ht2g, -, -⟩ := evalExprs?_shape ht₂
  obtain ⟨hs3g, hs3f, -⟩ := evalExprss?_shape hE
  obtain ⟨ht3g, -, -⟩ := evalExprss?_shape ht₃
  have hvs : vs.length = m.globals.length := by
    rw [evalGlobals?_length _ _ hg, Module.closedGlobalTypes, List.length_map]
  have hag : ∀ a, a < s.globals.length →
      shiftMap ι s.globals.length t.globals.length 0 a = ι a := fun a ha => shiftMap_lt ha
  obtain ⟨t₄, ht₄, hst₄, hbd⟩ := allocModule?_twice' hst hinj hb hst₃ hag
    ((hs3g.trans hs2g).trans hs1g) ((ht3g.trans ht2g).trans ht1g) ((hs3f.trans hs2f).trans hs1f)
    hxb hvs rfl hM
  rw [hc₁, hst₀]
  exact ⟨⟨t₄, { module := moduleView (shiftMap ι s.globals.length t.globals.length
      m.globals.length) mi }, segCode m⟩, shiftMap ι s.globals.length t.globals.length
      m.globals.length, prepare?_of' hguard ht₁' ht₂ ht₃ ht₄, rfl, rfl,
    shiftMap_injective _ hinj (lt_of_emb hst), hst₄, fun a ha => shiftMap_lt ha, hbd⟩

/-- The run of `instantiateOnce?`: `$evalglobals`, the residue's preparation, then the direct
segment initialisation. -/
theorem once_inv' {s : Store H} {m : Module} {xas : List ExternAddr} {s' : Store H}
    {f' : Frame} {st : Option FuncIdx} (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ s₁ f₁ vs c₁,
      evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
        (m.globals.map Global.init) = some (s₁, f₁, vs) ∧
      prepare? evalConst? s₁ m.globalResidue
        (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st) ∧
      initSegments? evalConst? c₁.store c₁.frame m.globalResidue = some (s', f') := by
  unfold instantiateOnce? at ho
  split at ho
  · cases ho
  · rename_i s₁ f₁ vs hg
    unfold instantiateDirect? prepareDirect? at ho
    split at ho
    · cases ho
    · rename_i c₁ st₀ hp
      split at ho
      · cases ho
      · rename_i s'' f'' hi
        cases ho
        exact ⟨s₁, f₁, vs, c₁, hg, hp, hi⟩

/-- With segments and global imports: the spec configuration is the renamed residue
configuration, whose segment code `initSegments?` runs directly to the once store. -/
theorem prepare_once_gen {s t : Store H} {ι : Nat → Nat}
    (hst : Emb ι Univ s t) (hinj : Function.Injective ι)
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr}
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {s' : Store H} {f' : Frame} {st : Option FuncIdx}
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ (c c₁ : Config H) (ι' : Nat → Nat),
      prepare? evalConst? t m (xas.map (external ι)) = some (c, st) ∧
      initSegments? evalConst? c₁.store c₁.frame m.globalResidue = some (s', f') ∧
      c.code = c₁.code ∧ c.frame = frame ι' c₁.frame ∧ Function.Injective ι' ∧
      Emb ι' Univ c₁.store c.store ∧ (∀ a, a < s.globals.length → ι' a = ι a) ∧
      ∀ fi ∈ c₁.store.funcs, ModDom (· < c₁.store.globals.length) fi.module := by
  obtain ⟨s₁, f₁, vs, c₁, hg, hp, hi⟩ := once_inv' ho
  obtain ⟨c, ι', hc, hcode, hframe, hinj', he, hag, hbd⟩ :=
    prepare_residue_emb hst hinj hb hxb hg hp
  exact ⟨c, c₁, ι', hc, hi, hcode, hframe, hinj', he, hag, hbd⟩

/-- The residue configuration's code is the module's segment code. -/
theorem residue_code {s₁ : Store H} {m : Module} {xas : List ExternAddr} {c₁ : Config H}
    {st : Option FuncIdx} (hp : prepare? evalConst? s₁ m.globalResidue xas = some (c₁, st)) :
    c₁.code = segCode m := by
  obtain ⟨s₂, f₂, rT, s₃, f₃, rE, s₄, mi, -, -, -, hc, -, -⟩ := prepare?_residue' hp
  rw [hc]

end Silmaril.Proofs.Wasm.Models.V2CoreSpecH
