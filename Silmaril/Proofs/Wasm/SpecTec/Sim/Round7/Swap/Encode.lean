module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Swap.NxInstr
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Unstrip.Basic
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.ExpEnc.Config

/-!
# Round 7, the export swap: the encoder lemma

Ingredient 4 of G9's plan for `Round7.Task.swapEquiv` (`docs/projects/spectec/README.md`, §2), at the value level:

* `eraseV_configV`: `eraseV (configV hn c) = configV hn (stripConfig c)`. Erasing the export
  lists of the image is the image of the stripped configuration.
* `allIn_configV`: the only records of `configV hn c` with an `EXPORTS` field are the images of
  the module instances of `c` (`Round7.mods c`). Every other encoder builds no such record
  (`nxB_*`, a copy of the `efB` sweep of `Round7/ExpEnc`).
* `qInj_QC`: under `StripInj c`, `eraseV` is injective on `QC c`, hence (by
  `Round7.Swap.eraseV_inj`) on every `AllIn (QC c)` value.
* `allIn_configV_unstrip`: for export-free `d`, `configV hn (mapConfig (unstrip c) d)` is
  `AllIn (QC c)`.
* `eq_configV_unstrip`: **the reconstruction**. Under `StripInj c`, a value `w` that is
  `AllIn (QC c)` and erases to the image of an export-free `d` is the image of
  `mapConfig (unstrip c) d`. This is the last step of the backward half of `Task.swapEquiv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.SpecTec.Equiv.RuntimeBridge
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-! ## `eraseV` fixes values without `EXPORTS` records -/

mutual
theorem eraseV_of_nxB : ∀ v : Value, nxB v = true → eraseV v = v
  | .bool _, _ => rfl
  | .num _, _ => rfl
  | .text _, _ => rfl
  | .tuple vs, h => by rw [eraseV_tuple, eraseVs_of_nxBs vs h]
  | .case _ w, h => by rw [eraseV_case, eraseV_of_nxB w h]
  | .struct gs, h => by rw [eraseV_struct, eraseVf_of_nxBf gs h]
  | .list vs, h => by rw [eraseV_list, eraseVs_of_nxBs vs h]
  | .opt none, _ => rfl
  | .opt (some w), h => by rw [eraseV_opt_some, eraseV_of_nxB w h]

theorem eraseVs_of_nxBs : ∀ vs : List Value, nxBs vs = true → eraseVs vs = vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [nxBs, Bool.and_eq_true] at h
    simp only [eraseVs, eraseV_of_nxB v h.1, eraseVs_of_nxBs vs h.2]

theorem eraseVf_of_nxBf : ∀ gs : List (IL.AtomS × Value), nxBf gs = true → eraseVf gs = gs
  | [], _ => rfl
  | (a, v) :: gs, h => by
    simp only [nxBf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [eraseVf_cons, eraseVf_of_nxBf gs h.2, ite_eq_right h.1.2, eraseV_of_nxB v h.1.1]
end

/-! ## The leaves build no `EXPORTS` records -/

@[simp] theorem nxB_bytesToValue (bs : ByteArray) : nxB (bytesToValue bs) = true := by
  simp only [bytesToValue, nxB_list, nxBs_map]
  exact List.all_eq_true.2 fun _ _ => rfl

@[simp] theorem nxB_cGlobalTypeV (g : Validation.CGlobalType) : nxB (cGlobalTypeV g) = true := by
  simp only [cGlobalTypeV, nxB_case, nxB_tuple, nxBs_cons, nxB_mutability, nxB_tyV, nxBs_nil,
    Bool.and_self]

@[simp] theorem nxB_cTableTypeV (t : Validation.CTableType) : nxB (cTableTypeV t) = true := by
  simp only [cTableTypeV, nxB_case, nxB_tuple, nxBs_cons, nxB_addrType, nxB_limits, nxB_tyV,
    nxBs_nil, Bool.and_self]

@[simp] theorem nxB_fieldValV (v : FieldVal) : nxB (fieldValV v) = true := by
  cases v <;> simp [fieldValV, Silmaril.SpecTec.Equiv.Execution.pctV]

@[simp] theorem nxB_exportInstToValue (e : ExportInst) : nxB (exportInstToValue e) = true := by
  obtain ⟨n, a⟩ := e
  cases a <;> simp [exportInstToValue, nameToValue, charToValue, externAddrToValue]

theorem nxB_locals (l : List (Option Val)) :
    nxB (.list (l.map fun o => .opt (o.map valV))) = true := by
  simp

theorem nxB_codeV (hn : H → String) (fi : FuncInst H) :
    nxB (match fi.code with
      | .wasm fn => .case "FUNC" (.tuple [Silmaril.SpecTec.Equiv.Execution.pctV fn.type.toNat,
          .list (fn.locals.map fun t => .case "LOCAL" (Encode.toValue t)),
          .list (instrsToV fn.body)])
      | .host h => .case "_HOSTFUNC" (.text (hn h))) = true := by
  split <;> simp [nxB_instrsToV, Silmaril.SpecTec.Equiv.Execution.pctV]

theorem nxB_storeRest (s : Store H) :
    nxB (.list (s.tags.map (tagInstToValue CT))) = true ∧
    nxB (.list (s.globals.map globalInstV)) = true ∧
    nxB (.list (s.mems.map memInstToValue)) = true ∧
    nxB (.list (s.tables.map (tableInstToValue CT))) = true ∧
    nxB (.list (s.datas.map dataInstToValue)) = true ∧
    nxB (.list (s.elems.map (elemInstToValue CT))) = true ∧
    nxB (.list (s.structs.map structInstV)) = true ∧
    nxB (.list (s.arrays.map arrayInstV)) = true ∧
    nxB (.list (s.exns.map exnInstV)) = true := by
  simp [tagInstToValue, globalInstV, memInstToValue, tableInstToValue, dataInstToValue,
    elemInstToValue, structInstV, arrayInstV, exnInstV, CT]

/-! ## Erasing the image is the image of the stripped configuration -/

theorem eraseV_moduleInstToValue (m : ModuleInst) :
    eraseV (moduleInstToValue CT m) = moduleInstToValue CT (stripModule m) := by
  rw [← eraseV_of_efB _ (ExpEnc.efB_moduleInstToValue (m := stripModule m) rfl)]
  simp [moduleInstToValue, stripModule]

theorem eraseV_frameV (f : Frame) : eraseV (frameV f) = frameV (mapFrame stripModule f) := by
  simp only [frameV, mapFrame, eraseV_struct, eraseVf_cons, eraseVf_nil, String.reduceEq,
    ite_false, eraseV_moduleInstToValue]
  rw [eraseV_of_nxB _ (nxB_locals f.locals)]

mutual
theorem eraseV_adminToV :
    ∀ a : Admin, eraseV (adminToV a) = adminToV (mapAdmin stripModule a)
  | .plain i => by simp only [adminToV, mapAdmin]; exact eraseV_of_nxB _ (nxB_instrToV i)
  | .ref r => by simp only [adminToV, mapAdmin]; exact eraseV_of_nxB _ (nxB_refToValue r)
  | .callRefType d => by
    simp only [adminToV, mapAdmin]; exact eraseV_of_nxB _ (by simp [CT])
  | .returnCallRefType d => by
    simp only [adminToV, mapAdmin]; exact eraseV_of_nxB _ (by simp [CT])
  | .label n cont body => by
    simp only [adminToV, mapAdmin, eraseV_case, eraseV_tuple, eraseVs, eraseV_num,
      eraseV_list, eraseVs_of_nxBs _ (nxB_instrsToV cont), eraseVs_adminsToV body]
  | .handler n cs body => by
    have hc : nxB (.list (cs.map Encode.toValue)) = true := by simp
    simp only [adminToV, mapAdmin, eraseV_case, eraseV_tuple, eraseVs, eraseV_num,
      eraseV_of_nxB _ hc, eraseV_list, eraseVs_adminsToV body]
  | .frame n f body => by
    simp only [adminToV, mapAdmin, eraseV_case, eraseV_tuple, eraseVs, eraseV_num,
      eraseV_frameV f, eraseV_list, eraseVs_adminsToV body]
  | .trap => by
    simp only [adminToV, mapAdmin]
    exact eraseV_of_nxB _ rfl

theorem eraseVs_adminsToV :
    ∀ l : List Admin, eraseVs (adminsToV l) = adminsToV (mapAdmins stripModule l)
  | [] => rfl
  | a :: l => by
    simp only [adminsToV, mapAdmins, eraseVs, eraseV_adminToV a, eraseVs_adminsToV l]
end

theorem eraseV_funcInstV (hn : H → String) (fi : FuncInst H) :
    eraseV (funcInstV hn fi) = funcInstV hn (mapFI stripModule fi) := by
  rw [← eraseV_of_efB _ (ExpEnc.efB_funcInstV hn (fi := mapFI stripModule fi) rfl)]
  simp only [funcInstV, mapFI, eraseV_struct, eraseVf_cons, eraseVf_nil, String.reduceEq,
    ite_false, eraseV_moduleInstToValue]
  rfl

theorem eraseV_storeV (hn : H → String) (s : Store H) :
    eraseV (storeV hn s) = storeV hn (mapStore stripModule s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := nxB_storeRest (H := H) s
  simp only [storeV, mapStore, eraseV_struct, eraseVf_cons, eraseVf_nil, String.reduceEq,
    ite_false]
  rw [eraseV_of_nxB _ h1, eraseV_of_nxB _ h2, eraseV_of_nxB _ h3, eraseV_of_nxB _ h4,
    eraseV_of_nxB _ h5, eraseV_of_nxB _ h6, eraseV_of_nxB _ h7, eraseV_of_nxB _ h8,
    eraseV_of_nxB _ h9, eraseV_list', List.map_map, List.map_map]
  have hf : (eraseV ∘ funcInstV hn) = (funcInstV hn ∘ mapFI stripModule) :=
    funext fun fi => eraseV_funcInstV hn fi
  rw [hf]

/-- **The encoder lemma for the swap**: erasing the export lists of the image of `c` gives the
image of `stripConfig c`. -/
theorem eraseV_configV (hn : H → String) (c : Config H) :
    eraseV (configV hn c) = configV hn (stripConfig c) := by
  rw [← mapConfig_stripModule]
  simp only [configV, stateV, mapConfig, eraseV_case, eraseV_tuple, eraseVs, eraseV_storeV,
    eraseV_frameV, eraseV_list, eraseVs_adminsToV]

/-! ## The module records of the image -/

section AllInImage

variable {Q : Value → Prop}

theorem allIn_moduleInstToValue {m : ModuleInst} (hm : Q (moduleInstToValue CT m)) :
    AllIn Q (moduleInstToValue CT m) := by
  refine ⟨fun _ => hm, ?_⟩
  simp only [AllInf_cons, AllInf_nil, and_true]
  refine ⟨allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_,
    allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_, allIn_of_nxB Q _ ?_,
    allIn_of_nxB Q _ ?_⟩ <;> simp [CT]

theorem allIn_frameV {f : Frame} (hm : Q (moduleInstToValue CT f.module)) :
    AllIn Q (frameV f) := by
  refine ⟨fun h => absurd h (by simp), ?_⟩
  simp only [AllInf_cons, AllInf_nil, and_true]
  exact ⟨allIn_of_nxB Q _ (nxB_locals f.locals), allIn_moduleInstToValue hm⟩

mutual
theorem allIn_adminToV :
    ∀ a : Admin, (∀ m ∈ modsAdmin a, Q (moduleInstToValue CT m)) → AllIn Q (adminToV a)
  | .plain i, _ => allIn_of_nxB Q _ (nxB_instrToV i)
  | .ref r, _ => allIn_of_nxB Q _ (nxB_refToValue r)
  | .callRefType d, _ => allIn_of_nxB Q _ (by simp [adminToV, CT])
  | .returnCallRefType d, _ => allIn_of_nxB Q _ (by simp [adminToV, CT])
  | .label n cont body, h => by
    simp only [adminToV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true]
    exact ⟨trivial, allIn_of_nxB Q _ (by simp [nxB_instrsToV cont]),
      allIns_adminsToV body (by simpa [modsAdmin] using h)⟩
  | .handler n cs body, h => by
    simp only [adminToV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true]
    exact ⟨trivial, allIn_of_nxB Q _ (by simp),
      allIns_adminsToV body (by simpa [modsAdmin] using h)⟩
  | .frame n f body, h => by
    simp only [adminToV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true]
    simp only [modsAdmin, List.mem_cons, forall_eq_or_imp] at h
    exact ⟨trivial, allIn_frameV h.1, allIns_adminsToV body h.2⟩
  | .trap, _ => allIn_of_nxB Q _ rfl

theorem allIns_adminsToV :
    ∀ l : List Admin, (∀ m ∈ modsAdmins l, Q (moduleInstToValue CT m)) →
      AllIns Q (adminsToV l)
  | [], _ => trivial
  | a :: l, h => by
    simp only [modsAdmins, List.mem_append, or_imp, forall_and] at h
    exact ⟨allIn_adminToV a h.1, allIns_adminsToV l h.2⟩
end

theorem allIn_funcInstV (hn : H → String) {fi : FuncInst H}
    (hm : Q (moduleInstToValue CT fi.module)) : AllIn Q (funcInstV hn fi) := by
  refine ⟨fun h => absurd h (by simp), ?_⟩
  simp only [AllInf_cons, AllInf_nil, and_true]
  exact ⟨allIn_of_nxB Q _ (by simp [CT]), allIn_moduleInstToValue hm,
    allIn_of_nxB Q _ (nxB_codeV hn fi)⟩

theorem allIn_storeV (hn : H → String) {s : Store H}
    (hm : ∀ fi ∈ s.funcs, Q (moduleInstToValue CT fi.module)) : AllIn Q (storeV hn s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := nxB_storeRest (H := H) s
  refine ⟨fun h => absurd h (by simp), ?_⟩
  simp only [AllInf_cons, AllInf_nil, and_true]
  refine ⟨allIn_of_nxB Q _ h1, allIn_of_nxB Q _ h2, allIn_of_nxB Q _ h3, allIn_of_nxB Q _ h4,
    ?_, allIn_of_nxB Q _ h5, allIn_of_nxB Q _ h6, allIn_of_nxB Q _ h7, allIn_of_nxB Q _ h8,
    allIn_of_nxB Q _ h9⟩
  simp only [AllIn_list, allIns_iff, List.mem_map]
  rintro _ ⟨fi, hfi, rfl⟩
  exact allIn_funcInstV hn (hm fi hfi)

/-- The image of `c` is `AllIn Q` as soon as the images of its module instances satisfy `Q`. -/
theorem allIn_configV_of (hn : H → String) {c : Config H}
    (hm : ∀ m ∈ mods c, Q (moduleInstToValue CT m)) : AllIn Q (configV hn c) := by
  simp only [mods, List.mem_append, List.mem_map, List.mem_cons] at hm
  simp only [configV, stateV, AllIn_case, AllIn_tuple, AllIns_cons, AllIns_nil, and_true,
    AllIn_list]
  exact ⟨⟨allIn_storeV hn fun fi hfi => hm _ (Or.inl ⟨fi, hfi, rfl⟩),
      allIn_frameV (hm _ (Or.inr (Or.inl rfl)))⟩,
    allIns_adminsToV c.code fun m h => hm m (Or.inr (Or.inr h))⟩

end AllInImage

/-- **The only `EXPORTS` records of `configV hn c` are its module instances.** -/
theorem allIn_configV (hn : H → String) (c : Config H) : AllIn (InMods c) (configV hn c) :=
  allIn_configV_of hn fun m hm => ⟨m, hm, rfl⟩

/-! ## Injectivity under `StripInj` -/

theorem inMods_QC {c : Config H} {r : Value} (h : InMods c r) : QC c r := Or.inl h

/-- **Under `StripInj c`, `eraseV` is injective on `QC c`.** -/
theorem qInj_QC {c : Config H} (hinj : StripInj c) : QInj (QC c) := by
  have key : ∀ m₁ m₂ : ModuleInst, eraseV (moduleInstToValue CT m₁) =
      eraseV (moduleInstToValue CT m₂) → stripModule m₁ = stripModule m₂ := fun m₁ m₂ h => by
    rw [eraseV_moduleInstToValue, eraseV_moduleInstToValue] at h
    exact moduleInstToValue_inj CT h
  have hfix : ∀ m : ModuleInst, m.exports = [] → stripModule m = m := fun m h => by
    cases m; simp_all [stripModule]
  rintro x y (⟨m₁, h₁, rfl⟩ | ⟨m₁, e₁, rfl, n₁⟩) (⟨m₂, h₂, rfl⟩ | ⟨m₂, e₂, rfl, n₂⟩) h <;>
    have hs := key _ _ h
  · rw [hinj m₁ h₁ m₂ h₂ hs]
  · rw [hfix m₂ e₂] at hs
    have := n₂ m₁ h₁ hs
    rw [← hs, hfix m₁ this]
  · rw [hfix m₁ e₁] at hs
    have := n₁ m₂ h₂ hs.symm
    rw [hs, hfix m₂ this]
  · rw [hfix m₁ e₁, hfix m₂ e₂] at hs
    rw [hs]

/-! ## The reconstruction -/

mutual
theorem modsAdmin_map (μ : ModuleInst → ModuleInst) :
    ∀ a : Admin, modsAdmin (mapAdmin μ a) = (modsAdmin a).map μ
  | .plain _ => rfl
  | .ref _ => rfl
  | .callRefType _ => rfl
  | .returnCallRefType _ => rfl
  | .label _ _ body => by simp only [mapAdmin, modsAdmin, modsAdmins_map μ body]
  | .handler _ _ body => by simp only [mapAdmin, modsAdmin, modsAdmins_map μ body]
  | .frame _ f body => by
    simp only [mapAdmin, modsAdmin, mapFrame, modsAdmins_map μ body, List.map_cons]
  | .trap => rfl

theorem modsAdmins_map (μ : ModuleInst → ModuleInst) :
    ∀ l : List Admin, modsAdmins (mapAdmins μ l) = (modsAdmins l).map μ
  | [] => rfl
  | a :: l => by
    simp only [mapAdmins, modsAdmins, modsAdmin_map μ a, modsAdmins_map μ l, List.map_append]
end

theorem mods_mapConfig (μ : ModuleInst → ModuleInst) (c : Config H) :
    mods (mapConfig μ c) = (mods c).map μ := by
  simp [mods, mapConfig, mapStore, mapFI, mapFrame, modsAdmins_map]

theorem exports_of_stripped {d : Config H} (hd : Stripped d) {m : ModuleInst} (hm : m ∈ mods d) :
    m.exports = [] := by
  have h : mods d = (mods d).map stripModule := by
    conv_lhs => rw [← hd, ← mapConfig_stripModule]
    exact mods_mapConfig _ _
  rw [h, List.mem_map] at hm
  obtain ⟨m', _, rfl⟩ := hm
  rfl

/-- **The image of `mapConfig (unstrip c) d` is `AllIn (QC c)`**, for export-free `d`. -/
theorem allIn_configV_unstrip (hn : H → String) (c : Config H) {d : Config H} (hd : Stripped d) :
    AllIn (QC c) (configV hn (mapConfig (unstrip c) d)) := by
  refine allIn_configV_of hn fun m hm => ?_
  rw [mods_mapConfig, List.mem_map] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  by_cases hx : ∃ m ∈ mods c, stripModule m = m₀
  · have hu : unstrip c m₀ = hx.choose := by simp only [unstrip, dite_eq_left hx]
    exact Or.inl ⟨_, hu ▸ hx.choose_spec.1, by rw [hu]⟩
  · have hu : unstrip c m₀ = m₀ := by simp only [unstrip, dite_eq_right hx]
    refine Or.inr ⟨m₀, exports_of_stripped hd hm₀, by rw [hu], ?_⟩
    exact fun m' hm' hs => absurd ⟨m', hm', hs⟩ hx

/-- **The reconstruction**: under `StripInj c`, a value that is `AllIn (QC c)` and erases to the
image of an export-free `d` is the image of `mapConfig (unstrip c) d`. -/
theorem eq_configV_unstrip (hn : H → String) {c d : Config H} (hinj : StripInj c)
    (hd : Stripped d) {w : Value} (hw : AllIn (QC c) w) (he : eraseV w = configV hn d) :
    w = configV hn (mapConfig (unstrip c) d) := by
  refine eraseV_inj (qInj_QC hinj) hw (allIn_configV_unstrip hn c hd) ?_
  rw [he, eraseV_configV, ← mapConfig_stripModule, mapConfig_comp]
  conv_lhs => rw [← hd, ← mapConfig_stripModule]
  congr 2
  funext m
  exact (stripModule_unstrip c m).symm

end Silmaril.Wasm.SpecTec.Sim.Round7.Swap
