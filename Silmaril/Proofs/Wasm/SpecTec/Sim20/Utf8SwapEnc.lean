module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8SwapValue
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.Thms

/-!
# Re-encoding export lists: one configuration

* `swapS_swapS`: the exchange `swapS S` of each `u ∈ S` with its re-encoding `encV S u` is an
  involution. The re-encodings are longer than every member of `S` and pairwise distinct
  (`encV_not_mem`, `encV_inj`).
* `swapS_encV`: `swapS S` takes a re-encoding back to its original.
* **`swapV_configV_exp`**: if `τ` takes the image of `F m` back to the image of `m`'s exports
  for every module instance `m` of `c`, then `swapV τ` takes the image of `expConfig20 F c` to
  the image of `c`. The other parts of the image have no `EXPORTS` record.
* `modsQ_mods20`: every module instance of `c` is in `mods20 c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim20
open Silmaril.Wasm.SpecTec.Sim20.Utf8Strip (ModsQ AdminMods AdminsMods)

/-! ## The exchange -/

theorem le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simpa using Nat.le_add_left_of_le (ih h)

theorem vlen_lt_bnd {S : List Value} {u : Value} (hu : u ∈ S) : vlen u < bnd S :=
  Nat.lt_succ_of_le (le_sum_of_mem (List.mem_map_of_mem hu))

@[simp] theorem vlen_expV (l : List ExportInst) : vlen (expV l) = l.length := by
  simp [expV, vlen]

theorem vlen_encV (S : List Value) (u : Value) : vlen (encV S u) = bnd S + S.idxOf u := by
  simp [encV]

/-- **A re-encoding is not a member of `S`.** -/
theorem encV_not_mem {S : List Value} (u : Value) : encV S u ∉ S := fun h => by
  have := vlen_lt_bnd h
  rw [vlen_encV] at this
  omega

/-- **The re-encoding is injective on `S`.** -/
theorem encV_inj {S : List Value} {u u' : Value} (hu : u ∈ S) (h : encV S u = encV S u') :
    u = u' := by
  have hl := congrArg vlen h
  rw [vlen_encV, vlen_encV] at hl
  exact (List.idxOf_inj hu).1 (by omega)

theorem swapS_of_mem {S : List Value} {v : Value} (hv : v ∈ S) : swapS S v = encV S v := by
  simp [swapS, hv]

/-- **`swapS S` takes a re-encoding back.** -/
theorem swapS_encV {S : List Value} {u : Value} (hu : u ∈ S) : swapS S (encV S u) = u := by
  have hn := encV_not_mem (S := S) u
  have hf : ∃ u', S.find? (fun x => encV S x == encV S u) = some u' := by
    cases h : S.find? (fun x => encV S x == encV S u) with
    | none => exact absurd (List.find?_eq_none.1 h u hu) (by simp)
    | some u' => exact ⟨u', rfl⟩
  obtain ⟨u', hu'⟩ := hf
  have hm : u' ∈ S := List.mem_of_find?_eq_some hu'
  have he : encV S u' = encV S u := by simpa using List.find?_some hu'
  simp only [swapS, hn, ite_false, hu']
  exact encV_inj hm he

/-- **`swapS S` is an involution.** -/
theorem swapS_swapS (S : List Value) (v : Value) : swapS S (swapS S v) = v := by
  by_cases hv : v ∈ S
  · rw [swapS_of_mem hv, swapS_encV hv]
  · cases h : S.find? (fun u => encV S u == v) with
    | none =>
      have : swapS S v = v := by simp only [swapS, hv, ite_false, h]
      rw [this, this]
    | some u =>
      have hm : u ∈ S := List.mem_of_find?_eq_some h
      have he : encV S u = v := by simpa using List.find?_some h
      have : swapS S v = u := by simp only [swapS, hv, ite_false, h]
      rw [this, swapS_of_mem hm, he]

/-- The image of the re-encoded exports of `m` is the re-encoding of `m`'s export image. -/
theorem expV_encExp20 (S : List Value) (m : ModuleInst) :
    expV (encExp20 S m) = encV S (expV m.exports) := rfl

/-- **`swapS S` takes the re-encoded exports of `m` back** when `m`'s export image is in `S`. -/
theorem swapS_expV_enc {S : List Value} {m : ModuleInst} (hm : expV m.exports ∈ S) :
    swapS S (expV (encExp20 S m)) = expV m.exports := by
  rw [expV_encExp20, swapS_encV hm]

/-! ## Images of re-encoded configurations -/

variable {τ : Value → Value} {F : ModuleInst → List ExportInst} {H : Type} {hn : H → String}

theorem moduleInstV_eq (m : ModuleInst) : moduleInstV m =
    .struct [("TYPES", .list (m.types.map funcTypeV)), ("FUNCS", addrsV m.funcs),
      ("GLOBALS", addrsV m.globals), ("TABLES", addrsV m.tables), ("MEMS", addrsV m.mems),
      ("ELEMS", addrsV m.elems), ("DATAS", addrsV m.datas), ("EXPORTS", expV m.exports)] := rfl

/-- **`swapV τ` on a re-encoded module image.** -/
theorem swapV_moduleInstV {m : ModuleInst} (h : τ (expV (F m)) = expV m.exports) :
    swapV τ (moduleInstV (expModule20 F m)) = moduleInstV m := by
  rw [moduleInstV_eq, moduleInstV_eq]
  simp only [swapV_struct, swapVf_cons, swapVf_nil, expModule20]
  simp only [show ("TYPES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("FUNCS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("GLOBALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("TABLES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MEMS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("ELEMS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("DATAS" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, ite_true, h]
  simp only [swapV_of_nxB _ (nxB_addrsV _)]
  rw [swapV_of_nxB _ (by simp)]

theorem swapV_frameV {f : Frame} (h : τ (expV (F f.module)) = expV f.module.exports) :
    swapV τ (frameV (expFrame20 F f)) = frameV f := by
  simp only [frameV, expFrame20, swapV_struct, swapVf_cons, swapVf_nil,
    show ("LOCALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MODULE" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, swapV_moduleInstV h]
  rw [swapV_of_nxB _ (by simp)]

theorem swapV_funcInstV {fi : FuncInst H} (h : τ (expV (F fi.module)) = expV fi.module.exports) :
    swapV τ (funcInstV hn (expFI20 F fi)) = funcInstV hn fi := by
  simp only [funcInstV, expFI20, swapV_struct, swapVf_cons, swapVf_nil,
    show ("TYPE" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MODULE" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("CODE" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, swapV_moduleInstV h]
  rw [swapV_of_nxB _ (nxB_funcTypeV _), swapV_of_nxB _ (by split <;> simp)]

theorem map_swapV_of_nxB {α : Type} (f : α → Value) (hf : ∀ a, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxB (f a) = true)
    (l : List α) : (l.map f).map (swapV τ) = l.map f := by
  rw [List.map_map]
  exact List.map_congr_left fun a _ => swapV_of_nxB _ (hf a)

theorem swapV_storeV {s : Store H}
    (h : ∀ fi ∈ s.funcs, τ (expV (F fi.module)) = expV fi.module.exports) :
    swapV τ (storeV hn (expStore20 F s)) = storeV hn s := by
  simp only [storeV, expStore20, swapV_struct, swapVf_cons, swapVf_nil,
    show ("FUNCS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("GLOBALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("TABLES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MEMS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("ELEMS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("DATAS" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, swapV_list]
  have hF : ((s.funcs.map (expFI20 F)).map (funcInstV hn)).map (swapV τ) =
      s.funcs.map (funcInstV hn) := by
    simp only [List.map_map]
    exact List.map_congr_left fun fi hfi => swapV_funcInstV (h fi hfi)
  rw [hF, map_swapV_of_nxB _ nxB_globalInstV, map_swapV_of_nxB _ nxB_tableInstV,
    map_swapV_of_nxB _ nxB_memInstV, map_swapV_of_nxB _ nxB_elemInstV,
    map_swapV_of_nxB _ nxB_dataInstV]

mutual
theorem swapV_adminToV : ∀ (a : Admin), AdminMods (fun m => τ (expV (F m)) = expV m.exports) a →
    swapV τ (adminToV (expAdmin20 F a)) = adminToV a
  | .plain i, _ => swapV_of_nxB _ (nxB_instrToV i)
  | .refFuncAddr _, _ | .refHostAddr _, _ | .callAddr _, _ | .trap, _ => rfl
  | .label n cont body, h => by
    simp only [expAdmin20, adminToV, swapV_case, swapV_tuple, List.map_cons, List.map_nil,
      swapV_num, swapV_list]
    have hc : (instrsToV cont).map (swapV τ) = instrsToV cont := by
      rw [← swapVs_eq_map]; exact swapVs_of_nxBs _ (nxBs_instrsToV cont)
    rw [swapVs_adminsToV body h, hc]
  | .frame n f body, h => by
    simp only [expAdmin20, adminToV, swapV_case, swapV_tuple, List.map_cons, List.map_nil,
      swapV_num, swapV_list]
    rw [swapVs_adminsToV body h.2, swapV_frameV h.1]

theorem swapVs_adminsToV : ∀ (l : List Admin),
    AdminsMods (fun m => τ (expV (F m)) = expV m.exports) l →
    (adminsToV (expAdmins20 F l)).map (swapV τ) = adminsToV l
  | [], _ => rfl
  | a :: l, h => by
    simp only [expAdmins20, adminsToV, List.map_cons]
    rw [swapV_adminToV a h.1, swapVs_adminsToV l h.2]
end

/-- **`swapV τ` takes the image of a re-encoded configuration to the image of `c`.** -/
theorem swapV_configV_exp {c : Config H} (h : ModsQ (fun m => τ (expV (F m)) = expV m.exports) c) :
    swapV τ (configV hn (expConfig20 F c)) = configV hn c := by
  simp only [configV, stateV, expConfig20, swapV_case, swapV_tuple, List.map_cons, List.map_nil,
    swapV_list]
  rw [swapV_storeV h.funcs, swapV_frameV h.frame, swapVs_adminsToV _ h.code]

/-! ## The module instances of a configuration -/

mutual
theorem adminMods_mods20 {L : List ModuleInst} : ∀ (a : Admin), (∀ m ∈ adminMods20 a, m ∈ L) →
    AdminMods (fun m => m ∈ L) a
  | .label _ _ body, h => adminsMods_mods20 body h
  | .frame _ _ body, h => ⟨h _ (List.mem_cons_self ..),
      adminsMods_mods20 body fun m hm => h m (List.mem_cons_of_mem _ hm)⟩
  | .plain _, _ | .refFuncAddr _, _ | .refHostAddr _, _ | .callAddr _, _ | .trap, _ => trivial

theorem adminsMods_mods20 {L : List ModuleInst} : ∀ (l : List Admin),
    (∀ m ∈ adminsMods20 l, m ∈ L) → AdminsMods (fun m => m ∈ L) l
  | [], _ => trivial
  | a :: l, h => ⟨adminMods_mods20 a fun m hm => h m (List.mem_append_left _ hm),
      adminsMods_mods20 l fun m hm => h m (List.mem_append_right _ hm)⟩
end

/-- **Every module instance of `c` is in `mods20 c`.** -/
theorem modsQ_mods20 (c : Config H) : ModsQ (fun m => m ∈ mods20 c) c where
  funcs _ hfi := List.mem_append_left _ (List.mem_map_of_mem hfi)
  frame := List.mem_append_right _ (List.mem_cons_self ..)
  code := adminsMods_mods20 c.code fun _ hm =>
    List.mem_append_right _ (List.mem_cons_of_mem _ hm)

section
variable {Q Q' : ModuleInst → Prop}

mutual
theorem adminMods_mono (hQ : ∀ m, Q m → Q' m) : ∀ (a : Admin), AdminMods Q a → AdminMods Q' a
  | .label _ _ body, h => adminsMods_mono hQ body h
  | .frame _ _ body, h => ⟨hQ _ h.1, adminsMods_mono hQ body h.2⟩
  | .plain _, _ | .refFuncAddr _, _ | .refHostAddr _, _ | .callAddr _, _ | .trap, _ => trivial

theorem adminsMods_mono (hQ : ∀ m, Q m → Q' m) :
    ∀ (l : List Admin), AdminsMods Q l → AdminsMods Q' l
  | [], _ => trivial
  | a :: l, h => ⟨adminMods_mono hQ a h.1, adminsMods_mono hQ l h.2⟩
end

/-- `ModsQ` is monotone in its property. -/
theorem modsQ_mono {c : Config H} (hQ : ∀ m, Q m → Q' m) (h : ModsQ Q c) : ModsQ Q' c :=
  ⟨fun fi hfi => hQ _ (h.funcs fi hfi), hQ _ h.frame, adminsMods_mono hQ _ h.code⟩
end

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
