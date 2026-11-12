module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.Thms
public import Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.Thms

/-!
# Re-encoding 1.0 export lists: values and images

* `nxB_*`: the 1.0 encoders other than `moduleInstV` build no `EXPORTS` record
  (`nxB_instrToV10`, the store's instances, the code of a function).
* `swapS10_swapS10`, `swapS10_encV10`: the exchange of one configuration is an involution that
  takes re-encodings back (the 2.0 argument, `Utf8Swap.swapS_swapS`, at the 1.0 export image).
* **`swapV_configV_exp10`**: `swapV τ` takes the image of a re-encoded host-free configuration to
  the image of the configuration, when `τ` takes each re-encoded export list back.
* `modsQ10_mods10`, `mem_mods10`: `mods10 c` lists the module instances of `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst ExportInst ExternVal)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (nxB nxBs nxBf)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap (swapV swapVs swapVf swapV_of_nxB swapVs_eq_map
  swapV_struct swapVf_cons swapVf_nil swapV_case swapV_tuple swapV_list swapV_num vlen bnd
  vlen_lt_bnd le_sum_of_mem)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10 (ModsQ10 AdminMods10 AdminsMods10 FuncMod10)

/-! ## The 1.0 encoders -/

@[simp] theorem nxB_limitsV10 (a : Nat) (b : Option Nat) : nxB (Sim10.limitsV a b) = true := by
  cases b <;> rfl
@[simp] theorem nxB_funcTypeV10 (ft : V1.FuncType) : nxB (Sim10.funcTypeV ft) = true := by
  simp [Sim10.funcTypeV]
@[simp] theorem nxB_mutV10 (m : Mutability) : nxB (Sim10.mutV m) = true := by cases m <;> rfl
@[simp] theorem nxB_blockTypeV10 (bt : V1.BlockType) : nxB (Sim10.blockTypeV bt) = true := by
  cases bt <;> simp [Sim10.blockTypeV]
@[simp] theorem nxB_numV10 (v : Execution.Runtime.Value) : nxB (Sim10.numV v) = true := by
  rcases v with ⟨_ | t, b⟩
  · rfl
  · exact Sim20.Utf8Swap.nxB_floatV t b
@[simp] theorem nxB_valV10 (v : Execution.Runtime.Value) : nxB (Sim10.valV v) = true := by
  simp [Sim10.valV]
@[simp] theorem nxB_intUnOpV10 (o : V1.IntUnOp) : nxB (Sim10.intUnOpV o) = true := by
  cases o <;> rfl
@[simp] theorem nxB_cvtOpV10 (o : V1.ConvertOp) : nxB (Sim10.cvtOpV o) = true := by
  cases o <;> simp [Sim10.cvtOpV]
@[simp] theorem nxB_memargV10 (a : V1.MemArg) : nxB (Sim10.memargV a) = true := rfl
@[simp] theorem nxB_szV10 (p : V1.PackSize) : nxB (Sim10.szV p) = true := rfl
@[simp] theorem nxB_idxV10 {k : IndexKind} (x : Idx k) : nxB (Sim10.idxV x) = true := rfl

/-- **1.0 instruction images have no `EXPORTS` record.** -/
theorem nxB_instrToV10 (i : V1.Instr) : nxB (Sim10.instrToV i) = true := by
  induction i using V1.Instr.rec (motive_2 := fun l => nxBs (Sim10.instrsToV l) = true) with
  | nil => rfl
  | cons _ _ h₁ h₂ => simp only [Sim10.instrsToV, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxBs_cons,
      h₁, h₂, Bool.and_self]
  | block _ _ h => simp [Sim10.instrToV, h]
  | loop _ _ h => simp [Sim10.instrToV, h]
  | if_ _ _ _ h₁ h₂ => simp [Sim10.instrToV, h₁, h₂]
  | intLoad _ p _ => cases p <;> simp [Sim10.instrToV]
  | intStore _ p _ => cases p <;> simp [Sim10.instrToV]
  | _ => simp [Sim10.instrToV]

@[simp] theorem nxB_instrToV10' (i : V1.Instr) : nxB (Sim10.instrToV i) = true := nxB_instrToV10 i

@[simp] theorem nxBs_instrsToV10 (l : List V1.Instr) : nxBs (Sim10.instrsToV l) = true := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [Sim10.instrsToV, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxBs_cons,
      nxB_instrToV10, ih, Bool.and_self]

@[simp] theorem nxB_funcV10 (fn : V1.Func) : nxB (Sim10.funcV fn) = true := by
  simp [Sim10.funcV]
@[simp] theorem nxB_globalInstV10 (g : Execution.Runtime.GlobalInst) :
    nxB (Sim10.globalInstV g) = true := by
  simp [Sim10.globalInstV, Sim10.globalTypeV]
@[simp] theorem nxB_tableInstV10 (t : Execution.Runtime.TableInst) :
    nxB (Sim10.tableInstV t) = true := by
  have hr : ∀ r : Option (Execution.Runtime.Addr .func),
      nxB (.opt (r.map fun a => .num (.natN a.value))) = true := fun r => by cases r <;> rfl
  simp [Sim10.tableInstV, hr]
@[simp] theorem nxB_memInstV10 (m : Execution.Runtime.MemInst) : nxB (Sim10.memInstV m) = true := by
  simp only [Sim10.memInstV, nxB, nxBf, nxB_limitsV10]
  simp [Sim10.bytesV]

/-! ## The exchange -/

@[simp] theorem vlen_expV10 (l : List ExportInst) : vlen (expV10 l) = l.length := by
  simp [expV10, vlen]

theorem vlen_encV10 (S : List Value) (u : Value) : vlen (encV10 S u) = bnd S + S.idxOf u := by
  simp [encV10]

theorem encV10_not_mem {S : List Value} (u : Value) : encV10 S u ∉ S := fun h => by
  have := vlen_lt_bnd h
  rw [vlen_encV10] at this
  omega

theorem encV10_inj {S : List Value} {u u' : Value} (hu : u ∈ S) (h : encV10 S u = encV10 S u') :
    u = u' := by
  have hl := congrArg vlen h
  rw [vlen_encV10, vlen_encV10] at hl
  exact (List.idxOf_inj hu).1 (by omega)

theorem swapS10_of_mem {S : List Value} {v : Value} (hv : v ∈ S) : swapS10 S v = encV10 S v := by
  simp [swapS10, hv]

theorem swapS10_encV10 {S : List Value} {u : Value} (hu : u ∈ S) : swapS10 S (encV10 S u) = u := by
  have hn := encV10_not_mem (S := S) u
  have hf : ∃ u', S.find? (fun x => encV10 S x == encV10 S u) = some u' := by
    cases h : S.find? (fun x => encV10 S x == encV10 S u) with
    | none => exact absurd (List.find?_eq_none.1 h u hu) (by simp)
    | some u' => exact ⟨u', rfl⟩
  obtain ⟨u', hu'⟩ := hf
  have hm : u' ∈ S := List.mem_of_find?_eq_some hu'
  have he : encV10 S u' = encV10 S u := by simpa using List.find?_some hu'
  simp only [swapS10, hn, ite_false, hu']
  exact encV10_inj hm he

/-- **`swapS10 S` is an involution.** -/
theorem swapS10_swapS10 (S : List Value) (v : Value) : swapS10 S (swapS10 S v) = v := by
  by_cases hv : v ∈ S
  · rw [swapS10_of_mem hv, swapS10_encV10 hv]
  · cases h : S.find? (fun u => encV10 S u == v) with
    | none =>
      have : swapS10 S v = v := by simp only [swapS10, hv, ite_false, h]
      rw [this, this]
    | some u =>
      have hm : u ∈ S := List.mem_of_find?_eq_some h
      have he : encV10 S u = v := by simpa using List.find?_some h
      have : swapS10 S v = u := by simp only [swapS10, hv, ite_false, h]
      rw [this, swapS10_of_mem hm, he]

/-- `swapS10 S` moves a value into the exchanged ones, or fixes it. -/
theorem swapS10_cases (S : List Value) (u : Value) :
    swapS10 S u ∈ S ++ S.map (encV10 S) ∨ swapS10 S u = u := by
  by_cases hm : u ∈ S
  · rw [swapS10_of_mem hm]
    exact Or.inl (List.mem_append_right _ (List.mem_map_of_mem hm))
  · cases h : S.find? (fun x => encV10 S x == u) with
    | none => exact Or.inr (by simp only [swapS10, hm, ite_false, h])
    | some u₀ =>
      have : swapS10 S u = u₀ := by simp only [swapS10, hm, ite_false, h]
      rw [this]
      exact Or.inl (List.mem_append_left _ (List.mem_of_find?_eq_some h))

theorem swapS10_expV_enc {S : List Value} {m : ModuleInst} (hm : expV10 m.exports ∈ S) :
    swapS10 S (expV10 (encExp10 S m)) = expV10 m.exports :=
  swapS10_encV10 hm

/-! ## Images of re-encoded configurations -/

variable {τ : Value → Value} {F : ModuleInst → List ExportInst} {H : Type} {hn : H → String}

theorem moduleInstV10_eq (m : ModuleInst) : Sim10.moduleInstV m =
    .struct [("TYPES", .list (m.types.map Sim10.funcTypeV)), ("FUNCS", Sim10.addrsV m.funcs),
      ("GLOBALS", Sim10.addrsV m.globals), ("TABLES", Sim10.addrsV m.tables),
      ("MEMS", Sim10.addrsV m.memories), ("EXPORTS", expV10 m.exports)] := rfl

@[simp] theorem nxB_addrsV10 {k : Execution.Runtime.AddrKind} (xs : List (Execution.Runtime.Addr k)) :
    nxB (Sim10.addrsV xs) = true := by
  simp [Sim10.addrsV]

theorem swapV_moduleInstV10 {m : ModuleInst} (h : τ (expV10 (F m)) = expV10 m.exports) :
    swapV τ (Sim10.moduleInstV (expModule10 F m)) = Sim10.moduleInstV m := by
  rw [moduleInstV10_eq, moduleInstV10_eq]
  simp only [swapV_struct, swapVf_cons, swapVf_nil, expModule10]
  simp only [show ("TYPES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("FUNCS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("GLOBALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("TABLES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MEMS" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, ite_true, h]
  simp only [swapV_of_nxB _ (nxB_addrsV10 _)]
  rw [swapV_of_nxB _ (by simp)]

theorem swapV_frameV10 {f : Frame} (h : τ (expV10 (F f.module)) = expV10 f.module.exports) :
    swapV τ (Sim10.frameV (expFrame10 F f)) = Sim10.frameV f := by
  simp only [Sim10.frameV, expFrame10, swapV_struct, swapVf_cons, swapVf_nil,
    show ("LOCALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MODULE" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, swapV_moduleInstV10 h]
  rw [swapV_of_nxB _ (by simp)]

theorem swapV_funcInstV10 {fi : FuncInst V1.Func H}
    (h : FuncMod10 (fun m => τ (expV10 (F m)) = expV10 m.exports) fi)
    (hh : ∀ t h', fi ≠ .host t h') :
    swapV τ (Sim10.funcInstV hn (expFI10 F fi)) = Sim10.funcInstV hn fi := by
  cases fi with
  | wasm t m fn =>
    simp only [expFI10, Sim10.funcInstV, swapV_struct, swapVf_cons, swapVf_nil,
      show ("TYPE" : IL.AtomS) ≠ "EXPORTS" by decide,
      show ("MODULE" : IL.AtomS) ≠ "EXPORTS" by decide,
      show ("CODE" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false,
      swapV_moduleInstV10 (h t m fn rfl)]
    rw [swapV_of_nxB _ (nxB_funcTypeV10 _), swapV_of_nxB _ (nxB_funcV10 _)]
  | host t h' => exact absurd rfl (hh t h')

theorem map_swapV_of_nxB10 {α : Type} (f : α → Value)
    (hf : ∀ a, Silmaril.Wasm.SpecTec.Sim.Round7.Swap.nxB (f a) = true) (l : List α) :
    (l.map f).map (swapV τ) = l.map f := by
  rw [List.map_map]
  exact List.map_congr_left fun a _ => swapV_of_nxB _ (hf a)

theorem noHost10_mem {s : Store H} (hh : Whole.NoHost10 s) :
    ∀ fi ∈ s.funcs, ∀ t h', fi ≠ .host t h' := by
  intro fi hfi t h' he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hfi
  exact hh i t h' (by rw [List.getElem?_eq_getElem hi, he])

theorem swapV_storeV10 {s : Store H}
    (h : ∀ fi ∈ s.funcs, FuncMod10 (fun m => τ (expV10 (F m)) = expV10 m.exports) fi)
    (hh : Whole.NoHost10 s) :
    swapV τ (Sim10.storeV hn (expStore10 F s)) = Sim10.storeV hn s := by
  simp only [Sim10.storeV, expStore10, swapV_struct, swapVf_cons, swapVf_nil,
    show ("FUNCS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("GLOBALS" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("TABLES" : IL.AtomS) ≠ "EXPORTS" by decide,
    show ("MEMS" : IL.AtomS) ≠ "EXPORTS" by decide, ite_false, swapV_list]
  have hF : ((s.funcs.map (expFI10 F)).map (Sim10.funcInstV hn)).map (swapV τ) =
      s.funcs.map (Sim10.funcInstV hn) := by
    simp only [List.map_map]
    exact List.map_congr_left fun fi hfi => swapV_funcInstV10 (h fi hfi) (noHost10_mem hh fi hfi)
  rw [hF, map_swapV_of_nxB10 _ nxB_globalInstV10, map_swapV_of_nxB10 _ nxB_tableInstV10,
    map_swapV_of_nxB10 _ nxB_memInstV10]

mutual
theorem swapV_adminToV10 : ∀ (a : Admin),
    AdminMods10 (fun m => τ (expV10 (F m)) = expV10 m.exports) a →
    swapV τ (Sim10.adminToV (expAdmin10 F a)) = Sim10.adminToV a
  | .source i, _ => swapV_of_nxB _ (nxB_instrToV10 i)
  | .invoke _, _ | .trap, _ => rfl
  | .label n cont body, h => by
    simp only [expAdmin10, Sim10.adminToV, swapV_case, swapV_tuple, List.map_cons, List.map_nil,
      swapV_num, swapV_list]
    have hc : (Sim10.instrsToV cont).map (swapV τ) = Sim10.instrsToV cont := by
      rw [← swapVs_eq_map]; exact Sim20.Utf8Swap.swapVs_of_nxBs _ (nxBs_instrsToV10 cont)
    rw [swapVs_adminsToV10 body h, hc]
  | .frame n f body, h => by
    simp only [expAdmin10, Sim10.adminToV, swapV_case, swapV_tuple, List.map_cons, List.map_nil,
      swapV_num, swapV_list]
    rw [swapVs_adminsToV10 body h.2, swapV_frameV10 h.1]

theorem swapVs_adminsToV10 : ∀ (l : List Admin),
    AdminsMods10 (fun m => τ (expV10 (F m)) = expV10 m.exports) l →
    (Sim10.adminsToV (expAdmins10 F l)).map (swapV τ) = Sim10.adminsToV l
  | [], _ => rfl
  | a :: l, h => by
    simp only [expAdmins10, Sim10.adminsToV, List.map_cons]
    rw [swapV_adminToV10 a h.1, swapVs_adminsToV10 l h.2]
end

/-- **`swapV τ` takes the image of a re-encoded host-free configuration to the image of `c`.** -/
theorem swapV_configV_exp10 {c : Config H}
    (h : ModsQ10 (fun m => τ (expV10 (F m)) = expV10 m.exports) c) (hh : Whole.NoHost10 c.store) :
    swapV τ (Sim10.configV hn (expConfig10 F c)) = Sim10.configV hn c := by
  simp only [Sim10.configV, Sim10.stateV, expConfig10, swapV_case, swapV_tuple, List.map_cons,
    List.map_nil, swapV_list]
  rw [swapV_storeV10 h.funcs hh, swapV_frameV10 h.frame, swapVs_adminsToV10 _ h.code]

/-! ## The module instances of a configuration -/

section
variable {Q Q' : ModuleInst → Prop}

mutual
theorem adminMods10_of : ∀ {L : List ModuleInst} (a : Admin), (∀ m ∈ adminMods10 a, m ∈ L) →
    AdminMods10 (fun m => m ∈ L) a
  | _, .label _ _ body, h => adminsMods10_of body h
  | _, .frame _ _ body, h => ⟨h _ (List.mem_cons_self ..),
      adminsMods10_of body fun m hm => h m (List.mem_cons_of_mem _ hm)⟩
  | _, .source _, _ | _, .invoke _, _ | _, .trap, _ => trivial

theorem adminsMods10_of : ∀ {L : List ModuleInst} (l : List Admin),
    (∀ m ∈ adminsMods10 l, m ∈ L) → AdminsMods10 (fun m => m ∈ L) l
  | _, [], _ => trivial
  | _, a :: l, h => ⟨adminMods10_of a fun m hm => h m (List.mem_append_left _ hm),
      adminsMods10_of l fun m hm => h m (List.mem_append_right _ hm)⟩
end

/-- **Every module instance of `c` is in `mods10 c`.** -/
theorem modsQ10_mods10 (c : Config H) : ModsQ10 (fun m => m ∈ mods10 c) c where
  funcs fi hfi := fun t m fn he => List.mem_append_left _ (List.mem_flatMap.2 ⟨fi, hfi, by
    subst he; exact List.mem_singleton_self _⟩)
  frame := List.mem_append_right _ (List.mem_cons_self ..)
  code := adminsMods10_of c.code fun _ hm => List.mem_append_right _ (List.mem_cons_of_mem _ hm)

mutual
theorem adminMods10_mono (hQ : ∀ m, Q m → Q' m) : ∀ (a : Admin), AdminMods10 Q a → AdminMods10 Q' a
  | .label _ _ body, h => adminsMods10_mono hQ body h
  | .frame _ _ body, h => ⟨hQ _ h.1, adminsMods10_mono hQ body h.2⟩
  | .source _, _ | .invoke _, _ | .trap, _ => trivial

theorem adminsMods10_mono (hQ : ∀ m, Q m → Q' m) :
    ∀ (l : List Admin), AdminsMods10 Q l → AdminsMods10 Q' l
  | [], _ => trivial
  | a :: l, h => ⟨adminMods10_mono hQ a h.1, adminsMods10_mono hQ l h.2⟩
end

theorem modsQ10_mono {c : Config H} (hQ : ∀ m, Q m → Q' m) (h : ModsQ10 Q c) : ModsQ10 Q' c :=
  ⟨fun fi hfi t m fn he => hQ _ (h.funcs fi hfi t m fn he), hQ _ h.frame,
    adminsMods10_mono hQ _ h.code⟩

mutual
theorem mem_adminMods10 : ∀ (a : Admin), AdminMods10 Q a → ∀ m ∈ adminMods10 a, Q m
  | .label _ _ body, h, m, hm => mem_adminsMods10 body h m hm
  | .frame _ _ body, h, m, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact mem_adminsMods10 body h.2 m hm
  | .source _, _, _, hm | .invoke _, _, _, hm | .trap, _, _, hm => nomatch hm

theorem mem_adminsMods10 : ∀ (l : List Admin), AdminsMods10 Q l → ∀ m ∈ adminsMods10 l, Q m
  | [], _, _, hm => nomatch hm
  | a :: l, h, m, hm => by
    rcases List.mem_append.1 hm with hm | hm
    · exact mem_adminMods10 a h.1 m hm
    · exact mem_adminsMods10 l h.2 m hm
end

/-- **Every module instance in `mods10 c` has a property all module instances of `c` have.** -/
theorem mem_mods10 {c : Config H} (h : ModsQ10 Q c) : ∀ m ∈ mods10 c, Q m := by
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨fi, hfi, hm⟩ := List.mem_flatMap.1 hm
    cases fi with
    | wasm t m' fn =>
      obtain rfl := List.mem_singleton.1 hm
      exact h.funcs _ hfi t m fn rfl
    | host _ _ => cases hm
  · rcases List.mem_cons.1 hm with rfl | hm
    · exact h.frame
    · exact mem_adminsMods10 _ h.code m hm
end

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
