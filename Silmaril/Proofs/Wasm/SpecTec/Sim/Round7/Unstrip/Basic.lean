module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Unstrip.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Strip.Thms

/-!
# Round 7: export-only rewritings of configurations

Facts about `mapConfig μ` for an export-only `μ` (`ExportOnly μ`), used by the Core equivariance
of `Step` (`Raw/…/Round7/Unstrip/Step.lean`) and by the assembly of `Task.wholeStepValidREI`:

* `μ` keeps every field but the export list (`exportOnly_types`, `exportOnly_funcs`, …), so it
  commutes with `blockType?`, `instRef`, `Frame.forCall` and `Admin.retToCallIn`;
* `mapAdmins` commutes with `++`, fixes atomic code, and `mapConfig stripModule` is
  `stripConfig` (`mapConfig_stripModule`);
* `mapConfig μ (mapConfig ν c) = mapConfig (μ ∘ ν) c`, and `mapConfig μ c = c` when `μ` fixes
  `mods c`;
* `Bwd.ConfigEq` is preserved by `mapConfig μ`, and export-freeness (`Stripped`) by `ConfigEq`;
* `unstrip c` is export-only and, under `StripInj c`, inverts `stripModule` on `mods c`
  (`unstrip_strip`), so `mapConfig (unstrip c) (stripConfig c) = c` (`mapConfig_unstrip_strip`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Export-only rewritings keep every other field -/

section ExportOnly

variable {μ : ModuleInst → ModuleInst}

theorem exportOnly_eq (hμ : ExportOnly μ) (m : ModuleInst) :
    μ m = { m with exports := (μ m).exports } := by
  have h := hμ m
  revert h
  generalize μ m = m'
  intro h
  cases m; cases m'
  simp only [stripModule, ModuleInst.mk.injEq] at h ⊢
  simp only [h, and_self]

theorem exportOnly_types (hμ : ExportOnly μ) (m : ModuleInst) : (μ m).types = m.types := by
  rw [exportOnly_eq hμ m]

theorem exportOnly_funcs (hμ : ExportOnly μ) (m : ModuleInst) : (μ m).funcs = m.funcs := by
  rw [exportOnly_eq hμ m]

theorem exportOnly_tags (hμ : ExportOnly μ) (m : ModuleInst) : (μ m).tags = m.tags := by
  rw [exportOnly_eq hμ m]

theorem exportOnly_stripModule : ExportOnly stripModule := fun _ => rfl

theorem ExportOnly.comp {ν : ModuleInst → ModuleInst} (hμ : ExportOnly μ) (hν : ExportOnly ν) :
    ExportOnly (μ ∘ ν) := fun m => (hμ (ν m)).trans (hν m)

theorem blockType?_exportOnly (hμ : ExportOnly μ) (m : ModuleInst) :
    (μ m).blockType? = m.blockType? := by
  funext bt
  cases bt <;> simp [ModuleInst.blockType?, ModuleInst.instVal, exportOnly_types hμ]

theorem instRef_exportOnly (hμ : ExportOnly μ) (m : ModuleInst) :
    (μ m).instRef = m.instRef := by
  funext rt
  simp [ModuleInst.instRef, exportOnly_types hμ]

theorem forCall_exportOnly (hμ : ExportOnly μ) (m : ModuleInst) (vs : List Val)
    (ls : List ValType) : Frame.forCall (μ m) vs ls = mapFrame μ (Frame.forCall m vs ls) := by
  simp [Frame.forCall, mapFrame, exportOnly_types hμ]

theorem retToCallIn_exportOnly (hμ : ExportOnly μ) (m : ModuleInst) (a : Admin) :
    a.retToCallIn (μ m) = a.retToCallIn m := by
  cases a with
  | plain i => cases i <;> simp [Admin.retToCallIn, exportOnly_types hμ]
  | _ => rfl

theorem stripFI_mapFI (hμ : ExportOnly μ) (fi : FuncInst H) : stripFI (mapFI μ fi) = stripFI fi := by
  simp [stripFI, mapFI, hμ fi.module]

theorem mapStore_funcs_strip (hμ : ExportOnly μ) (s : Store H) :
    (mapStore μ s).funcs.map stripFI = s.funcs.map stripFI := by
  simp [mapStore, Function.comp_def, stripFI_mapFI hμ]

end ExportOnly

/-! ## `mapAdmins` -/

section Map

variable (μ : ModuleInst → ModuleInst)

@[simp] theorem mapAdmins_nil : mapAdmins μ [] = [] := rfl

@[simp] theorem mapAdmins_cons (a : Admin) (l : List Admin) :
    mapAdmins μ (a :: l) = mapAdmin μ a :: mapAdmins μ l := rfl

theorem mapAdmins_eq_map : ∀ l : List Admin, mapAdmins μ l = l.map (mapAdmin μ)
  | [] => rfl
  | a :: l => by simp [mapAdmins_eq_map l]

@[simp] theorem mapAdmins_append (l r : List Admin) :
    mapAdmins μ (l ++ r) = mapAdmins μ l ++ mapAdmins μ r := by
  simp [mapAdmins_eq_map]

theorem mapAdmin_atomic {a : Admin} (h : Atomic a) : mapAdmin μ a = a := by
  cases a <;> simp_all [Atomic, mapAdmin]

theorem mapAdmins_atomic {l : List Admin} (h : AllAtomic l) : mapAdmins μ l = l := by
  rw [mapAdmins_eq_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun a ha => mapAdmin_atomic μ (h a ha)

@[simp] theorem mapAdmins_vals (vs : List Val) : mapAdmins μ (vals vs) = vals vs :=
  mapAdmins_atomic μ (allAtomic_vals vs)

@[simp] theorem mapAdmin_plain (i : Instr) : mapAdmin μ (.plain i) = .plain i := rfl
@[simp] theorem mapAdmin_ref (r : Ref) : mapAdmin μ (.ref r) = .ref r := rfl
@[simp] theorem mapAdmin_trap : mapAdmin μ .trap = .trap := rfl
@[simp] theorem mapAdmin_callRefType (d : DefType) :
    mapAdmin μ (.callRefType d) = .callRefType d := rfl
@[simp] theorem mapAdmin_returnCallRefType (d : DefType) :
    mapAdmin μ (.returnCallRefType d) = .returnCallRefType d := rfl
@[simp] theorem mapAdmin_label (n : Nat) (cont : List Instr) (body : List Admin) :
    mapAdmin μ (.label n cont body) = .label n cont (mapAdmins μ body) := rfl
@[simp] theorem mapAdmin_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    mapAdmin μ (.handler n cs body) = .handler n cs (mapAdmins μ body) := rfl
@[simp] theorem mapAdmin_frame (n : Nat) (f : Frame) (body : List Admin) :
    mapAdmin μ (.frame n f body) = .frame n (mapFrame μ f) (mapAdmins μ body) := rfl
@[simp] theorem mapAdmin_toAdmin (v : Val) : mapAdmin μ v.toAdmin = v.toAdmin :=
  mapAdmin_atomic μ (atomic_toAdmin v)

@[simp] theorem mapAdmins_expression (es : List Instr) :
    mapAdmins μ (expression es) = expression es :=
  mapAdmins_atomic μ ((allAtomic_expression es).mpr trivial)

@[simp] theorem mapAdmins_resultToAdmin (r : Result) : mapAdmins μ r.toAdmin = r.toAdmin :=
  mapAdmins_atomic μ ((allAtomic_toAdmin r).mpr trivial)

theorem mapAdmins_length (l : List Admin) : (mapAdmins μ l).length = l.length := by
  simp [mapAdmins_eq_map]

theorem mapAdmins_ne_nil {l : List Admin} (h : l ≠ []) : mapAdmins μ l ≠ [] := by
  intro h'
  exact h (List.length_eq_zero_iff.mp ((mapAdmins_length μ l).symm.trans
    (List.length_eq_zero_iff.mpr h')))

theorem map_mapFI_strip {μ : ModuleInst → ModuleInst} (hμ : ExportOnly μ) (F : List (FuncInst H)) :
    (F.map (mapFI μ)).map stripFI = F.map stripFI := by
  simp [Function.comp_def, stripFI_mapFI hμ]

theorem mapStore_addExn (s : Store H) (e : ExnInst) :
    mapStore μ (s.addExn e) = (mapStore μ s).addExn e := rfl

@[simp] theorem mapStore_exns (s : Store H) : (mapStore μ s).exns = s.exns := rfl

@[simp] theorem mapStore_tags (s : Store H) : (mapStore μ s).tags = s.tags := rfl

theorem mapStore_funcs_get (s : Store H) (a : Nat) :
    (mapStore μ s).funcs[a]? = (s.funcs[a]?).map (mapFI μ) := by
  simp [mapStore]

mutual
theorem mapAdmin_strip : ∀ a : Admin, mapAdmin stripModule a = stripAdmin a
  | .label n cont body => by simp only [mapAdmin, stripAdmin, mapAdmins_strip body]
  | .handler n cs body => by simp only [mapAdmin, stripAdmin, mapAdmins_strip body]
  | .frame n f body => by simp only [mapAdmin, stripAdmin, mapAdmins_strip body]; rfl
  | .plain _ => rfl
  | .ref _ => rfl
  | .callRefType _ => rfl
  | .returnCallRefType _ => rfl
  | .trap => rfl

theorem mapAdmins_strip : ∀ l : List Admin, mapAdmins stripModule l = stripAdmins l
  | [] => rfl
  | a :: l => by simp only [mapAdmins, stripAdmins, mapAdmin_strip a, mapAdmins_strip l]
end

/-- **`stripConfig` is `mapConfig stripModule`.** -/
theorem mapConfig_stripModule (c : Config H) : mapConfig stripModule c = stripConfig c := by
  simp only [mapConfig, stripConfig, mapAdmins_strip]
  rfl

/-! ## Composition and identity -/

mutual
theorem mapAdmin_comp (ν : ModuleInst → ModuleInst) :
    ∀ a : Admin, mapAdmin μ (mapAdmin ν a) = mapAdmin (μ ∘ ν) a
  | .label n cont body => by simp only [mapAdmin, mapAdmins_comp ν body]
  | .handler n cs body => by simp only [mapAdmin, mapAdmins_comp ν body]
  | .frame n f body => by simp only [mapAdmin, mapAdmins_comp ν body]; rfl
  | .plain _ => rfl
  | .ref _ => rfl
  | .callRefType _ => rfl
  | .returnCallRefType _ => rfl
  | .trap => rfl

theorem mapAdmins_comp (ν : ModuleInst → ModuleInst) :
    ∀ l : List Admin, mapAdmins μ (mapAdmins ν l) = mapAdmins (μ ∘ ν) l
  | [] => rfl
  | a :: l => by simp only [mapAdmins, mapAdmin_comp ν a, mapAdmins_comp ν l]
end

theorem mapConfig_comp (ν : ModuleInst → ModuleInst) (c : Config H) :
    mapConfig μ (mapConfig ν c) = mapConfig (μ ∘ ν) c := by
  simp only [mapConfig, mapAdmins_comp, mapStore, mapFrame, List.map_map]
  rfl

mutual
theorem mapAdmin_id_of : ∀ a : Admin, (∀ m ∈ modsAdmin a, μ m = m) → mapAdmin μ a = a
  | .label n cont body, h => by
      simp only [mapAdmin, mapAdmins_id_of body (by simpa [modsAdmin] using h)]
  | .handler n cs body, h => by
      simp only [mapAdmin, mapAdmins_id_of body (by simpa [modsAdmin] using h)]
  | .frame n f body, h => by
      simp only [modsAdmin, List.mem_cons, forall_eq_or_imp] at h
      simp only [mapAdmin, mapFrame, h.1, mapAdmins_id_of body h.2]
  | .plain _, _ => rfl
  | .ref _, _ => rfl
  | .callRefType _, _ => rfl
  | .returnCallRefType _, _ => rfl
  | .trap, _ => rfl

theorem mapAdmins_id_of : ∀ l : List Admin, (∀ m ∈ modsAdmins l, μ m = m) → mapAdmins μ l = l
  | [], _ => rfl
  | a :: l, h => by
      simp only [modsAdmins, List.mem_append] at h
      simp only [mapAdmins, mapAdmin_id_of a (fun m hm => h m (.inl hm)),
        mapAdmins_id_of l (fun m hm => h m (.inr hm))]
end

/-- `mapConfig μ` is the identity on a configuration whose modules `μ` fixes. -/
theorem mapConfig_id_of {c : Config H} (h : ∀ m ∈ mods c, μ m = m) : mapConfig μ c = c := by
  obtain ⟨s, f, is⟩ := c
  simp only [mods, List.mem_append, List.mem_map, List.mem_cons] at h
  have hF : s.funcs.map (mapFI μ) = s.funcs := by
    refine (List.map_congr_left fun fi hfi => ?_).trans (List.map_id s.funcs)
    simp only [mapFI, id_eq, h _ (.inl ⟨fi, hfi, rfl⟩)]
  have hs : mapStore μ s = s := by
    simp only [mapStore, hF]
  have hf : mapFrame μ f = f := by simp only [mapFrame, h _ (.inr (.inl rfl))]
  simp only [mapConfig, hs, hf, mapAdmins_id_of μ is (fun m hm => h m (.inr (.inr hm)))]

end Map

/-! ## `Bwd.ConfigEq` and export-freeness -/

section ConfigEq

theorem mapAdmin_callRef (μ : ModuleInst → ModuleInst) {a : Admin} (h : a.IsCallRef) :
    mapAdmin μ a = a := mapAdmin_atomic μ (atomic_of_isCallRef h)

mutual
theorem adminEq_map (μ : ModuleInst → ModuleInst) :
    ∀ {a b : Admin}, Bwd.AdminEq a b → Bwd.AdminEq (mapAdmin μ a) (mapAdmin μ b)
  | _, _, .refl _ => .refl _
  | _, _, .call ha hb => by
      rw [mapAdmin_callRef μ ha, mapAdmin_callRef μ hb]
      exact .call ha hb
  | _, _, .label h => .label (codeEq_map μ h)
  | _, _, .handler h => .handler (codeEq_map μ h)
  | _, _, .frame h => .frame (codeEq_map μ h)

theorem codeEq_map (μ : ModuleInst → ModuleInst) :
    ∀ {l r : List Admin}, Bwd.CodeEq l r → Bwd.CodeEq (mapAdmins μ l) (mapAdmins μ r)
  | _, _, .nil => .nil
  | _, _, .cons ha hl => .cons (adminEq_map μ ha) (codeEq_map μ hl)
end

/-- **`Bwd.ConfigEq` is preserved by `mapConfig μ`.** -/
theorem configEq_map (μ : ModuleInst → ModuleInst) {c d : Config H} (h : Bwd.ConfigEq c d) :
    Bwd.ConfigEq (mapConfig μ c) (mapConfig μ d) := by
  obtain ⟨hs, hf, hc⟩ := h
  exact ⟨by simp only [mapConfig, hs], by simp only [mapConfig, hf], codeEq_map μ hc⟩

mutual
theorem adminEq_stripped :
    ∀ {a b : Admin}, Bwd.AdminEq a b → stripAdmin a = a → stripAdmin b = b
  | _, _, .refl _, h => h
  | _, _, .call _ hb, _ => stripAdmin_atomic (atomic_of_isCallRef hb)
  | _, _, .label h, ha => by
      simp only [stripAdmin, Admin.label.injEq, true_and] at ha ⊢
      exact codeEq_stripped h ha
  | _, _, .handler h, ha => by
      simp only [stripAdmin, Admin.handler.injEq, true_and] at ha ⊢
      exact codeEq_stripped h ha
  | _, _, .frame h, ha => by
      simp only [stripAdmin, Admin.frame.injEq, true_and] at ha ⊢
      exact ⟨ha.1, codeEq_stripped h ha.2⟩

theorem codeEq_stripped :
    ∀ {l r : List Admin}, Bwd.CodeEq l r → stripAdmins l = l → stripAdmins r = r
  | _, _, .nil, _ => rfl
  | _, _, .cons ha hl, h => by
      simp only [stripAdmins, List.cons.injEq] at h ⊢
      exact ⟨adminEq_stripped ha h.1, codeEq_stripped hl h.2⟩
end

/-- **Export-freeness is preserved by `Bwd.ConfigEq`.** -/
theorem stripped_of_configEq {c d : Config H} (h : Bwd.ConfigEq c d) (hc : Stripped c) :
    Stripped d := by
  obtain ⟨s, f, is⟩ := c
  obtain ⟨s', f', js⟩ := d
  obtain ⟨rfl, rfl, hcode⟩ := h
  obtain ⟨hs, hf, his⟩ := stripped_iff.mp hc
  exact stripped_mk hs hf (codeEq_stripped hcode his)

end ConfigEq

/-! ## Un-stripping -/

section Unstrip

theorem stripModule_unstrip (c : Config H) (m₀ : ModuleInst) :
    stripModule (unstrip c m₀) = stripModule m₀ := by
  unfold unstrip
  split
  · next h =>
    have h₁ : stripModule h.choose = m₀ := h.choose_spec.2
    calc stripModule h.choose = stripModule (stripModule h.choose) := rfl
      _ = stripModule m₀ := by rw [h₁]
  · rfl

/-- **Un-stripping is export-only.** -/
theorem exportOnly_unstrip (c : Config H) : ExportOnly (unstrip c) := stripModule_unstrip c

/-- **Under `StripInj c`, `unstrip c` inverts `stripModule` on the modules of `c`.** -/
theorem unstrip_strip {c : Config H} (hinj : StripInj c) {m : ModuleInst} (hm : m ∈ mods c) :
    unstrip c (stripModule m) = m := by
  have hex : ∃ m' ∈ mods c, stripModule m' = stripModule m := ⟨m, hm, rfl⟩
  unfold unstrip
  split
  · next h => exact hinj _ h.choose_spec.1 _ hm h.choose_spec.2
  · next h => exact absurd hex h

/-- **Un-stripping undoes stripping**, under `StripInj c`. -/
theorem mapConfig_unstrip_strip {c : Config H} (hinj : StripInj c) :
    mapConfig (unstrip c) (stripConfig c) = c := by
  rw [← mapConfig_stripModule, mapConfig_comp]
  exact mapConfig_id_of _ fun _ hm => unstrip_strip hinj hm

/-- The round trip `unstrip c ∘ stripModule` fixes `c`, under `StripInj c`. -/
theorem mapConfig_unstrip_comp {c : Config H} (hinj : StripInj c) :
    mapConfig (unstrip c ∘ stripModule) c = c :=
  mapConfig_id_of _ fun _ hm => unstrip_strip hinj hm

/-- With no exports anywhere, `StripInj` holds. -/
theorem stripInj_of_stripped {c : Config H} (hc : ∀ m ∈ mods c, stripModule m = m) :
    StripInj c := fun m₁ h₁ m₂ h₂ h => by rw [← hc m₁ h₁, ← hc m₂ h₂, h]

/-- **A configuration whose module instances are all one module satisfies `StripInj`**, whatever
that module exports. -/
theorem stripInj_of_single {c : Config H} {m₀ : ModuleInst} (h : ∀ m ∈ mods c, m = m₀) :
    StripInj c := fun m₁ h₁ m₂ h₂ _ => (h m₁ h₁).trans (h m₂ h₂).symm

end Unstrip

end Silmaril.Wasm.SpecTec.Sim.Round7
