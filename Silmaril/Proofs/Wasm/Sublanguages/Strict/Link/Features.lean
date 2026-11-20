module

public import Silmaril.Wasm.Sublanguages.Strict.Link.Defs

public section

namespace Silmaril.Proofs.Wasm.Sublanguages.StrictLink

open Silmaril.Wasm Silmaril.Wasm.Models Silmaril.Wasm.Sublanguages Silmaril.Wasm.Link

private theorem mapM_invariants {α β : Type} {check : α → Option β} {src : List α} {dst : List β}
    {before : α → Bool} {after : β → Bool}
    (preserve : ∀ entry ∈ src, ∀ next, check entry = some next → after next = before entry)
    (h : src.mapM check = some dst) : dst.length = src.length ∧ dst.all after = src.all before := by
  induction src generalizing dst with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons entry rest ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨next, hNext, tail, hTail, rfl⟩ := h
    obtain ⟨hLength, hAll⟩ := ih (fun elem mem => preserve elem (List.mem_cons_of_mem _ mem)) hTail
    simp [hLength, hAll, preserve entry (by simp) next hNext]

private theorem heap_features {offset src dst} (h : GC.heap? offset src = some dst) (caps : FeatureSet) :
    HeapType.inFeatB caps dst = HeapType.inFeatB caps src := by
  cases src with
  | abstract _ => cases h; rfl
  | typeIdx idx =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl

private theorem ref_features {offset src dst} (h : GC.refType? offset src = some dst) (caps : FeatureSet) :
    RefType.inFeatB caps dst = RefType.inFeatB caps src := by
  simp only [GC.refType?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨_, h, rfl⟩ := h
  simp only [RefType.inFeatB, heap_features h]

private theorem val_features {offset src dst} (h : GC.valType? offset src = some dst) (caps : FeatureSet) :
    ValType.inFeatB caps dst = ValType.inFeatB caps src := by
  cases src with
  | num _ | vec _ => cases h; rfl
  | ref _ =>
    rw [GC.valType?] at h
    obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ref_features mapped caps

private theorem block_features {offset src dst} (h : GC.blockType? offset src = some dst) (caps : FeatureSet) :
    BlockType.inFeatB caps dst = BlockType.inFeatB caps src := by
  cases src with
  | empty => cases h; rfl
  | value _ =>
    rw [GC.blockType?] at h
    obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
    exact val_features mapped caps
  | typeIdx _ =>
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl

private theorem field_features {offset src dst} (h : GC.fieldType? offset src = some dst) (caps : FeatureSet) :
    FieldType.inFeatB caps dst = FieldType.inFeatB caps src := by
  simp only [GC.fieldType?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨_, h, rfl⟩ := h
  cases hs : src.storage with
  | packed _ => rw [hs, GC.storageType?] at h; cases h; simp [FieldType.inFeatB, hs]
  | val _ =>
    rw [hs, GC.storageType?] at h
    obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [FieldType.inFeatB, StorageType.inFeatB, hs, val_features mapped]

private theorem sub_features {offset src dst} (h : GC.subType? offset src = some dst) (caps : FeatureSet) :
    SubType.inFeatB caps dst = SubType.inFeatB caps src := by
  simp only [GC.subType?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨supers, hSupers, _, h, rfl⟩ := h
  have len := (mapM_invariants (before := fun _ => true) (after := fun _ => true)
    (fun _ _ _ _ => rfl) hSupers).1
  have empty : supers.isEmpty = src.supertypes.isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.isEmpty_iff_length_eq_zero, len]
  simp only [SubType.inFeatB, empty]
  congr 1
  cases hs : src.body with
  | func signature =>
    rw [hs, GC.compositeType?] at h
    simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, hParams, _, hResults, rfl⟩ := h
    obtain ⟨_, hp⟩ := mapM_invariants (fun _ _ _ eq => val_features eq caps) hParams
    obtain ⟨hl, hr⟩ := mapM_invariants (fun _ _ _ eq => val_features eq caps) hResults
    simp [FuncType.inFeatB, hp, hl, hr]
  | struct _ =>
    rw [hs, GC.compositeType?] at h
    obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [(mapM_invariants (fun _ _ _ eq => field_features eq caps) mapped).2]
  | array _ =>
    rw [hs, GC.compositeType?] at h
    obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [field_features mapped]

private theorem rec_features {offset src dst} (h : GC.recType? offset src = some dst) (caps : FeatureSet) :
    RecType.inFeatB caps dst = RecType.inFeatB caps src := by
  rw [GC.recType?] at h
  obtain ⟨_, mapped, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hl, ha⟩ := mapM_invariants (fun _ _ _ eq => sub_features eq caps) mapped
  simp [RecType.inFeatB, hl, ha]

private theorem ins_all (caps : FeatureSet) (body : List Instr) :
    Instr.insInFeatB caps body = body.all (Instr.inFeatB caps) := by
  induction body with
  | nil => rfl
  | cons _ _ ih => rw [Instr.insInFeatB, List.all_cons, ih]

private theorem instruction_features (caps : FeatureSet) (relocation : GC.Relocation)
    (src dst : Instr) (h : GC.instruction? relocation src = some dst) :
    Instr.inFeatB caps dst = Instr.inFeatB caps src := by
  have nested (body : List Instr) (smaller : ∀ i ∈ body, sizeOf i < sizeOf src) (result : List Instr)
      (eq : body.attach.mapM (fun i => GC.instruction? relocation i.val) = some result) :
      Instr.insInFeatB caps result = Instr.insInFeatB caps body := by
    rw [ins_all, ins_all]
    have eqAll := (mapM_invariants (fun entry _ next eq' =>
      have := smaller entry.val entry.property
      instruction_features caps relocation entry.val next eq') eq).2
    rwa [List.all_subtype (fun _ _ => rfl), List.unattach_attach] at eqAll
  cases src <;>
    try simp only [GC.instruction?, Option.map_eq_map, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq, reduceCtorEq] at h
  case block t body | loop t body =>
    obtain ⟨_, ht, result, hb, rfl⟩ := h
    have eq := nested body (fun i mem => by have := List.sizeOf_lt_of_mem mem; simp_wf; omega) result hb
    simp only [Instr.inFeatB, Instr.headB, block_features ht, eq]
  case if_ t yes no =>
    obtain ⟨_, ht, yes', hy, no', hn, rfl⟩ := h
    have eqYes := nested yes (fun i mem => by have := List.sizeOf_lt_of_mem mem; simp_wf; omega) yes' hy
    have eqNo := nested no (fun i mem => by have := List.sizeOf_lt_of_mem mem; simp_wf; omega) no' hn
    simp only [Instr.inFeatB, Instr.headB, block_features ht, eqYes, eqNo]
  case select types =>
    cases types with
    | none => rw [GC.instruction?] at h; cases h; rfl
    | some _ =>
      simp only [GC.instruction?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨_, ht, rfl⟩ := h
      have eq := (mapM_invariants (fun _ _ _ eq => val_features eq caps) ht).2
      simp only [Instr.inFeatB, Instr.headB, eq]
  case refNull =>
    obtain ⟨_, ht, rfl⟩ := h
    simp only [Instr.inFeatB, Instr.headB, heap_features ht]
  case refTest | refCast =>
    obtain ⟨_, ht, rfl⟩ := h
    simp only [Instr.inFeatB, Instr.headB, ref_features ht]
  case brOnCast | brOnCastFail =>
    obtain ⟨_, ht, _, ht', rfl⟩ := h
    simp only [Instr.inFeatB, Instr.headB, ref_features ht, ref_features ht']
  all_goals first
    | subst dst; rfl
    | obtain ⟨_, _, rfl⟩ := h; rfl
    | obtain ⟨_, _, _, _, rfl⟩ := h; rfl
termination_by sizeOf src

private theorem func_features {relocation src dst} (h : GC.func? relocation src = some dst)
    (caps : FeatureSet) : Func.inFeatB caps dst = Func.inFeatB caps src := by
  simp only [GC.func?, GC.instructions?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨_, _, _, locals, _, body, rfl⟩ := h
  simp only [Func.inFeatB, ins_all, (mapM_invariants (fun _ _ _ eq => val_features eq caps) locals).2,
    (mapM_invariants (fun entry _ next => instruction_features caps relocation entry next) body).2]

private theorem section_features (sections : LocalSections) (imports : List FunctionImport) (caps : FeatureSet) :
    Module.InFeat caps (sections.assemble imports) ↔
      sections.types.all (RecType.inFeatB caps) = true ∧ sections.funcs.all (Func.inFeatB caps) = true := by
  simp [Module.InFeat, Module.inFeatB, LocalSections.assemble, FunctionImport.toCore, Function.comp_def,
    ExternType.inFeatB, List.filter_map, Import.isMemory, Import.isTable]

theorem assemble_features {namespaceName : String} {provider : LocalSections} {consumer : FunctionModule}
    {result : LocalSections} (caps : FeatureSet)
    (hp : Module.InFeat caps (provider.assemble [])) (hc : Module.InFeat caps consumer.toCore)
    (h : StrictLink.assemble? namespaceName provider consumer = some result) :
    Module.InFeat caps (result.assemble []) := by
  obtain ⟨providerTypes, providerFuncs⟩ := (section_features provider [] caps).mp hp
  obtain ⟨consumerTypes, consumerFuncs⟩ := (section_features consumer.sections consumer.imports caps).mp hc
  unfold StrictLink.assemble? at h
  split at h
  · contradiction
  · simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, _, _, h⟩ := h
    split at h
    · contradiction
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨_, _, _, types, _, funcs, _, _, _, providerRelocated, rfl⟩ := h
      have typesEq := (mapM_invariants (fun _ _ _ eq => rec_features eq caps) types).2
      have funcsEq := (mapM_invariants (fun _ _ _ eq => func_features eq caps) funcs).2
      have providerEq := (mapM_invariants (fun _ _ _ eq => func_features eq caps) providerRelocated).2
      apply (section_features _ [] caps).mpr
      simp [List.all_append, typesEq, funcsEq, providerEq, providerTypes, providerFuncs, consumerTypes, consumerFuncs]

end Silmaril.Proofs.Wasm.Sublanguages.StrictLink
