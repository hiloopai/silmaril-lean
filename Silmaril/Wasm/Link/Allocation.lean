module

public import Silmaril.Wasm.Link.GC
public import Silmaril.Wasm.Execution.Core.Instantiation
public import Silmaril.Wasm.Validation.RollClosed

@[expose] public section

/-! # Closed GC types after linker relocation

The static linker shifts every absolute type index in the consumer by the
provider's type count. This file relates that actual partial rewrite to the
semantic type allocator. The resulting agreement concerns closed type tags;
it does not yet establish preservation of whole-module execution.
-/

namespace Silmaril.Wasm.Link.GC.Allocation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

/-- The semantic counterpart of the linker's absolute type-index shift. -/
def shift (offset : Nat) : Subst
  | .idx i => some (.idx (offset + i))
  | .recv _ => none

@[simp] theorem shift_minusRecs (offset : Nat) :
    (shift offset).minusRecs = shift offset := by
  funext v
  cases v <;> rfl

private theorem ofList_subst {k : TKind} (σ : Subst) (xs : List (Ty k)) :
    Ty.ofList (xs.map (·.subst σ)) = (Ty.ofList xs).subst σ := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [Ty.subst, ih]

private theorem mapM_lift {α β γ : Type} {f : α → Option β}
    {g : α → γ} {l : β → γ}
    (hf : ∀ {a b}, f a = some b → l b = g a)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ys.map l = xs.map g := by
  have hr : List.Forall₂ (fun a b => l b = g a) xs ys :=
    List.mapM_some_forall₂ (R := fun a b => l b = g a) (fun h => hf h) h
  clear h
  induction hr with
  | nil => rfl
  | cons hab _ ih => simp [hab, ih]

theorem relocated_liftTypeIdx {offset : Nat} {x y : TypeIdx}
    (h : shiftIdx? offset x = some y) :
    liftTypeIdx y = (liftTypeIdx x).subst (shift offset) := by
  have hy : y.toNat = offset + x.toNat :=
    ((Idx.ofNat?_eq_some_iff _ _).mp h).symm
  simp [liftTypeIdx, Ty.subst, shift, hy]

theorem relocated_liftHeap {offset : Nat} {h h' : HeapType}
    (he : heap? offset h = some h') :
    liftHeap h' = (liftHeap h).subst (shift offset) := by
  cases h with
  | abstract a => simp [heap?] at he; subst h'; rfl
  | typeIdx x =>
    cases hs : shiftIdx? offset x with
    | none => simp [heap?, hs] at he
    | some y =>
      simp [heap?, hs] at he
      subst h'
      simp only [liftHeap, Ty.subst]
      rw [relocated_liftTypeIdx hs]

theorem relocated_liftRef {offset : Nat} {r r' : RefType}
    (h : refType? offset r = some r') :
    liftRef r' = (liftRef r).subst (shift offset) := by
  cases hh : heap? offset r.heap with
  | none => simp [refType?, hh] at h
  | some heap =>
    simp [refType?, hh] at h
    subst r'
    simp only [liftRef, Ty.subst]
    rw [relocated_liftHeap hh]

theorem relocated_liftVal {offset : Nat} {v v' : ValType}
    (h : valType? offset v = some v') :
    liftVal v' = (liftVal v).subst (shift offset) := by
  cases v with
  | num n => simp [valType?] at h; subst v'; rfl
  | vec n => simp [valType?] at h; subst v'; rfl
  | ref r =>
    cases hr : refType? offset r with
    | none => simp [valType?, hr] at h
    | some r' =>
      simp [valType?, hr] at h
      subst v'
      simp only [liftVal, Ty.subst]
      rw [relocated_liftRef hr]

theorem relocated_liftStorage {offset : Nat} {s s' : StorageType}
    (h : storageType? offset s = some s') :
    liftStorage s' = (liftStorage s).subst (shift offset) := by
  cases s with
  | packed p => simp [storageType?] at h; subst s'; rfl
  | val v =>
    cases hv : valType? offset v with
    | none => simp [storageType?, hv] at h
    | some v' =>
      simp [storageType?, hv] at h
      subst s'
      simp only [liftStorage, Ty.subst]
      rw [relocated_liftVal hv]

theorem relocated_liftField {offset : Nat} {f f' : FieldType}
    (h : fieldType? offset f = some f') :
    liftField f' = (liftField f).subst (shift offset) := by
  cases hs : storageType? offset f.storage with
  | none => simp [fieldType?, hs] at h
  | some storage =>
    simp [fieldType?, hs] at h
    subst f'
    simp only [liftField, Ty.subst]
    rw [relocated_liftStorage hs]

theorem relocated_liftComp {offset : Nat} {c c' : CompositeType}
    (h : compositeType? offset c = some c') :
    liftComp c' = (liftComp c).subst (shift offset) := by
  cases c with
  | func f =>
    cases hp : f.params.mapM (valType? offset) with
    | none => simp [compositeType?, hp] at h
    | some ps =>
      cases hr : f.results.mapM (valType? offset) with
      | none => simp [compositeType?, hp, hr] at h
      | some rs =>
        simp [compositeType?, hp, hr] at h
        subst c'
        simp only [liftComp, liftResult, Ty.subst]
        rw [mapM_lift (g := fun v => (liftVal v).subst (shift offset)) relocated_liftVal hp,
          mapM_lift (g := fun v => (liftVal v).subst (shift offset)) relocated_liftVal hr]
        simpa only [List.map_map, Function.comp_def] using congrArg₂ Ty.func
          (ofList_subst (shift offset) (f.params.map liftVal))
          (ofList_subst (shift offset) (f.results.map liftVal))
  | struct fs =>
    cases hf : fs.mapM (fieldType? offset) with
    | none => simp [compositeType?, hf] at h
    | some fs' =>
      simp [compositeType?, hf] at h
      subst c'
      simp only [liftComp, Ty.subst]
      rw [mapM_lift (g := fun f => (liftField f).subst (shift offset)) relocated_liftField hf]
      simpa only [List.map_map, Function.comp_def] using congrArg Ty.struct
        (ofList_subst (shift offset) (fs.map liftField))
  | array f =>
    cases hf : fieldType? offset f with
    | none => simp [compositeType?, hf] at h
    | some f' =>
      simp [compositeType?, hf] at h
      subst c'
      simp only [liftComp, Ty.subst]
      rw [relocated_liftField hf]

theorem relocated_liftSub {offset : Nat} {s s' : SubType}
    (h : subType? offset s = some s') :
    liftSub s' = (liftSub s).subst (shift offset) := by
  cases hs : s.supertypes.mapM (shiftIdx? offset) with
  | none => simp [subType?, hs] at h
  | some supers =>
    cases hc : compositeType? offset s.body with
    | none => simp [subType?, hs, hc] at h
    | some body =>
      simp [subType?, hs, hc] at h
      subst s'
      simp only [liftSub, Ty.subst]
      rw [mapM_lift (g := fun x => (liftTypeIdx x).subst (shift offset))
        relocated_liftTypeIdx hs, relocated_liftComp hc]
      simpa only [List.map_map, Function.comp_def] using congrArg
        (fun sups => Ty.sub s.final_ sups ((liftComp s.body).subst (shift offset)))
        (ofList_subst (shift offset) (s.supertypes.map liftTypeIdx))

/-- Successful source relocation shifts precisely the free absolute indices
of the lifted recursion group, preserving its recursive binding structure. -/
theorem relocated_liftRec {offset : Nat} {r r' : RecType}
    (h : recType? offset r = some r') :
    liftRec r' = (liftRec r).subst (shift offset) := by
  cases hs : r.types.mapM (subType? offset) with
  | none => simp [recType?, hs] at h
  | some subs =>
    simp [recType?, hs] at h
    subst r'
    simp only [liftRec, Ty.subst, shift_minusRecs]
    rw [mapM_lift (g := fun s => (liftSub s).subst (shift offset)) relocated_liftSub hs]
    simpa only [List.map_map, Function.comp_def] using congrArg Ty.group
      (ofList_subst (shift offset) (r.types.map liftSub))

theorem relocated_length {offset : Nat} {r r' : RecType}
    (h : recType? offset r = some r') : r'.types.length = r.types.length := by
  have he := relocated_liftRec h
  have hl := congrArg (fun t : CRecType => t.subs.length) he
  simpa [liftRec, Ty.subst, Ty.subs, Ty.length_subst, Ty.length_ofList] using hl

@[simp] private theorem rho_minusRecs (x n : Nat) :
    (RollClosed.rho x n).minusRecs = RollClosed.rho x n :=
  Subst.minusRecs_eq (fun _ => rfl)

@[simp] private theorem all_minusRecs (xs : List CTypeUse) :
    (Subst.all xs).minusRecs = Subst.all xs :=
  Subst.minusRecs_eq (fun _ => rfl)

/-- Rolling a shifted type at its new group position and closing against the
extended prefix gives exactly its original rolled, closed form. The bound
excludes invalid references to groups that have not yet been allocated. -/
theorem shift_roll_close {k : TKind} (t : Ty k) (pre prior : List DefType) (n : Nat)
    (hb : ∀ y ∈ t.freeIdx, y < prior.length + n) :
    (((t.subst (shift pre.length)).subst
      (RollClosed.rho (pre.length + prior.length) n)).subst
        (Subst.all ((pre ++ prior).map .dt))) =
    (t.subst (RollClosed.rho prior.length n)).subst (Subst.all (prior.map .dt)) := by
  induction t with
  | idx y =>
    have hy := hb y (by simp [Ty.freeIdx])
    by_cases hlt : y < prior.length
    · have h₁ : ¬ prior.length ≤ y := by omega
      have h₂ : ¬ pre.length + prior.length ≤ pre.length + y := by omega
      simp only [Ty.subst, shift, Option.getD_some, RollClosed.rho,
        h₁, h₂, false_and, ↓reduceIte, Option.getD_none, Subst.all,
        List.getElem?_map]
      rw [List.getElem?_append_right (by omega : pre.length ≤ pre.length + y)]
      simp [List.getElem?_eq_getElem hlt]
    · have hge : prior.length ≤ y := by omega
      have hge' : pre.length + prior.length ≤ pre.length + y := by omega
      have hlt' : pre.length + y < pre.length + prior.length + n := by omega
      have hd : pre.length + y - (pre.length + prior.length) = y - prior.length := by
        omega
      simp [Ty.subst, shift, RollClosed.rho, hge, hge', hy, hlt', hd, Subst.all]
  | cons a l iha ihl =>
    simp only [Ty.subst]
    rw [iha (fun y hy => hb y (by simp [Ty.freeIdx, hy])),
      ihl (fun y hy => hb y (by simp [Ty.freeIdx, hy]))]
  | func a l iha ihl =>
    simp only [Ty.subst]
    rw [iha (fun y hy => hb y (by simp [Ty.freeIdx, hy])),
      ihl (fun y hy => hb y (by simp [Ty.freeIdx, hy]))]
  | sub fin a l iha ihl =>
    simp only [Ty.subst]
    rw [iha (fun y hy => hb y (by simp [Ty.freeIdx, hy])),
      ihl (fun y hy => hb y (by simp [Ty.freeIdx, hy]))]
  | group subs ih =>
    simp only [Ty.subst, shift_minusRecs, rho_minusRecs, all_minusRecs]
    rw [ih (by simpa [Ty.freeIdx] using hb)]
  | recv i => rfl
  | _ => simp_all [Ty.subst, Ty.freeIdx]

/-- A relocated recursion group allocates the same closed tags, including
cross-group references and recursive references within the current group. -/
theorem relocated_rollGroup (pre : List DefType) {C : Context} {r r' : RecType}
    (hr : recType? pre.length r = some r')
    (hb : ∀ y ∈ (liftRec r).freeIdx, y < C.types.length + r.types.length) :
    ({ C with types := pre ++ C.types } : Context).rollGroup r' = C.rollGroup r := by
  have hl := relocated_length hr
  have he := relocated_liftRec hr
  have hs : Ty.ofList (r'.types.map liftSub) =
      (Ty.ofList (r.types.map liftSub)).subst (shift pre.length) := by
    simpa only [liftRec, Ty.subst, shift_minusRecs, Ty.group.injEq] using he
  rw [RollClosed.rollGroup_eq, RollClosed.rollGroup_eq, hl]
  have hg : RollClosed.rsubs (pre ++ C.types) r'.types = RollClosed.rsubs C.types r.types := by
    simp only [RollClosed.rsubs, hl, hs, List.length_append]
    exact shift_roll_close _ pre C.types r.types.length (by simpa [liftRec, Ty.freeIdx] using hb)
  rw [hg]

/-- The relocated allocation fold extends any provider prefix with the
consumer's original closed tags. Scoping comes from `TypesOk`, rather than an
assumption that the two allocations agree. -/
theorem relocated_allocTypes_foldl (pre : List DefType)
    {C : Context} {rts shifted : List RecType} {dts : List DefType}
    (ht : TypesOk C rts dts)
    (hr : rts.mapM (recType? pre.length) = some shifted) :
    shifted.foldl (fun acc rt => acc ++ ({ types := acc } : Context).rollGroup rt)
      (pre ++ C.types) = pre ++ C.types ++ dts := by
  induction ht generalizing shifted with
  | nil =>
    simp at hr
    subst shifted
    simp
  | @cons C rt rts dts hok _ ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hr
    obtain ⟨rt', hrt, rts', hrts, rfl⟩ := hr
    have hb : ∀ y ∈ (liftRec rt).freeIdx, y < C.types.length + rt.types.length := by
      intro y hy
      simp only [liftRec, Ty.freeIdx, Ty.mem_freeIdx_ofList, List.mem_map] at hy
      obtain ⟨_, ⟨st, hst, rfl⟩, hy⟩ := hy
      have := hok.freeIdx_lt st hst y hy
      simpa [Context.length_rollGroup] using this
    simp only [List.foldl_cons]
    change rts'.foldl _ ((pre ++ C.types) ++
      ({ C with types := pre ++ C.types } : Context).rollGroup rt') = _
    rw [relocated_rollGroup pre hrt hb]
    simpa only [List.append_assoc] using ih hrts

/-- The closed allocator contributes one tag per source recursion-group member. -/
theorem allocTypes_length (rts : List RecType) :
    (allocTypes rts).length = (rts.flatMap RecType.types).length := by
  have hfold : ∀ acc : List DefType,
      (rts.foldl (fun acc rt => acc ++ ({ types := acc } : Context).rollGroup rt) acc).length =
        acc.length + (rts.flatMap RecType.types).length := by
    induction rts with
    | nil => intro acc; simp
    | cons rt rts ih =>
      intro acc
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [ih]
      simp [Context.length_rollGroup, Nat.add_assoc]
  simpa only [allocTypes, Context.rollGroup, List.length_nil, Nat.zero_add] using hfold []

/-- Closed consumer tags survive the exact offset used by the linker. -/
theorem relocated_allocTypes_append {provider consumer : Module} {shifted : List RecType}
    {dts : List DefType} (hc : TypesOk {} consumer.types dts)
    (hr : consumer.types.mapM (recType? provider.typeDefinitions.length) = some shifted) :
    allocTypes (provider.types ++ shifted) = allocTypes provider.types ++ allocTypes consumer.types := by
  have he : (allocTypes provider.types).length = provider.typeDefinitions.length :=
    allocTypes_length provider.types
  have hr' : consumer.types.mapM (recType? (allocTypes provider.types).length) = some shifted := by
    rwa [he]
  have hf := relocated_allocTypes_foldl (allocTypes provider.types) hc hr'
  change shifted.foldl _ (allocTypes provider.types ++ []) =
    allocTypes provider.types ++ [] ++ dts at hf
  rw [allocTypes_eq hc]
  simpa only [allocTypes, Context.rollGroup, List.foldl_append, List.append_nil] using hf

/-- Successful assembly gives structural equality of the allocated closed
tags, with the original provider tags followed by the original consumer tags. -/
theorem assemble?_allocTypes {namespaceName : String} {provider consumer result : Module}
    (h : assemble? namespaceName provider consumer = some result) :
    allocTypes result.types = allocTypes provider.types ++ allocTypes consumer.types := by
  unfold assemble? at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨providerType, _, consumerType, hc, h⟩ := h
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨imports, _, shifted, hs, funcs, _, globals, _, exports, _,
        providerFuncs, _, providerGlobals, _, rfl⟩ := h
      have ht : ∃ dts, TypesOk {} consumer.types dts := by
        cases Validation.validate?_sound hc
        exact ⟨_, by assumption⟩
      obtain ⟨dts, ht⟩ := ht
      exact relocated_allocTypes_append ht hs

/-- The actual validated linker preserves the allocator's closed GC type tags. -/
theorem link?_allocTypes {namespaceName : String} {provider consumer result : Module}
    (h : link? namespaceName provider consumer = some result) :
    allocTypes result.types = allocTypes provider.types ++ allocTypes consumer.types := by
  obtain ⟨assembled, ha, hv⟩ := Option.bind_eq_some_iff.mp h
  have he : assembled = result := by
    unfold validated? at hv
    split at hv
    · exact Option.some.inj hv
    · cases hv
  subst result
  exact assemble?_allocTypes ha

/-- Every successfully shifted consumer type index retrieves its original
closed tag from the linked allocation. -/
theorem link?_consumer_type_lookup {namespaceName : String} {provider consumer result : Module}
    {x y : TypeIdx} (h : link? namespaceName provider consumer = some result)
    (hs : shiftIdx? provider.typeDefinitions.length x = some y) :
    (allocTypes result.types)[y.toNat]? = (allocTypes consumer.types)[x.toNat]? := by
  have hy : y.toNat = provider.typeDefinitions.length + x.toNat :=
    ((Idx.ofNat?_eq_some_iff _ _).mp hs).symm
  have hp : (allocTypes provider.types).length = provider.typeDefinitions.length :=
    allocTypes_length provider.types
  rw [link?_allocTypes h, hy, List.getElem?_append_right (by omega), hp]
  simp

/-- Existing provider tags keep their indices in the linked allocation. -/
theorem link?_provider_type_lookup {namespaceName : String} {provider consumer result : Module}
    {x : TypeIdx} {d : DefType} (h : link? namespaceName provider consumer = some result)
    (hp : (allocTypes provider.types)[x.toNat]? = some d) :
    (allocTypes result.types)[x.toNat]? = some d := by
  rw [link?_allocTypes h, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hp).1]
  exact hp

end Silmaril.Wasm.Link.GC.Allocation
