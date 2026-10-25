module

public import Silmaril.Wasm.Link.Preparation
public import Mathlib.Logic.Equiv.Defs

/-! # Global addresses under a block permutation

Ordinary separate preparation stores the global blocks as
`ambient, provider-init, provider-copy, consumer-init, consumer-copy`.
Linked preparation puts `consumer-init` before `provider-copy`. Swapping those
adjacent blocks preserves global values, reads and updates. Function and GC
addresses do not change.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.GlobalPermutation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H α : Type}

/-- Exchange two adjacent address intervals, fixing all other addresses. -/
def swapBlocks (base left right address : Nat) : Nat :=
  if address < base then address
  else if address < base + left then address + right
  else if address < base + left + right then address - left
  else address

theorem swapBlocks_before {base left right address : Nat} (h : address < base) :
    swapBlocks base left right address = address := by simp [swapBlocks, h]

theorem swapBlocks_left {base left right address : Nat}
    (lo : base ≤ address) (hi : address < base + left) :
    swapBlocks base left right address = address + right := by
  simp [swapBlocks, show ¬ address < base by omega, hi]

theorem swapBlocks_right {base left right address : Nat}
    (lo : base + left ≤ address) (hi : address < base + left + right) :
    swapBlocks base left right address = address - left := by
  simp [swapBlocks, show ¬ address < base by omega,
    show ¬ address < base + left by omega, hi]

theorem swapBlocks_after {base left right address : Nat}
    (h : base + left + right ≤ address) :
    swapBlocks base left right address = address := by
  simp [swapBlocks, show ¬ address < base by omega,
    show ¬ address < base + left by omega, show ¬ address < base + left + right by omega]

theorem swapBlocks_inverse (base left right address : Nat) :
    swapBlocks base right left (swapBlocks base left right address) = address := by
  by_cases before : address < base
  · rw [swapBlocks_before before, swapBlocks_before before]
  · by_cases first : address < base + left
    · rw [swapBlocks_left (by omega) first,
        swapBlocks_right (by omega) (by omega)]
      omega
    · by_cases second : address < base + left + right
      · rw [swapBlocks_right (by omega) second,
          swapBlocks_left (by omega) (by omega)]
        omega
      · have fixed : swapBlocks base left right address = address := swapBlocks_after (by omega)
        rw [fixed, swapBlocks_after (by omega)]

/-- The address permutation used to normalize ordinary preparation. -/
def blocks (base left right : Nat) : Nat ≃ Nat where
  toFun := swapBlocks base left right
  invFun := swapBlocks base right left
  left_inv := swapBlocks_inverse base left right
  right_inv := swapBlocks_inverse base right left

@[simp] theorem blocks_apply (base left right address : Nat) :
    blocks base left right address = swapBlocks base left right address := rfl

@[simp] theorem blocks_symm_apply (base left right address : Nat) :
    (blocks base left right).symm address = swapBlocks base right left address := rfl

/-- Target lookups at renamed addresses return exactly the source values,
including failed lookups. -/
def Lookup (p : Nat ≃ Nat) (source target : List α) : Prop :=
  ∀ address, target[p address]? = source[address]?

theorem Lookup.symm {p : Nat ≃ Nat} {source target : List α}
    (h : Lookup p source target) : Lookup p.symm target source := by
  intro address
  simpa only [Equiv.apply_symm_apply] using (h (p.symm address)).symm

/-- Updating one source address and its target image preserves all lookups. -/
theorem Lookup.modify {p : Nat ≃ Nat} {source target : List α}
    (h : Lookup p source target) (address : Nat) (f : α → α) :
    Lookup p (source.modify address f) (target.modify (p address) f) := by
  intro other
  rw [List.getElem?_modify, List.getElem?_modify, h other]
  congr 1
  funext value
  simp only [p.injective.eq_iff]

/-- Swapping actual list blocks realizes the address permutation. -/
theorem blocks_lookup (front left right suffix : List α) :
    Lookup (blocks front.length left.length right.length)
      (front ++ left ++ right ++ suffix) (front ++ right ++ left ++ suffix) := by
  intro address
  simp only [blocks_apply, List.append_assoc]
  by_cases before : address < front.length
  · rw [swapBlocks_before before, List.getElem?_append_left before,
      List.getElem?_append_left before]
  · by_cases first : address < front.length + left.length
    · rw [swapBlocks_left (by omega) first,
        List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega),
        List.getElem?_append_left (by omega),
        List.getElem?_append_right (by omega),
        List.getElem?_append_left (by omega)]
      congr 1
      omega
    · by_cases second : address < front.length + left.length + right.length
      · rw [swapBlocks_right (by omega) second,
          List.getElem?_append_right (by omega),
          List.getElem?_append_left (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_left (by omega)]
        congr 1
        omega
      · rw [swapBlocks_after (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega),
          List.getElem?_append_right (by omega)]
        congr 1
        omega

/-- The initialized and copied blocks produced by ordinary preparation. -/
theorem ordinary_blocks (ambient provider consumer : List α) :
    Lookup (blocks (ambient.length + provider.length) provider.length consumer.length)
      (ambient ++ provider ++ provider ++ consumer ++ consumer)
      (ambient ++ provider ++ consumer ++ provider ++ consumer) := by
  simpa only [List.length_append, List.append_assoc] using
    blocks_lookup (ambient ++ provider) provider consumer consumer

/-- Every provider installed address moves past the consumer initializer block. -/
theorem provider_address (ambient provider consumer i : Nat) (hi : i < provider) :
    blocks (ambient + provider) provider consumer (ambient + provider + i) =
      ambient + provider + consumer + i := by
  rw [blocks_apply, swapBlocks_left (by omega) (by omega)]
  omega

/-- The consumer installed block already has the same address on both sides. -/
theorem consumer_address (ambient provider consumer i : Nat) :
    blocks (ambient + provider) provider consumer (ambient + 2 * provider + consumer + i) =
      ambient + 2 * provider + consumer + i := by
  rw [blocks_apply, swapBlocks_after (by omega)]

/-- All ambient global addresses are fixed. -/
theorem ambient_address (ambient provider consumer address : Nat) (h : address < ambient) :
    blocks (ambient + provider) provider consumer address = address := by
  rw [blocks_apply, swapBlocks_before (by omega)]

def external (p : Nat ≃ Nat) : ExternAddr → ExternAddr
  | .global address => .global (p address)
  | other => other

def moduleView (p : Nat ≃ Nat) (m : ModuleInst) : ModuleInst :=
  { m with
    globals := m.globals.map p
    exports := m.exports.map (fun e => { e with addr := external p e.addr }) }

def frame (p : Nat ≃ Nat) (f : Frame) : Frame :=
  { f with module := moduleView p f.module }

def function (p : Nat ≃ Nat) (f : FuncInst H) : FuncInst H :=
  { f with module := match f.code with
    | .wasm _ => moduleView p f.module
    | .host _ => f.module }

@[simp] theorem external_inverse (p : Nat ≃ Nat) (address : ExternAddr) :
    external p.symm (external p address) = address := by
  cases address <;> simp [external]

@[simp] theorem moduleView_inverse (p : Nat ≃ Nat) (m : ModuleInst) :
    moduleView p.symm (moduleView p m) = m := by
  cases m
  simp [moduleView, List.map_map, _root_.Function.comp_def]

@[simp] theorem frame_inverse (p : Nat ≃ Nat) (f : Frame) :
    frame p.symm (frame p f) = f := by
  cases f
  simp [frame]

@[simp] theorem function_inverse (p : Nat ≃ Nat) (f : FuncInst H) :
    function p.symm (function p f) = f := by
  rcases f with ⟨type, view, code⟩
  cases code <;> simp [function]

/-- A global renaming changes only global addresses and module views. -/
structure Renamed (p : Nat ≃ Nat) (source target : Store H) : Prop where
  globals : Lookup p source.globals target.globals
  functions : target.funcs = source.funcs.map (function p)
  tags : source.tags = target.tags
  mems : source.mems = target.mems
  tables : source.tables = target.tables
  datas : source.datas = target.datas
  elems : source.elems = target.elems
  structs : source.structs = target.structs
  arrays : source.arrays = target.arrays
  exns : source.exns = target.exns

/-- Undoing the address permutation reverses the whole store relation. -/
theorem Renamed.symm {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) : Renamed p.symm target source := by
  refine ⟨h.globals.symm, ?_, h.tags.symm, h.mems.symm, h.tables.symm,
    h.datas.symm, h.elems.symm, h.structs.symm, h.arrays.symm, h.exns.symm⟩
  rw [h.functions, List.map_map]
  simp only [_root_.Function.comp_def, function_inverse, List.map_id']

theorem Renamed.function_lookup {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) {address : Nat} {f : FuncInst H}
    (lookup : source.funcs[address]? = some f) :
    target.funcs[address]? = some (function p f) := by
  simp only [h.functions, List.getElem?_map, lookup, Option.map_some]

theorem Renamed.function_tag_lookup {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) :
    source.funcs[address]?.map FuncInst.type = target.funcs[address]?.map FuncInst.type := by
  simp only [h.functions, List.getElem?_map, Option.map_map, function,
    _root_.Function.comp_def]

theorem Renamed.refOk {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) {r : Ref} {type : CRefType}
    (valid : RefOk source r type) : RefOk target r type := by
  induction valid with
  | null => exact .null
  | i31 bits => exact .i31 bits
  | struct lookup => exact .struct (h.structs ▸ lookup)
  | array lookup => exact .array (h.arrays ▸ lookup)
  | @func address fi lookup => exact .func (fi := function p fi) (h.function_lookup lookup)
  | exn lookup => exact .exn (h.exns ▸ lookup)
  | host address => exact .host address
  | extern _ hn ih => exact .extern ih hn
  | sub _ valid sub ih => exact .sub ih valid sub

theorem Renamed.refOk_iff {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (r : Ref) (type : CRefType) :
    RefOk source r type ↔ RefOk target r type := ⟨h.refOk, h.symm.refOk⟩

theorem Renamed.valOk_iff {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (v : Val) (type : CValType) :
    ValOk source v type ↔ ValOk target v type := by
  constructor
  · intro valid
    cases valid with
    | num value => exact .num value
    | vec bits => exact .vec bits
    | ref hr => exact .ref (h.refOk hr)
  · intro valid
    cases valid with
    | num value => exact .num value
    | vec bits => exact .vec bits
    | ref hr => exact .ref (h.symm.refOk hr)

theorem Renamed.fieldValOk_iff {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (v : FieldVal) (type : CStorageType) :
    FieldValOk source v type ↔ FieldValOk target v type := by
  constructor
  · intro valid
    cases valid with
    | val hv => exact .val ((h.valOk_iff _ _).mp hv)
    | pack pack bits => exact .pack pack bits
  · intro valid
    cases valid with
    | val hv => exact .val ((h.valOk_iff _ _).mpr hv)
    | pack pack bits => exact .pack pack bits

theorem Renamed.setGlobal {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) (value : Val) :
    Renamed p (source.setGlobal address value) (target.setGlobal (p address) value) :=
  ⟨h.globals.modify address (fun g => { g with value := value }), h.functions,
    h.tags, h.mems, h.tables, h.datas, h.elems, h.structs, h.arrays, h.exns⟩

theorem Renamed.setMem {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) (value : MemInst) :
    Renamed p (source.setMem address value) (target.setMem address value) :=
  ⟨h.globals, h.functions, h.tags, congrArg (fun ms => ms.set address value) h.mems,
    h.tables, h.datas, h.elems, h.structs, h.arrays, h.exns⟩

theorem Renamed.setTable {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) (value : TableInst) :
    Renamed p (source.setTable address value) (target.setTable address value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, congrArg (fun ts => ts.set address value) h.tables,
    h.datas, h.elems, h.structs, h.arrays, h.exns⟩

theorem Renamed.setElem {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) (refs : List Ref) :
    Renamed p (source.setElem address refs) (target.setElem address refs) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas,
    congrArg (fun es => es.modify address (fun e => { e with refs := refs })) h.elems,
    h.structs, h.arrays, h.exns⟩

theorem Renamed.setData {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address : Nat) (bytes : ByteArray) :
    Renamed p (source.setData address bytes) (target.setData address bytes) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables,
    congrArg (fun ds => ds.modify address (fun _ => ⟨bytes⟩)) h.datas,
    h.elems, h.structs, h.arrays, h.exns⟩

theorem Renamed.setStructField {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address field : Nat) (value : FieldVal) :
    Renamed p (source.setStructField address field value)
      (target.setStructField address field value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas, h.elems,
    congrArg (fun ss => ss.modify address (fun st => { st with fields := st.fields.set field value })) h.structs,
    h.arrays, h.exns⟩

theorem Renamed.setArrayField {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (address field : Nat) (value : FieldVal) :
    Renamed p (source.setArrayField address field value)
      (target.setArrayField address field value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas, h.elems, h.structs,
    congrArg (fun ss => ss.modify address (fun st => { st with fields := st.fields.set field value })) h.arrays,
    h.exns⟩

theorem Renamed.addStruct {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (value : StructInst) :
    Renamed p (source.addStruct value) (target.addStruct value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas, h.elems,
    congrArg (fun ss => ss ++ [value]) h.structs, h.arrays, h.exns⟩

theorem Renamed.addArray {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (value : ArrayInst) :
    Renamed p (source.addArray value) (target.addArray value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas, h.elems, h.structs,
    congrArg (fun ss => ss ++ [value]) h.arrays, h.exns⟩

theorem Renamed.addExn {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) (value : ExnInst) :
    Renamed p (source.addExn value) (target.addExn value) :=
  ⟨h.globals, h.functions, h.tags, h.mems, h.tables, h.datas, h.elems, h.structs, h.arrays,
    congrArg (fun es => es ++ [value]) h.exns⟩

theorem Renamed.global_lookup {p : Nat ≃ Nat} {source target : Store H}
    (h : Renamed p source target) {f : Frame} {x : GlobalIdx} {address : Nat} {g : GlobalInst}
    (lookup : source.global? f x = some (address, g)) :
    target.global? (frame p f) x = some (p address, g) := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff] at lookup
  obtain ⟨a, ha, hg⟩ := lookup
  obtain ⟨g', hg, he⟩ := hg
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [Store.global?, frame, moduleView, List.getElem?_map, ha, Option.map_some,
    Option.bind_eq_bind, Option.bind_some, h.globals a, hg, Option.pure_def]

/-- All local and global leaf steps commute with global address renaming.
The source and target update the same value at corresponding global addresses. -/
theorem variable_step {p : Nat ≃ Nat} {source target source' : Store H}
    {f f' : Frame} {code out : List Admin} (h : Renamed p source target)
    (step : VariableStep ⟨source, f, code⟩ ⟨source', f', out⟩) :
    ∃ target', VariableStep ⟨target, frame p f, code⟩ ⟨target', frame p f', out⟩ ∧
      Renamed p source' target' := by
  cases step with
  | localGet lookup => exact ⟨target, .localGet lookup, h⟩
  | localSet bound => exact ⟨target, .localSet bound, h⟩
  | localTee => exact ⟨target, .localTee, h⟩
  | globalGet lookup => exact ⟨target, .globalGet (h.global_lookup lookup), h⟩
  | @globalSet _ _ x address g value lookup =>
    exact ⟨target.setGlobal (p address) value, .globalSet (h.global_lookup lookup),
      h.setGlobal address value⟩

/-- Reference tests and casts observe unchanged tags and GC objects. The
renamed function definitions have exactly the same closed call tags. -/
theorem reference_step {p : Nat ≃ Nat} {source target : Store H}
    {f : Frame} {code out : List Admin} (h : Renamed p source target)
    (step : RefStep ⟨source, f, code⟩ ⟨source, f, out⟩) :
    RefStep ⟨target, frame p f, code⟩ ⟨target, frame p f, out⟩ := by
  cases step with
  | refNull ht => exact .refNull ht
  | refFunc hf => exact .refFunc hf
  | refI31 bits => exact .refI31 bits
  | isNullTrue => exact .isNullTrue
  | isNullFalse hn => exact .isNullFalse hn
  | asNonNullNull => exact .asNonNullNull
  | asNonNullAddr hn => exact .asNonNullAddr hn
  | eqNull => exact .eqNull
  | eqTrue hn => exact .eqTrue hn
  | eqFalse hn => exact .eqFalse hn
  | testTrue valid => exact .testTrue (h.refOk valid)
  | testFalse invalid => exact .testFalse (fun valid => invalid (h.symm.refOk valid))
  | castSucceed valid => exact .castSucceed (h.refOk valid)
  | castFail invalid => exact .castFail (fun valid => invalid (h.symm.refOk valid))
  | i31GetNull sign => exact .i31GetNull sign
  | i31GetNum sign bits => exact .i31GetNum sign bits
  | externConvertNull => exact .externConvertNull
  | externConvertAddr hn => exact .externConvertAddr hn
  | anyConvertNull => exact .anyConvertNull
  | anyConvertAddr r => exact .anyConvertAddr r

end Silmaril.Wasm.Link.GC.GlobalPermutation
