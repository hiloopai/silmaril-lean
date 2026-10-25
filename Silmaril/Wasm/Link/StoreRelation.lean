module

public import Silmaril.Wasm.Link.Functions
public import Silmaril.Wasm.Link.Initializers

/-! # Stores containing corresponding linked function definitions

Runtime values and all non-function store fields agree exactly. At each function
address, the closed call tag agrees; the definition either remains unchanged or
carries the actual static relocation of its code and module views. This relation
does not assume preservation of execution.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.StoreRelation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Ambient definitions stay unchanged. Linked wasm definitions keep their
closed call tag and carry their exact source-code and module-view relocation. -/
inductive Function : FuncInst H → FuncInst H → Prop where
  | same (fi : FuncInst H) : Function fi fi
  | relocated {tag : DefType} {sourceModule targetModule : ModuleInst}
      {source target : Func} (r : Relocation)
      (views : Views.Successful r sourceModule targetModule)
      (rewrite : Functions.Rewrite r source target) :
      Function ⟨tag, sourceModule, .wasm source⟩ ⟨tag, targetModule, .wasm target⟩

theorem Function.type_eq {source target : FuncInst H} (h : Function source target) :
    source.type = target.type := by cases h <;> rfl

/-- The state fields observed and mutated by runtime instructions. -/
structure State (source target : Store H) : Prop where
  tags : source.tags = target.tags
  globals : source.globals = target.globals
  mems : source.mems = target.mems
  tables : source.tables = target.tables
  datas : source.datas = target.datas
  elems : source.elems = target.elems
  structs : source.structs = target.structs
  arrays : source.arrays = target.arrays
  exns : source.exns = target.exns

theorem State.refl (s : Store H) : State s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem State.symm {s t : Store H} (h : State s t) : State t s :=
  ⟨h.tags.symm, h.globals.symm, h.mems.symm, h.tables.symm, h.datas.symm,
    h.elems.symm, h.structs.symm, h.arrays.symm, h.exns.symm⟩

theorem State.trans {s t u : Store H} (h : State s t) (h' : State t u) : State s u :=
  ⟨h.tags.trans h'.tags, h.globals.trans h'.globals, h.mems.trans h'.mems,
    h.tables.trans h'.tables, h.datas.trans h'.datas, h.elems.trans h'.elems,
    h.structs.trans h'.structs, h.arrays.trans h'.arrays, h.exns.trans h'.exns⟩

theorem State.data {s t : Store H} (h : State s t) : Initializers.Data s t :=
  ⟨h.globals, h.structs, h.arrays⟩

structure Related (source target : Store H) : Prop extends State source target where
  functions : List.Forall₂ Function source.funcs target.funcs

theorem Related.refl (s : Store H) : Related s s := by
  refine ⟨State.refl s, ?_⟩
  generalize s.funcs = fs
  induction fs with
  | nil => exact .nil
  | cons fi fs ih => exact .cons (.same fi) ih

private theorem forall₂_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) {i : Nat} {x : α}
    (hx : xs[i]? = some x) : ∃ y, ys[i]? = some y ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hx
  | @cons a b xs ys hab _ ih =>
    cases i with
    | zero => simp at hx; subst x; exact ⟨b, rfl, hab⟩
    | succ i => exact ih (by simpa using hx)

theorem Related.function_lookup {source target : Store H} (h : Related source target)
    {a : Nat} {fi : FuncInst H} (hf : source.funcs[a]? = some fi) :
    ∃ fi', target.funcs[a]? = some fi' ∧ Function fi fi' :=
  forall₂_lookup h.functions hf

theorem Related.function_lookup_reverse {source target : Store H} (h : Related source target)
    {a : Nat} {fi' : FuncInst H} (hf : target.funcs[a]? = some fi') :
    ∃ fi, source.funcs[a]? = some fi ∧ Function fi fi' := by
  have hr := h.functions.flip
  exact forall₂_lookup hr hf

theorem Related.function_types {source target : Store H} (h : Related source target) :
    source.funcs.map FuncInst.type = target.funcs.map FuncInst.type := by
  have hr := h.functions
  generalize hx : source.funcs = xs at hr ⊢
  generalize hy : target.funcs = ys at hr ⊢
  clear hx hy
  induction hr with
  | nil => rfl
  | cons hf _ ih => simp only [List.map_cons, hf.type_eq, ih]

theorem Related.function_tag_lookup {source target : Store H} (h : Related source target)
    (a : Nat) : source.funcs[a]?.map FuncInst.type = target.funcs[a]?.map FuncInst.type := by
  have he := congrArg (fun xs => xs[a]?) h.function_types
  simpa only [List.getElem?_map] using he

theorem Related.ref_type {source target : Store H} (h : Related source target) (r : Ref) :
    r.type? source = r.type? target := by
  cases r <;> simp only [Ref.type?, h.structs, h.arrays, h.exns]
  case func a =>
    simpa only [Option.map_map, _root_.Function.comp_def] using
      congrArg (Option.map (fun d => Ty.ref false (.defHeap d))) (h.function_tag_lookup a)

theorem Related.refOk {source target : Store H} (h : Related source target)
    {r : Ref} {type : CRefType} (valid : RefOk source r type) : RefOk target r type := by
  induction valid with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct hs => exact .struct (h.structs ▸ hs)
  | array hs => exact .array (h.arrays ▸ hs)
  | func hf =>
    obtain ⟨fi', ht, hr⟩ := h.function_lookup hf
    rw [hr.type_eq]
    exact .func ht
  | exn hs => exact .exn (h.exns ▸ hs)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem Related.refOk_reverse {source target : Store H} (h : Related source target)
    {r : Ref} {type : CRefType} (valid : RefOk target r type) : RefOk source r type := by
  induction valid with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct hs => exact .struct (h.structs.symm ▸ hs)
  | array hs => exact .array (h.arrays.symm ▸ hs)
  | func hf =>
    obtain ⟨fi, ht, hr⟩ := h.function_lookup_reverse hf
    rw [← hr.type_eq]
    exact .func ht
  | exn hs => exact .exn (h.exns.symm ▸ hs)
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

/-- Cast success and cast failure agree although wasm bodies and module index
tables may differ in the two stores. -/
theorem Related.refOk_iff {source target : Store H} (h : Related source target)
    (r : Ref) (type : CRefType) : RefOk source r type ↔ RefOk target r type :=
  ⟨h.refOk, h.refOk_reverse⟩

theorem Related.valOk_iff {source target : Store H} (h : Related source target)
    (v : Val) (type : CValType) : ValOk source v type ↔ ValOk target v type := by
  constructor
  · intro valid
    cases valid with
    | num v => exact .num v
    | vec b => exact .vec b
    | ref hr => exact .ref (h.refOk hr)
  · intro valid
    cases valid with
    | num v => exact .num v
    | vec b => exact .vec b
    | ref hr => exact .ref (h.refOk_reverse hr)

theorem Related.fieldValOk_iff {source target : Store H} (h : Related source target)
    (v : FieldVal) (type : CStorageType) : FieldValOk source v type ↔ FieldValOk target v type := by
  constructor
  · intro valid
    cases valid with
    | val hv => exact .val ((h.valOk_iff _ _).mp hv)
    | pack p b => exact .pack p b
  · intro valid
    cases valid with
    | val hv => exact .val ((h.valOk_iff _ _).mpr hv)
    | pack p b => exact .pack p b

/-! ## Matching runtime mutations -/

theorem Related.setGlobal {source target : Store H} (h : Related source target)
    (a : Nat) (v : Val) : Related (source.setGlobal a v) (target.setGlobal a v) :=
  ⟨⟨h.tags, congrArg (fun gs => gs.modify a (fun g => { g with value := v })) h.globals, h.mems, h.tables, h.datas, h.elems, h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setTable {source target : Store H} (h : Related source target)
    (a : Nat) (v : TableInst) : Related (source.setTable a v) (target.setTable a v) :=
  ⟨⟨h.tags, h.globals, h.mems, congrArg (fun ts => ts.set a v) h.tables, h.datas, h.elems, h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setMem {source target : Store H} (h : Related source target)
    (a : Nat) (v : MemInst) : Related (source.setMem a v) (target.setMem a v) :=
  ⟨⟨h.tags, h.globals, congrArg (fun ms => ms.set a v) h.mems, h.tables, h.datas, h.elems, h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setElem {source target : Store H} (h : Related source target)
    (a : Nat) (refs : List Ref) : Related (source.setElem a refs) (target.setElem a refs) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, congrArg (fun es => es.modify a (fun e => { e with refs := refs })) h.elems, h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setData {source target : Store H} (h : Related source target)
    (a : Nat) (bytes : ByteArray) : Related (source.setData a bytes) (target.setData a bytes) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, congrArg (fun ds => ds.modify a (fun _ => ⟨bytes⟩)) h.datas, h.elems, h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setStructField {source target : Store H} (h : Related source target)
    (a i : Nat) (v : FieldVal) : Related (source.setStructField a i v) (target.setStructField a i v) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, h.elems, congrArg (fun ss => ss.modify a (fun st => { st with fields := st.fields.set i v })) h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.setArrayField {source target : Store H} (h : Related source target)
    (a i : Nat) (v : FieldVal) : Related (source.setArrayField a i v) (target.setArrayField a i v) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, h.elems, h.structs, congrArg (fun ss => ss.modify a (fun st => { st with fields := st.fields.set i v })) h.arrays, h.exns⟩, h.functions⟩

theorem Related.addStruct {source target : Store H} (h : Related source target)
    (v : StructInst) : Related (source.addStruct v) (target.addStruct v) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, h.elems, congrArg (fun ss => ss ++ [v]) h.structs, h.arrays, h.exns⟩, h.functions⟩

theorem Related.addArray {source target : Store H} (h : Related source target)
    (v : ArrayInst) : Related (source.addArray v) (target.addArray v) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, h.elems, h.structs, congrArg (fun ss => ss ++ [v]) h.arrays, h.exns⟩, h.functions⟩

theorem Related.addExn {source target : Store H} (h : Related source target)
    (v : ExnInst) : Related (source.addExn v) (target.addExn v) :=
  ⟨⟨h.tags, h.globals, h.mems, h.tables, h.datas, h.elems, h.structs, h.arrays, congrArg (fun ss => ss ++ [v]) h.exns⟩, h.functions⟩

/-! ## Actual single-allocation function lists -/

theorem once_function_list {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : instantiateOnce? s m (Preparation.imports as) = some (s', f, start)) :
    ∃ types,
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some types ∧
      s'.funcs = s.funcs ++ Preparation.functionInstances f.module types m.funcs := by
  obtain ⟨s₁, _, _, hg, ha, _, _⟩ := PreparationOnce.once_allocation profile run
  obtain ⟨_, hsf, _⟩ := evalGlobals?_shape hg
  obtain ⟨types, ht, hs⟩ := PreparationOnce.residue_store profile ha
  exact ⟨types, ht, by rw [hs, hsf]⟩

/-- Every source lookup in the newly allocated section comes from the actual
source definition and its actual closed tag lookup. -/
theorem once_defined_function {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : instantiateOnce? s m (Preparation.imports as) = some (s', f, start))
    {n : Nat} {fi : FuncInst H} (hf : s'.funcs[s.funcs.length+n]? = some fi) :
    ∃ fn d, m.funcs[n]? = some fn ∧ (allocTypes m.types)[fn.type.toNat]? = some d ∧
      fi = ⟨d, f.module, .wasm fn⟩ := by
  obtain ⟨types, ht, hs⟩ := once_function_list profile run
  rw [hs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Preparation.functionInstances, List.getElem?_map] at hf
  obtain ⟨⟨d, fn⟩, hzip, heq⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨hd, hfn⟩ := List.getElem?_zip_eq_some.mp hzip
  obtain ⟨d', hd', lookup⟩ := forall₂_lookup (forall₂_of_mapM ht) hfn
  have he : d' = d := Option.some.inj (hd'.symm.trans hd)
  subst d'
  exact ⟨fn, d, hfn, lookup, heq.symm⟩

private theorem forall₂_of_lookup {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (length : xs.length = ys.length)
    (lookup : ∀ (i : Nat) (x : α), xs[i]? = some x → ∃ y, ys[i]? = some y ∧ R x y) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp length.symm
    subst ys; exact .nil
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_cons, List.length_nil] at length; omega
    | cons y ys =>
      obtain ⟨y', hy', hr⟩ := lookup 0 x rfl
      have hy : y' = y := Option.some.inj hy'.symm
      subst y'
      refine .cons hr (ih (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using length) ?_)
      intro i x' hx
      exact lookup (i+1) x' hx

theorem once_old_function {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : instantiateOnce? s m (Preparation.imports as) = some (s', f, start))
    {a : Nat} {fi : FuncInst H} (bound : a < s.funcs.length)
    (hf : s'.funcs[a]? = some fi) : s.funcs[a]? = some fi := by
  obtain ⟨_, _, hs⟩ := once_function_list profile run
  rw [hs, List.getElem?_append_left bound] at hf
  exact hf

/-- Every function address in the two actual final stores contains matching
ambient code, unchanged provider code, or the exact relocated consumer code. -/
theorem separate_linked_functions {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL)) :
    List.Forall₂ Function sc.funcs sl.funcs := by
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  have countP := (Views.once_counts w.providerProfile hp).1
  have countC := (Views.once_counts w.consumerProfile hc).1
  have countL := (Views.once_counts hprofile hm).1
  have countR : result.funcs.length = provider.funcs.length + consumer.funcs.length := by
    rw [w.output]
    simp only [List.length_append, w.providerFuncs_length, w.funcs_length]
  apply forall₂_of_lookup
  · rw [countC, countP, countL, countR, Nat.add_assoc]
  · intro a fi hf
    by_cases ambient : a < s.funcs.length
    · have oldP : a < sp.funcs.length := by omega
      have hsp := once_old_function w.consumerProfile hc oldP hf
      have hs := once_old_function w.providerProfile hp ambient hsp
      exact ⟨fi, Views.once_function_retained hprofile hm hs, .same fi⟩
    · by_cases providerPart : a < sp.funcs.length
      · have hsp := once_old_function w.consumerProfile hc providerPart hf
        have ha : s.funcs.length + (a-s.funcs.length) = a := by omega
        obtain ⟨fn, d, hfn, hd, he⟩ := once_defined_function w.providerProfile hp
          (n := a-s.funcs.length) (by simpa only [ha] using hsp)
        subst fi
        obtain ⟨_, ht, views⟩ := Functions.provider_final_binding w hl hp hc hm hfn hd
        obtain ⟨fn', _, rewrite⟩ := w.provider_func_lookup hfn
        have hid := Identity.func_identity rewrite
        subst fn'
        exact ⟨_, by simpa only [ha] using ht,
          .relocated Recipe.identity views (Functions.rewrite rewrite)⟩
      · have ha : sp.funcs.length + (a-sp.funcs.length) = a := by omega
        obtain ⟨fn, d, hfn, hd, he⟩ := once_defined_function w.consumerProfile hc
          (n := a-sp.funcs.length) (by simpa only [ha] using hf)
        subst fi
        obtain ⟨fn', _, ht, rewrite, views⟩ := Functions.consumer_binding w hl hp hc hm hfn hd
        have haddr : s.funcs.length + provider.funcs.length + (a-sp.funcs.length) = a := by omega
        exact ⟨_, by simpa only [haddr] using ht,
          .relocated (Recipe.relocation provider w.imports) views rewrite⟩

/-! ## Store fields unaffected by constant initialization -/

structure Static (source target : Store H) : Prop where
  tags : source.tags = target.tags
  mems : source.mems = target.mems
  tables : source.tables = target.tables
  datas : source.datas = target.datas
  elems : source.elems = target.elems
  exns : source.exns = target.exns

theorem Static.refl (s : Store H) : Static s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Static.symm {s t : Store H} (h : Static s t) : Static t s :=
  ⟨h.tags.symm, h.mems.symm, h.tables.symm, h.datas.symm, h.elems.symm, h.exns.symm⟩

theorem Static.trans {s t u : Store H} (h : Static s t) (h' : Static t u) : Static s u :=
  ⟨h.tags.trans h'.tags, h.mems.trans h'.mems, h.tables.trans h'.tables,
    h.datas.trans h'.datas, h.elems.trans h'.elems, h.exns.trans h'.exns⟩

private theorem structNew_static {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    (run : structNew? s f vs x = some (s', vs')) : Static s s' := by
  unfold structNew? at run
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨d, _, fs, _, ⟨pre, args⟩, _, run⟩ := run
  split at run
  · cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases run

private theorem arrayNewFixed_static {s s' : Store H} {f : Frame} {vs vs' : List Val} {x : TypeIdx}
    {n : Fin (2^32)} (run : arrayNewFixed? s f vs x n = some (s', vs')) : Static s s' := by
  unfold arrayNewFixed? at run
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  obtain ⟨d, _, ft, _, ⟨pre, args⟩, _, run⟩ := run
  split at run
  · cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases run

theorem constInstr_static {s s' : Store H} {f : Frame} {vs vs' : List Val} {i : Instr}
    (run : constInstr? s f vs i = some (s', vs')) : Static s s' := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
  all_goals first
    | (obtain ⟨rfl, _⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, run⟩ := run; first
        | (obtain ⟨rfl, _⟩ := run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
        | skip)
    | skip
  case refI31 => obtain ⟨_, _, run⟩ := run; cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  case structNew => exact structNew_static run
  case structNewDefault => obtain ⟨_, _, _, _, run⟩ := run; exact structNew_static run
  case arrayNew => obtain ⟨_, _, run⟩ := run; exact arrayNewFixed_static run
  case arrayNewDefault =>
    obtain ⟨_, _, _, _, _, _, _, _, run⟩ := run; exact arrayNewFixed_static run
  case arrayNewFixed => exact arrayNewFixed_static run
  case externConvertAny =>
    split at run
    · split at run <;> (cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
    · cases run
  case anyConvertExtern =>
    split at run
    · cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · cases run
  case intBinOp =>
    split at run
    · simp only [Option.bind_eq_some_iff] at run
      obtain ⟨_, _, _, _, _, _, run⟩ := run
      split at run
      · cases run; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases run
    · cases run

theorem constExpr_static {s s' : Store H} {f : Frame} {e : Expr} {vs : List Val}
    (run : constExpr? s f e = some (s', vs)) : Static s s' := by
  unfold constExpr? at run
  suffices ∀ (es : Expr) (st result : Store H × List Val),
      es.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 f st.2 i) st = some result →
        Static st.1 result.1 from this e (s, []) (s', vs) run
  intro es
  induction es with
  | nil =>
    intro st result run
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at run
    subst result; exact .refl _
  | cons i es ih =>
    intro st result run
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨st₁, h₁, h₂⟩ := run
    exact (constInstr_static h₁).trans (ih st₁ result h₂)

theorem evalConst_static {s s' : Store H} {f : Frame} {e : Expr} {v : Val}
    (run : evalConst? s f e = some (s', v)) : Static s s' := by
  unfold evalConst? at run
  split at run
  · rename_i source value he
    cases run; exact constExpr_static he
  · cases run

theorem evalGlobals_static {s s' : Store H} {f f' : Frame}
    {types : List CGlobalType} {es : List Expr} {vs : List Val}
    (run : evalGlobals? evalConst? s f types es = some (s', f', vs)) : Static s s' := by
  induction types generalizing s f es vs with
  | nil =>
    cases es with
    | nil => cases run; exact .refl _
    | cons => simp only [evalGlobals?, reduceCtorEq] at run
  | cons type types ih =>
    cases es with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons e es =>
      simp only [evalGlobals?] at run
      split at run
      · cases run
      · rename_i source value he
        split at run
        · cases run
        · rename_i result final values hg
          cases run
          have ha : Static source (allocGlobal source type value).1 :=
            ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          exact (evalConst_static he).trans (ha.trans (ih hg))

theorem once_static {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : instantiateOnce? s m (Preparation.imports as) = some (s', f, start)) : Static s s' := by
  obtain ⟨s₁, _, _, hg, ha, _, _⟩ := PreparationOnce.once_allocation profile run
  obtain ⟨_, _, hs⟩ := PreparationOnce.residue_store profile ha
  rw [hs]
  have stat := evalGlobals_static hg
  exact ⟨stat.tags, stat.mems, stat.tables, stat.datas, stat.elems, stat.exns⟩

/-- The complete store relation follows from actual initializer execution and
actual allocation of the separate modules and of the partial linker's output. -/
theorem separate_linked {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL)) :
    Related sc sl := by
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  have data := Initializers.separate_linked_data w hl hp hc hm
  have stat := ((once_static w.providerProfile hp).trans (once_static w.consumerProfile hc)).symm.trans
    (once_static hprofile hm)
  exact ⟨⟨stat.tags, data.globals, stat.mems, stat.tables, stat.datas, stat.elems,
    data.structs, data.arrays, stat.exns⟩, separate_linked_functions w hl hp hc hm⟩

end Silmaril.Wasm.Link.GC.StoreRelation
