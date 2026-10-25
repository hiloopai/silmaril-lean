module

public import Silmaril.Wasm.Link.Views
public import Silmaril.Wasm.Link.Identity

/-! # Constant initializer transport under static linking

Constant evaluation reads module index tables, globals and closed GC tags. It
does not read stored function bodies: separately allocating provider functions
before consumer initialization can therefore differ from linked initialization.
The relation below compares the data used by the actual constant evaluator.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Initializers

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The store fields observed or extended by constant evaluation. Function
instances may already have been allocated in only one store. -/
structure Data (source target : Store H) : Prop where
  globals : source.globals = target.globals
  structs : source.structs = target.structs
  arrays : source.arrays = target.arrays

theorem Data.refl (s : Store H) : Data s s := ⟨rfl, rfl, rfl⟩

theorem Data.symm {s t : Store H} (h : Data s t) : Data t s :=
  ⟨h.globals.symm, h.structs.symm, h.arrays.symm⟩

theorem Data.trans {s t u : Store H} (h : Data s t) (h' : Data t u) : Data s u :=
  ⟨h.globals.trans h'.globals, h.structs.trans h'.structs, h.arrays.trans h'.arrays⟩

theorem Data.addStruct {source target : Store H} (h : Data source target) (v : StructInst) :
    Data (source.addStruct v) (target.addStruct v) := by
  exact ⟨h.globals, by simp only [Store.addStruct, h.structs], h.arrays⟩

theorem Data.addArray {source target : Store H} (h : Data source target) (v : ArrayInst) :
    Data (source.addArray v) (target.addArray v) := by
  exact ⟨h.globals, h.structs, by simp only [Store.addArray, h.arrays]⟩

theorem Data.global_lookup {source target : Store H} {left right : Frame}
    {r : Relocation} (h : Data source target)
    (views : Views.Successful r left.module right.module)
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst}
    (hr : shiftIdx? r.globals x = some y)
    (hg : source.global? left x = some (a, g)) :
    target.global? right y = some (a, g) := by
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨a', ha, g', hg, rfl, rfl⟩ := hg
  simp only [Store.global?, views.globals hr ha, Option.bind_eq_bind, Option.bind_some, ← h.globals, hg, Option.pure_def]

theorem type_lookup {left right : Frame} {r : Relocation}
    (views : Views.Successful r left.module right.module)
    {x y : TypeIdx} {d : DefType} (hr : shiftIdx? r.types x = some y)
    (hd : left.type? x = some d) : right.type? y = some d :=
  views.types hr hd

theorem structNew_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {x y : TypeIdx}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (hr : shiftIdx? r.types x = some y)
    (run : structNew? source left vs x = some (result, out)) :
    ∃ result', structNew? target right vs y = some (result', out) ∧ Data result result' := by
  simp only [structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addStruct _⟩
    simp only [structNew?, Option.bind_eq_bind, type_lookup views hr hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.structs]
  · cases run

theorem arrayNewFixed_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {x y : TypeIdx} {n : Fin (2^32)}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (hr : shiftIdx? r.types x = some y)
    (run : arrayNewFixed? source left vs x n = some (result, out)) :
    ∃ result', arrayNewFixed? target right vs y n = some (result', out) ∧ Data result result' := by
  simp only [arrayNewFixed?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addArray _⟩
    simp only [arrayNewFixed?, Option.bind_eq_bind, type_lookup views hr hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.arrays]
  · cases run

/-- The executable evaluator runs the actual relocated constant instruction
with the same stack and result values. GC allocations have identical contents
and addresses, even when the stores contain different function instances. -/
theorem instruction_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {i i' : Instr}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (rewrite : instruction? r i = some i')
    (run : constInstr? source left vs i = some (result, out)) :
    ∃ result', constInstr? target right vs i' = some (result', out) ∧ Data result result' := by
  cases i <;> simp only [constInstr?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    reduceCtorEq, Prod.exists] at run
  all_goals simp only [instruction?, Option.map_eq_map, Option.map_eq_some_iff,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at rewrite
  case vecConst => cases rewrite
  case intConst t x =>
    subst i'; cases run; exact ⟨target, rfl, h⟩
  case floatConst t x =>
    subst i'; cases run; exact ⟨target, rfl, h⟩
  case refNull ht =>
    obtain ⟨ht', _, rfl⟩ := rewrite
    cases run; exact ⟨target, rfl, h⟩
  case refFunc x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨a, ha, run⟩ := run
    cases run
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, views.functions hy ha, Option.bind_some], h⟩
  case refI31 =>
    subst i'
    obtain ⟨pre, v, hp, b, hb, run⟩ := run
    cases run
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hb], h⟩
  case globalGet x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨a, g, hg, run⟩ := run
    cases run
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, h.global_lookup views hy hg,
      Option.bind_some], h⟩
  case intBinOp t op =>
    subst i'
    split at run
    · rename_i hop
      simp only [Option.bind_eq_some_iff, Prod.exists] at run
      obtain ⟨pre, v₁, v₂, hp, x, hx, y, hy, run⟩ := run
      split at run
      · rename_i z hz
        cases run
        exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, ite_eq_left hop, hp, Option.bind_some,
          hx, hy, hz], h⟩
      · cases run
    · cases run
  case anyConvertExtern =>
    subst i'
    obtain ⟨pre, v, hp, run⟩ := run
    split at run
    · cases run
      exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some], h⟩
    · cases run
      exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some], h⟩
    · cases run
  case externConvertAny =>
    subst i'
    obtain ⟨pre, v, hp, run⟩ := run
    split at run
    · split at run
      · cases run
        exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]; split <;> simp_all, h⟩
      · cases run
        exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some]; split <;> simp_all, h⟩
    · cases run
  case structNew x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact structNew_transport h views hy run
  case structNewDefault x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
    obtain ⟨result', ht, data⟩ := structNew_transport h views hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, type_lookup views hy hd,
      Option.bind_some, hf, hv]; exact ht, data⟩
  case arrayNew x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨pre, v, nv, hp, n, hn, run⟩ := run
    obtain ⟨result', ht, data⟩ := arrayNewFixed_transport h views hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn]; exact ht, data⟩
  case arrayNewDefault x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
    obtain ⟨result', ht, data⟩ := arrayNewFixed_transport h views hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn,
      type_lookup views hy hd, hf, hv]; exact ht, data⟩
  case arrayNewFixed x n =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact arrayNewFixed_transport h views hy run

theorem fold_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {e e' : Expr}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (rewrite : instructions? r e = some e')
    (run : e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 left st.2 i)
      (source, vs) = some (result, out)) :
    ∃ result',
      e'.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 right st.2 i)
        (target, vs) = some (result', out) ∧ Data result result' := by
  have hr := List.mapM_some_forall₂ (R := fun i i' => instruction? r i = some i')
    (fun h => h) rewrite
  clear rewrite
  induction hr generalizing source target vs with
  | nil =>
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, rfl, h⟩
  | cons hi _ ih =>
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨source₁, vs₁⟩, h₁, h₂⟩ := run
    obtain ⟨target₁, ht₁, data₁⟩ := instruction_transport h views hi h₁
    obtain ⟨result', ht₂, data₂⟩ := ih data₁ h₂
    exact ⟨result', by simp only [List.foldlM_cons, Option.bind_eq_bind, ht₁,
      Option.bind_some]; exact ht₂, data₂⟩

theorem expression_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {out : List Val} {e e' : Expr}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (rewrite : instructions? r e = some e')
    (run : constExpr? source left e = some (result, out)) :
    ∃ result', constExpr? target right e' = some (result', out) ∧ Data result result' :=
  fold_transport h views rewrite run

/-- Actual relocated initializer evaluation yields exactly the original value,
with equal global and GC data. This requires no premise about preserving
execution: the proof follows `constInstr?` and its fold. -/
theorem constant_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {value : Val} {e e' : Expr}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (rewrite : instructions? r e = some e')
    (run : evalConst? source left e = some (result, value)) :
    ∃ result', evalConst? target right e' = some (result', value) ∧ Data result result' := by
  unfold evalConst? at run
  split at run
  · rename_i source' value' hc
    cases run
    obtain ⟨result', ht, data⟩ := expression_transport h views rewrite hc
    exact ⟨result', by simp only [evalConst?, ht], data⟩
  · cases run

theorem Data.allocGlobal {source target : Store H} (h : Data source target)
    (type : CGlobalType) (value : Val) :
    Data (allocGlobal source type value).1 (allocGlobal target type value).1 :=
  ⟨congrArg (fun xs : List GlobalInst => xs ++ [GlobalInst.mk type value]) h.globals, h.structs, h.arrays⟩

/-- Extending both initializer frames with the same newly allocated global
preserves relocation. The linked frame already contains the provider prefix. -/
theorem append_global {source target : ModuleInst} {r : Relocation}
    (views : Views.Successful r source target)
    (length : target.globals.length = r.globals + source.globals.length) (a : Nat) :
    Views.Successful r
      {source with globals := source.globals ++ [a]}
      {target with globals := target.globals ++ [a]} := by
  refine ⟨views.functions, ?_, views.types⟩
  intro x y b hr hx
  have hy := LinkExecution.shiftIdx?_toNat hr
  by_cases hi : x.toNat < source.globals.length
  · rw [List.getElem?_append_left hi] at hx
    rw [List.getElem?_append_left (by omega : y.toNat < target.globals.length)]
    exact views.globals hr hx
  · have hge : source.globals.length ≤ x.toNat := Nat.le_of_not_gt hi
    rw [List.getElem?_append_right hge] at hx
    have hb := (List.getElem?_eq_some_iff.mp hx).1
    have he : x.toNat = source.globals.length := by simp only [List.length_singleton] at hb; omega
    rw [he, Nat.sub_self] at hx
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
    subst b
    rw [hy, he, ← length, List.getElem?_append_right (by omega), Nat.sub_self]
    rfl

/-- Sequential initialization transports every actual relocated expression,
including reads of preceding globals, with equal values and equal GC data. -/
theorem globals_transport {source target result : Store H} {left right final : Frame}
    {r : Relocation} {values : List Val} {types : List CGlobalType} {es es' : List Expr}
    (h : Data source target) (views : Views.Successful r left.module right.module)
    (length : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : List.Forall₂ (fun e e' => instructions? r e = some e') es es')
    (run : evalGlobals? evalConst? source left types es = some (result, final, values)) :
    ∃ result' final',
      evalGlobals? evalConst? target right types es' = some (result', final', values) ∧
      Data result result' ∧ Views.Successful r final.module final'.module ∧
      final'.module.globals.length = r.globals + final.module.globals.length := by
  induction rewrite generalizing types source target left right values with
  | nil =>
    cases types with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨target, right, rfl, h, views, length⟩
    | cons => simp only [evalGlobals?, reduceCtorEq] at run
  | @cons e e' es es' he _ ih =>
    cases types with
    | nil => simp only [evalGlobals?, reduceCtorEq] at run
    | cons type types =>
      simp only [evalGlobals?] at run
      split at run
      · cases run
      · rename_i source₁ value hv
        split at run
        · cases run
        · rename_i result₁ final₁ values₁ hg
          cases run
          obtain ⟨target₁, ht, data₁⟩ := constant_transport h views he hv
          have ha : (allocGlobal source₁ type value).2 = (allocGlobal target₁ type value).2 :=
            congrArg List.length data₁.globals
          have views₁ := append_global views length (allocGlobal source₁ type value).2
          have length₁ : (right.module.globals ++ [(allocGlobal target₁ type value).2]).length =
              r.globals + (left.module.globals ++ [(allocGlobal source₁ type value).2]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          obtain ⟨result', final', hrun, data₂, views₂, length₂⟩ :=
            ih (right := { right with module := { right.module with
              globals := right.module.globals ++ [(allocGlobal target₁ type value).2] } })
              (data₁.allocGlobal type value) (by simpa only [ha] using views₁) length₁ hg
          exact ⟨result', final', by simp only [evalGlobals?, ht, hrun], data₂, views₂, length₂⟩

/-- Successful type lookups and source scoping suffice to preserve a closed
value type. The linked type table may contain an additional provider prefix. -/
theorem closed_value_type {left right : ModuleInst} {r : Relocation} {v v' : ValType}
    (views : Views.Successful r left right) (rewrite : valType? r.types v = some v')
    (scope : ∀ x ∈ (liftVal v).freeIdx, x < left.types.length) :
    right.instVal v' = left.instVal v := by
  cases v with
  | num n =>
    simp only [valType?, Option.some.injEq] at rewrite
    subst v'; rfl
  | vec n =>
    simp only [valType?, Option.some.injEq] at rewrite
    subst v'; rfl
  | ref ref =>
    rcases ref with ⟨nullable, heap⟩
    cases heap with
    | abstract a =>
      simp only [valType?, refType?, heap?, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.map_eq_map, Option.map_some, Option.some.injEq] at rewrite
      subst v'; cases a <;> rfl
    | typeIdx x =>
      simp only [valType?, refType?, heap?, Option.bind_eq_bind, Option.map_eq_map,
        Option.map_eq_some_iff, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at rewrite
      obtain ⟨ref', ⟨heap', ⟨y, hy, rfl⟩, rfl⟩, rfl⟩ := rewrite
      have hx : x.toNat < left.types.length := scope x.toNat (by simp [liftVal, liftRef,
        liftHeap, liftTypeIdx, Ty.freeIdx])
      have hd := List.getElem?_eq_getElem hx
      simp only [ModuleInst.instVal, liftVal, liftRef, liftHeap, liftTypeIdx,
        Ty.substAll, Ty.subst, Subst.all, List.getElem?_map, hd,
        views.types hy hd, Option.map_some, Option.getD_some]

/-- Source rewriting retains mutability and gives the exact relocated
initializer expression and declared value type. -/
theorem global_rewrite {r : Relocation} {source target : Global}
    (rewrite : global? r source = some target) :
    source.type.mutability = target.type.mutability ∧
      valType? r.types source.type.value = some target.type.value ∧
      instructions? r source.init = some target.init := by
  simp only [global?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at rewrite
  obtain ⟨type, ht, init, hi, rfl⟩ := rewrite
  exact ⟨rfl, ht, hi⟩

theorem closed_global_type {left right : ModuleInst} {r : Relocation} {source target : Global}
    (views : Views.Successful r left right) (rewrite : global? r source = some target)
    (scope : ∀ x ∈ (liftVal source.type.value).freeIdx, x < left.types.length) :
    (⟨target.type.mutability, right.instVal target.type.value⟩ : CGlobalType) =
      ⟨source.type.mutability, left.instVal source.type.value⟩ := by
  obtain ⟨hmut, htype, _⟩ := global_rewrite rewrite
  rw [← hmut, closed_value_type views htype scope]

/-- Validation of a closed global declaration excludes unallocated source
type indices, even before its initializer has run. -/
theorem global_type_scope {C : Context} {g : Global} {gt : CGlobalType}
    (valid : GlobalOk C g gt) :
    ∀ x ∈ (liftVal g.type.value).freeIdx, x < C.types.length := by
  obtain ⟨rfl, hv, _⟩ := valid
  intro x hx
  by_contra hn
  have hg : C.types[x]? = none := List.getElem?_eq_none (by omega)
  have hs : Subst.all (C.types.map .dt) (.idx x) = none := by
    simp only [Subst.all, List.getElem?_map, hg, Option.map_none]
  exact hn (TyOk.freeIdx_lt hv x (Ty.freeIdx_subst_of_none _ _ x hx hs))

theorem globals_scope {C : Context} {gs : List Global} {gts : List CGlobalType}
    (valid : GlobalsOk C gs gts) :
    ∀ g ∈ gs, ∀ x ∈ (liftVal g.type.value).freeIdx, x < C.types.length := by
  induction valid with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | @cons C g gs gt gts hg _ ih =>
    intro g' hmem
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact global_type_scope hg
    · exact ih g' hmem

theorem module_globals_scope {m : Module} {mt : CModuleType} (valid : ModuleOk m mt) :
    ∀ g ∈ m.globals, ∀ x ∈ (liftVal g.type.value).freeIdx, x < (allocTypes m.types).length := by
  cases valid with
  | mk ht hi hc' hc htags hg hmems htables hfuncs hdata helems hstart hexports hdisjoint =>
    rw [allocTypes_eq ht]
    simpa only [hc'] using globals_scope hg

/-- Closing a list of declarations against the module's actual tag table. -/
def closedTypes (m : ModuleInst) (gs : List Global) : List CGlobalType :=
  gs.map fun g => ⟨g.type.mutability, m.instVal g.type.value⟩

theorem closed_types_rewrite {left right : ModuleInst} {r : Relocation}
    {source target : List Global} (views : Views.Successful r left right)
    (scope : ∀ g ∈ source, ∀ x ∈ (liftVal g.type.value).freeIdx, x < left.types.length)
    (rewrite : source.mapM (global? r) = some target) :
    closedTypes right target = closedTypes left source := by
  have hr := List.mapM_some_forall₂ (R := fun g g' => global? r g = some g')
    (fun h => h) rewrite
  clear rewrite
  induction hr with
  | nil => rfl
  | @cons g g' gs gs' hg _ ih =>
    simp only [closedTypes, List.map_cons]
    rw [closed_global_type views hg (scope g (by simp))]
    exact congrArg (_ :: ·) (ih (fun g hmem => scope g (by simp [hmem])))

theorem initializer_rewrite {r : Relocation} {source target : List Global}
    (rewrite : source.mapM (global? r) = some target) :
    List.Forall₂ (fun e e' => instructions? r e = some e')
      (source.map Global.init) (target.map Global.init) := by
  have hr := List.mapM_some_forall₂ (R := fun g g' => global? r g = some g')
    (fun h => h) rewrite
  clear rewrite
  induction hr with
  | nil => exact .nil
  | cons hg _ ih => exact .cons (global_rewrite hg).2.2 ih

/-- The actual linked module closes its global declarations to the original
provider tags followed by the original consumer tags. -/
theorem link_closed_global_types {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result) :
    Module.closedGlobalTypes result =
      Module.closedGlobalTypes provider ++ Module.closedGlobalTypes consumer := by
  let leftP : ModuleInst := { types := allocTypes provider.types }
  let leftC : ModuleInst := { types := allocTypes consumer.types }
  let right : ModuleInst := { types := allocTypes result.types }
  have viewsP : Views.Successful Recipe.identity leftP right := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y a hr hx; simp [leftP] at hx
    · intro x y a hr hx; simp [leftP] at hx
    · intro x y d hr hx
      have hy : x = y := Option.some.inj ((Identity.shift_zero x).symm.trans hr)
      subst y
      exact Allocation.link?_provider_type_lookup hl hx
  have viewsC : Views.Successful (Recipe.relocation provider w.imports) leftC right := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y a hr hx; simp [leftC] at hx
    · intro x y a hr hx; simp [leftC] at hx
    · intro x y d hr hx
      exact (Allocation.link?_consumer_type_lookup hl hr).trans hx
  have hp := closed_types_rewrite viewsP
    (module_globals_scope (validate?_sound w.providerValidation)) w.providerGlobalsRewrite
  have hc := closed_types_rewrite viewsC
    (module_globals_scope (validate?_sound w.consumerValidation)) w.globalsRewrite
  change closedTypes right result.globals = closedTypes leftP provider.globals ++
    closedTypes leftC consumer.globals
  rw [w.output]
  simp only [closedTypes, List.map_append] at hp hc ⊢
  rw [hp, hc]

theorem initial_tables {s s' : Store H} {m : Module} {as : List Nat}
    {f : Frame} {start : Option FuncIdx} (profile : inProfile m = true)
    (run : instantiateOnce? s m (Preparation.imports as) = some (s', f, start)) :
    (ModuleInst.initial s m (Preparation.imports as)).funcs = f.module.funcs ∧
      (ModuleInst.initial s m (Preparation.imports as)).types = f.module.types := by
  rw [Views.once_functions profile run, PreparationOnce.once_types profile run]
  simp only [ModuleInst.initial, Preparation.imports_funcs, Preparation.addresses,
    and_self]

theorem empty_globals_views {source target left right : ModuleInst} {r : Relocation}
    (views : Views.Successful r source target) (lf : left.funcs = source.funcs)
    (rf : right.funcs = target.funcs) (lt : left.types = source.types)
    (rt : right.types = target.types) (lg : left.globals = []) :
    Views.Successful r left right := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y a hr hx; rw [lf] at hx; rw [rf]; exact views.functions hr hx
  · intro x y a hr hx; simp only [lg, List.getElem?_nil, reduceCtorEq] at hx
  · intro x y d hr hx; rw [lt] at hx; rw [rt]; exact views.types hr hx

theorem residue_data {s s₁ s' : Store H} {m : Module} {as : List Nat} {mi : ModuleInst}
    (profile : inProfile m = true)
    (run : allocModule? s₁ m.globalResidue (PreparationOnce.residueImports s m as)
      [] [] [] = some (s', mi)) : Data s₁ s' := by
  obtain ⟨_, _, hs⟩ := PreparationOnce.residue_store profile run
  rw [hs]
  exact ⟨rfl, rfl, rfl⟩

/-- Sequential global initialization is the actual evaluator's concatenated
run, including its evolving frame and GC store. -/
theorem globals_append {s s₁ s₂ : Store H} {f f₁ f₂ : Frame}
    {types₁ types₂ : List CGlobalType} {es₁ es₂ : List Expr} {values₁ values₂ : List Val}
    (first : evalGlobals? evalConst? s f types₁ es₁ = some (s₁, f₁, values₁))
    (second : evalGlobals? evalConst? s₁ f₁ types₂ es₂ = some (s₂, f₂, values₂)) :
    evalGlobals? evalConst? s f (types₁ ++ types₂) (es₁ ++ es₂) =
      some (s₂, f₂, values₁ ++ values₂) := by
  induction types₁ generalizing s f es₁ values₁ with
  | nil =>
    cases es₁ with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at first
      obtain ⟨rfl, rfl, rfl⟩ := first
      exact second
    | cons => simp only [evalGlobals?, reduceCtorEq] at first
  | cons type types ih =>
    cases es₁ with
    | nil => simp only [evalGlobals?, reduceCtorEq] at first
    | cons e es =>
      simp only [evalGlobals?] at first
      split at first
      · cases first
      · rename_i source value he
        split at first
        · cases first
        · rename_i result final values hg
          cases first
          simp only [List.cons_append, evalGlobals?, he, ih hg]

/-- Actual separate provider/consumer instantiation and actual instantiation
of the linker's output allocate identical globals and GC objects. Stored
function definitions may differ because their module views and code relocate. -/
theorem separate_linked_data {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (Preparation.imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat))) =
        some (sc, fc, startC))
    (hm : instantiateOnce? s result (Preparation.imports []) = some (sl, fl, startL)) :
    Data sc sl := by
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  obtain ⟨sP, fP, vsP, hgp, hap, _, _⟩ := PreparationOnce.once_allocation w.providerProfile hp
  obtain ⟨sC, fC, vsC, hgc, hac, _, _⟩ := PreparationOnce.once_allocation w.consumerProfile hc
  obtain ⟨sL, fL, vsL, hgl, hal, _, _⟩ := PreparationOnce.once_allocation hprofile hm
  have tablesP := initial_tables w.providerProfile hp
  have tablesC := initial_tables w.consumerProfile hc
  have tablesL := initial_tables hprofile hm
  have viewP := empty_globals_views (Views.provider w hl hp hm)
    tablesP.1 tablesL.1 tablesP.2 tablesL.2
    (Preparation.imports_globals [])
  have rewriteP := initializer_rewrite w.providerGlobalsRewrite
  rw [Identity.provider_globals w] at rewriteP
  obtain ⟨targetP, frameP, htp, dataP, _, _⟩ :=
    globals_transport (right := ⟨[], ModuleInst.initial s result (Preparation.imports [])⟩)
      (Data.refl s) viewP
      (by simp only [ModuleInst.initial, Preparation.imports_globals, Recipe.identity,
        List.length_nil, Nat.zero_add]) rewriteP hgp
  have shapeP := (evalGlobals?_shape htp).2.2
  have funcsP : frameP.module.funcs = fl.module.funcs := by rw [shapeP]; exact tablesL.1
  have typesP : frameP.module.types = fl.module.types := by rw [shapeP]; exact tablesL.2
  have viewC := empty_globals_views (Views.consumer w hl hp hc hm)
    tablesC.1 funcsP tablesC.2 typesP
    (Preparation.imports_globals (w.imports.map (fun (f : FuncIdx) => s.funcs.length+f.toNat)))
  have lengthC : frameP.module.globals.length =
      (Recipe.relocation provider w.imports).globals +
        (ModuleInst.initial sp consumer
          (Preparation.imports (w.imports.map (fun f => s.funcs.length+f.toNat)))).globals.length := by
    rw [shapeP]
    simp only [ModuleInst.initial, Preparation.imports_globals, List.nil_append,
      List.length_map, List.length_range, Module.closedGlobalTypes, Recipe.relocation,
      List.length_nil, Nat.add_zero]
  have dataInputC : Data sp targetP := (residue_data w.providerProfile hap).symm.trans dataP
  obtain ⟨targetC, frameC, htc, dataC, _, _⟩ :=
    globals_transport (right := frameP) dataInputC viewC lengthC (initializer_rewrite w.globalsRewrite) hgc
  have hinits : result.globals.map Global.init =
      provider.globals.map Global.init ++ w.globals.map Global.init := by
    have hg : result.globals = w.providerGlobals ++ w.globals := congrArg Module.globals w.output
    rw [hg, Identity.provider_globals w, List.map_append]
  have hmerged : evalGlobals? evalConst? s
      ⟨[], ModuleInst.initial s result (Preparation.imports [])⟩
      (Module.closedGlobalTypes result) (result.globals.map Global.init) =
        some (targetC, frameC, vsP ++ vsC) := by
    rw [link_closed_global_types w hl, hinits]
    exact globals_append htp htc
  have hstore : targetC = sL := congrArg Prod.fst (Option.some.inj (hmerged.symm.trans hgl))
  have dataL := residue_data hprofile hal
  rw [← hstore] at dataL
  exact (residue_data w.consumerProfile hac).symm.trans (dataC.trans dataL)

end Silmaril.Wasm.Link.GC.Initializers
