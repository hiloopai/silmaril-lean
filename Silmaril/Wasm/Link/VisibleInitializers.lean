module

public import Silmaril.Wasm.Link.Initializers

/-! # Initializers with distinct global addresses

Constant evaluation observes the globals named by its frame, not every global
in the ambient store. Corresponding frame-visible globals have the same closed
type and value, while their addresses and ambient store lengths may differ.
GC objects and forward function-reference addresses still agree exactly.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.VisibleInitializers

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- Successful function and closed-type lookups agree. A visible global may
occupy a different store address in the two configurations. -/
structure Related (r : Relocation) (source target : Store H) (left right : Frame) : Prop where
  functions : ∀ {x y : FuncIdx} {a : Nat}, function? r x = some y →
    left.module.funcs[x.toNat]? = some a → right.module.funcs[y.toNat]? = some a
  types : ∀ {x y : TypeIdx} {d : DefType}, shiftIdx? r.types x = some y →
    left.module.types[x.toNat]? = some d → right.module.types[y.toNat]? = some d
  globals : ∀ {x y : GlobalIdx} {a : Nat} {g : GlobalInst}, shiftIdx? r.globals x = some y →
    source.global? left x = some (a, g) → ∃ b, target.global? right y = some (b, g)
  structs : source.structs = target.structs
  arrays : source.arrays = target.arrays

theorem Related.of_data {source target : Store H} {left right : Frame} {r : Relocation}
    (data : Initializers.Data source target)
    (views : Views.Successful r left.module right.module) : Related r source target left right :=
  ⟨views.functions, views.types,
    fun hr hg => ⟨_, data.global_lookup views hr hg⟩, data.structs, data.arrays⟩

/-- An initializer frame with no globals cannot observe extra ambient global
blocks. Function and type tables can still refer to future linked definitions. -/
theorem Related.of_empty_globals {source target : Store H} {left right : Frame} {r : Relocation}
    (views : Views.Successful r left.module right.module) (empty : left.module.globals = [])
    (structs : source.structs = target.structs) (arrays : source.arrays = target.arrays) :
    Related r source target left right := by
  refine ⟨views.functions, views.types, ?_, structs, arrays⟩
  intro x y a g rewrite lookup
  simp only [Store.global?, empty, List.getElem?_nil, Option.bind_eq_bind,
    Option.bind_none, reduceCtorEq] at lookup

theorem Related.global_lookup {source target : Store H} {left right : Frame} {r : Relocation}
    (h : Related r source target left right) {x y : GlobalIdx} {a : Nat} {g : GlobalInst}
    (rewrite : shiftIdx? r.globals x = some y)
    (lookup : source.global? left x = some (a, g)) :
    ∃ b, target.global? right y = some (b, g) := h.globals rewrite lookup

theorem type_lookup {source target : Store H} {left right : Frame} {r : Relocation}
    (h : Related r source target left right) {x y : TypeIdx} {d : DefType}
    (rewrite : shiftIdx? r.types x = some y) (lookup : left.type? x = some d) :
    right.type? y = some d := h.types rewrite lookup

theorem Related.addStruct {source target : Store H} {left right : Frame} {r : Relocation}
    (h : Related r source target left right) (v : StructInst) :
    Related r (source.addStruct v) (target.addStruct v) left right := by
  refine ⟨h.functions, h.types, ?_, by simp only [Store.addStruct, h.structs], h.arrays⟩
  intro x y a g rewrite lookup
  exact h.globals rewrite lookup

theorem Related.addArray {source target : Store H} {left right : Frame} {r : Relocation}
    (h : Related r source target left right) (v : ArrayInst) :
    Related r (source.addArray v) (target.addArray v) left right := by
  refine ⟨h.functions, h.types, ?_, h.structs, by simp only [Store.addArray, h.arrays]⟩
  intro x y a g rewrite lookup
  exact h.globals rewrite lookup

theorem structNew_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {x y : TypeIdx}
    (h : Related r source target left right)
    (hr : shiftIdx? r.types x = some y)
    (run : structNew? source left vs x = some (result, out)) :
    ∃ result', structNew? target right vs y = some (result', out) ∧ Related r result result' left right := by
  simp only [structNew?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, fs, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addStruct _⟩
    simp only [structNew?, Option.bind_eq_bind, type_lookup h hr hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.structs]
  · cases run

theorem arrayNewFixed_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {x y : TypeIdx} {n : Fin (2^32)}
    (h : Related r source target left right)
    (hr : shiftIdx? r.types x = some y)
    (run : arrayNewFixed? source left vs x n = some (result, out)) :
    ∃ result', arrayNewFixed? target right vs y n = some (result', out) ∧ Related r result result' left right := by
  simp only [arrayNewFixed?, Option.bind_eq_bind, Option.bind_eq_some_iff, Prod.exists] at run
  obtain ⟨d, hd, ft, hf, pre, args, hp, run⟩ := run
  split at run
  · rename_i hall
    cases run
    refine ⟨_, ?_, h.addArray _⟩
    simp only [arrayNewFixed?, Option.bind_eq_bind, type_lookup h hr hd, Option.bind_some, hf, hp,
      ite_eq_left hall, ← h.arrays]
  · cases run

/-- The executable evaluator runs the actual relocated constant instruction
with the same stack and result values. GC allocations have identical contents
and addresses, even when the stores contain different function instances. -/
theorem instruction_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {i i' : Instr}
    (h : Related r source target left right)
    (rewrite : instruction? r i = some i')
    (run : constInstr? source left vs i = some (result, out)) :
    ∃ result', constInstr? target right vs i' = some (result', out) ∧ Related r result result' left right := by
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
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, h.functions hy ha, Option.bind_some], h⟩
  case refI31 =>
    subst i'
    obtain ⟨pre, v, hp, b, hb, run⟩ := run
    cases run
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hb], h⟩
  case globalGet x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨a, g, hg, run⟩ := run
    cases run
    obtain ⟨b, targetGlobal⟩ := h.global_lookup hy hg
    exact ⟨target, by simp only [constInstr?, Option.bind_eq_bind, targetGlobal,
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
    exact structNew_transport h hy run
  case structNewDefault x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨d, hd, fs, hf, dvs, hv, run⟩ := run
    obtain ⟨result', ht, data⟩ := structNew_transport h hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, type_lookup h hy hd,
      Option.bind_some, hf, hv]; exact ht, data⟩
  case arrayNew x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨pre, v, nv, hp, n, hn, run⟩ := run
    obtain ⟨result', ht, data⟩ := arrayNewFixed_transport h hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn]; exact ht, data⟩
  case arrayNewDefault x =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    obtain ⟨pre, nv, hp, n, hn, d, hd, ft, hf, v, hv, run⟩ := run
    obtain ⟨result', ht, data⟩ := arrayNewFixed_transport h hy run
    exact ⟨result', by simp only [constInstr?, Option.bind_eq_bind, hp, Option.bind_some, hn,
      type_lookup h hy hd, hf, hv]; exact ht, data⟩
  case arrayNewFixed x n =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact arrayNewFixed_transport h hy run

theorem fold_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {vs out : List Val} {e e' : Expr}
    (h : Related r source target left right)
    (rewrite : instructions? r e = some e')
    (run : e.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 left st.2 i)
      (source, vs) = some (result, out)) :
    ∃ result',
      e'.foldlM (fun (st : Store H × List Val) i => constInstr? st.1 right st.2 i)
        (target, vs) = some (result', out) ∧ Related r result result' left right := by
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
    obtain ⟨target₁, ht₁, data₁⟩ := instruction_transport h hi h₁
    obtain ⟨result', ht₂, data₂⟩ := ih data₁ h₂
    exact ⟨result', by simp only [List.foldlM_cons, Option.bind_eq_bind, ht₁,
      Option.bind_some]; exact ht₂, data₂⟩

theorem expression_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {out : List Val} {e e' : Expr}
    (h : Related r source target left right)
    (rewrite : instructions? r e = some e')
    (run : constExpr? source left e = some (result, out)) :
    ∃ result', constExpr? target right e' = some (result', out) ∧ Related r result result' left right :=
  fold_transport h rewrite run

/-- Actual relocated initializer evaluation yields exactly the original value,
with equal frame-visible globals and GC data. This requires no premise about preserving
execution: the proof follows `constInstr?` and its fold. -/
theorem constant_transport {source target result : Store H} {left right : Frame}
    {r : Relocation} {value : Val} {e e' : Expr}
    (h : Related r source target left right)
    (rewrite : instructions? r e = some e')
    (run : evalConst? source left e = some (result, value)) :
    ∃ result', evalConst? target right e' = some (result', value) ∧ Related r result result' left right := by
  unfold evalConst? at run
  split at run
  · rename_i source' value' hc
    cases run
    obtain ⟨result', ht, data⟩ := expression_transport h rewrite hc
    exact ⟨result', by simp only [evalConst?, ht], data⟩
  · cases run


/-- Every source frame-visible address already denotes a stored global.
This excludes a dangling old address becoming live at the next allocation. -/
def Bounded (s : Store H) (f : Frame) : Prop :=
  ∀ a ∈ f.module.globals, a < s.globals.length

theorem Bounded.empty {s : Store H} {f : Frame} (empty : f.module.globals = []) :
    Bounded s f := by
  intro a member
  simp only [empty, List.not_mem_nil] at member

/-- Appending globals outside a bounded source frame's visible addresses leaves
its observations unchanged. This includes ordinary allocation's copied block. -/
theorem Related.source_globals_append {source target : Store H} {left right : Frame}
    {r : Relocation} (h : Related r source target left right) (bounded : Bounded source left)
    (extra : List GlobalInst) :
    Related r {source with globals := source.globals ++ extra} target left right := by
  refine ⟨h.functions, h.types, ?_, h.structs, h.arrays⟩
  intro x y a g rewrite lookup
  simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at lookup
  obtain ⟨a', index, g', stored, addressEq, globalEq⟩ := lookup
  subst a'
  subst g'
  have addressBound := bounded a (List.mem_of_getElem? index)
  rw [List.getElem?_append_left addressBound] at stored
  apply h.globals (a := a) rewrite
  simp only [Store.global?, Option.bind_eq_bind, index, Option.bind_some, stored, Option.pure_def]

theorem Bounded.constant {source result : Store H} {left : Frame} {e : Expr} {v : Val}
    (bounded : Bounded source left) (run : evalConst? source left e = some (result, v)) :
    Bounded result left := by
  intro a member
  rw [(evalConst?_shape run).1]
  exact bounded a member

theorem Bounded.allocGlobal {source : Store H} {left : Frame}
    (bounded : Bounded source left) (type : CGlobalType) (value : Val) :
    Bounded (allocGlobal source type value).1
      {left with module := {left.module with
        globals := left.module.globals ++ [(allocGlobal source type value).2]}} := by
  intro a member
  simp only [Execution.Core.allocGlobal, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · have bound := bounded a member
    simpa only [Execution.Core.allocGlobal, List.length_append, List.length_singleton] using
      (show a < source.globals.length + 1 by omega)
  · simp only [Execution.Core.allocGlobal, List.length_append, List.length_singleton]
    omega

/-- Each frame records its own fresh address. The addresses may differ because
one ambient store contains additional invisible globals. -/
theorem Related.allocGlobal {source target : Store H} {left right : Frame} {r : Relocation}
    (h : Related r source target left right) (bounded : Bounded source left)
    (length : right.module.globals.length = r.globals + left.module.globals.length)
    (type : CGlobalType) (value : Val) :
    Related r (allocGlobal source type value).1 (allocGlobal target type value).1
      {left with module := {left.module with
        globals := left.module.globals ++ [(allocGlobal source type value).2]}}
      {right with module := {right.module with
        globals := right.module.globals ++ [(allocGlobal target type value).2]}} := by
  refine ⟨h.functions, h.types, ?_, h.structs, h.arrays⟩
  intro x y a g rewrite lookup
  have hy := LinkExecution.shiftIdx?_toNat rewrite
  simp only [Store.global?, Execution.Core.allocGlobal, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, Prod.mk.injEq] at lookup
  obtain ⟨a', index, g', stored, addressEq, globalEq⟩ := lookup
  subst a'
  subst g'
  by_cases old : x.toNat < left.module.globals.length
  · rw [List.getElem?_append_left old] at index
    have addressBound := bounded a (List.mem_of_getElem? index)
    rw [List.getElem?_append_left addressBound] at stored
    have sourceLookup : source.global? left x = some (a, g) := by
      simp only [Store.global?, Option.bind_eq_bind, index, Option.bind_some, stored,
        Option.pure_def]
    obtain ⟨b, targetLookup⟩ := h.globals rewrite sourceLookup
    simp only [Store.global?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq, Prod.mk.injEq] at targetLookup
    obtain ⟨b', targetIndex, g', targetStored, addressEq, globalEq⟩ := targetLookup
    subst b'
    subst g'
    have targetBound := (List.getElem?_eq_some_iff.mp targetStored).1
    refine ⟨b, ?_⟩
    simp only [Store.global?, Execution.Core.allocGlobal,
      List.getElem?_append_left (by omega : y.toNat < right.module.globals.length),
      targetIndex, Option.bind_eq_bind, Option.bind_some,
      List.getElem?_append_left targetBound, targetStored, Option.pure_def]
  · have after : left.module.globals.length ≤ x.toNat := by omega
    rw [List.getElem?_append_right after] at index
    have bound := (List.getElem?_eq_some_iff.mp index).1
    have atFresh : x.toNat = left.module.globals.length := by
      simp only [List.length_singleton] at bound
      omega
    rw [atFresh, Nat.sub_self] at index
    simp only [List.getElem?_cons_zero, Option.some.injEq] at index
    subst a
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at stored
    simp only [List.getElem?_cons_zero, Option.some.injEq] at stored
    subst g
    have targetFresh : y.toNat = right.module.globals.length := by omega
    refine ⟨target.globals.length, ?_⟩
    simp only [Store.global?, Execution.Core.allocGlobal, targetFresh,
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

/-- Sequential initialization preserves exact visible values and GC heaps even
when each store allocates its globals at different fresh addresses. -/
theorem globals_transport {source target result : Store H} {left right final : Frame}
    {r : Relocation} {values : List Val} {types : List CGlobalType} {es es' : List Expr}
    (h : Related r source target left right) (bounded : Bounded source left)
    (length : right.module.globals.length = r.globals + left.module.globals.length)
    (rewrite : List.Forall₂ (fun e e' => instructions? r e = some e') es es')
    (run : evalGlobals? evalConst? source left types es = some (result, final, values)) :
    ∃ result' final',
      evalGlobals? evalConst? target right types es' = some (result', final', values) ∧
      Related r result result' final final' ∧ Bounded result final ∧
      final'.module.globals.length = r.globals + final.module.globals.length := by
  induction rewrite generalizing types source target left right values with
  | nil =>
    cases types with
    | nil =>
      simp only [evalGlobals?, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      exact ⟨target, right, rfl, h, bounded, length⟩
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
          obtain ⟨target₁, ht, related₁⟩ := constant_transport h he hv
          have bounded₁ := bounded.constant hv
          have related₂ := related₁.allocGlobal bounded₁ length type value
          have bounded₂ := bounded₁.allocGlobal type value
          have length₁ : (right.module.globals ++ [(allocGlobal target₁ type value).2]).length =
              r.globals + (left.module.globals ++ [(allocGlobal source₁ type value).2]).length := by
            simp only [List.length_append, List.length_singleton]
            omega
          obtain ⟨result', final', hrun, related₃, bounded₃, length₂⟩ :=
            ih related₂ bounded₂ length₁ hg
          exact ⟨result', final', by simp only [evalGlobals?, ht, hrun],
            related₃, bounded₃, length₂⟩

end Silmaril.Wasm.Link.GC.VisibleInitializers
