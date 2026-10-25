module

public import Silmaril.Wasm.Link.ControlInversion

/-! # Aggregate reductions across linked stores

Structures and arrays retain their runtime addresses and closed tags. Matching
allocations and field updates preserve the store relation, including the actual
forward and backward unrolling of array copies.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.AggregateSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

open AdminRelation

private theorem values_instruction {mode : Mode} {left right : ModuleInst}
    {vs : List Val} {i : Instr} {code : List Admin}
    (nonvalue : (Admin.plain i).val? = none)
    (h : Control mode left right (vals vs ++ [.plain i]) code)
    (nonthrow : i ≠ .throwRef := by intro h; cases h) :
    ∃ j, code = vals vs ++ [.plain j] ∧ Instruction mode i j :=
  h.values_instruction nonvalue nonthrow

private theorem type_same {left right : Frame} (modules : left.module = right.module)
    {x : TypeIdx} {d : DefType} (hd : left.type? x = some d) :
    right.type? x = some d := by
  simpa only [Frame.type?, modules] using hd

private theorem elem_same {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : ElemIdx} {a : Nat} {e : ElemInst} (he : source.elem? left x = some (a, e)) :
    target.elem? right x = some (a, e) := by
  simpa only [Store.elem?, modules, stores.elems] using he

private theorem data_same {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : DataIdx} {a : Nat} {d : DataInst} (hd : source.data? left x = some (a, d)) :
    target.data? right x = some (a, d) := by
  simpa only [Store.data?, modules, stores.datas] using hd

/-- All 42 aggregate rules transport unchanged ambient syntax across stores
whose non-function runtime data agree. -/
theorem aggregate_same {source target source' : Store H} {left right : Frame}
    {code out : List Admin} (stores : StoreRelation.Related source target)
    (modules : left.module = right.module)
    (step : AggregateStep ⟨source, left, code⟩ ⟨source', left, out⟩) :
    ∃ target', AggregateStep ⟨target, right, code⟩ ⟨target', right, out⟩ ∧
      StoreRelation.Related source' target' := by
  cases step with
  | structNew hd he hn hp =>
    exact ⟨_, by simpa only [stores.structs] using
      AggregateStep.structNew (s := target) (type_same modules hd) he hn hp,
      stores.addStruct _⟩
  | structNewDefault hd he hv =>
    exact ⟨_, .structNewDefault (type_same modules hd) he hv, stores⟩
  | structGetNull => exact ⟨_, .structGetNull, stores⟩
  | structGetStruct hs hf hd he hi hu =>
    exact ⟨_, .structGetStruct (stores.structs ▸ hs) hf (type_same modules hd) he hi hu, stores⟩
  | structSetNull => exact ⟨_, .structSetNull, stores⟩
  | structSetStruct hd he hi hs hf hp =>
    exact ⟨_, .structSetStruct (type_same modules hd) he hi (stores.structs ▸ hs) hf hp,
      stores.setStructField _ _ _⟩
  | arrayNew v n => exact ⟨_, .arrayNew v n, stores⟩
  | arrayNewDefault hd he hv =>
    exact ⟨_, .arrayNewDefault (type_same modules hd) he hv, stores⟩
  | arrayNewFixed hd he hn hp =>
    exact ⟨_, by simpa only [stores.arrays] using
      AggregateStep.arrayNewFixed (s := target) (type_same modules hd) he hn hp,
      stores.addArray _⟩
  | arrayNewElemOob he hb => exact ⟨_, .arrayNewElemOob (elem_same stores modules he) hb, stores⟩
  | arrayNewElemAlloc he hb => exact ⟨_, .arrayNewElemAlloc (elem_same stores modules he) hb, stores⟩
  | arrayNewDataOob hd he ht hz hb =>
    exact ⟨_, .arrayNewDataOob (type_same modules hd) he (data_same stores modules ht) hz hb, stores⟩
  | arrayNewDataNum hd he ht hz hb hv =>
    exact ⟨_, .arrayNewDataNum (type_same modules hd) he (data_same stores modules ht) hz hb hv, stores⟩
  | arrayGetNull => exact ⟨_, .arrayGetNull, stores⟩
  | arrayGetOob ha hb => exact ⟨_, .arrayGetOob (stores.arrays ▸ ha) hb, stores⟩
  | arrayGetArray ha hi hd he hu =>
    exact ⟨_, .arrayGetArray (stores.arrays ▸ ha) hi (type_same modules hd) he hu, stores⟩
  | arraySetNull => exact ⟨_, .arraySetNull, stores⟩
  | arraySetOob ha hb => exact ⟨_, .arraySetOob (stores.arrays ▸ ha) hb, stores⟩
  | arraySetArray ha hi hd he hp =>
    exact ⟨_, .arraySetArray (stores.arrays ▸ ha) hi (type_same modules hd) he hp,
      stores.setArrayField _ _ _⟩
  | arrayLenNull => exact ⟨_, .arrayLenNull, stores⟩
  | arrayLenArray ha => exact ⟨_, .arrayLenArray (stores.arrays ▸ ha), stores⟩
  | arrayFillNull => exact ⟨_, .arrayFillNull, stores⟩
  | arrayFillOob ha hb => exact ⟨_, .arrayFillOob (stores.arrays ▸ ha) hb, stores⟩
  | arrayFillZero ha hb => exact ⟨_, .arrayFillZero (stores.arrays ▸ ha) hb, stores⟩
  | arrayFillSucc ha hb hn => exact ⟨_, .arrayFillSucc (stores.arrays ▸ ha) hb hn, stores⟩
  | arrayCopyNull₁ => exact ⟨_, .arrayCopyNull₁, stores⟩
  | arrayCopyNull₂ => exact ⟨_, .arrayCopyNull₂, stores⟩
  | arrayCopyOob₁ ha hb => exact ⟨_, .arrayCopyOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayCopyOob₂ ha hb => exact ⟨_, .arrayCopyOob₂ (stores.arrays ▸ ha) hb, stores⟩
  | arrayCopyZero ha₁ ha₂ hb =>
    exact ⟨_, .arrayCopyZero (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb, stores⟩
  | arrayCopyLe ha₁ ha₂ hb hn hd he hl =>
    exact ⟨_, .arrayCopyLe (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb hn
      (type_same modules hd) he hl, stores⟩
  | arrayCopyGt ha₁ ha₂ hb hn hd he hl =>
    exact ⟨_, .arrayCopyGt (stores.arrays ▸ ha₁) (stores.arrays ▸ ha₂) hb hn
      (type_same modules hd) he hl, stores⟩
  | arrayInitElemNull => exact ⟨_, .arrayInitElemNull, stores⟩
  | arrayInitElemOob₁ ha hb => exact ⟨_, .arrayInitElemOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayInitElemOob₂ he hb => exact ⟨_, .arrayInitElemOob₂ (elem_same stores modules he) hb, stores⟩
  | arrayInitElemZero ha he hb =>
    exact ⟨_, .arrayInitElemZero (stores.arrays ▸ ha) (elem_same stores modules he) hb, stores⟩
  | arrayInitElemSucc ha he hb hn hr =>
    exact ⟨_, .arrayInitElemSucc (stores.arrays ▸ ha) (elem_same stores modules he) hb hn hr, stores⟩
  | arrayInitDataNull => exact ⟨_, .arrayInitDataNull, stores⟩
  | arrayInitDataOob₁ ha hb => exact ⟨_, .arrayInitDataOob₁ (stores.arrays ▸ ha) hb, stores⟩
  | arrayInitDataOob₂ hd he ht hz hb =>
    exact ⟨_, .arrayInitDataOob₂ (type_same modules hd) he (data_same stores modules ht) hz hb, stores⟩
  | arrayInitDataZero ha ht hb =>
    exact ⟨_, .arrayInitDataZero (stores.arrays ▸ ha) (data_same stores modules ht) hb, stores⟩
  | arrayInitDataNum ha hd he ht hb hn hv =>
    exact ⟨_, .arrayInitDataNum (stores.arrays ▸ ha) (type_same modules hd) he
      (data_same stores modules ht) hb hn hv, stores⟩

/-- Every aggregate step accepted by the actual code rewrite has a matching
step in the other store. Segment instructions rejected by the linker cannot
occur in this mode. The relation also covers the instructions emitted while
unrolling defaults, fills and either direction of a copy. -/
theorem aggregate_relocated {source target source' : Store H} {left right : Frame}
    {r : Relocation} {code out targetCode : List Admin}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module)
    (step : AggregateStep ⟨source, left, code⟩ ⟨source', left, out⟩)
    (control : Control (.relocated r) left.module right.module code targetCode) :
    ∃ target' targetOut,
      AggregateStep ⟨target, right, targetCode⟩ ⟨target', right, targetOut⟩ ∧
      StoreRelation.Related source' target' ∧
      Control (.relocated r) left.module right.module out targetOut := by
  cases step
  all_goals
    first
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, .ref _, .i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, .i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
  all_goals
    simp only [Instruction, instruction?, Option.map_eq_map, Option.map_eq_some_iff,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, reduceCtorEq] at rewrite
  case structNew =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, by simpa only [stores.structs] using
      AggregateStep.structNew (s := target) (views.types hy (by assumption)) (by assumption) (by assumption) (by assumption),
      stores.addStruct _, .ref .nil⟩
  case structNewDefault =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .structNewDefault (views.types hy (by assumption)) (by assumption) (by assumption), stores,
      (Control.values _ _ _ _).append (.plain (by simp [Instruction, instruction?, hy]) .nil)⟩
  case structGetNull =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .structGetNull, stores, .trap .nil⟩
  case structGetStruct =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .structGetStruct (by rwa [← stores.structs]) (by assumption) (views.types hy (by assumption)) (by assumption) (by assumption) (by assumption),
      stores, .val .nil⟩
  case structSetNull =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .structSetNull, stores, .trap .nil⟩
  case structSetStruct =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .structSetStruct (views.types hy (by assumption)) (by assumption) (by assumption) (by rwa [← stores.structs]) (by assumption) (by assumption),
      stores.setStructField _ _ _, .nil⟩
  case arrayNew v n =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayNew v n, stores,
      (Control.values _ _ _ _).append (.plain (by simp [Instruction, instruction?, hy]) .nil)⟩
  case arrayNewDefault =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayNewDefault (views.types hy (by assumption)) (by assumption) (by assumption), stores,
      (Control.values _ _ _ _).append (.plain (by simp [Instruction, instruction?, hy]) .nil)⟩
  case arrayNewFixed =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, by simpa only [stores.arrays] using
      AggregateStep.arrayNewFixed (s := target) (views.types hy (by assumption)) (by assumption) (by assumption) (by assumption),
      stores.addArray _, .ref .nil⟩
  case arrayGetNull =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayGetNull, stores, .trap .nil⟩
  case arrayGetOob =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayGetOob (by rwa [← stores.arrays]) (by assumption), stores, .trap .nil⟩
  case arrayGetArray =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayGetArray (by rwa [← stores.arrays]) (by assumption) (views.types hy (by assumption)) (by assumption) (by assumption),
      stores, .val .nil⟩
  case arraySetNull =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arraySetNull, stores, .trap .nil⟩
  case arraySetOob =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arraySetOob (by rwa [← stores.arrays]) (by assumption), stores, .trap .nil⟩
  case arraySetArray =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arraySetArray (by rwa [← stores.arrays]) (by assumption) (views.types hy (by assumption)) (by assumption) (by assumption),
      stores.setArrayField _ _ _, .nil⟩
  case arrayLenNull =>
    subst j
    exact ⟨_, _, .arrayLenNull, stores, .trap .nil⟩
  case arrayLenArray =>
    subst j
    exact ⟨_, _, .arrayLenArray (by rwa [← stores.arrays]), stores, .val .nil⟩
  case arrayFillNull =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayFillNull, stores, .trap .nil⟩
  case arrayFillOob =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayFillOob (by rwa [← stores.arrays]) (by assumption), stores, .trap .nil⟩
  case arrayFillZero =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayFillZero (by rwa [← stores.arrays]) (by assumption), stores, .nil⟩
  case arrayFillSucc =>
    obtain ⟨y, hy, rfl⟩ := rewrite
    exact ⟨_, _, .arrayFillSucc (by rwa [← stores.arrays]) (by assumption) (by assumption), stores,
      .ref (.val (.val (.plain (by simp [Instruction, instruction?, hy])
        (.ref (.val (.val (.val (.plain (by simp [Instruction, instruction?, hy]) .nil))))))))⟩
  case arrayCopyNull₁ =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyNull₁, stores, .trap .nil⟩
  case arrayCopyNull₂ =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyNull₂, stores, .trap .nil⟩
  case arrayCopyOob₁ =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyOob₁ (by rwa [← stores.arrays]) (by assumption), stores, .trap .nil⟩
  case arrayCopyOob₂ =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyOob₂ (by rwa [← stores.arrays]) (by assumption), stores, .trap .nil⟩
  case arrayCopyZero =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyZero (by rwa [← stores.arrays]) (by rwa [← stores.arrays]) (by assumption), stores, .nil⟩
  case arrayCopyLe =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyLe (by rwa [← stores.arrays]) (by rwa [← stores.arrays]) (by assumption) (by assumption)
      (views.types hy₂ (by assumption)) (by assumption) (by assumption), stores,
      .ref (.val (.ref (.val (.plain (by simp [Instruction, instruction?, hy₂])
        (.plain (by simp [Instruction, instruction?, hy₁])
          (.ref (.val (.ref (.val (.val
            (.plain (by simp [Instruction, instruction?, hy₁, hy₂]) .nil)))))))))))⟩
  case arrayCopyGt =>
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := rewrite
    exact ⟨_, _, .arrayCopyGt (by rwa [← stores.arrays]) (by rwa [← stores.arrays]) (by assumption) (by assumption)
      (views.types hy₂ (by assumption)) (by assumption) (by assumption), stores,
      .ref (.val (.ref (.val (.plain (by simp [Instruction, instruction?, hy₂])
        (.plain (by simp [Instruction, instruction?, hy₁])
          (.ref (.val (.ref (.val (.val
            (.plain (by simp [Instruction, instruction?, hy₁, hy₂]) .nil)))))))))))⟩


/-- The ambient-code case uses the same administrative relation as relocated
code, while retaining every aggregate instruction outside the linker fragment. -/
theorem aggregate_same_control {source target source' : Store H} {left right : Frame}
    {code out targetCode : List Admin}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    (step : AggregateStep ⟨source, left, code⟩ ⟨source', left, out⟩)
    (control : Control .same left.module right.module code targetCode) :
    ∃ target' targetOut,
      AggregateStep ⟨target, right, targetCode⟩ ⟨target', right, targetOut⟩ ∧
      StoreRelation.Related source' target' ∧
      Control .same left.module right.module out targetOut := by
  have original := step
  cases step
  all_goals
    first
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, .ref _, .i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, .i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _, _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _, _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [_, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _, .i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.i32 _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := [.ref _]) (h := control) (by rfl)
    | obtain ⟨j, rfl, rewrite⟩ := values_instruction (vs := []) (h := control) (by rfl)
  all_goals
    change _ = j at rewrite
    subst j
    obtain ⟨target', targetStep, related⟩ := aggregate_same stores modules original
    refine ⟨target', _, targetStep, related, ?_⟩
    rw [← modules]
    exact Control.same _ _

private theorem same_view {source target : ModuleInst} (view : View .same source target) :
    source = target := by cases view; rfl

private theorem relocated_view {r : Relocation} {source target : ModuleInst}
    (view : View (.relocated r) source target) : Views.Successful r source target := by
  cases view
  assumption

/-- The aggregate family preserves paired runtime data and administrative
code in both modes, with no additional annotation or typing premise. -/
theorem aggregate {source target source' : Store H} {left right : Frame}
    {mode : Mode} {code out targetCode : List Admin}
    (stores : StoreRelation.Related source target)
    (view : View mode left.module right.module)
    (step : AggregateStep ⟨source, left, code⟩ ⟨source', left, out⟩)
    (control : Control mode left.module right.module code targetCode) :
    ∃ target' targetOut,
      AggregateStep ⟨target, right, targetCode⟩ ⟨target', right, targetOut⟩ ∧
      StoreRelation.Related source' target' ∧
      Control mode left.module right.module out targetOut := by
  cases mode with
  | same => exact aggregate_same_control stores (same_view view) step control
  | relocated r => exact aggregate_relocated stores (relocated_view view) step control

end Silmaril.Wasm.Link.GC.AggregateSimulation
