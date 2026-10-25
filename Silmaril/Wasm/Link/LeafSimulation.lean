module

public import Silmaril.Wasm.Link.StoreRelation

/-! # Reference and variable rules across linked stores

The stores contain the same values and closed function tags. Locals agree,
while successful module lookups and scoped reference annotations account for
the actual relocated source indices. These are operational leaf rules for the
recursive administrative simulation.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.LeafSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem reference_same {source target : Store H} {left right : Frame} {code out : List Admin}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    (step : RefStep ⟨source, left, code⟩ ⟨source, left, out⟩) :
    RefStep ⟨target, right, code⟩ ⟨target, right, out⟩ := by
  cases step with
  | refNull ht => exact .refNull ht
  | refFunc hf => exact .refFunc (modules ▸ hf)
  | refI31 i => exact .refI31 i
  | isNullTrue => exact .isNullTrue
  | isNullFalse hn => exact .isNullFalse hn
  | asNonNullNull => exact .asNonNullNull
  | asNonNullAddr hn => exact .asNonNullAddr hn
  | eqNull => exact .eqNull
  | eqTrue hn => exact .eqTrue hn
  | eqFalse hn => exact .eqFalse hn
  | testTrue hv => exact .testTrue (modules ▸ stores.refOk hv)
  | testFalse hv => exact .testFalse (fun ht => hv (modules.symm ▸ stores.refOk_reverse ht))
  | castSucceed hv => exact .castSucceed (modules ▸ stores.refOk hv)
  | castFail hv => exact .castFail (fun ht => hv (modules.symm ▸ stores.refOk_reverse ht))
  | i31GetNull sign => exact .i31GetNull sign
  | i31GetNum sign i => exact .i31GetNum sign i
  | externConvertNull => exact .externConvertNull
  | externConvertAddr hn => exact .externConvertAddr hn
  | anyConvertNull => exact .anyConvertNull
  | anyConvertAddr r => exact .anyConvertAddr r

/-- These reference-rule inputs carry no module index or type annotation
that needs source relocation. -/
def IndependentReference : List Admin → Prop
  | [.plain (.refNull _)] | [.plain (.refFunc _)]
  | [.ref _, .plain (.refTest _)] | [.ref _, .plain (.refCast _)] => False
  | _ => True

theorem reference_independent {source target : Store H} {left right : Frame} {code out : List Admin}
    (step : RefStep ⟨source, left, code⟩ ⟨source, left, out⟩)
    (independent : IndependentReference code) :
    RefStep ⟨target, right, code⟩ ⟨target, right, out⟩ := by
  cases step <;> simp only [IndependentReference] at independent
  case refI31 i => exact .refI31 i
  case isNullTrue => exact .isNullTrue
  case isNullFalse hn => exact .isNullFalse hn
  case asNonNullNull => exact .asNonNullNull
  case asNonNullAddr hn => exact .asNonNullAddr hn
  case eqNull => exact .eqNull
  case eqTrue hn => exact .eqTrue hn
  case eqFalse hn => exact .eqFalse hn
  case i31GetNull sign => exact .i31GetNull sign
  case i31GetNum sign i => exact .i31GetNum sign i
  case externConvertNull => exact .externConvertNull
  case externConvertAddr hn => exact .externConvertAddr hn
  case anyConvertNull => exact .anyConvertNull
  case anyConvertAddr r => exact .anyConvertAddr r

theorem global_lookup_same {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) (modules : left.module = right.module)
    {x : GlobalIdx} {a : Nat} {g : GlobalInst} (lookup : source.global? left x = some (a, g)) :
    target.global? right x = some (a, g) := by
  simpa only [Store.global?, ← modules, ← stores.globals] using lookup

/-- Every local/global rule transports in unchanged module views, including
its exact updated local cells and its retained store relation. -/
theorem variable_same {source target source' : Store H} {left right left' : Frame}
    {code out : List Admin} (stores : StoreRelation.Related source target)
    (modules : left.module = right.module) (locals : left.locals = right.locals)
    (step : VariableStep ⟨source, left, code⟩ ⟨source', left', out⟩) :
    ∃ target' right', VariableStep ⟨target, right, code⟩ ⟨target', right', out⟩ ∧
      StoreRelation.Related source' target' ∧ left'.module = right'.module ∧
      left'.locals = right'.locals := by
  cases step with
  | localGet lookup =>
    exact ⟨target, right, .localGet (by simpa only [Frame.local?, locals] using lookup),
      stores, modules, locals⟩
  | @localSet _ _ x v bound =>
    exact ⟨target, right.setLocal x v, .localSet (locals ▸ bound), stores, modules,
      congrArg (fun ls => ls.set x.toNat (some v)) locals⟩
  | localTee => exact ⟨target, right, .localTee, stores, modules, locals⟩
  | globalGet lookup =>
    exact ⟨target, right, .globalGet (global_lookup_same stores modules lookup), stores, modules, locals⟩
  | @globalSet _ _ x a g v lookup =>
    exact ⟨target.setGlobal a v, right, .globalSet (global_lookup_same stores modules lookup),
      stores.setGlobal a v, modules, locals⟩

theorem localGet {target : Store H} {left right : Frame} {x : LocalIdx} {v : Val}
    (locals : left.locals = right.locals) (lookup : left.local? x = some (some v)) :
    VariableStep ⟨target, right, [.plain (.localGet x)]⟩ ⟨target, right, [v.toAdmin]⟩ :=
  .localGet (by simpa only [Frame.local?, locals] using lookup)

theorem localSet {source target : Store H} {left right : Frame} {x : LocalIdx} {v : Val}
    (stores : StoreRelation.Related source target) (locals : left.locals = right.locals)
    (bound : x.toNat < left.locals.length) :
    VariableStep ⟨target, right, [v.toAdmin, .plain (.localSet x)]⟩
      ⟨target, right.setLocal x v, []⟩ ∧
      StoreRelation.Related source target ∧
      (left.setLocal x v).locals = (right.setLocal x v).locals :=
  ⟨.localSet (locals ▸ bound), stores, congrArg (fun ls => ls.set x.toNat (some v)) locals⟩

theorem localTee {target : Store H} {right : Frame} (x : LocalIdx) (v : Val) :
    VariableStep ⟨target, right, [v.toAdmin, .plain (.localTee x)]⟩
      ⟨target, right, [v.toAdmin, v.toAdmin, .plain (.localSet x)]⟩ := .localTee

theorem global_lookup {source target : Store H} {left right : Frame} {r : Relocation}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module)
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst}
    (rewrite : shiftIdx? r.globals x = some y)
    (lookup : source.global? left x = some (a, g)) :
    target.global? right y = some (a, g) :=
  stores.toState.data.global_lookup views rewrite lookup

theorem globalGet {source target : Store H} {left right : Frame} {r : Relocation}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module)
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst}
    (rewrite : shiftIdx? r.globals x = some y)
    (lookup : source.global? left x = some (a, g)) :
    VariableStep ⟨target, right, [.plain (.globalGet y)]⟩
      ⟨target, right, [g.value.toAdmin]⟩ := .globalGet (global_lookup stores views rewrite lookup)

theorem globalSet {source target : Store H} {left right : Frame} {r : Relocation}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module)
    {x y : GlobalIdx} {a : Nat} {g : GlobalInst} (v : Val)
    (rewrite : shiftIdx? r.globals x = some y)
    (lookup : source.global? left x = some (a, g)) :
    VariableStep ⟨target, right, [v.toAdmin, .plain (.globalSet y)]⟩
      ⟨target.setGlobal a v, right, []⟩ ∧
      StoreRelation.Related (source.setGlobal a v) (target.setGlobal a v) :=
  ⟨.globalSet (global_lookup stores views rewrite lookup), stores.setGlobal a v⟩

theorem refNull {target : Store H} {right : Frame} {r : Relocation}
    {source targetHeap : HeapType} (rewrite : heap? r.types source = some targetHeap) :
    instruction? r (.refNull source) = some (.refNull targetHeap) ∧
      RefStep ⟨target, right, [.plain (.refNull targetHeap)]⟩ ⟨target, right, [.ref .null]⟩ :=
  ⟨by simp only [instruction?, rewrite, Option.map_eq_map, Option.map_some], .refNull targetHeap⟩

theorem refFunc {target : Store H} {left right : Frame} {r : Relocation}
    (views : Views.Successful r left.module right.module) {x y : FuncIdx} {a : Nat}
    (rewrite : function? r x = some y) (lookup : left.module.funcs[x.toNat]? = some a) :
    RefStep ⟨target, right, [.plain (.refFunc y)]⟩ ⟨target, right, [.ref (.func a)]⟩ :=
  .refFunc (views.functions rewrite lookup)

theorem testTrue_of_tag {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) {rt rt' : RefType} {v : Ref}
    (tag : right.module.instRef rt' = left.module.instRef rt)
    (valid : RefOk source v (left.module.instRef rt)) :
    RefStep ⟨target, right, [.ref v, .plain (.refTest rt')]⟩ ⟨target, right, [constI32 1]⟩ := by
  apply RefStep.testTrue
  rw [tag]
  exact stores.refOk valid

theorem testFalse_of_tag {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) {rt rt' : RefType} {v : Ref}
    (tag : right.module.instRef rt' = left.module.instRef rt)
    (invalid : ¬ RefOk source v (left.module.instRef rt)) :
    RefStep ⟨target, right, [.ref v, .plain (.refTest rt')]⟩ ⟨target, right, [constI32 0]⟩ := by
  apply RefStep.testFalse
  rw [tag]
  exact fun h => invalid (stores.refOk_reverse h)

theorem castSucceed_of_tag {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) {rt rt' : RefType} {v : Ref}
    (tag : right.module.instRef rt' = left.module.instRef rt)
    (valid : RefOk source v (left.module.instRef rt)) :
    RefStep ⟨target, right, [.ref v, .plain (.refCast rt')]⟩ ⟨target, right, [.ref v]⟩ := by
  apply RefStep.castSucceed
  rw [tag]
  exact stores.refOk valid

theorem castFail_of_tag {source target : Store H} {left right : Frame}
    (stores : StoreRelation.Related source target) {rt rt' : RefType} {v : Ref}
    (tag : right.module.instRef rt' = left.module.instRef rt)
    (invalid : ¬ RefOk source v (left.module.instRef rt)) :
    RefStep ⟨target, right, [.ref v, .plain (.refCast rt')]⟩ ⟨target, right, [.trap]⟩ := by
  apply RefStep.castFail
  rw [tag]
  exact fun h => invalid (stores.refOk_reverse h)

end Silmaril.Wasm.Link.GC.LeafSimulation
