module

public import Silmaril.Wasm.Link.AdminRelation
public import Silmaril.Wasm.Link.ControlViews

/-! # Control-rule transport for linked stores

Blocks, loops and calls use the actual relocated type and function lookups.
The resulting labels and nested call frames are related administrative code,
with identical values, locals and result arities in the two stores.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.ControlSimulation

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open AdminRelation

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem block {source target : Store H} {left right : Frame} {r : Relocation}
    {bt bt' : BlockType} {body body' : List Instr} {args : List Val}
    {params results : List CValType}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (typeRewrite : blockType? r.types bt = some bt')
    (bodyRewrite : instructions? r body = some body')
    (scope : ControlViews.BlockScoped left.module.types.length bt)
    (lookup : left.module.blockType? bt = some (params, results))
    (arity : args.length = params.length) :
    Step P host ⟨target, right, vals args ++ [.plain (.block bt' body')]⟩
      ⟨target, right, [.label results.length [] (vals args ++ expression body')]⟩ ∧
    Configs ⟨source, left, [.label results.length [] (vals args ++ expression body)]⟩
      ⟨target, right, [.label results.length [] (vals args ++ expression body')]⟩ := by
  exact ⟨.block (ControlViews.block_lookup views typeRewrite scope lookup) arity,
    .mk stores ⟨.relocated views, locals⟩
      (.label rfl ((Control.values _ _ _ args).append (Control.expression bodyRewrite)) .nil)⟩

theorem loop {source target : Store H} {left right : Frame} {r : Relocation}
    {bt bt' : BlockType} {body body' : List Instr} {args : List Val}
    {params results : List CValType}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (typeRewrite : blockType? r.types bt = some bt')
    (bodyRewrite : instructions? r body = some body')
    (scope : ControlViews.BlockScoped left.module.types.length bt)
    (lookup : left.module.blockType? bt = some (params, results))
    (arity : args.length = params.length) :
    Step P host ⟨target, right, vals args ++ [.plain (.loop bt' body')]⟩
      ⟨target, right, [.label params.length [.loop bt' body'] (vals args ++ expression body')]⟩ ∧
    Configs ⟨source, left, [.label params.length [.loop bt body] (vals args ++ expression body)]⟩
      ⟨target, right, [.label params.length [.loop bt' body'] (vals args ++ expression body')]⟩ := by
  have attached : body.attach.mapM (fun nested => instruction? r nested.val) = some body' := by
    rw [List.mapM_subtype (g := instruction? r) (fun _ _ => rfl), List.unattach_attach]
    exact bodyRewrite
  have rewrite : instruction? r (.loop bt body) = some (.loop bt' body') := by
    simp only [instruction?, typeRewrite, attached, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  have continuation : Instructions (.relocated r) [.loop bt body] [.loop bt' body'] := by
    simp only [Instructions, instructions?, List.mapM_cons, rewrite, List.mapM_nil,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  exact ⟨.loop (ControlViews.block_lookup views typeRewrite scope lookup) arity,
    .mk stores ⟨.relocated views, locals⟩
      (.label continuation ((Control.values _ _ _ args).append (Control.expression bodyRewrite)) .nil)⟩

theorem ifTrue {source target : Store H} {left right : Frame} {r : Relocation}
    {c : BitVec 32} {bt bt' : BlockType} {yes yes' no' : List Instr}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (typeRewrite : blockType? r.types bt = some bt')
    (bodyRewrite : instructions? r yes = some yes') (condition : c ≠ 0) :
    Step P host ⟨target, right, [constI32 c, .plain (.if_ bt' yes' no')]⟩
      ⟨target, right, [.plain (.block bt' yes')]⟩ ∧
    Configs ⟨source, left, [.plain (.block bt yes)]⟩
      ⟨target, right, [.plain (.block bt' yes')]⟩ := by
  have attached : yes.attach.mapM (fun nested => instruction? r nested.val) = some yes' := by
    rw [List.mapM_subtype (g := instruction? r) (fun _ _ => rfl), List.unattach_attach]
    exact bodyRewrite
  exact ⟨.ifTrue condition, .mk stores ⟨.relocated views, locals⟩
    (.plain (by simp only [Instruction, instruction?, typeRewrite, attached,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]) .nil)⟩

theorem ifFalse {source target : Store H} {left right : Frame} {r : Relocation}
    {bt bt' : BlockType} {yes' no no' : List Instr}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (typeRewrite : blockType? r.types bt = some bt')
    (bodyRewrite : instructions? r no = some no') :
    Step P host ⟨target, right, [constI32 0, .plain (.if_ bt' yes' no')]⟩
      ⟨target, right, [.plain (.block bt' no')]⟩ ∧
    Configs ⟨source, left, [.plain (.block bt no)]⟩
      ⟨target, right, [.plain (.block bt' no')]⟩ := by
  have attached : no.attach.mapM (fun nested => instruction? r nested.val) = some no' := by
    rw [List.mapM_subtype (g := instruction? r) (fun _ _ => rfl), List.unattach_attach]
    exact bodyRewrite
  exact ⟨.ifFalse, .mk stores ⟨.relocated views, locals⟩
    (.plain (by simp only [Instruction, instruction?, typeRewrite, attached,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]) .nil)⟩

theorem call {source target : Store H} {left right : Frame} {r : Relocation}
    {x y : FuncIdx} {address : Nat} {function : FuncInst H}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (rewrite : function? r x = some y) (lookup : left.module.funcs[x.toNat]? = some address)
    (definition : source.funcs[address]? = some function) :
    Step P host ⟨target, right, [.plain (.call y)]⟩
      ⟨target, right, [.ref (.func address), .callRefType function.type]⟩ ∧
    Configs ⟨source, left, [.ref (.func address), .callRefType function.type]⟩
      ⟨target, right, [.ref (.func address), .callRefType function.type]⟩ := by
  obtain ⟨function', lookup', paired⟩ := stores.function_lookup definition
  have step := Step.call (P := P) (host := host) (f := right)
    (views.functions rewrite lookup) lookup'
  rw [← paired.type_eq] at step
  exact ⟨step, .mk stores ⟨.relocated views, locals⟩ (.ref (.callRefType .nil))⟩

theorem returnCall {source target : Store H} {left right : Frame} {r : Relocation}
    {x y : FuncIdx} {address : Nat} {function : FuncInst H}
    (stores : StoreRelation.Related source target)
    (views : Views.Successful r left.module right.module) (locals : left.locals = right.locals)
    (rewrite : function? r x = some y) (lookup : left.module.funcs[x.toNat]? = some address)
    (definition : source.funcs[address]? = some function) :
    Step P host ⟨target, right, [.plain (.returnCall y)]⟩
      ⟨target, right, [.ref (.func address), .returnCallRefType function.type]⟩ ∧
    Configs ⟨source, left, [.ref (.func address), .returnCallRefType function.type]⟩
      ⟨target, right, [.ref (.func address), .returnCallRefType function.type]⟩ := by
  obtain ⟨function', lookup', paired⟩ := stores.function_lookup definition
  have step := Step.returnCall (P := P) (host := host) (f := right)
    (views.functions rewrite lookup) lookup'
  rw [← paired.type_eq] at step
  exact ⟨step, .mk stores ⟨.relocated views, locals⟩ (.ref (.returnCallRefType .nil))⟩

/-- Tail calls resolve an indexed annotation in the frame they leave. The
resulting closed administrative annotation is then independent of the caller's
module, which can have a different relocation mode. -/
theorem tail_annotation {left right : ModuleInst} {r : Relocation}
    {x y : TypeIdx} {tag : DefType} (views : Views.Successful r left right)
    (rewrite : shiftIdx? r.types x = some y) (lookup : left.types[x.toNat]? = some tag) :
    (Admin.plain (.returnCallRef x)).retToCallIn left = .callRefType tag ∧
      (Admin.plain (.returnCallRef y)).retToCallIn right = .callRefType tag := by
  exact ⟨by simp only [Admin.retToCallIn, lookup],
    by simp only [Admin.retToCallIn, views.types rewrite lookup]⟩

theorem tail_call {source target : Store H} {caller caller' left right : Frame}
    {mode : Mode} {r : Relocation} {n address : Nat} {discard args : List Val}
    {rest' : List Admin} {x y : TypeIdx} {tag : DefType}
    {function : FuncInst H} {params results : Ty (.list .val)}
    (stores : StoreRelation.Related source target) (callers : Frames mode caller caller')
    (views : Views.Successful r left.module right.module)
    (rewrite : shiftIdx? r.types x = some y) (lookup : left.module.types[x.toNat]? = some tag)
    (definition : source.funcs[address]? = some function)
    (signature : Expand function.type (.func params results)) (arity : args.length = params.length) :
    Step P host
      ⟨target, caller', [.frame n right
        (vals discard ++ vals args ++ [.ref (.func address), .plain (.returnCallRef y)] ++ rest')]⟩
      ⟨target, caller', vals args ++ [.ref (.func address), .callRefType tag]⟩ ∧
    Configs
      ⟨source, caller, vals args ++ [.ref (.func address),
        (Admin.plain (.returnCallRef x)).retToCallIn left.module]⟩
      ⟨target, caller', vals args ++ [.ref (.func address), .callRefType tag]⟩ := by
  obtain ⟨function', definition', paired⟩ := stores.function_lookup definition
  obtain ⟨annotation, annotation'⟩ := tail_annotation views rewrite lookup
  constructor
  · have step := Step.returnCallRefFrameAddr (P := P) (host := host) (f := caller')
      (fi := right) (k := n) (vs' := discard) (rest := rest')
      (c := .plain (.returnCallRef y)) trivial definition' (paired.type_eq ▸ signature) arity
    rw [annotation'] at step
    exact step
  · rw [annotation]
    exact .mk stores callers ((Control.values _ _ _ args).append (.ref (.callRefType .nil)))

theorem label_values {source target : Store H} {left right : Frame} {mode : Mode}
    {n : Nat} {cont' : List Instr} {values : List Val}
    (stores : StoreRelation.Related source target) (frames : Frames mode left right) :
    Step P host ⟨target, right, [.label n cont' (vals values)]⟩ ⟨target, right, vals values⟩ ∧
    Configs ⟨source, left, vals values⟩ ⟨target, right, vals values⟩ :=
  ⟨.labelVals, .mk stores frames (Control.values _ _ _ values)⟩

theorem frame_values {source target : Store H} {left right inner' : Frame} {mode : Mode}
    {n : Nat} {values : List Val}
    (stores : StoreRelation.Related source target) (frames : Frames mode left right)
    (arity : values.length = n) :
    Step P host ⟨target, right, [.frame n inner' (vals values)]⟩ ⟨target, right, vals values⟩ ∧
    Configs ⟨source, left, vals values⟩ ⟨target, right, vals values⟩ :=
  ⟨.frameVals arity, .mk stores frames (Control.values _ _ _ values)⟩

/-- Context lifting retains each caller's module and locals while the inner
frame executes with its own (possibly different) relocation mode. -/
theorem frame_context {source target source' target' : Store H}
    {caller caller' left right left' right' : Frame} {mode calleeMode : Mode}
    {n : Nat} {body body' out out' : List Admin}
    (stores : StoreRelation.Related source' target')
    (callers : Frames mode caller caller') (frames : Frames calleeMode left' right')
    (code : Control calleeMode left'.module right'.module out out')
    (sourceStep : Step P host ⟨source, left, body⟩ ⟨source', left', out⟩)
    (targetStep : Step P host ⟨target, right, body'⟩ ⟨target', right', out'⟩) :
    Step P host ⟨source, caller, [.frame n left body]⟩ ⟨source', caller, [.frame n left' out]⟩ ∧
    Step P host ⟨target, caller', [.frame n right body']⟩ ⟨target', caller', [.frame n right' out']⟩ ∧
    Configs ⟨source', caller, [.frame n left' out]⟩ ⟨target', caller', [.frame n right' out']⟩ :=
  ⟨.ctxtFrame sourceStep, .ctxtFrame targetStep, .mk stores callers (.frame frames code .nil)⟩

end Silmaril.Wasm.Link.GC.ControlSimulation
