module

public import Silmaril.Wasm.Link.Views
public import Silmaril.Wasm.Link.Identity

/-! # Stored functions from actual separate and linked preparation

Provider definitions retain their exact source code. Consumer definitions keep
their closed call tags and carry the actual rewritten type, locals and body.
Both preparations install corresponding definitions at the same function
address; their module views are related by `Views.Successful`.
-/

@[expose] public section
namespace Silmaril.Wasm.Link.GC.Functions

open Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics
open Preparation

variable {H : Type}

/-- The source fields used to create the actual rewritten function. -/
structure Rewrite (r : Relocation) (source target : Func) : Prop where
  type : shiftIdx? r.types source.type = some target.type
  locals : source.locals.mapM (valType? r.types) = some target.locals
  body : instructions? r source.body = some target.body

theorem rewrite {r : Relocation} {source target : Func}
    (h : func? r source = some target) : Rewrite r source target := by
  simp only [func?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨type, ht, locals, hl, body, hb, rfl⟩ := h
  exact ⟨ht, hl, hb⟩

/-- Relocating a declared local keeps its default (or its unset state).
Reference defaults depend on nullability, not on the relocated heap tag. -/
theorem local_default {offset : Nat} {source target : ValType}
    (h : valType? offset source = some target) (left right : List DefType) :
    defaultVal? ((liftVal source).substAll (left.map .dt)) =
      defaultVal? ((liftVal target).substAll (right.map .dt)) := by
  cases source with
  | num n =>
    simp only [valType?, Option.some.injEq] at h
    subst target
    cases n <;> rfl
  | vec v =>
    simp only [valType?, Option.some.injEq] at h
    subst target
    rfl
  | ref r =>
    rcases r with ⟨nullable, heap⟩
    simp only [valType?, refType?, Option.bind_eq_bind, Option.map_eq_map,
      Option.map_eq_some_iff, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨ref', ⟨heap', _, rfl⟩, rfl⟩ := h
    cases nullable <;> rfl

/-- Arguments and initialized local cells match in the two call frames.
Only their module index tables differ. -/
theorem Rewrite.forCall_locals {r : Relocation} {source target : Func}
    (h : Rewrite r source target) (left right : ModuleInst) (args : List Val) :
    (Frame.forCall left args source.locals).locals =
      (Frame.forCall right args target.locals).locals := by
  have hr := List.mapM_some_forall₂ (R := fun a b => valType? r.types a = some b)
    (fun h => h) h.locals
  have hm : source.locals.map (fun t => defaultVal? ((liftVal t).substAll (left.types.map .dt))) =
      target.locals.map (fun t => defaultVal? ((liftVal t).substAll (right.types.map .dt))) := by
    generalize hx : source.locals = xs at hr ⊢
    generalize hy : target.locals = ys at hr ⊢
    clear hx hy
    induction hr with
    | nil => rfl
    | cons hab _ ih =>
      simp only [List.map_cons, local_default hab left.types right.types, ih]
  exact congrArg (args.map some ++ ·) hm

/-- Actual provider allocations share the address, closed tag and unchanged
body, while retaining their respective source and linked module views. -/
theorem provider_binding {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sl : Store H} {fp fl : Frame} {startP startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL))
    {n : Nat} {fn : Func} {d : DefType}
    (hf : provider.funcs[n]? = some fn) (hd : (allocTypes provider.types)[fn.type.toNat]? = some d) :
    sp.funcs[s.funcs.length+n]? = some ⟨d, fp.module, .wasm fn⟩ ∧
      sl.funcs[s.funcs.length+n]? = some ⟨d, fl.module, .wasm fn⟩ ∧
      Views.Successful Recipe.identity fp.module fl.module := by
  obtain ⟨fn', hf', hr⟩ := w.provider_func_lookup hf
  have he := Identity.func_identity hr
  subst fn'
  have hd' := Allocation.link?_provider_type_lookup hl hd
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  exact ⟨(PreparationOnce.once_function w.providerProfile hp hf hd).2,
    (PreparationOnce.once_function hprofile hm hf' hd').2, Views.provider w hl hp hm⟩

/-- Actual consumer allocations share the address and original closed call
tag. The linked store contains the exact source rewrite produced by the linker. -/
theorem consumer_binding {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc, fc, startC))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL))
    {n : Nat} {fn : Func} {d : DefType}
    (hf : consumer.funcs[n]? = some fn) (hd : (allocTypes consumer.types)[fn.type.toNat]? = some d) :
    ∃ fn',
      sc.funcs[s.funcs.length+provider.funcs.length+n]? = some ⟨d, fc.module, .wasm fn⟩ ∧
      sl.funcs[s.funcs.length+provider.funcs.length+n]? = some ⟨d, fl.module, .wasm fn'⟩ ∧
      Rewrite (Recipe.relocation provider w.imports) fn fn' ∧
      Views.Successful (Recipe.relocation provider w.imports) fc.module fl.module := by
  obtain ⟨fn', hf', hr⟩ := w.consumer_func_lookup hf
  have parts := rewrite hr
  have hd' : (allocTypes result.types)[fn'.type.toNat]? = some d :=
    (Allocation.link?_consumer_type_lookup hl parts.type).trans hd
  have hprofile : inProfile result = true := by rw [w.output]; rfl
  have hcounts := Views.once_counts w.providerProfile hp
  refine ⟨fn', ?_, ?_, parts, Views.consumer w hl hp hc hm⟩
  · simpa only [hcounts.1] using (PreparationOnce.once_function w.consumerProfile hc hf hd).2
  · simpa only [Nat.add_assoc] using (PreparationOnce.once_function hprofile hm hf' hd').2

/-- Preparing the consumer retains the provider's exact stored definition.
Both source modules are now installed in one store, as in component linking. -/
theorem provider_final_binding {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc, fc, startC))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL))
    {n : Nat} {fn : Func} {d : DefType}
    (hf : provider.funcs[n]? = some fn) (hd : (allocTypes provider.types)[fn.type.toNat]? = some d) :
    sc.funcs[s.funcs.length+n]? = some ⟨d, fp.module, .wasm fn⟩ ∧
      sl.funcs[s.funcs.length+n]? = some ⟨d, fl.module, .wasm fn⟩ ∧
      Views.Successful Recipe.identity fp.module fl.module := by
  obtain ⟨hs, ht, hv⟩ := provider_binding w hl hp hm hf hd
  exact ⟨Views.once_function_retained w.consumerProfile hc hs, ht, hv⟩

/-- Corresponding stored definitions enter actual administrative call frames
with identical argument/local cells and result arity. The target body is the
linker's source rewrite; this is the entry bridge, not a whole-body simulation. -/
theorem call_entry_pair {P : Profile} {host : HostSemantics H}
    {sourceStore targetStore : Store H} {sourceCaller targetCaller : Frame}
    {sourceModule targetModule : ModuleInst} {address : Nat} {tag : DefType}
    {source target : Func} {r : Relocation} {args : List Val} {params results : Ty (.list .val)}
    (hs : sourceStore.funcs[address]? = some ⟨tag, sourceModule, .wasm source⟩)
    (ht : targetStore.funcs[address]? = some ⟨tag, targetModule, .wasm target⟩)
    (hr : Rewrite r source target) (he : Expand tag (.func params results))
    (hn : args.length = params.length) :
    Step P host
      ⟨sourceStore, sourceCaller, vals args ++ [.ref (.func address), .callRefType tag]⟩
      ⟨sourceStore, sourceCaller, [.frame results.length (Frame.forCall sourceModule args source.locals)
        [.label results.length [] (expression source.body)]]⟩ ∧
    Step P host
      ⟨targetStore, targetCaller, vals args ++ [.ref (.func address), .callRefType tag]⟩
      ⟨targetStore, targetCaller, [.frame results.length (Frame.forCall targetModule args target.locals)
        [.label results.length [] (expression target.body)]]⟩ ∧
    (Frame.forCall sourceModule args source.locals).locals =
      (Frame.forCall targetModule args target.locals).locals :=
  ⟨.callRefFunc (c := .callRefType tag) trivial hs he hn rfl,
    .callRefFunc (c := .callRefType tag) trivial ht he hn rfl,
    hr.forCall_locals sourceModule targetModule args⟩

/-- Actual separate and linked consumer definitions enter matching call frames
at the same allocated address, with the exact relocated body. -/
theorem consumer_entry {P : Profile} {host : HostSemantics H}
    {namespaceName provider consumer result}
    (w : Recipe.Assembly namespaceName provider consumer result)
    (hl : link? namespaceName provider consumer = some result)
    {s sp sc sl : Store H} {fp fc fl : Frame} {startP startC startL : Option FuncIdx}
    (hp : instantiateOnce? s provider (imports []) = some (sp, fp, startP))
    (hc : instantiateOnce? sp consumer
      (imports (w.imports.map (fun f => s.funcs.length+f.toNat))) = some (sc, fc, startC))
    (hm : instantiateOnce? s result (imports []) = some (sl, fl, startL))
    {n : Nat} {fn : Func} {d : DefType} {args : List Val} {params results : Ty (.list .val)}
    (hf : consumer.funcs[n]? = some fn) (hd : (allocTypes consumer.types)[fn.type.toNat]? = some d)
    (he : Expand d (.func params results)) (hn : args.length = params.length) :
    ∃ fn', Rewrite (Recipe.relocation provider w.imports) fn fn' ∧
      Step P host
        ⟨sc, fc, vals args ++ [.ref (.func (s.funcs.length+provider.funcs.length+n)), .callRefType d]⟩
        ⟨sc, fc, [.frame results.length (Frame.forCall fc.module args fn.locals)
          [.label results.length [] (expression fn.body)]]⟩ ∧
      Step P host
        ⟨sl, fl, vals args ++ [.ref (.func (s.funcs.length+provider.funcs.length+n)), .callRefType d]⟩
        ⟨sl, fl, [.frame results.length (Frame.forCall fl.module args fn'.locals)
          [.label results.length [] (expression fn'.body)]]⟩ ∧
      (Frame.forCall fc.module args fn.locals).locals =
        (Frame.forCall fl.module args fn'.locals).locals := by
  obtain ⟨fn', hs, ht, hr, _⟩ := consumer_binding w hl hp hc hm hf hd
  exact ⟨fn', hr, call_entry_pair hs ht hr he hn⟩

end Silmaril.Wasm.Link.GC.Functions
