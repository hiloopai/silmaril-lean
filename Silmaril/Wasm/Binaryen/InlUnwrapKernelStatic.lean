module

public import Silmaril.Wasm.Binaryen.InlUnwrapKernelRunning

@[expose] public section

/-! # Exact reverse heads for static folded arms

The actual selected conditional branch is retained. Entering its block creates
the guarded folded-label phase, including a body that is already all values.
These heads make a real step, so they need neither transformed typing nor a
rank-decrease argument. The original folding guards remain explicit.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded Det

variable {R : List Instr} {H : Type} {P : Profile}
variable {rank : List Admin → Nat} {m : Nat}

/-- Match the selected true head by the same true head on the original arm.
Only the selected arm's original folding guard is needed. -/
theorem fold_if_true_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {bt : BlockType} {yes yes' no common : List Instr}
    {originalRest bareRest : List Admin} {ambient : List Val} {c : BitVec 32}
    (stores : StoreRel F s t) (body : UIL R yes yes')
    (safe : FoldOk (yes ++ common)) (rest : KUL R originalRest bareRest)
    (condition : c ≠ 0) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨s, f, vals ambient ++ [.plain (.block bt yes')] ++ (expression common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [constI32 c,
        .plain (.if_ bt (yes ++ common) (no ++ common))] ++ originalRest⟩ m := by
  refine ⟨⟨t, f, vals ambient ++ [.plain (.block bt (yes ++ common))] ++ originalRest⟩,
    Or.inl (.single ?_), stores, rfl, .base (Or.inl ?_)⟩
  · exact Step.append_right (Step.vals_left (Step.ifTrue condition) ambient) originalRest
  · simpa only [List.append_assoc, List.singleton_append] using
      (KUL.refl (vals ambient)).append (KUL.foldBlock bt body safe rest)

/-- Match the selected false head without changing its condition or outcome. -/
theorem fold_if_false_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {bt : BlockType} {yes no no' common : List Instr}
    {originalRest bareRest : List Admin} {ambient : List Val} {c : BitVec 32}
    (stores : StoreRel F s t) (body : UIL R no no')
    (safe : FoldOk (no ++ common)) (rest : KUL R originalRest bareRest)
    (condition : c = 0) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨s, f, vals ambient ++ [.plain (.block bt no')] ++ (expression common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ [constI32 c,
        .plain (.if_ bt (yes ++ common) (no ++ common))] ++ originalRest⟩ m := by
  subst c
  refine ⟨⟨t, f, vals ambient ++ [.plain (.block bt (no ++ common))] ++ originalRest⟩,
    Or.inl (.single ?_), stores, rfl, .base (Or.inl ?_)⟩
  · exact Step.append_right (Step.vals_left Step.ifFalse ambient) originalRest
  · simpa only [List.append_assoc, List.singleton_append] using
      (KUL.refl (vals ambient)).append (KUL.foldBlock bt body safe rest)

/-- The actual block-type and argument-count witnesses enter the original
block. Its common suffix stays inside the original label, related to the bare
suffix outside the selected label; no non-value or transformed-typing premise
is imposed on the running body. -/
theorem fold_block_reverse
    {F : FuncInst H → FuncInst H → Prop} {s t : Store H} {f : Frame}
    {bt : BlockType} {body body' common : List Instr}
    {originalRest bareRest : List Admin} {ambient args : List Val}
    {inputs outputs : List CValType}
    (stores : StoreRel F s t) (related : UIL R body body')
    (safe : FoldOk (body ++ common)) (rest : KUL R originalRest bareRest)
    (blockType : f.module.blockType? bt = some (inputs, outputs))
    (arity : args.length = inputs.length) :
    RankedMatched rank P noHost F (fun x y => UIL R y x) (fun x y => KUL R y x)
      ⟨s, f, vals ambient ++ [.label outputs.length [] (vals args ++ expression body')] ++
        (expression common ++ bareRest)⟩
      ⟨t, f, vals ambient ++ (vals args ++ [.plain (.block bt (body ++ common))]) ++
        originalRest⟩ m := by
  refine ⟨⟨t, f, vals ambient ++
    [.label outputs.length [] (vals args ++ expression (body ++ common))] ++ originalRest⟩,
    Or.inl (.single ?_), stores, rfl, .base (Or.inl ?_)⟩
  · exact Step.append_right (Step.vals_left (Step.block blockType arity) ambient) originalRest
  · have bodyRelated := (KUL.refl (vals args)).append (KUL.of_UIL related)
    have guarded : NoEsc ((vals args ++ expression body) ++ expression common) := by
      simpa [expression, List.map_append, List.append_assoc] using noEsc_fold safe args
    simpa [expression, List.map_append, List.append_assoc, List.singleton_append] using
      (KUL.refl (vals ambient)).append (KUL.foldLabel bodyRelated guarded rest)

end Silmaril.Wasm.Binaryen.Unwrap
