module

public import Silmaril.Wasm.Binaryen.InlUnwrapCoreRel
public import Silmaril.Wasm.Binaryen.InlUnwrapActiveAlignment
public import Silmaril.Wasm.Binaryen.InlUnwrapTypedValues

@[expose] public section

/-! # Entering recursive runtime phases of the typed unwrap converse

The actual block supplies its operand boundary. Exact selected-step transport
then returns to `UL.run`, retaining related callees and continuations. This is
the local site-to-running phase, not a converse for every `UL` constructor.
-/

namespace Silmaril.Wasm.Binaryen.Unwrap

open Execution.Core Execution.Core.Sim Validation Numerics SingleThreaded

variable {H : Type} {P : Profile}

/-- Value operands do not introduce escapes into a region. -/
theorem NoEsc.vals_left {body : List Admin} (safe : NoEsc body) (args : List Val) :
    NoEsc (vals args ++ body) := by
  obtain ⟨⟨S, budget⟩, labels⟩ := safe
  exact ⟨⟨S, by simpa only [AdmsB_append, AdmsB_vals, true_and] using budget⟩,
    by simpa only [AdmsLab_append, AdmsLab_vals, true_and] using labels⟩

/-- A computational bare-body step enters the original block's running phase.
The ambient target typing supplies the real signature and operand split. The
result has the full recursive `UL` relation, including related called bodies. -/
theorem block_active_run_match {body : List Instr}
    {F : FuncInst H → FuncInst H → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel (fun x y => UIL body y x) fi gi)
    {s s' t : Store H} {f f' : Frame} {vs bodyValues : List Val} {bt : BlockType}
    {sourceRest targetRest after tail : List Admin} {e : Admin}
    (stores : StoreRel F s t) (rest : UL body targetRest sourceRest)
    (typed : ContextTyped ⟨t, f, vals vs ++ [.plain (.block bt body)] ++ targetRest⟩)
    (shape : expression body = vals bodyValues ++ e :: tail)
    (he : e.val? = none) (notrap : e ≠ .trap) (nothrow : e ≠ .plain .throwRef)
    (safe : NoEsc (expression body))
    (selected : Step P Det.noHost
      ⟨s, f, vals vs ++ expression body ++ sourceRest⟩ ⟨s', f', after⟩) :
    ∃ next : Config H,
      Relation.TransGen (Step P Det.noHost)
        ⟨t, f, vals vs ++ [.plain (.block bt body)] ++ targetRest⟩ next ∧
      CfgRel F (fun x y => UL body y x) ⟨s', f', after⟩ next ∧ ContextTyped next := by
  obtain ⟨pre, args, ps, rs, split, resolved, arity⟩ := ContextTyped.block_ready typed
  obtain ⟨t', innerAfter, sourceCore, matched, stores', safe', afterEq, related⟩ :=
    block_active_match (BI := fun x y => UIL body y x) (B := fun x y => UL body y x)
      hF stores resolved arity (by simpa only [split] using typed)
      shape he notrap nothrow (safe.vals_left args) (by simpa only [split] using selected)
  have core := UL.of_core_reverse related
  obtain ⟨sourceInner, sourceEq, running⟩ := UL.vals_append_inv core
  have result : UL body (vals pre ++ [.label rs.length [] innerAfter] ++ targetRest) after := by
    rw [afterEq, sourceEq]
    simpa only [List.append_assoc, List.singleton_append] using
      (UL.of_vals pre).append (UL.run running safe' rest)
  have matched' : Relation.TransGen (Step P Det.noHost)
      ⟨t, f, vals vs ++ [.plain (.block bt body)] ++ targetRest⟩
      ⟨t', f', vals pre ++ [.label rs.length [] innerAfter] ++ targetRest⟩ := by
    simpa only [split] using matched
  exact ⟨_, matched', ⟨stores', rfl, result⟩, typed.steps matched'.to_reflTransGen⟩

/-- When the bare region is already values, the target enters and leaves its
block, preserving its literal outer prefix and the recursive continuation. -/
theorem block_values_run_related {body : List Instr} {F : FuncInst H → FuncInst H → Prop}
    {s t : Store H} {f : Frame} {vs us : List Val} {bt : BlockType}
    {sourceRest targetRest : List Admin}
    (stores : StoreRel F s t) (rest : UL body targetRest sourceRest)
    (typed : ContextTyped ⟨t, f, vals vs ++ [.plain (.block bt body)] ++ targetRest⟩)
    (values : expression body = vals us) :
    ∃ next : Config H,
      Steps P Det.noHost ⟨t, f, vals vs ++ [.plain (.block bt body)] ++ targetRest⟩ next ∧
      CfgRel F (fun x y => UL body y x)
        ⟨s, f, vals vs ++ expression body ++ sourceRest⟩ next ∧ ContextTyped next := by
  have run := Steps.append_right (block_values_run (P := P) typed.suffix values) targetRest
  refine ⟨⟨t, f, vals vs ++ vals us ++ targetRest⟩, run, ⟨stores, rfl, ?_⟩, typed.steps run⟩
  rw [values]
  exact ((UL.of_vals vs).append (UL.of_vals us)).append rest

/-- A trap or thrown exception discards the inner and outer continuations of
an inserted runtime label, retaining the exact kernel and store/frame. -/
theorem label_kernel_run {host : HostSemantics H} {s : Store H} {f : Frame}
    {n : Nat} {cont : List Instr} {pre inner : List Val} {rest suffix k : List Admin}
    (kernel : k = [.trap] ∨ ∃ a, k = throwing a) :
    Steps P host
      ⟨s, f, vals pre ++ [.label n cont (vals inner ++ k ++ rest)] ++ suffix⟩
      ⟨s, f, k⟩ := by
  have inside := Closure.steps_label (Closure.steps_kernel (P := P) (host := host)
    (t := s) (f := f) kernel inner rest) n cont
  have bubble : Step P host ⟨s, f, [.label n cont k]⟩ ⟨s, f, k⟩ := by
    rcases kernel with rfl | ⟨a, rfl⟩
    · exact .trapLabel
    · exact .throwRefLabel
  exact (Steps.append_right (Steps.vals_left (inside.tail bubble) pre) suffix).trans
    (Closure.steps_kernel kernel pre suffix)

/-- Once the actual block's inner code has a trap/exception kernel, entry and
context discard reach exactly that kernel, including both outer continuations. -/
theorem block_kernel_run {host : HostSemantics H} {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {ps rs : List CValType}
    {pre args inner : List Val} {rest suffix k : List Admin}
    (resolved : f.module.blockType? bt = some (ps, rs)) (arity : args.length = ps.length)
    (kernel : k = [.trap] ∨ ∃ a, k = throwing a)
    (shape : vals args ++ expression body = vals inner ++ k ++ rest) :
    Steps P host ⟨s, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ suffix⟩
      ⟨s, f, k⟩ := by
  have entry : Step P host
      ⟨s, f, vals (pre ++ args) ++ [.plain (.block bt body)] ++ suffix⟩
      ⟨s, f, vals pre ++ [.label rs.length [] (vals inner ++ k ++ rest)] ++ suffix⟩ := by
    simpa only [shape, vals_append, List.append_assoc] using
      Step.append_right (Step.vals_left (Step.block (P := P) (host := host)
        (s := s) (body := body) resolved arity) pre) suffix
  exact entry.steps.trans (label_kernel_run kernel)

end Silmaril.Wasm.Binaryen.Unwrap
