module

public import Silmaril.Wasm.Binaryen.MergeBackState

@[expose] public section

/-! # Exact backward matching for structural control rules

These lemmas retain the source-to-target relation after the particular target
control transition, including rewritten block bodies and label continuations.
-/

namespace Silmaril.Wasm.Binaryen.MergeUntyped

open Execution.Core Numerics Validation
open Silmaril.Wasm.Link.GC Silmaril.Wasm.Link.GC.AdminRelation

variable {H : Type} {P : Profile} {host : HostSemantics H}

private theorem attached_instructions {r : Relocation} {body body' : List Instr}
    (rewrite : body.attach.mapM (fun nested => instruction? r nested.val) = some body') :
    instructions? r body = some body' := by
  rw [List.mapM_subtype (g := instruction? r) (fun _ _ => rfl), List.unattach_attach] at rewrite
  exact rewrite

private theorem empty_instructions (mode : Mode) : Instructions mode [] [] := by
  cases mode <;> rfl

private theorem singleton_instructions {mode : Mode} {i j : Instr}
    (rewrite : Instruction mode i j) : Instructions mode [i] [j] := by
  cases mode with
  | same => change i = j at rewrite; cases rewrite; rfl
  | relocated r =>
    change instruction? r i = some j at rewrite
    simp only [Instructions, instructions?, List.mapM_cons, List.mapM_nil, rewrite,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]

private theorem branch_instruction (mode : Mode) (l : LabelIdx) :
    Instruction mode (.br l) (.br l) := by
  cases mode <;> simp only [Instruction, instruction?]

private theorem block_body {mode : Mode} {bt₀ bt : BlockType} {body₀ body : List Instr}
    (rewrite : Instruction mode (.block bt₀ body₀) (.block bt body)) :
    Instructions mode body₀ body := by
  cases mode with
  | same => change Instr.block bt₀ body₀ = Instr.block bt body at rewrite; cases rewrite; rfl
  | relocated r =>
    simp only [Instruction, instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at rewrite
    obtain ⟨bt', _, body', hbody, heq⟩ := rewrite
    cases heq
    exact attached_instructions hbody

private theorem loop_body {mode : Mode} {bt₀ bt : BlockType} {body₀ body : List Instr}
    (rewrite : Instruction mode (.loop bt₀ body₀) (.loop bt body)) :
    Instructions mode body₀ body := by
  cases mode with
  | same => change Instr.loop bt₀ body₀ = Instr.loop bt body at rewrite; cases rewrite; rfl
  | relocated r =>
    simp only [Instruction, instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at rewrite
    obtain ⟨bt', _, body', hbody, heq⟩ := rewrite
    cases heq
    exact attached_instructions hbody

private theorem if_blocks {mode : Mode} {bt₀ bt : BlockType} {yes₀ no₀ yes no : List Instr}
    (rewrite : Instruction mode (.if_ bt₀ yes₀ no₀) (.if_ bt yes no)) :
    Instruction mode (.block bt₀ yes₀) (.block bt yes) ∧
      Instruction mode (.block bt₀ no₀) (.block bt no) := by
  cases mode with
  | same =>
    change Instr.if_ bt₀ yes₀ no₀ = Instr.if_ bt yes no at rewrite
    cases rewrite
    exact ⟨rfl, rfl⟩
  | relocated r =>
    simp only [Instruction, instruction?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at rewrite
    obtain ⟨bt', hbt, yes', hyes, no', hno, heq⟩ := rewrite
    cases heq
    constructor <;>
      simp only [Instruction, instruction?, hbt, hyes, hno, Option.bind_eq_bind,
        Option.bind_some, Option.pure_def]

private theorem cast_test_type {mode : Mode} {left right : Frame} {failure : Bool}
    {l : LabelIdx} {a₀ b₀ a b : RefType} (frames : Frames mode left right)
    (rewrite : Instruction mode (StructuralSimulation.cast_instr failure l a₀ b₀)
      (StructuralSimulation.cast_instr failure l a b))
    (scope : b₀.Scoped left.module.types.length) :
    left.module.instRef b₀ = right.module.instRef b := by
  obtain ⟨a', b', equation, types⟩ := StructuralSimulation.cast_annotation frames rewrite scope
  cases failure <;> simp only [StructuralSimulation.cast_instr, Bool.false_eq_true,
    ↓reduceIte, Instr.brOnCast.injEq, Instr.brOnCastFail.injEq] at equation
  all_goals obtain ⟨_, rfl, rfl⟩ := equation
  all_goals exact types.symm

private theorem returnCallRef_source {mode : Mode} {left right : ModuleInst} {c₀ c : Admin}
    (control : Control mode left right [c₀] [c]) (call : c.IsReturnCallRef) :
    c₀.IsReturnCallRef := by
  obtain ⟨c', rest, equation, call', _⟩ := control.returnCallRef_right call
  have same : c₀ = c' := (List.cons.inj equation).1
  exact same ▸ call'

namespace BackwardStep

theorem block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {ps rs : List CValType} (lookup : f.module.blockType? bt = some (ps, rs))
    (arity : vs.length = ps.length) :
    BackwardStep P host ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
      ⟨s, f, [.label rs.length [] (vals vs ++ expression body)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨i, rfl, rewrite⟩ := matching.code.vals_plain_right rfl
  obtain ⟨bt₀, body₀, rfl, lookup₀⟩ := inv_block matching.frames.view rewrite
    (xi_of_mem scope (by simp)) lookup
  exact ⟨_, .block lookup₀ arity, matching.stores, matching.frames,
    .label (empty_instructions _) ((Control.values _ _ _ vs).append
      (Control.expression (block_body rewrite))) .nil⟩

theorem loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {ps rs : List CValType} (lookup : f.module.blockType? bt = some (ps, rs))
    (arity : vs.length = ps.length) :
    BackwardStep P host ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
      ⟨s, f, [.label ps.length [.loop bt body] (vals vs ++ expression body)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨i, rfl, rewrite⟩ := matching.code.vals_plain_right rfl
  obtain ⟨bt₀, body₀, rfl, lookup₀⟩ := inv_loop matching.frames.view rewrite
    (xi_of_mem scope (by simp)) lookup
  exact ⟨_, .loop lookup₀ arity, matching.stores, matching.frames,
    .label (singleton_instructions rewrite) ((Control.values _ _ _ vs).append
      (Control.expression (loop_body rewrite))) .nil⟩

theorem ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {yes no : List Instr} (condition : c ≠ 0) :
    BackwardStep P host ⟨s, f, [constI32 c, .plain (.if_ bt yes no)]⟩
      ⟨s, f, [.plain (.block bt yes)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨bt₀, yes₀, no₀, rfl⟩ := inv_if rewrite
  exact ⟨_, .ifTrue condition, matching.stores, matching.frames, .plain (if_blocks rewrite).1 .nil⟩

theorem ifFalse {s : Store H} {f : Frame} {bt : BlockType} {yes no : List Instr} :
    BackwardStep P host ⟨s, f, [constI32 0, .plain (.if_ bt yes no)]⟩
      ⟨s, f, [.plain (.block bt no)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨bt₀, yes₀, no₀, rfl⟩ := inv_if rewrite
  exact ⟨_, .ifFalse, matching.stores, matching.frames, .plain (if_blocks rewrite).2 .nil⟩

theorem labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val} :
    BackwardStep P host ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  obtain rfl := body.vals_right_exact
  exact ⟨_, .labelVals, matching.stores, matching.frames, Control.values _ _ _ vs⟩

theorem brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin}
    (zero : l.toNat = 0) (arity : vs.length = n) :
    BackwardStep P host
      ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest', rfl, continuation, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  rw [← vals_append] at body
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  refine ⟨⟨s₀, f₀, vals vs ++ expression cont₀⟩, ?_, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append (Control.expression continuation)⟩
  have step : Step P host
      ⟨s₀, f₀, [.label n cont₀ (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest₀)]⟩ _ :=
    .brLabelZero zero arity
  rwa [← vals_append] at step

theorem brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} (positive : 0 < l.toNat) :
    BackwardStep P host ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest', rfl, _, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brLabelSucc positive, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append (.plain (branch_instruction _ _) .nil)⟩

theorem brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} :
    BackwardStep P host ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨body₀, rest', rfl, _, _, body, tail⟩ := matching.code.handler_right
  obtain rfl := tail.nil_right
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brHandler, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append (.plain (branch_instruction _ _) .nil)⟩

theorem brIfTrue {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx}
    (condition : c ≠ 0) :
    BackwardStep P host ⟨s, f, [constI32 c, .plain (.brIf l)]⟩ ⟨s, f, [.plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brIfTrue condition, matching.stores, matching.frames,
    .plain (branch_instruction _ _) .nil⟩

theorem brIfFalse {s : Store H} {f : Frame} {l : LabelIdx} :
    BackwardStep P host ⟨s, f, [constI32 0, .plain (.brIf l)]⟩ ⟨s, f, []⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brIfFalse, matching.stores, matching.frames, .nil⟩

theorem brTableLt {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx}
    {fallback label : LabelIdx} (lookup : ls[i.toNat]? = some label) :
    BackwardStep P host ⟨s, f, [constI32 i, .plain (.brTable ls fallback)]⟩
      ⟨s, f, [.plain (.br label)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control j rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brTableLt lookup, matching.stores, matching.frames,
    .plain (branch_instruction _ _) .nil⟩

theorem brTableGe {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx}
    {fallback : LabelIdx} (bound : ls.length ≤ i.toNat) :
    BackwardStep P host ⟨s, f, [constI32 i, .plain (.brTable ls fallback)]⟩
      ⟨s, f, [.plain (.br fallback)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control j rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brTableGe bound, matching.stores, matching.frames,
    .plain (branch_instruction _ _) .nil⟩

theorem brOnNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
    BackwardStep P host ⟨s, f, [.ref .null, .plain (.brOnNull l)]⟩
      ⟨s, f, [.plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brOnNullNull, matching.stores, matching.frames,
    .plain (branch_instruction _ _) .nil⟩

theorem brOnNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx}
    (nonnull : v ≠ .ref .null) :
    BackwardStep P host ⟨s, f, [v.toAdmin, .plain (.brOnNull l)]⟩ ⟨s, f, [v.toAdmin]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brOnNullAddr nonnull, matching.stores, matching.frames, .val .nil⟩

theorem brOnNonNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
    BackwardStep P host ⟨s, f, [.ref .null, .plain (.brOnNonNull l)]⟩ ⟨s, f, []⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brOnNonNullNull, matching.stores, matching.frames, .nil⟩

theorem brOnNonNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx}
    (nonnull : v ≠ .ref .null) :
    BackwardStep P host ⟨s, f, [v.toAdmin, .plain (.brOnNonNull l)]⟩
      ⟨s, f, [v.toAdmin, .plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  inv_head control i rewrite
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .brOnNonNullAddr nonnull, matching.stores, matching.frames,
    .val (.plain (branch_instruction _ _) .nil)⟩

theorem brOnCastSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx}
    {a b : RefType} (valid : RefOk s r (f.module.instRef b)) :
    BackwardStep P host ⟨s, f, [.ref r, .plain (.brOnCast l a b)]⟩
      ⟨s, f, [.ref r, .plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCast rewrite
  have annotationScope := (xi_of_mem (i := .brOnCast l a₀ b₀) scope (by simp)).1
  simp only [CodeScope.Instruction] at annotationScope
  have types := cast_test_type (failure := false) matching.frames rewrite
    annotationScope.2
  have valid₀ := matching.stores.refOk_reverse valid
  rw [← types] at valid₀
  exact ⟨_, .brOnCastSucceed valid₀, matching.stores, matching.frames,
    .ref (.plain (branch_instruction _ _) .nil)⟩

theorem brOnCastFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx}
    {a b : RefType} (invalid : ¬ RefOk s r (f.module.instRef b)) :
    BackwardStep P host ⟨s, f, [.ref r, .plain (.brOnCast l a b)]⟩ ⟨s, f, [.ref r]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCast rewrite
  have annotationScope := (xi_of_mem (i := .brOnCast l a₀ b₀) scope (by simp)).1
  simp only [CodeScope.Instruction] at annotationScope
  have types := cast_test_type (failure := false) matching.frames rewrite
    annotationScope.2
  have invalid₀ : ¬ RefOk s₀ r (f₀.module.instRef b₀) := by
    rw [types]
    exact fun h => invalid (matching.stores.refOk h)
  exact ⟨_, .brOnCastFail invalid₀, matching.stores, matching.frames, .ref .nil⟩

theorem brOnCastFailSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx}
    {a b : RefType} (valid : RefOk s r (f.module.instRef b)) :
    BackwardStep P host ⟨s, f, [.ref r, .plain (.brOnCastFail l a b)]⟩ ⟨s, f, [.ref r]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCastFail rewrite
  have annotationScope := (xi_of_mem (i := .brOnCastFail l a₀ b₀) scope (by simp)).1
  simp only [CodeScope.Instruction] at annotationScope
  have types := cast_test_type (failure := true) matching.frames rewrite
    annotationScope.2
  have valid₀ := matching.stores.refOk_reverse valid
  rw [← types] at valid₀
  exact ⟨_, .brOnCastFailSucceed valid₀, matching.stores, matching.frames, .ref .nil⟩

theorem brOnCastFailFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx}
    {a b : RefType} (invalid : ¬ RefOk s r (f.module.instRef b)) :
    BackwardStep P host ⟨s, f, [.ref r, .plain (.brOnCastFail l a b)]⟩
      ⟨s, f, [.ref r, .plain (.br l)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  have control := matching.code
  inv_head control i rewrite
  obtain ⟨a₀, b₀, rfl⟩ := inv_brOnCastFail rewrite
  have annotationScope := (xi_of_mem (i := .brOnCastFail l a₀ b₀) scope (by simp)).1
  simp only [CodeScope.Instruction] at annotationScope
  have types := cast_test_type (failure := true) matching.frames rewrite
    annotationScope.2
  have invalid₀ : ¬ RefOk s₀ r (f₀.module.instRef b₀) := by
    rw [types]
    exact fun h => invalid (matching.stores.refOk h)
  exact ⟨_, .brOnCastFailFail invalid₀, matching.stores, matching.frames,
    .ref (.plain (branch_instruction _ _) .nil)⟩

theorem call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (lookup : f.module.funcs[x.toNat]? = some a) (definition : s.funcs[a]? = some fi) :
    BackwardStep P host ⟨s, f, [.plain (.call x)]⟩
      ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨i, rfl, rewrite⟩ := Control.vals_plain_right (vs := []) matching.code rfl
  obtain ⟨x₀, rfl, lookup₀⟩ := inv_call matching.frames.view rewrite
    (xi_of_mem scope (by simp)) lookup
  obtain ⟨fi₀, definition₀, functions⟩ := matching.stores.function_lookup_reverse definition
  have sourceStep := Step.call (P := P) (host := host) (f := f₀) lookup₀ definition₀
  rw [functions.type_eq] at sourceStep
  exact ⟨_, sourceStep, matching.stores, matching.frames, .ref (.callRefType .nil)⟩

theorem returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (lookup : f.module.funcs[x.toNat]? = some a) (definition : s.funcs[a]? = some fi) :
    BackwardStep P host ⟨s, f, [.plain (.returnCall x)]⟩
      ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨i, rfl, rewrite⟩ := Control.vals_plain_right (vs := []) matching.code rfl
  obtain ⟨x₀, rfl, lookup₀⟩ := inv_returnCall matching.frames.view rewrite
    (xi_of_mem scope (by simp)) lookup
  obtain ⟨fi₀, definition₀, functions⟩ := matching.stores.function_lookup_reverse definition
  have sourceStep := Step.returnCall (P := P) (host := host) (f := f₀) lookup₀ definition₀
  rw [functions.type_eq] at sourceStep
  exact ⟨_, sourceStep, matching.stores, matching.frames, .ref (.returnCallRefType .nil)⟩

theorem callRefNull {s : Store H} {f : Frame} {c : Admin} (call : c.IsCallRef) :
    BackwardStep P host ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨rest, rfl, tail⟩ := matching.code.ref_right
  obtain ⟨c₀, rest₀, rfl, call₀, tail₀⟩ := tail.callRef_right call
  obtain rfl := tail₀.nil_right
  exact ⟨_, .callRefNull call₀, matching.stores, matching.frames, .trap .nil⟩

theorem callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (call : c.IsCallRef) (definition : s.funcs[a]? = some fi)
    (signature : Expand fi.type (.func ps rs)) (arity : vs.length = ps.length)
    (wasm : fi.code = .wasm code) :
    BackwardStep P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨R, rfl, body⟩ := matching.code.vals_right
  obtain ⟨rest, rfl, tail⟩ := body.ref_right
  obtain ⟨c₀, rest₀, rfl, call₀, tail₀⟩ := tail.callRef_right call
  obtain rfl := tail₀.nil_right
  obtain ⟨fi₀, definition₀, functions⟩ := matching.stores.function_lookup_reverse definition
  obtain ⟨code₀, wasm₀⟩ := Function.wasm_back functions wasm
  obtain ⟨code', calleeMode, wasm', frames, codeRelation⟩ := function_entry functions wasm₀ vs
  rw [wasm] at wasm'
  cases wasm'
  exact ⟨_, .callRefFunc call₀ definition₀ (functions.type_eq ▸ signature) arity wasm₀,
    matching.stores, matching.frames,
    .frame frames (.label (empty_instructions _) codeRelation .nil) .nil⟩

theorem callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
    BackwardStep P host ⟨s, f, [.plain (.callIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨i, rfl, rewrite⟩ := Control.vals_plain_right (vs := []) matching.code rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  cases mode with
  | same => exact ⟨_, .callIndirect, matching.stores, matching.frames,
      .plain rfl (.plain rfl (.plain rfl .nil))⟩
  | relocated r => simp only [Instruction, instruction?, reduceCtorEq] at rewrite

theorem returnCallIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
    BackwardStep P host ⟨s, f, [.plain (.returnCallIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.returnCallRef y)]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨i, rfl, rewrite⟩ := Control.vals_plain_right (vs := []) matching.code rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  cases mode with
  | same => exact ⟨_, .returnCallIndirect, matching.stores, matching.frames,
      .plain rfl (.plain rfl (.plain rfl .nil))⟩
  | relocated r => simp only [Instruction, instruction?, reduceCtorEq] at rewrite

theorem returnCallRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {c : Admin} {rest : List Admin} (call : c.IsReturnCallRef) :
    BackwardStep P host ⟨s, f, [.label n cont (vals vs ++ [c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [c]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest', rfl, _, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  rw [List.append_assoc] at body
  obtain ⟨R, rfl, hR⟩ := body.vals_right
  obtain ⟨c₀, rest₀, rfl, annotation, _⟩ := hR.cons_right
  have call₀ := returnCallRef_source annotation call
  refine ⟨⟨s₀, f₀, vals vs ++ [c₀]⟩, ?_, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append annotation⟩
  simpa only [List.append_assoc, List.singleton_append] using
    (Step.returnCallRefLabel (P := P) (host := host) (s := s₀) (f := f₀)
      (k := n) (cont := cont₀) (vs := vs) (rest := rest₀) call₀)

theorem returnCallRefHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {c : Admin} {rest : List Admin} (call : c.IsReturnCallRef) :
    BackwardStep P host ⟨s, f, [.handler n cs (vals vs ++ [c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [c]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨body₀, rest', rfl, _, _, body, tail⟩ := matching.code.handler_right
  obtain rfl := tail.nil_right
  rw [List.append_assoc] at body
  obtain ⟨R, rfl, hR⟩ := body.vals_right
  obtain ⟨c₀, rest₀, rfl, annotation, _⟩ := hR.cons_right
  have call₀ := returnCallRef_source annotation call
  refine ⟨⟨s₀, f₀, vals vs ++ [c₀]⟩, ?_, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append annotation⟩
  simpa only [List.append_assoc, List.singleton_append] using
    (Step.returnCallRefHandler (P := P) (host := host) (s := s₀) (f := f₀)
      (k := n) (cs := cs) (vs := vs) (rest := rest₀) call₀)

theorem returnCallRefFrameNull {s : Store H} {f fi : Frame} {n : Nat}
    {vs : List Val} {c : Admin} {rest : List Admin} (call : c.IsReturnCallRef) :
    BackwardStep P host ⟨s, f, [.frame n fi (vals vs ++ [.ref .null, c] ++ rest)]⟩
      ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨innerMode, fi₀, body₀, rest', rfl, _, body, tail⟩ := matching.code.frame_right
  obtain rfl := tail.nil_right
  rw [List.append_assoc] at body
  obtain ⟨R, rfl, hR⟩ := body.vals_right
  obtain ⟨R', rfl, hR'⟩ := hR.ref_right
  obtain ⟨c₀, rest₀, rfl, annotation, _⟩ := hR'.cons_right
  have call₀ := returnCallRef_source annotation call
  refine ⟨⟨s₀, f₀, [.trap]⟩, ?_, matching.stores, matching.frames, .trap .nil⟩
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    (Step.returnCallRefFrameNull (P := P) (host := host) (s := s₀) (f := f₀)
      (fi := fi₀) (k := n) (vs := vs) (rest := rest₀) call₀)

theorem returnCallRefFrameAddr {s : Store H} {f fi : Frame} {n : Nat}
    {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
    {ps rs : Ty (.list .val)} (call : c.IsReturnCallRef) (definition : s.funcs[a]? = some fn)
    (signature : Expand fn.type (.func ps rs)) (arity : vs.length = ps.length) :
    BackwardStep P host ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching scope
  obtain ⟨innerMode, fi₀, body₀, rest', rfl, innerFrames, body, tail⟩ := matching.code.frame_right
  obtain rfl := tail.nil_right
  rw [← vals_append, List.append_assoc] at body
  obtain ⟨R, rfl, hR⟩ := body.vals_right
  obtain ⟨R', rfl, hR'⟩ := hR.ref_right
  obtain ⟨c₀, rest₀, rfl, annotation, _⟩ := hR'.cons_right
  have call₀ := returnCallRef_source annotation call
  obtain ⟨fn₀, definition₀, functions⟩ := matching.stores.function_lookup_reverse definition
  simp only [xas_cons_iff, xa_frame, xas_nil, and_true] at scope
  have annotationScope : AdminScope.Admin fi₀.module.types.length c₀ :=
    xa_admin _ _ (scope c₀ (by simp))
  refine ⟨⟨s₀, f₀, vals vs ++ [.ref (.func a), c₀.retToCallIn fi₀.module]⟩,
    ?_, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append
      (.ref (StructuralSimulation.ret_to_call innerFrames annotation call₀ annotationScope))⟩
  have step : Step P host
      ⟨s₀, f₀, [.frame n fi₀ (vals vs' ++ vals vs ++ [.ref (.func a), c₀] ++ rest₀)]⟩ _ :=
    .returnCallRefFrameAddr call₀ definition₀ (functions.type_eq ▸ signature) arity
  rw [← vals_append] at step
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using step

theorem frameVals {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val}
    (arity : vs.length = n) :
    BackwardStep P host ⟨s, f, [.frame n fi (vals vs)]⟩ ⟨s, f, vals vs⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨innerMode, fi₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.frame_right
  obtain rfl := tail.nil_right
  obtain rfl := body.vals_right_exact
  exact ⟨_, .frameVals arity, matching.stores, matching.frames, Control.values _ _ _ vs⟩

theorem returnFrame {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val}
    {rest : List Admin} (arity : vs.length = n) :
    BackwardStep P host
      ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨innerMode, fi₀, body₀, rest', rfl, _, body, tail⟩ := matching.code.frame_right
  obtain rfl := tail.nil_right
  rw [← vals_append] at body
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  refine ⟨⟨s₀, f₀, vals vs⟩, ?_, matching.stores, matching.frames, Control.values _ _ _ vs⟩
  have step : Step P host
      ⟨s₀, f₀, [.frame n fi₀ (vals vs' ++ vals vs ++ [.plain .return_] ++ rest₀)]⟩ _ :=
    .returnFrame arity
  rwa [← vals_append] at step

theorem returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin} :
    BackwardStep P host ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest', rfl, _, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .returnLabel, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append (.plain rewrite .nil)⟩

theorem returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {rest : List Admin} :
    BackwardStep P host ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨body₀, rest', rfl, _, _, body, tail⟩ := matching.code.handler_right
  obtain rfl := tail.nil_right
  obtain ⟨i, rest₀, rfl, rewrite, _⟩ := body.vals_plain_rest_right rfl
  obtain rfl := inv_fixed rewrite (fun _ h => h)
  exact ⟨_, .returnHandler, matching.stores, matching.frames,
    (Control.values _ _ _ vs).append (.plain rewrite .nil)⟩

theorem trapInstrs {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (nonempty : vs ≠ [] ∨ rest ≠ []) :
    BackwardStep P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  have control := matching.code
  rw [List.append_assoc] at control
  obtain ⟨R, rfl, hR⟩ := control.vals_right
  obtain ⟨rest₀, rfl, tail⟩ := hR.trap_right
  have nonempty₀ : vs ≠ [] ∨ rest₀ ≠ [] := by
    rcases nonempty with h | h
    · exact .inl h
    · right
      intro empty
      subst empty
      exact h tail.nil_left
  refine ⟨⟨s₀, f₀, [.trap]⟩, ?_, matching.stores, matching.frames, .trap .nil⟩
  simpa only [List.append_assoc, List.singleton_append] using
    (Step.trapInstrs nonempty₀ : Step P host
      ⟨s₀, f₀, vals vs ++ [.trap] ++ rest₀⟩ ⟨s₀, f₀, [.trap]⟩)

theorem trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} :
    BackwardStep P host ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨cont₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.label_right
  obtain rfl := tail.nil_right
  obtain ⟨rest₀, rfl, tail₀⟩ := body.trap_right
  obtain rfl := tail₀.nil_right
  exact ⟨_, .trapLabel, matching.stores, matching.frames, .trap .nil⟩

theorem trapHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} :
    BackwardStep P host ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨body₀, rest, rfl, _, _, body, tail⟩ := matching.code.handler_right
  obtain rfl := tail.nil_right
  obtain ⟨rest₀, rfl, tail₀⟩ := body.trap_right
  obtain rfl := tail₀.nil_right
  exact ⟨_, .trapHandler, matching.stores, matching.frames, .trap .nil⟩

theorem trapFrame {s : Store H} {f fi : Frame} {n : Nat} :
    BackwardStep P host ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  rintro mode ⟨s₀, f₀, X⟩ matching _
  obtain ⟨innerMode, fi₀, body₀, rest, rfl, _, body, tail⟩ := matching.code.frame_right
  obtain rfl := tail.nil_right
  obtain ⟨rest₀, rfl, tail₀⟩ := body.trap_right
  obtain rfl := tail₀.nil_right
  exact ⟨_, .trapFrame, matching.stores, matching.frames, .trap .nil⟩

end BackwardStep

/-- Every structural control rule matches the exact chosen target successor.
This includes calls into corresponding actual wasm bodies and scoped tail-call
annotations escaping a nested frame. -/
theorem structural_back_matching {target target' : Config H} (step : Step P host target target')
    (structural : StructuralSimulation.IsStructural step) : BackwardStep P host target target' := by
  cases structural
  all_goals first
    | exact BackwardStep.block (by assumption) (by assumption)
    | exact BackwardStep.loop (by assumption) (by assumption)
    | exact BackwardStep.ifTrue (by assumption)
    | exact BackwardStep.ifFalse
    | exact BackwardStep.labelVals
    | exact BackwardStep.brLabelZero (by assumption) (by assumption)
    | exact BackwardStep.brLabelSucc (by assumption)
    | exact BackwardStep.brHandler
    | exact BackwardStep.brIfTrue (by assumption)
    | exact BackwardStep.brIfFalse
    | exact BackwardStep.brTableLt (by assumption)
    | exact BackwardStep.brTableGe (by assumption)
    | exact BackwardStep.brOnNullNull
    | exact BackwardStep.brOnNullAddr (by assumption)
    | exact BackwardStep.brOnNonNullNull
    | exact BackwardStep.brOnNonNullAddr (by assumption)
    | exact BackwardStep.brOnCastSucceed (by assumption)
    | exact BackwardStep.brOnCastFail (by assumption)
    | exact BackwardStep.brOnCastFailSucceed (by assumption)
    | exact BackwardStep.brOnCastFailFail (by assumption)
    | exact BackwardStep.call (by assumption) (by assumption)
    | exact BackwardStep.returnCall (by assumption) (by assumption)
    | exact BackwardStep.callRefNull (by assumption)
    | exact BackwardStep.callRefFunc (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption)
    | exact BackwardStep.returnCallRefLabel (by assumption)
    | exact BackwardStep.returnCallRefHandler (by assumption)
    | exact BackwardStep.returnCallRefFrameNull (by assumption)
    | exact BackwardStep.returnCallRefFrameAddr (by assumption) (by assumption) (by assumption)
        (by assumption)
    | exact BackwardStep.callIndirect
    | exact BackwardStep.returnCallIndirect
    | exact BackwardStep.frameVals (by assumption)
    | exact BackwardStep.returnFrame (by assumption)
    | exact BackwardStep.returnLabel
    | exact BackwardStep.returnHandler
    | exact BackwardStep.trapInstrs (by assumption)
    | exact BackwardStep.trapLabel
    | exact BackwardStep.trapHandler
    | exact BackwardStep.trapFrame

end Silmaril.Wasm.Binaryen.MergeUntyped
