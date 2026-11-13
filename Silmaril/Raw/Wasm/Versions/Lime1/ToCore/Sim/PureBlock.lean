module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PBCommon

@[expose] public section

/-! # Lime1 → Core step simulation: structured control head rules

For each structured-control `PureStep` constructor `K` (`block`, `loop`, `ifZero`,
`ifNonzero`, `brIfZero`, `brIfNonzero`, `brTable`), `ToCoreSim.pure_K` shows that
the head redex, related by `Sim` to a Core configuration, is matched by one Core
step. All of these redexes have rigid images (normalisation fixes them), so the
Core configuration is literally the Lime1 image, and the result is the Lime1 image
of the reduct (`blk_simple`). Block types resolve against the Core frame's
`module.types`, which are the erased = unerased images `V1.FuncType.toDefType`.
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Lime1.Execution.ToCore
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- Generic head simulation for a redex with rigid image. -/
theorem blk_simple {tgt : CHostSemantics H} {s : Store H} {f : Frame}
    {code code' : List Admin} {c : CConfig H}
    (hr : ∀ y ∈ Admin.listToCore s code, Rigid y) (hwf : Admin.listWF s code')
    (hstep : ∀ (cs : CStore H) (cf : CFrame), Frame.erase cf = f.toCore →
      Silmaril.Wasm.Execution.Core.Step Profile.spec tgt
        ⟨cs, cf, Admin.listToCore s code⟩ ⟨cs, cf, Admin.listToCore s code'⟩)
    (hs : Sim ⟨s, f, code⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, code'⟩ c' := by
  obtain ⟨hn, hcwf⟩ := hs
  obtain ⟨cs, cf, cl⟩ := c
  rw [Config.norm_eq_toCore_iff] at hn
  obtain ⟨hst, hf, hl⟩ := hn
  have hcl : cl = Admin.listToCore s code := map_norm_eq_of_rigid hr hl
  subst hcl
  refine ⟨⟨cs, cf, Admin.listToCore s code'⟩, .single (hstep cs cf hf), ?_, ?_⟩
  · rw [Config.norm_eq_toCore_iff]
    exact ⟨hst, hf, map_norm_listToCore _ _ _⟩
  · exact ⟨hcwf.1, hcwf.2.1, hwf⟩

theorem blk_types {cf : CFrame} {f : Frame} (hf : Frame.erase cf = f.toCore) :
    cf.module.types = f.module.types.map V1.FuncType.toDefType :=
  congrArg (fun x => x.module.types) hf

theorem blk_listWF_values (s : Store H) (vs : List Value) : Admin.listWF s (values vs) := by
  induction vs with
  | nil => simp [values]
  | cons v vs ih =>
    rcases v with ⟨⟨_ | _⟩, _⟩ <;>
      simpa [values, value, Admin.listWF, Admin.WF] using ih

theorem blk_listWF_expression (s : Store H) (es : Expr) : Admin.listWF s (expression es) := by
  induction es with
  | nil => simp [expression]
  | cons e es ih => simpa [expression, Admin.listWF, Admin.WF] using ih

theorem blk_listWF_append (s : Store H) (xs ys : List Admin) (hx : Admin.listWF s xs)
    (hy : Admin.listWF s ys) : Admin.listWF s (xs ++ ys) := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    simp only [List.cons_append, Admin.listWF] at hx ⊢
    exact ⟨hx.1, ih hx.2⟩

theorem blk_rigid_vals (vs : List Silmaril.Wasm.Execution.Core.Val) :
    ∀ y ∈ Silmaril.Wasm.Execution.Core.vals vs, Rigid y := by
  simp only [Silmaril.Wasm.Execution.Core.vals, List.mem_map]
  rintro _ ⟨v, _, rfl⟩; exact Rigid.val v

theorem blk_value_i32 (s : Store H) (c : BitVec 32) :
    Admin.toCore s (value (.int .i32 c)) = [Silmaril.Wasm.Execution.Core.constI32 c] := rfl

/-- Lime1 block-type resolution against the Core image of the module's types. -/
theorem blk_blockType {types : List FuncType} {bt : BlockType} {ft : FuncType}
    {m : CModuleInst} (ht : m.types = types.map V1.FuncType.toDefType)
    (h : blockType? types bt = some ft) :
    ∃ t₁ t₂, m.blockType? bt.toCore = some (t₁, t₂) ∧
      t₁.length = ft.params.length ∧ t₂.length = ft.results.length := by
  cases bt with
  | empty =>
    simp [blockType?] at h; subst h
    exact ⟨[], [], rfl, rfl, rfl⟩
  | value t =>
    simp [blockType?] at h; subst h
    exact ⟨[], _, rfl, rfl, rfl⟩
  | typeIdx i =>
    simp only [blockType?] at h
    refine ⟨ft.params.map Silmaril.Wasm.Validation.Ty.num,
      ft.results.map Silmaril.Wasm.Validation.Ty.num, ?_, by simp, by simp⟩
    simp [BlockType.toCore, Silmaril.Wasm.Execution.Core.ModuleInst.blockType?, ht, h,
      Silmaril.Wasm.Validation.DefType.funcType?, V1.FuncType.toDefType_expand]

theorem blk_src_values (vs : List Value) (i : Instr) :
    ∀ a ∈ values vs ++ [(.source i : Admin)], pb_IsSrc a := by
  simp only [values, List.mem_append, List.mem_map, List.mem_singleton]
  rintro a (⟨v, _, rfl⟩ | rfl) <;> simp

theorem pure_block {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {bt : BlockType} {body : Expr} {ft : FuncType} {vs : List Value}
    (resolved : blockType? f.module.types bt = some ft) (arity : vs.length = ft.params.length)
    (hs : Sim ⟨s, f, values vs ++ [.source (.block bt body)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.label ft.results.length [] (values vs ++ expression body)]⟩ c' := by
  refine pb_finish_same hs (blk_src_values _ _) ?_ ?_
  · simp only [Admin.listWF, Admin.WF, and_true]
    exact blk_listWF_append _ _ _ (blk_listWF_values _ _) (blk_listWF_expression _ _)
  · obtain ⟨t₁, t₂, hbt, h₁, h₂⟩ := blk_blockType (blk_types (pb_frameEq hs)) resolved
    have := Silmaril.Wasm.Execution.Core.Step.block (P := Profile.spec) (host := tgt)
      (s := c.store) (f := c.frame) (body := Expr.toCore body) (vs := vs.map Value.toCore) hbt
      (by simp [h₁, arity])
    simpa [listToCore_append, Instr.toCore, h₂, Expr.toCore_eq_map] using this

theorem pure_loop {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {bt : BlockType} {body : Expr} {ft : FuncType} {vs : List Value}
    (resolved : blockType? f.module.types bt = some ft) (arity : vs.length = ft.params.length)
    (hs : Sim ⟨s, f, values vs ++ [.source (.loop bt body)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.label ft.params.length [.loop bt body] (values vs ++ expression body)]⟩ c' := by
  refine pb_finish_same hs (blk_src_values _ _) ?_ ?_
  · simp only [Admin.listWF, Admin.WF, and_true]
    exact blk_listWF_append _ _ _ (blk_listWF_values _ _) (blk_listWF_expression _ _)
  · obtain ⟨t₁, t₂, hbt, h₁, h₂⟩ := blk_blockType (blk_types (pb_frameEq hs)) resolved
    have := Silmaril.Wasm.Execution.Core.Step.loop (P := Profile.spec) (host := tgt)
      (s := c.store) (f := c.frame) (body := Expr.toCore body) (vs := vs.map Value.toCore) hbt
      (by simp [h₁, arity])
    simpa [listToCore_append, Instr.toCore, h₁, Expr.toCore_eq_map] using this

theorem pure_ifZero {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {bt : BlockType} {left right : Expr}
    (hs : Sim ⟨s, f, [value (.int .i32 0), .source (.if_ bt left right)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.source (.block bt right)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .ifFalse)

theorem pure_ifNonzero {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {bt : BlockType} {left right : Expr} {c₀ : BitVec 32} (h : c₀ ≠ 0)
    (hs : Sim ⟨s, f, [value (.int .i32 c₀), .source (.if_ bt left right)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.source (.block bt left)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .ifTrue h)

theorem pure_brIfZero {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {l : LabelIdx}
    (hs : Sim ⟨s, f, [value (.int .i32 0), .source (.brIf l)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, []⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .brIfFalse)

theorem pure_brIfNonzero {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {l : LabelIdx} {c₀ : BitVec 32} (h : c₀ ≠ 0)
    (hs : Sim ⟨s, f, [value (.int .i32 c₀), .source (.brIf l)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.source (.br l)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .brIfTrue h)

theorem pure_brTable {tgt : CHostSemantics H} {s : Store H} {f : Frame} {c : CConfig H}
    {ls : List LabelIdx} {default : LabelIdx} {c₀ : BitVec 32}
    (hs : Sim ⟨s, f, [value (.int .i32 c₀), .source (.brTable ls default)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.source (.br (ls[c₀.toNat]?.getD default))]⟩ c' := by
  refine pb_finish_same hs (by simp) (by simp) ?_
  pb_norm
  cases hl : ls[c₀.toNat]? with
  | some l => exact .brTableLt hl
  | none => exact .brTableGe (List.getElem?_eq_none_iff.mp hl)

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
