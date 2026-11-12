module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Sim.PBCommon

@[expose] public section

/-! # Step simulation: basic pure head rules

Parametric, numeric and `local.tee` rules of `PureStep`: each is exactly one
Core step (`ParametricStep`, `NumericStep` under `Profile.spec`, or
`VariableStep.localTee`) between the images.
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Lime1.Execution.ToCore

variable {H : Type}

theorem pure_nop {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {c : ToCore.CConfig H} (hs : Sim ⟨s, f, [.source .nop]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, []⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .parametric .nop)

theorem pure_unreachable {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {c : ToCore.CConfig H} (hs : Sim ⟨s, f, [.source .unreachable]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .parametric .unreachable)

theorem pure_drop {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame} {v : Value}
    {c : ToCore.CConfig H} (hs : Sim ⟨s, f, [value v, .source .drop]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, []⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .parametric (.drop _))

theorem pure_selectZero {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {a b : Value} (_sameType : a.type = b.type) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value a, value b, value (.int .i32 0), .source .select]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value b]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .parametric (.selectFalse _ _ _))

theorem pure_selectNonzero {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {a b : Value} (_sameType : a.type = b.type) {cc : BitVec 32} (h : cc ≠ 0)
    {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value a, value b, value (.int .i32 cc), .source .select]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value a]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .parametric (.selectTrue h))

theorem pure_localTee {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {i : LocalIdx} {v : Value} {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value v, .source (.localTee i)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value v, value v, .source (.localSet i)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .variable .localTee)

theorem pure_intUnary {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : IntType} {op : IntUnOp} {x : BitVec t.width} (_valid : op.toCore.valid t = true)
    {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int t x), .source (.intUnOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.int t (Numerics.intUnOp t op.toCore x))]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric .intUnOp)

theorem pure_intBinary {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : IntType} {op : IntBinOp} {x y z : BitVec t.width}
    (h : Numerics.intBinOp t op x y = .ok z) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int t x), value (.int t y), .source (.intBinOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.int t z)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.intBinOp h))

theorem pure_intBinaryTrap {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {err : Numerics.IntTrap}
    (h : Numerics.intBinOp t op x y = .error err) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int t x), value (.int t y), .source (.intBinOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.intBinOpTrap h))

theorem pure_intTest {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : IntType} {op : IntTestOp} {x : BitVec t.width} {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int t x), .source (.intTestOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.int .i32 (Numerics.intTestOp t op x))]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric .intTestOp)

theorem pure_intRel {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : IntType} {op : IntRelOp} {x y : BitVec t.width} {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int t x), value (.int t y), .source (.intRelOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.int .i32 (Numerics.intRelOp t op x y))]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric .intRelOp)

theorem pure_floatUnary {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : FloatType} {op : FloatUnOp} {x y : BitVec t.width}
    (h : Numerics.floatUnOpRel t op x y) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.float t x), .source (.floatUnOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.float t y)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.floatUnOp h))

theorem pure_floatBinary {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : FloatType} {op : FloatBinOp} {x y z : BitVec t.width}
    (h : Numerics.floatBinOpRel t op x y z) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.float t x), value (.float t y), .source (.floatBinOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.float t z)]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.floatBinOp h))

theorem pure_floatRel {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {t : FloatType} {op : FloatRelOp} {x y : BitVec t.width} {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.float t x), value (.float t y), .source (.floatRelOp t op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value (.int .i32 (Numerics.floatRelOp t op x y))]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric .floatRelOp)

theorem pure_convert {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {op : ConvertOp} {x : Numerics.NumValue op.source} {y : Numerics.NumValue op.target}
    (h : Numerics.convertRel op x (.ok y)) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value ⟨op.source, x⟩, .source (.convert op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [value ⟨op.target, y⟩]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.convert h))

theorem pure_convertTrap {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {op : ConvertOp} {x : Numerics.NumValue op.source} {err : Numerics.FloatTrap}
    (h : Numerics.convertRel op x (.error err)) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value ⟨op.source, x⟩, .source (.convert op)]⟩ c) :
    ∃ c', Relation.TransGen (Silmaril.Wasm.Execution.Core.Step Profile.spec tgt) c c' ∧
      Sim ⟨s, f, [.trap]⟩ c' :=
  pb_finish_same hs (by simp) (by simp) (by pb_norm; exact .numeric (.convertTrap h))

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
