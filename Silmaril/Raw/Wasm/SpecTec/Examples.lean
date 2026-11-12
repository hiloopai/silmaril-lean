module

public import Silmaril.Raw.Wasm.SpecTec.Encode

@[expose] public section

/-! Concrete payload checks include asymmetric operands and nonzero indices, so
schema-annotation agreement alone cannot establish these equations. -/

namespace Silmaril.Wasm.SpecTec

example : (encodeInstruction (.intLoad .i64 (some (.i16, .signed))
    ⟨⟨3, by decide⟩⟩ ⟨⟨1, by decide⟩, ⟨17, by decide⟩⟩)).toValue =
    node "LOAD" [node "I64" [],
      node "$some" [node "%_%" [node "%" [nat 16], node "S" []]],
      node "%" [nat 3],
      node "$record" [node "ALIGN" [node "%" [nat 1]],
        node "OFFSET" [node "%" [nat 17]]]] := by
  simp only [encodeInstruction]
  rfl

example : (encodeInstruction (.convert .wrap)).toValue =
    node "CVTOP" [node "I32" [], node "I64" [], node "WRAP" []] := by
  simp only [encodeInstruction]
  rfl

example : (encodeInstruction (.floatConst .f32 0xBF000000)).toValue =
    node "CONST" [node "F32" [], node "NEG" [node "NORM" [nat 0, .atom (-1)]]] := by
  simp only [encodeInstruction]
  rfl

example : (encodeInstruction (.vecExtBinOp .i8x16 .i16x8 (.extmul .high .unsigned))).toValue =
    node "VEXTBINOP" [
      node "%" [node "%X%" [node "I16" [], node "%" [nat 8]]],
      node "%" [node "%X%" [node "I8" [], node "%" [nat 16]]],
      node "EXTMUL" [node "HIGH" [], node "U" []]] := by
  simp only [encodeInstruction]
  rfl

example : (encodeInstruction (.tryTable .empty
    [.catchRef ⟨⟨2, by decide⟩⟩ ⟨⟨3, by decide⟩⟩]
    [.block (.typeIdx ⟨⟨4, by decide⟩⟩) [.intConst .i32 5]])).toValue =
    node "TRY_TABLE" [node "_RESULT" [node "$none" []],
      node "%" [node "$list" [node "CATCH_REF" [node "%" [nat 2], node "%" [nat 3]]]],
      node "$list" [node "BLOCK" [node "_IDX" [node "%" [nat 4]],
        node "$list" [node "CONST" [node "I32" [], node "%" [nat 5]]]]]] := by
  simp only [encodeInstruction, Constructor.toValue, sequenceField,
    List.attach_cons, List.attach_nil, List.map_cons, List.map_nil]
  rfl

example : (encodeInstruction (.floatLoad .f32 ⟨⟨2, by decide⟩⟩
    ⟨⟨0, by decide⟩, ⟨9, by decide⟩⟩)).toValue =
    node "LOAD" [node "F32" [], node "$none" [], node "%" [nat 2],
      node "$record" [node "ALIGN" [node "%" [nat 0]],
        node "OFFSET" [node "%" [nat 9]]]] := by
  simp only [encodeInstruction]
  rfl

end Silmaril.Wasm.SpecTec
