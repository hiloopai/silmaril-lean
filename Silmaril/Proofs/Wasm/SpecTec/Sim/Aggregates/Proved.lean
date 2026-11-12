module

public import Silmaril.Wasm.SpecTec.Sim.Aggregates.Defs
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms

/-!
# Aggregates: family R's 24 aggregate rules at `simEnv B`

Family R proved 24 of the 42 `AggregateStep` constructors as SpecTec steps for an arbitrary
environment holding the rules (`RefsGC/Aggregate.lean`, `RefsGC/AggregateIter.lean`). Here each is
restated as a forward obligation `FwdP (simEnv B) hn c c'` with the binders of its `AggregateStep`
constructor, the rule provenance discharged by `hasRuleAt_simEnv` and the `otherwise` tag table by
`readTable_simEnv`. `array.len-array` and `array.fill-succ` need the array to have fewer than
`2 ^ 32` fields; they take `Bounded s`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Aggregates

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open RefsGC

variable {H : Type} {hn : H → String} {B : Builtins}

/-- The pinned `Step_read` rules, in `simEnv B`. -/
theorem rd (B : Builtins) : Equiv.ExecRead.HasReadRules (simEnv B) := by
  have h := Equiv.ExecRead.hasReadRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The pinned `Step` rules, in `simEnv B`. -/
abbrev st (B : Builtins) : Equiv.ExecStepRules.HasStepRules (simEnv B) := hasStepRules_simEnv B

/-- An array of a bounded store has fewer than `2 ^ 32` fields. -/
theorem Bounded.array {s : Store H} (hb : Bounded s) {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) : ai.fields.length < 2 ^ 32 :=
  hb.arrays ai (List.mem_of_getElem? ha)

-- Every lemma takes the same three hypotheses, so that the assembly can apply them uniformly.
set_option linter.unusedSectionVars false

section
variable (T : TypingFacts (simEnv B) hn) (R : RTyping (simEnv B)) (G : RStoreFuns (simEnv B))
include T R G

/-! ## Null traps -/

theorem fwd_structGetNull {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : FieldIdx} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, .plain (.structGet sx x i)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_structGetNull (rd B).structGetNull R hz hc

theorem fwd_structSetNull {s : Store H} {f : Frame} {x : TypeIdx} {i : FieldIdx} {v : Val} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, v.toAdmin, .plain (.structSet x i)]⟩
      ⟨s, f, [.trap]⟩ :=
  RefsGC.fwd_structSetNull (st B).structSetNull T R

theorem fwd_arrayGetNull {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : BitVec 32} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, constI32 i, .plain (.arrayGet sx x)]⟩
      ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayGetNull (rd B).arrayGetNull R hz hc

theorem fwd_arraySetNull {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s, f, [.trap]⟩ :=
  RefsGC.fwd_arraySetNull (st B).arraySetNull T R

theorem fwd_arrayLenNull {s : Store H} {f : Frame} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, .plain .arrayLen]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayLenNull (rd B).arrayLenNull hz hc

theorem fwd_arrayFillNull {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val} :
    FwdP (simEnv B) hn
      ⟨s, f, [.ref .null, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
      ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayFillNull (rd B).arrayFillNull T R hz hc

theorem fwd_arrayCopyNull₁ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32}
    {r : Ref} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, constI32 i₁, .ref r, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayCopyNull₁ (rd B).arrayCopyNull1 T R hz hc

theorem fwd_arrayCopyNull₂ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32}
    {r : Ref} :
    FwdP (simEnv B) hn ⟨s, f, [.ref r, constI32 i₁, .ref .null, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayCopyNull₂ (rd B).arrayCopyNull2 T R hz hc

theorem fwd_arrayInitElemNull {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j n : BitVec 32} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayInitElemNull (rd B).arrayInitElemNull R hz hc

theorem fwd_arrayInitDataNull {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} :
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayInitDataNull (rd B).arrayInitDataNull R hz hc

/-! ## Out-of-bounds traps -/

theorem fwd_arrayGetOob {s : Store H} {f : Frame} {sx : Option Signedness} {x : TypeIdx}
    {i : BitVec 32} {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
    (h : ai.fields.length ≤ i.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, .plain (.arrayGet sx x)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayGetOob (rd B).arrayGetOob R G ha h hz hc

theorem fwd_arraySetOob {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : ai.fields.length ≤ i.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x)]⟩
      ⟨s, f, [.trap]⟩ :=
  RefsGC.fwd_arraySetOob (st B).arraySetOob T R G ha h

theorem fwd_arrayFillOob {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
    (h : ai.fields.length < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
      ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayFillOob (rd B).arrayFillOob T R G ha h hz hc

theorem fwd_arrayCopyOob₁ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32}
    {a₁ a₂ : Nat} {ai₁ : ArrayInst} (ha : s.arrays[a₁]? = some ai₁)
    (h : ai₁.fields.length < i₁.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayCopyOob₁ (rd B).arrayCopyOob1 R G ha h hz hc

theorem fwd_arrayCopyOob₂ {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ n : BitVec 32}
    {a₁ a₂ : Nat} {ai₂ : ArrayInst} (ha : s.arrays[a₂]? = some ai₂)
    (h : ai₂.fields.length < i₂.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 n,
      .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc => sread_arrayCopyOob₂ (rd B).arrayCopyOob2 R G ha h hz hc

theorem fwd_arrayInitElemOob₁ {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j n : BitVec 32} {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
    (h : ai.fields.length < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc =>
    sread_arrayInitElemOob₁ (rd B).arrayInitElemOob1 R G ha h hz hc

theorem fwd_arrayInitDataOob₁ {s : Store H} {f : Frame} {x : TypeIdx} {y : DataIdx}
    {i j n : BitVec 32} {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
    (h : ai.fields.length < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitData x y)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz hc =>
    sread_arrayInitDataOob₁ (rd B).arrayInitDataOob1 R G ha h hz hc

theorem fwd_arrayNewElemOob {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i n : BitVec 32} {ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (h : ei.refs.length < i.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, constI32 n, .plain (.arrayNewElem x y)]⟩
      ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz _ => sread_arrayNewElemOob (rd B).arrayNewElemOob R G he h hz

theorem fwd_arrayInitElemOob₂ {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j n : BitVec 32} {a ea : Nat} {ei : ElemInst} (he : s.elem? f y = some (ea, ei))
    (h : ei.refs.length < j.toNat + n.toNat) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 n,
      .plain (.arrayInitElem x y)]⟩ ⟨s, f, [.trap]⟩ :=
  fwd_of_sread T (st B).read fun hz _ =>
    sread_arrayInitElemOob₂ (rd B).arrayInitElemOob2 R G he h hz

/-! ## Length, and the `otherwise` rules of the iterating instructions -/

theorem fwd_arrayLenArray {s : Store H} {f : Frame} {a : Nat} {ai : ArrayInst}
    (ha : s.arrays[a]? = some ai) (hb : Bounded s) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, .plain .arrayLen]⟩
      ⟨s, f, [constI32 (BitVec.ofNat 32 ai.fields.length)]⟩ :=
  fwd_of_sread T (st B).read fun hz hc =>
    sread_arrayLenArray (rd B).arrayLenArray R G ha (hb.array ha) hz hc

theorem fwd_arrayFillZero {s : Store H} {f : Frame} {x : TypeIdx} {i : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai) (h : i.toNat ≤ ai.fields.length) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 0, .plain (.arrayFill x)]⟩
      ⟨s, f, []⟩ :=
  fwd_of_sread T (st B).read fun hz hc =>
    sread_arrayFillZero (rd B).arrayFillZero (rd B).arrayFillNull (rd B).arrayFillOob
      (readTable_simEnv B) T R G ha h hz hc

theorem fwd_arrayFillSucc {s : Store H} {f : Frame} {x : TypeIdx} {i n : BitVec 32} {v : Val}
    {a : Nat} {ai : ArrayInst} (ha : s.arrays[a]? = some ai)
    (h : i.toNat + n.toNat ≤ ai.fields.length) (hn0 : n ≠ 0) (hb : Bounded s) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, v.toAdmin, constI32 n, .plain (.arrayFill x)]⟩
      ⟨s, f, [arrRef a, constI32 i, v.toAdmin, .plain (.arraySet x),
        arrRef a, constI32 (i + 1), v.toAdmin, constI32 (n - 1), .plain (.arrayFill x)]⟩ :=
  fwd_of_sread T (st B).read fun hz hc =>
    sread_arrayFillSucc (rd B).arrayFillSucc (rd B).arrayFillNull (rd B).arrayFillOob
      (rd B).arrayFillZero (readTable_simEnv B) T R G ha h hn0 (hb.array ha) hz hc

theorem fwd_arrayCopyZero {s : Store H} {f : Frame} {x₁ x₂ : TypeIdx} {i₁ i₂ : BitVec 32}
    {a₁ a₂ : Nat} {ai₁ ai₂ : ArrayInst} (ha₁ : s.arrays[a₁]? = some ai₁)
    (ha₂ : s.arrays[a₂]? = some ai₂)
    (h : i₁.toNat ≤ ai₁.fields.length ∧ i₂.toNat ≤ ai₂.fields.length) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 0,
      .plain (.arrayCopy x₁ x₂)]⟩ ⟨s, f, []⟩ :=
  fwd_of_sread T (st B).read fun hz _ =>
    sread_arrayCopyZero (rd B).arrayCopyZero (rd B).arrayCopyOob1 (rd B).arrayCopyOob2
      (readTable_simEnv B) R G ha₁ ha₂ h hz

theorem fwd_arrayInitElemZero {s : Store H} {f : Frame} {x : TypeIdx} {y : ElemIdx}
    {i j : BitVec 32} {a ea : Nat} {ai : ArrayInst} {ei : ElemInst} (ha : s.arrays[a]? = some ai)
    (he : s.elem? f y = some (ea, ei)) (h : i.toNat ≤ ai.fields.length ∧ j.toNat ≤ ei.refs.length) :
    FwdP (simEnv B) hn ⟨s, f, [arrRef a, constI32 i, constI32 j, constI32 0,
      .plain (.arrayInitElem x y)]⟩ ⟨s, f, []⟩ :=
  fwd_of_sread T (st B).read fun hz _ =>
    sread_arrayInitElemZero (rd B).arrayInitElemZero (rd B).arrayInitElemOob1
      (rd B).arrayInitElemOob2 (readTable_simEnv B) R G ha he h hz

end

end Silmaril.Wasm.SpecTec.Sim.Aggregates
