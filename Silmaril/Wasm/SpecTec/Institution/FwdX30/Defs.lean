module

public import Silmaril.Wasm.SpecTec.Institution.Fwd30.Defs

/-!
# The forward direction at wasm-3.0, extended: definitions

`Fwd30.PureHead` and `Fwd30.ReadHead` classify the Core head steps that are `Step_pure` and
`Step_read` rules and need nothing beyond the typing of the encoding. This header names the next
part of that classification: the Core head steps whose forward leaves need the concrete
primitives `Round4Int.BI` (for the integer and float primitives, `$inst_reftype`, the store
functions), and which an earlier step left out.

* `PureHeadX P is is'`: the head steps that keep the state and are `Step_pure` rules:
  * every `NumericStep P` (`unop`, `binop`, `testop`, `relop`, `cvtop`, with their traps);
  * every `VectorStep P` from code without `FloatMissel` instructions (`AdminsSel`);
  * the reference rules of `Step_pure`: `ref.i31`, `ref.is_null`, `ref.as_non_null`, `ref.eq`,
    `i31.get`, `extern.convert_any`, `any.convert_extern`;
  * `array.new`, `br_on_null`/`br_on_non_null` at a non-null value, `local.tee`, and
    `handler` with values.
* `ReadHeadX P c is'`: the head steps that keep the state and are `Step_read` rules, beyond
  `local.get`/`global.get`:
  * `ref.null`, `ref.func`;
  * the table rules (`TableRead`: every `TableStep` whose instruction is `table.get`,
    `table.size`, `table.fill`, `table.copy` or `table.init`);
  * the memory rules (`MemRead`: the loads, `memory.size`, `memory.fill`, `memory.copy`,
    `memory.init`);
  * the aggregate rules (`AggRead`: every `AggregateStep` whose instruction is
    `struct.new_default`, `struct.get`, `array.new_default`, `array.new_elem`,
    `array.new_data`, `array.get`, `array.len`, `array.fill`, `array.copy`,
    `array.init_elem` or `array.init_data`);
  * the control rules (`CtrlRead`: `block`, `loop`, `call`, `return_call`, `return_call_ref`
    except out of a frame at an address, `throw_ref`, `try_table`).

Not classified: the cast rules of `Step_read` (`ref.test`, `ref.cast`, `br_on_cast`,
`br_on_cast_fail`), where the backend reading and the declarative one differ, and
`return_call_ref` out of a frame at an address, where Core's successor is the image only up to
`ConfigEq`.

`PureHeadX.step` and `ReadHeadX.step` (in `FwdX30.Thms`) check that both are Core steps.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdX30

open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (CValType)

variable {H : Type}

/-- **Core head steps that are `Step_pure` rules**, beyond `Fwd30.PureHead`. -/
inductive PureHeadX (P : Profile) : List Admin → List Admin → Prop where
  /-- The numeric family (`Step_pure/unop-val`, `binop-val`, `binop-trap`, `testop`, `relop`,
  `cvtop-val`, `cvtop-trap`). -/
  | numeric {is is' : List Admin} (h : NumericStep P is is') : PureHeadX P is is'
  /-- The vector family (`Step_pure/vvunop`, …, `vcvtop`, `vnarrow`), from code without
  `FloatMissel` instructions (`Round5.Target.AdminsSel`, which holds on round 6's domain). -/
  | vector {is is' : List Admin} (h : VectorStep P is is') (hsel : Silmaril.Wasm.SpecTec.Sim.Round5.Target.AdminsSel is) :
      PureHeadX P is is'
  /-- `Step_pure/ref.i31`. -/
  | refI31 (i : BitVec 32) :
      PureHeadX P [constI32 i, .plain .refI31] [.ref (.i31 (i.setWidth 31))]
  /-- `Step_pure/ref.is_null-true`. -/
  | isNullTrue : PureHeadX P [.ref .null, .plain .refIsNull] [constI32 1]
  /-- `Step_pure/ref.is_null-false`. -/
  | isNullFalse {r : Ref} (h : r ≠ .null) : PureHeadX P [.ref r, .plain .refIsNull] [constI32 0]
  /-- `Step_pure/ref.as_non_null-null`. -/
  | asNonNullNull : PureHeadX P [.ref .null, .plain .refAsNonNull] [.trap]
  /-- `Step_pure/ref.as_non_null-addr`. -/
  | asNonNullAddr {r : Ref} (h : r ≠ .null) :
      PureHeadX P [.ref r, .plain .refAsNonNull] [.ref r]
  /-- `Step_pure/ref.eq-null`. -/
  | eqNull : PureHeadX P [.ref .null, .ref .null, .plain .refEq] [constI32 1]
  /-- `Step_pure/ref.eq-true`. -/
  | eqTrue {r : Ref} (h : r ≠ .null) : PureHeadX P [.ref r, .ref r, .plain .refEq] [constI32 1]
  /-- `Step_pure/ref.eq-false`. -/
  | eqFalse {r₁ r₂ : Ref} (h : r₁ ≠ r₂) :
      PureHeadX P [.ref r₁, .ref r₂, .plain .refEq] [constI32 0]
  /-- `Step_pure/i31.get-null`. -/
  | i31GetNull (sx : Signedness) : PureHeadX P [.ref .null, .plain (.i31Get sx)] [.trap]
  /-- `Step_pure/i31.get-num`. -/
  | i31GetNum (sx : Signedness) (i : BitVec 31) :
      PureHeadX P [.ref (.i31 i), .plain (.i31Get sx)]
        [constI32 (match sx with | .signed => i.signExtend 32 | .unsigned => i.setWidth 32)]
  /-- `Step_pure/extern.convert_any-null`. -/
  | externConvertNull : PureHeadX P [.ref .null, .plain .externConvertAny] [.ref .null]
  /-- `Step_pure/extern.convert_any-addr`. -/
  | externConvertAddr {r : Ref} (h : r ≠ .null) :
      PureHeadX P [.ref r, .plain .externConvertAny] [.ref (.extern r)]
  /-- `Step_pure/any.convert_extern-null`. -/
  | anyConvertNull : PureHeadX P [.ref .null, .plain .anyConvertExtern] [.ref .null]
  /-- `Step_pure/any.convert_extern-addr`. -/
  | anyConvertAddr (r : Ref) : PureHeadX P [.ref (.extern r), .plain .anyConvertExtern] [.ref r]
  /-- `Step_pure/array.new`. -/
  | arrayNew {x : TypeIdx} (v : Val) (n : BitVec 32) :
      PureHeadX P [v.toAdmin, constI32 n, .plain (.arrayNew x)]
        (vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])
  /-- `Step_pure/br_on_null-addr`. -/
  | brOnNullAddr {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      PureHeadX P [v.toAdmin, .plain (.brOnNull l)] [v.toAdmin]
  /-- `Step_pure/br_on_non_null-addr`. -/
  | brOnNonNullAddr {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      PureHeadX P [v.toAdmin, .plain (.brOnNonNull l)] [v.toAdmin, .plain (.br l)]
  /-- `Step_pure/local.tee`. -/
  | localTee {v : Val} {x : LocalIdx} :
      PureHeadX P [v.toAdmin, .plain (.localTee x)] [v.toAdmin, v.toAdmin, .plain (.localSet x)]
  /-- `Step_pure/handler-vals`. -/
  | handlerVals {n : Nat} {cs : List Catch} {vs : List Val} :
      PureHeadX P [.handler n cs (vals vs)] (vals vs)

/-- The last instruction of `is` is a plain `i` with `p i`. -/
def LastIs (p : Instr → Bool) (is : List Admin) : Prop :=
  ∃ i, is.getLast? = some (.plain i) ∧ p i = true

/-- The instructions of the `Step_read` rules among Core's table steps: every `TableStep` but
`table.set`, `table.grow` and `elem.drop` (which are `Step` rules). -/
def tableReadInstr : Instr → Bool
  | .tableGet _ | .tableSize _ | .tableFill _ | .tableCopy _ _ | .tableInit _ _ => true
  | _ => false

/-- **Core's table steps that are `Step_read` rules**: `table.get`, `table.size`, `table.fill`,
`table.copy`, `table.init` (with their `oob`, `zero`, `succ`, `le`, `gt` cases). -/
def TableRead (P : Profile) (c : Config H) (is' : List Admin) : Prop :=
  TableStep P c ⟨c.store, c.frame, is'⟩ ∧ LastIs tableReadInstr c.code

/-- The instructions of the `Step_read` rules among Core's memory steps: every `MemoryStep` but
the stores, `memory.grow` and `data.drop` (which are `Step` rules). -/
def memReadInstr : Instr → Bool
  | .intLoad .. | .floatLoad .. | .vecLoad .. | .vecLoadLane .. | .memorySize _ | .memoryFill _
  | .memoryCopy .. | .memoryInit .. => true
  | _ => false

/-- **Core's memory steps that are `Step_read` rules**: the loads, `memory.size`,
`memory.fill`, `memory.copy` and `memory.init`, with all their cases. -/
def MemRead (P : Profile) (c : Config H) (is' : List Admin) : Prop :=
  MemoryStep P c ⟨c.store, c.frame, is'⟩ ∧ LastIs memReadInstr c.code

/-- The instructions of the `Step_read` rules among Core's aggregate steps: every
`AggregateStep` but `struct.new`, `struct.set`, `array.new` (a `Step_pure` rule, in `PureHeadX`),
`array.new_fixed` and `array.set` (which are `Step` rules). -/
def aggReadInstr : Instr → Bool
  | .structNewDefault _ | .structGet .. | .arrayNewDefault _ | .arrayNewElem .. | .arrayNewData ..
  | .arrayGet .. | .arrayLen | .arrayFill _ | .arrayCopy .. | .arrayInitElem .. | .arrayInitData .. =>
      true
  | _ => false

/-- **Core's aggregate steps that are `Step_read` rules**: `struct.new_default`, `struct.get`,
`array.new_default`, `array.new_elem`, `array.new_data`, `array.get`, `array.len`, `array.fill`,
`array.copy`, `array.init_elem`, `array.init_data`, with all their cases. -/
def AggRead (c : Config H) (is' : List Admin) : Prop :=
  AggregateStep c ⟨c.store, c.frame, is'⟩ ∧ LastIs aggReadInstr c.code

/-- **Core's control steps that are `Step_read` rules**: `block`, `loop`, `call`,
`return_call`, `return_call_ref` out of a label, a handler or a frame at `null`, `throw_ref` in
all its cases, and `try_table`. The constructors are those of Core's `Step` with the same names.
Not included: `return_call_ref` out of a frame at an address, whose SpecTec successor keeps the
`CALL_REF` index where Core resolves it (`Admin.retToCallIn`), so that Core's successor is the
image only up to `ConfigEq`. -/
inductive CtrlRead : Config H → List Admin → Prop where
  /-- `Step_read/block`. -/
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      CtrlRead ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        [.label t₂.length [] (vals vs ++ expression body)]
  /-- `Step_read/loop`. -/
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      CtrlRead ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        [.label t₁.length [.loop bt body] (vals vs ++ expression body)]
  /-- `Step_read/call`. -/
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      CtrlRead ⟨s, f, [.plain (.call x)]⟩ [.ref (.func a), .callRefType fi.type]
  /-- `Step_read/return_call`. -/
  | returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      CtrlRead ⟨s, f, [.plain (.returnCall x)]⟩
        [.ref (.func a), .returnCallRefType fi.type]
  /-- `Step_read/return_call_ref-label`. -/
  | returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      CtrlRead ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ (vals vs ++ [c])
  /-- `Step_read/return_call_ref-handler`. -/
  | returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      CtrlRead ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ (vals vs ++ [c])
  /-- `Step_read/return_call_ref-frame-null`. -/
  | returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (hc : c.IsReturnCallRef) :
      CtrlRead ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ [.trap]
  /-- `Step_read/throw_ref-null`. -/
  | throwRefNull {s : Store H} {f : Frame} :
      CtrlRead ⟨s, f, [.ref .null, .plain .throwRef]⟩ [.trap]
  /-- `Step_read/throw_ref-instrs`. -/
  | throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ []) :
      CtrlRead ⟨s, f, vals vs ++ throwing a ++ rest⟩ (throwing a)
  /-- `Step_read/throw_ref-label`. -/
  | throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
      CtrlRead ⟨s, f, [.label n cont (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-frame`. -/
  | throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      CtrlRead ⟨s, f, [.frame n fi (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-handler-empty`. -/
  | throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
      CtrlRead ⟨s, f, [.handler n [] (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-handler-catch`. -/
  | throwRefHandlerCatch {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      CtrlRead ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
        (vals e.fields ++ [.plain (.br l)])
  /-- `Step_read/throw_ref-handler-catch_ref`. -/
  | throwRefHandlerCatchRef {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      CtrlRead ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        (vals e.fields ++ [.ref (.exn a), .plain (.br l)])
  /-- `Step_read/throw_ref-handler-catch_all`. -/
  | throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : Nat} :
      CtrlRead ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩ [.plain (.br l)]
  /-- `Step_read/throw_ref-handler-catch_all_ref`. -/
  | throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
      {cs : List Catch} {a : Nat} :
      CtrlRead ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
        [.ref (.exn a), .plain (.br l)]
  /-- `Step_read/throw_ref-handler-next`. -/
  | throwRefHandlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (h : ¬ CatchMatches s f a c) :
      CtrlRead ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ [.handler n cs (throwing a)]
  /-- `Step_read/try_table`. -/
  | tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      CtrlRead ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
        [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]

/-- **Core head steps that are `Step_read` rules** (and keep the state), beyond
`Fwd30.ReadHead`. -/
inductive ReadHeadX (P : Profile) : Config H → List Admin → Prop where
  /-- `Step_read/ref.null`. -/
  | refNull {s : Store H} {f : Frame} (ht : HeapType) :
      ReadHeadX P ⟨s, f, [.plain (.refNull ht)]⟩ [.ref .null]
  /-- `Step_read/ref.func`. -/
  | refFunc {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat}
      (h : f.module.funcs[x.toNat]? = some a) :
      ReadHeadX P ⟨s, f, [.plain (.refFunc x)]⟩ [.ref (.func a)]
  /-- The table rules of `Step_read`. -/
  | table {c : Config H} {is' : List Admin} (h : TableRead P c is') : ReadHeadX P c is'
  /-- The memory rules of `Step_read`. -/
  | memory {c : Config H} {is' : List Admin} (h : MemRead P c is') : ReadHeadX P c is'
  /-- The control rules of `Step_read`. -/
  | ctrl {c : Config H} {is' : List Admin} (h : CtrlRead c is') : ReadHeadX P c is'
  /-- The aggregate rules of `Step_read`. -/
  | aggregate {c : Config H} {is' : List Admin} (h : AggRead c is') : ReadHeadX P c is'

end Silmaril.Wasm.SpecTec.Institution.FwdX30
