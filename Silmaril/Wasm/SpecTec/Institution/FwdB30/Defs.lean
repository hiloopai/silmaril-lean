module

public import Silmaril.Wasm.SpecTec.Institution.FwdX30.Defs

/-!
# The forward direction at the choice-made primitives `Wasm30.builtins`: definitions

`FwdX30` proved that the classified head steps (`PureHeadX`, `ReadHeadX`) are
`Step_pure`/`Step_read` facts at the concrete primitives `Round4Int.BI`, and `FwdX30Fin` that at
`Wasm30.builtins` every such fact is the classified successor (uniqueness). Existence at
`builtins` was left open: `builtins` is a `Classical.choose`, and nothing is known of its integer,
float, `$inst_reftype` or store primitives.

Many of the classified rules use no primitive at all: their forward leaves hold in every
evaluator `simEnv B`. This header names them.

* `PureG is is'`: the arms of `PureHeadX` whose leaves hold at every `B`: the reference rules
  other than `ref.i31` and `i31.get` at a number (which read `$wrap__`/`$extend__`), `array.new`,
  `br_on_null`/`br_on_non_null` at a non-null value, `local.tee` and `handler-vals`. The numeric
  and vector families and the two `i31` rules need the primitives' laws and are left out.
* `ReadG c is'`: `ref.null`, and the arms of `CtrlRead` whose leaves hold at every `B`: `call`,
  `return_call`, `return_call_ref` out of a label, a handler or a frame at `null`, and
  `throw_ref` other than its `catch`, `catch_ref` and `next` handler cases. Left out: `block`,
  `loop` and `try_table` (their leaves evaluate `$blocktype_` through a lemma stated at `BI`),
  the three `throw_ref` handler cases (helpers stated at `BI`), and `ref.func` and the table,
  memory and aggregate rules (store primitives).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation (CValType)

variable {H : Type}

/-- **The primitive-free `Step_pure` rules among `PureHeadX`.** -/
inductive PureG : List Admin → List Admin → Prop where
  /-- `Step_pure/ref.is_null-true`. -/
  | isNullTrue : PureG [.ref .null, .plain .refIsNull] [constI32 1]
  /-- `Step_pure/ref.is_null-false`. -/
  | isNullFalse {r : Ref} (h : r ≠ .null) : PureG [.ref r, .plain .refIsNull] [constI32 0]
  /-- `Step_pure/ref.as_non_null-null`. -/
  | asNonNullNull : PureG [.ref .null, .plain .refAsNonNull] [.trap]
  /-- `Step_pure/ref.as_non_null-addr`. -/
  | asNonNullAddr {r : Ref} (h : r ≠ .null) : PureG [.ref r, .plain .refAsNonNull] [.ref r]
  /-- `Step_pure/ref.eq-null`. -/
  | eqNull : PureG [.ref .null, .ref .null, .plain .refEq] [constI32 1]
  /-- `Step_pure/ref.eq-true`. -/
  | eqTrue {r : Ref} (h : r ≠ .null) : PureG [.ref r, .ref r, .plain .refEq] [constI32 1]
  /-- `Step_pure/ref.eq-false`. -/
  | eqFalse {r₁ r₂ : Ref} (h : r₁ ≠ r₂) : PureG [.ref r₁, .ref r₂, .plain .refEq] [constI32 0]
  /-- `Step_pure/i31.get-null`. -/
  | i31GetNull (sx : Signedness) : PureG [.ref .null, .plain (.i31Get sx)] [.trap]
  /-- `Step_pure/extern.convert_any-null`. -/
  | externConvertNull : PureG [.ref .null, .plain .externConvertAny] [.ref .null]
  /-- `Step_pure/extern.convert_any-addr`. -/
  | externConvertAddr {r : Ref} (h : r ≠ .null) :
      PureG [.ref r, .plain .externConvertAny] [.ref (.extern r)]
  /-- `Step_pure/any.convert_extern-null`. -/
  | anyConvertNull : PureG [.ref .null, .plain .anyConvertExtern] [.ref .null]
  /-- `Step_pure/any.convert_extern-addr`. -/
  | anyConvertAddr (r : Ref) : PureG [.ref (.extern r), .plain .anyConvertExtern] [.ref r]
  /-- `Step_pure/array.new`. -/
  | arrayNew {x : TypeIdx} (v : Val) (n : BitVec 32) :
      PureG [v.toAdmin, constI32 n, .plain (.arrayNew x)]
        (vals (List.replicate n.toNat v) ++ [.plain (.arrayNewFixed x ⟨n.toNat, n.isLt⟩)])
  /-- `Step_pure/br_on_null-addr`. -/
  | brOnNullAddr {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      PureG [v.toAdmin, .plain (.brOnNull l)] [v.toAdmin]
  /-- `Step_pure/br_on_non_null-addr`. -/
  | brOnNonNullAddr {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      PureG [v.toAdmin, .plain (.brOnNonNull l)] [v.toAdmin, .plain (.br l)]
  /-- `Step_pure/local.tee`. -/
  | localTee {v : Val} {x : LocalIdx} :
      PureG [v.toAdmin, .plain (.localTee x)] [v.toAdmin, v.toAdmin, .plain (.localSet x)]
  /-- `Step_pure/handler-vals`. -/
  | handlerVals {n : Nat} {cs : List Catch} {vs : List Val} :
      PureG [.handler n cs (vals vs)] (vals vs)

/-- **The primitive-free `Step_read` rules among `ReadHeadX`.** -/
inductive ReadG : Config H → List Admin → Prop where
  /-- `Step_read/ref.null`. -/
  | refNull {s : Store H} {f : Frame} (ht : HeapType) :
      ReadG ⟨s, f, [.plain (.refNull ht)]⟩ [.ref .null]
  /-- `Step_read/call`. -/
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      ReadG ⟨s, f, [.plain (.call x)]⟩ [.ref (.func a), .callRefType fi.type]
  /-- `Step_read/return_call`. -/
  | returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      ReadG ⟨s, f, [.plain (.returnCall x)]⟩ [.ref (.func a), .returnCallRefType fi.type]
  /-- `Step_read/return_call_ref-label`. -/
  | returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      ReadG ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ (vals vs ++ [c])
  /-- `Step_read/return_call_ref-handler`. -/
  | returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      ReadG ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ (vals vs ++ [c])
  /-- `Step_read/return_call_ref-frame-null`. -/
  | returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (hc : c.IsReturnCallRef) :
      ReadG ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ [.trap]
  /-- `Step_read/throw_ref-null`. -/
  | throwRefNull {s : Store H} {f : Frame} : ReadG ⟨s, f, [.ref .null, .plain .throwRef]⟩ [.trap]
  /-- `Step_read/throw_ref-instrs`. -/
  | throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ []) : ReadG ⟨s, f, vals vs ++ throwing a ++ rest⟩ (throwing a)
  /-- `Step_read/throw_ref-label`. -/
  | throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
      ReadG ⟨s, f, [.label n cont (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-frame`. -/
  | throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      ReadG ⟨s, f, [.frame n fi (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-handler-empty`. -/
  | throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
      ReadG ⟨s, f, [.handler n [] (throwing a)]⟩ (throwing a)
  /-- `Step_read/throw_ref-handler-catch_all`. -/
  | throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : Nat} : ReadG ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩ [.plain (.br l)]
  /-- `Step_read/throw_ref-handler-catch_all_ref`. -/
  | throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
      {cs : List Catch} {a : Nat} :
      ReadG ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩ [.ref (.exn a), .plain (.br l)]

end Silmaril.Wasm.SpecTec.Institution.FwdB30
