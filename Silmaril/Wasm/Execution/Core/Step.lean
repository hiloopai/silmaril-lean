module

public import Silmaril.Wasm.Execution.Core.Step.Parametric
public import Silmaril.Wasm.Execution.Core.Step.Numeric
public import Silmaril.Wasm.Execution.Core.Step.Vector
public import Silmaril.Wasm.Execution.Core.Step.Variable
public import Silmaril.Wasm.Execution.Core.Step.Table
public import Silmaril.Wasm.Execution.Core.Step.Memory
public import Silmaril.Wasm.Execution.Core.Step.Reference
public import Silmaril.Wasm.Execution.Core.Step.Aggregate
public import Silmaril.Foundations.InfiniteTrace

@[expose] public section

/-! # Core 3.0 reduction (§4.3): `Step`, `Steps`, `Diverges`, `EvalExpr`

One inductive `Step P host` over configurations. It contains, fully written out,
every rule that is *structural* or *control*:

* context rules `Step/ctxt-instrs`, `ctxt-label`, `ctxt-handler`, `ctxt-frame`;
* blocks (`block`, `loop`, `if-true/false`, `label-vals`);
* branches and their bubbling (`br-label-zero/succ`, `br-handler`, `br_if`,
  `br_table`, `br_on_null`, `br_on_non_null`, `br_on_cast`, `br_on_cast_fail`);
* calls (`call`, `call_ref-null/func/hostfunc-res/hostfunc-div`,
  `call_indirect`) and tail calls (`return_call`, `return_call_ref-label/handler/
  frame-null/frame-addr`, `return_call_indirect`), `frame-vals`, `return-frame/
  label/handler`;
* exceptions (`throw`, `throw_ref-null/instrs/label/frame/handler-empty/
  handler-catch, handler-catch_ref, handler-catch_all, handler-catch_all_ref, handler-next`, `try_table`,
  `handler-vals`);
* traps (`trap-instrs/label/handler/frame`).

Every other rule is in a per-family relation, entered through one constructor:

| constructor | relation | file | kind |
|---|---|---|---|
| `parametric` | `ParametricStep` | `Step/Parametric.lean` | pure |
| `numeric` | `NumericStep P` | `Step/Numeric.lean` | pure |
| `vector` | `VectorStep P` | `Step/Vector.lean` | pure |
| `variable` | `VariableStep` | `Step/Variable.lean` | state |
| `table` | `TableStep P` | `Step/Table.lean` | state |
| `memory` | `MemoryStep P` | `Step/Memory.lean` | state |
| `reference` | `RefStep` | `Step/Reference.lean` | state (read) |
| `aggregate` | `AggregateStep` | `Step/Aggregate.lean` | state |

The spec's split into `Step_pure`, `Step_read` and `Step` is not reproduced as
three relations: a pure family is lifted with the store and frame unchanged,
which is exactly `Step/pure` and `Step/read`.

`CALL_REF`/`RETURN_CALL_REF` exist as source instructions (with an index) and as
administrative forms with a runtime defined type; the call rules accept both
(`Admin.IsCallRef`), since the spec's rules ignore the annotation.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- `CALL_REF yy` in either representation. -/
def Admin.IsCallRef : Admin → Prop
  | .plain (.callRef _) => True
  | .callRefType _ => True
  | _ => False

/-- `RETURN_CALL_REF yy` in either representation. -/
def Admin.IsReturnCallRef : Admin → Prop
  | .plain (.returnCallRef _) => True
  | .returnCallRefType _ => True
  | _ => False

/-- The `CALL_REF yy` with the same annotation as a `RETURN_CALL_REF yy`. -/
def Admin.retToCall : Admin → Admin
  | .plain (.returnCallRef x) => .plain (.callRef x)
  | .returnCallRefType d => .callRefType d
  | a => a

/-- The `CALL_REF` for a `RETURN_CALL_REF` leaving a frame of module `m`: an
index-annotated `RETURN_CALL_REF y` is resolved against `m.types` (deviation from
SpecTec's `CALL_REF y`, which would be resolved in the caller's module). -/
def Admin.retToCallIn (m : ModuleInst) : Admin → Admin
  | .plain (.returnCallRef y) =>
      match m.types[y.toNat]? with
      | some d => .callRefType d
      | none => .plain (.callRef y)
  | .returnCallRefType d => .callRefType d
  | a => a

/-- `l - 1` for a label index. -/
def labelPred (l : LabelIdx) : LabelIdx :=
  ⟨⟨l.toNat - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) l.value.isLt⟩⟩

variable {H : Type}

/-- Does the handler clause `c` catch exception `a` (the premises of the
`throw_ref-handler-catch*` rules)? `throw_ref-handler-next` applies otherwise. -/
def CatchMatches (s : Store H) (f : Frame) (a : Nat) : Catch → Prop
  | .catch_ x _ | .catchRef x _ =>
      ∃ e ta, s.exns[a]? = some e ∧ f.module.tags[x.toNat]? = some ta ∧ e.tag = ta
  | .catchAll _ | .catchAllRef _ => True

/-- `REF.EXN_ADDR a` followed by `THROW_REF`. -/
abbrev throwing (a : Nat) : List Admin := [.ref (.exn a), .plain .throwRef]

inductive Step (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop where
  -- Delegated families
  | parametric {s : Store H} {f : Frame} {is is' : List Admin} (h : ParametricStep is is') :
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  | numeric {s : Store H} {f : Frame} {is is' : List Admin} (h : NumericStep P is is') :
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  | vector {s : Store H} {f : Frame} {is is' : List Admin} (h : VectorStep P is is') :
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  | variable {c c' : Config H} (h : VariableStep c c') : Step P host c c'
  | table {c c' : Config H} (h : TableStep P c c') : Step P host c c'
  | memory {c c' : Config H} (h : MemoryStep P c c') : Step P host c c'
  | reference {c c' : Config H} (h : RefStep c c') : Step P host c c'
  | aggregate {c c' : Config H} (h : AggregateStep c c') : Step P host c c'
  -- Contexts
  /-- `Step/ctxt-instrs`. -/
  | ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) (hne : vs ≠ [] ∨ rest ≠ []) :
      Step P host ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  /-- `Step/ctxt-label`. -/
  | ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
      (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Step P host ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  /-- `Step/ctxt-handler`. -/
  | ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
      (h : Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Step P host ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩
  /-- `Step/ctxt-frame`. -/
  | ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Step P host ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩
  -- Blocks
  /-- `Step_read/block`. -/
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      Step P host ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩
        ⟨s, f, [.label t₂.length [] (vals vs ++ expression body)]⟩
  /-- `Step_read/loop`. -/
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      Step P host ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩
        ⟨s, f, [.label t₁.length [.loop bt body] (vals vs ++ expression body)]⟩
  /-- `Step_pure/if-true`. -/
  | ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
      (hc : c ≠ 0) :
      Step P host ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₁)]⟩
  /-- `Step_pure/if-false`. -/
  | ifFalse {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr} :
      Step P host ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩ ⟨s, f, [.plain (.block bt b₂)]⟩
  /-- `Step_pure/label-vals`. -/
  | labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val} :
      Step P host ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩
  -- Branches
  /-- `Step_pure/br-label-zero`. -/
  | brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs' vs : List Val}
      {l : LabelIdx} {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n) :
      Step P host ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ expression cont⟩
  /-- `Step_pure/br-label-succ`. -/
  | brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {l : LabelIdx} {rest : List Admin} (hl : 0 < l.toNat) :
      Step P host ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩
  /-- `Step_pure/br-handler`. -/
  | brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {l : LabelIdx} {rest : List Admin} :
      Step P host ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br l)]⟩
  /-- `Step_pure/br_if-true`. -/
  | brIfTrue {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0) :
      Step P host ⟨s, f, [constI32 c, .plain (.brIf l)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step_pure/br_if-false`. -/
  | brIfFalse {s : Store H} {f : Frame} {l : LabelIdx} :
      Step P host ⟨s, f, [constI32 0, .plain (.brIf l)]⟩ ⟨s, f, []⟩
  /-- `Step_pure/br_table-lt`. -/
  | brTableLt {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (hi : ls[i.toNat]? = some l) :
      Step P host ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step_pure/br_table-ge`. -/
  | brTableGe {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
      (hi : ls.length ≤ i.toNat) :
      Step P host ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l')]⟩
  /-- `Step_pure/br_on_null-null`. -/
  | brOnNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
      Step P host ⟨s, f, [.ref .null, .plain (.brOnNull l)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step_pure/br_on_null-addr`. -/
  | brOnNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      Step P host ⟨s, f, [v.toAdmin, .plain (.brOnNull l)]⟩ ⟨s, f, [v.toAdmin]⟩
  /-- `Step_pure/br_on_non_null-null`. -/
  | brOnNonNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
      Step P host ⟨s, f, [.ref .null, .plain (.brOnNonNull l)]⟩ ⟨s, f, []⟩
  /-- `Step_pure/br_on_non_null-addr`. -/
  | brOnNonNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      Step P host ⟨s, f, [v.toAdmin, .plain (.brOnNonNull l)]⟩ ⟨s, f, [v.toAdmin, .plain (.br l)]⟩
  /-- `Step_read/br_on_cast-succeed`. -/
  | brOnCastSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      Step P host ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r, .plain (.br l)]⟩
  /-- `Step_read/br_on_cast-fail`. -/
  | brOnCastFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      Step P host ⟨s, f, [.ref r, .plain (.brOnCast l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step_read/br_on_cast_fail-succeed`. -/
  | brOnCastFailSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      Step P host ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩ ⟨s, f, [.ref r]⟩
  /-- `Step_read/br_on_cast_fail-fail`. -/
  | brOnCastFailFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      Step P host ⟨s, f, [.ref r, .plain (.brOnCastFail l rt₁ rt₂)]⟩
        ⟨s, f, [.ref r, .plain (.br l)]⟩
  -- Calls
  /-- `Step_read/call`. -/
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      Step P host ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩
  /-- `Step/call_ref-null`. -/
  | callRefNull {s : Store H} {f : Frame} {c : Admin} (hc : c.IsCallRef) :
      Step P host ⟨s, f, [.ref .null, c]⟩ ⟨s, f, [.trap]⟩
  /-- `Step/call_ref-func`: `FRAME_m{f} (LABEL_m{} instr*)`. -/
  | callRefFunc {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat} {fi : FuncInst H}
      {ps rs : Ty (.list .val)} {code : Func}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
      Step P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩
  /-- `Step/call_ref-hostfunc-res`. -/
  | callRefHost {s s' : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .host h)
      (hhost : host h s vs (.returned s' r)) :
      Step P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩
  /-- `Step/call_ref-hostfunc-div`: a divergent host call stutters. -/
  | callRefHostDiv {s : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged) :
      Step P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
  /-- `Step_read/return_call`. -/
  | returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      Step P host ⟨s, f, [.plain (.returnCall x)]⟩
        ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩
  /-- `Step_read/return_call_ref-label`. -/
  | returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      Step P host ⟨s, f, [.label k cont (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
  /-- `Step_read/return_call_ref-handler`. -/
  | returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {vs : List Val}
      {c : Admin} {rest : List Admin} (hc : c.IsReturnCallRef) :
      Step P host ⟨s, f, [.handler k cs (vals vs ++ [c] ++ rest)]⟩ ⟨s, f, vals vs ++ [c]⟩
  /-- `Step_read/return_call_ref-frame-null`. -/
  | returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {vs : List Val} {c : Admin}
      {rest : List Admin} (hc : c.IsReturnCallRef) :
      Step P host ⟨s, f, [.frame k fi (vals vs ++ [.ref .null, c] ++ rest)]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/return_call_ref-frame-addr`. Deviation: an index annotation is
  resolved against the exited frame's module (`Admin.retToCallIn`). -/
  | returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat}
      {c : Admin} {rest : List Admin} {fn : FuncInst H} {ps rs : Ty (.list .val)}
      (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
      (hn : vs.length = ps.length) :
      Step P host ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩
  /-- `Step_pure/call_indirect`. -/
  | callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
      Step P host ⟨s, f, [.plain (.callIndirect x y)]⟩
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]⟩
  /-- `Step_pure/return_call_indirect`. -/
  | returnCallIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
      Step P host ⟨s, f, [.plain (.returnCallIndirect x y)]⟩
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
          .plain (.returnCallRef y)]⟩
  /-- `Step_pure/frame-vals`. -/
  | frameVals {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val} (hn : vs.length = n) :
      Step P host ⟨s, f, [.frame n fi (vals vs)]⟩ ⟨s, f, vals vs⟩
  /-- `Step_pure/return-frame`. -/
  | returnFrame {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
      (hn : vs.length = n) :
      Step P host ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs⟩
  /-- `Step_pure/return-label`. -/
  | returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
      {rest : List Admin} :
      Step P host ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩
  /-- `Step_pure/return-handler`. -/
  | returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
      {rest : List Admin} :
      Step P host ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩
  -- Exceptions
  /-- `Step/throw`. -/
  | throw {s : Store H} {f : Frame} {x : TagIdx} {vs : List Val} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
      (hn : vs.length = ts.length) :
      Step P host ⟨s, f, vals vs ++ [.plain (.throw x)]⟩
        ⟨s.addExn ⟨ta, vs⟩, f, throwing s.exns.length⟩
  /-- `Step_read/throw_ref-null`. -/
  | throwRefNull {s : Store H} {f : Frame} :
      Step P host ⟨s, f, [.ref .null, .plain .throwRef]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_read/throw_ref-instrs`. -/
  | throwRefInstrs {s : Store H} {f : Frame} {vs : List Val} {a : Nat} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ []) :
      Step P host ⟨s, f, vals vs ++ throwing a ++ rest⟩ ⟨s, f, throwing a⟩
  /-- `Step_read/throw_ref-label`. -/
  | throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
      Step P host ⟨s, f, [.label n cont (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step_read/throw_ref-frame`. -/
  | throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      Step P host ⟨s, f, [.frame n fi (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step_read/throw_ref-handler-empty`. -/
  | throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
      Step P host ⟨s, f, [.handler n [] (throwing a)]⟩ ⟨s, f, throwing a⟩
  /-- `Step_read/throw_ref-handler-catch`. -/
  | throwRefHandlerCatch {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Step P host ⟨s, f, [.handler n (.catch_ x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩
  /-- `Step_read/throw_ref-handler-catch_ref`. -/
  | throwRefHandlerCatchRef {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Step P host ⟨s, f, [.handler n (.catchRef x l :: cs) (throwing a)]⟩
        ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩
  /-- `Step_read/throw_ref-handler-catch_all`. -/
  | throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : Nat} :
      Step P host ⟨s, f, [.handler n (.catchAll l :: cs) (throwing a)]⟩ ⟨s, f, [.plain (.br l)]⟩
  /-- `Step_read/throw_ref-handler-catch_all_ref`. -/
  | throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
      {cs : List Catch} {a : Nat} :
      Step P host ⟨s, f, [.handler n (.catchAllRef l :: cs) (throwing a)]⟩
        ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩
  /-- `Step_read/throw_ref-handler-next`. -/
  | throwRefHandlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (h : ¬ CatchMatches s f a c) :
      Step P host ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ ⟨s, f, [.handler n cs (throwing a)]⟩
  /-- `Step_read/try_table`. -/
  | tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {vs : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : vs.length = t₁.length) :
      Step P host ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩
        ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]⟩
  /-- `Step_pure/handler-vals`. -/
  | handlerVals {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val} :
      Step P host ⟨s, f, [.handler n cs (vals vs)]⟩ ⟨s, f, vals vs⟩
  -- Traps
  /-- `Step_pure/trap-instrs`. -/
  | trapInstrs {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
      (hne : vs ≠ [] ∨ rest ≠ []) :
      Step P host ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/trap-label`. -/
  | trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} :
      Step P host ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/trap-handler`. -/
  | trapHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} :
      Step P host ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩
  /-- `Step_pure/trap-frame`. -/
  | trapFrame {s : Store H} {f fi : Frame} {n : Nat} :
      Step P host ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩

/-- `Steps` (`~>*`). -/
abbrev Steps (P : Profile) (host : HostSemantics H) := Relation.ReflTransGen (Step P host)

/-- An infinite reduction sequence (includes divergent host calls). -/
def Diverges (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  InfiniteTrace (Step P host) c

/-- `Eval_expr: z; expr ~>* z'; val*`. -/
def EvalExpr (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (e : Expr)
    (s' : Store H) (f' : Frame) (vs : List Val) : Prop :=
  Steps P host ⟨s, f, expression e⟩ ⟨s', f', vals vs⟩

/-- A configuration is terminal when its code is a result. -/
def Config.Terminal (c : Config H) : Prop := ∃ r : Result, c.code = r.toAdmin

end Silmaril.Wasm.Execution.Core
