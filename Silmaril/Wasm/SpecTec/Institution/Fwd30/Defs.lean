module

public import Silmaril.Wasm.SpecTec.Institution.Wasm30.Defs

/-!
# The forward direction for `Step_pure` and `Step_read`, at wasm-3.0: definitions

`Wasm30.pureFact_sound` and `Wasm30.readFact_sound` say that every `Step_pure` and `Step_read`
fact of `stepModel B` from a valid configuration is a Core step. The converse needs to say which
Core steps are `Step_pure` and `Step_read` steps. Core has one step relation, but its constructors
carry the names of the SpecTec rules they transcribe (`Silmaril.Wasm.Execution.Core.Step`). This
header names the part of that classification for which the forward leaves exist and need nothing
beyond the typing of the encoding:

* `PureHead is is'`: the head steps that keep the state and are `Step_pure` rules. These are the
  parametric family (`unreachable`, `nop`, `drop`, `select`) and the control rules `if`, `label`
  with values, `br` at a label or handler, `br_if`, `br_table`, `br_on_null`/`br_on_non_null` at
  `null`, `call_indirect`, `return_call_indirect`, a frame with values, `return` at a frame, label
  or handler, and `trap` in a sequence, label, handler or frame.
* `ReadHead c is'`: the head steps that keep the state and are `Step_read` rules, at
  `local.get` and `global.get`.

`PureHead.step` and `ReadHead.step` (in `Fwd30.Thms`) check that both are Core steps. Not
covered: the numeric and vector families (their leaves need the primitives' laws, `IntB` and
family V), `br_on_null`/`br_on_non_null` at a non-null value, `handler` with values, and
every other `Step_read` rule (`block`, `loop`, calls, the casts, tables, memories, aggregates,
exceptions). Their forward leaves exist /6, but under more hypotheses than these.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Fwd30

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- **Core head steps that are `Step_pure` rules**, as a relation on code. -/
inductive PureHead : List Admin → List Admin → Prop where
  /-- `unreachable`, `nop`, `drop`, `select`. -/
  | parametric {is is' : List Admin} (h : ParametricStep is is') : PureHead is is'
  /-- `Step_pure/if-true`. -/
  | ifTrue {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} (hc : c ≠ 0) :
      PureHead [constI32 c, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₁)]
  /-- `Step_pure/if-false`. -/
  | ifFalse {bt : BlockType} {b₁ b₂ : List Instr} :
      PureHead [constI32 0, .plain (.if_ bt b₁ b₂)] [.plain (.block bt b₂)]
  /-- `Step_pure/label-vals`. -/
  | labelVals {n : Nat} {cont : List Instr} {vs : List Val} :
      PureHead [.label n cont (vals vs)] (vals vs)
  /-- `Step_pure/br-label-zero`. -/
  | brLabelZero {n : Nat} {cont : List Instr} {vs' vs : List Val} {l : LabelIdx}
      {rest : List Admin} (hl : l.toNat = 0) (hn : vs.length = n) :
      PureHead [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ expression cont)
  /-- `Step_pure/br-label-succ`. -/
  | brLabelSucc {n : Nat} {cont : List Instr} {vs : List Val} {l : LabelIdx} {rest : List Admin}
      (hl : 0 < l.toNat) :
      PureHead [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]
        (vals vs ++ [.plain (.br (labelPred l))])
  /-- `Step_pure/br-handler`. -/
  | brHandler {n : Nat} {cs : List Catch} {vs : List Val} {l : LabelIdx} {rest : List Admin} :
      PureHead [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)] (vals vs ++ [.plain (.br l)])
  /-- `Step_pure/br_if-true`. -/
  | brIfTrue {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0) :
      PureHead [constI32 c, .plain (.brIf l)] [.plain (.br l)]
  /-- `Step_pure/br_if-false`. -/
  | brIfFalse {l : LabelIdx} : PureHead [constI32 0, .plain (.brIf l)] []
  /-- `Step_pure/br_table-lt`. -/
  | brTableLt {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx} (hi : ls[i.toNat]? = some l) :
      PureHead [constI32 i, .plain (.brTable ls l')] [.plain (.br l)]
  /-- `Step_pure/br_table-ge`. -/
  | brTableGe {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx} (hi : ls.length ≤ i.toNat) :
      PureHead [constI32 i, .plain (.brTable ls l')] [.plain (.br l')]
  /-- `Step_pure/br_on_null-null`. -/
  | brOnNullNull {l : LabelIdx} : PureHead [.ref .null, .plain (.brOnNull l)] [.plain (.br l)]
  /-- `Step_pure/br_on_non_null-null`. -/
  | brOnNonNullNull {l : LabelIdx} : PureHead [.ref .null, .plain (.brOnNonNull l)] []
  /-- `Step_pure/call_indirect`. -/
  | callIndirect {x : TableIdx} {y : TypeIdx} :
      PureHead [.plain (.callIndirect x y)]
        [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]
  /-- `Step_pure/return_call_indirect`. -/
  | returnCallIndirect {x : TableIdx} {y : TypeIdx} :
      PureHead [.plain (.returnCallIndirect x y)]
        [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.returnCallRef y)]
  /-- `Step_pure/frame-vals`. -/
  | frameVals {fi : Frame} {n : Nat} {vs : List Val} (hn : vs.length = n) :
      PureHead [.frame n fi (vals vs)] (vals vs)
  /-- `Step_pure/return-frame`. -/
  | returnFrame {fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
      (hn : vs.length = n) :
      PureHead [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)] (vals vs)
  /-- `Step_pure/return-label`. -/
  | returnLabel {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin} :
      PureHead [.label n cont (vals vs ++ [.plain .return_] ++ rest)] (vals vs ++ [.plain .return_])
  /-- `Step_pure/return-handler`. -/
  | returnHandler {n : Nat} {cs : List Catch} {vs : List Val} {rest : List Admin} :
      PureHead [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]
        (vals vs ++ [.plain .return_])
  /-- `Step_pure/trap-instrs`. -/
  | trapInstrs {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ []) :
      PureHead (vals vs ++ [.trap] ++ rest) [.trap]
  /-- `Step_pure/trap-label`. -/
  | trapLabel {n : Nat} {cont : List Instr} : PureHead [.label n cont [.trap]] [.trap]
  /-- `Step_pure/trap-handler`. -/
  | trapHandler {n : Nat} {cs : List Catch} : PureHead [.handler n cs [.trap]] [.trap]
  /-- `Step_pure/trap-frame`. -/
  | trapFrame {fi : Frame} {n : Nat} : PureHead [.frame n fi [.trap]] [.trap]

/-- **Core head steps that are `Step_read` rules** (and keep the state), as a relation from a
configuration to the new code. -/
inductive ReadHead : Config H → List Admin → Prop where
  /-- `Step_read/local.get`. -/
  | localGet {s : Store H} {f : Frame} {x : LocalIdx} {v : Val} (h : f.local? x = some (some v)) :
      ReadHead ⟨s, f, [.plain (.localGet x)]⟩ [v.toAdmin]
  /-- `Step_read/global.get`. -/
  | globalGet {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
      (h : s.global? f x = some (a, g)) :
      ReadHead ⟨s, f, [.plain (.globalGet x)]⟩ [g.value.toAdmin]

end Silmaril.Wasm.SpecTec.Institution.Fwd30
