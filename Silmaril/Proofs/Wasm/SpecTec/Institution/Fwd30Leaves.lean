module

public import Silmaril.Wasm.SpecTec.Institution.Fwd30.Defs
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Typing.Thms

/-!
# The forward direction for `Step_pure` and `Step_read`: the declarative facts

For every `B`, every `PureHead is is'` with typed `is` is a `Step_pure` fact of the declarative
reading `SPure (simEnv B)`, and every `ReadHead c is'` with typed `c` and typed `is'` is a
`Step_read` fact `SRead (simEnv B)`. The proofs are the bodies 's forward leaves
(`Sim.fwd_ifTrue`, …, `IntNumeric.fwd_parametric`, `State.fwd_localGet`, `State.fwd_globalGet`)
stopped before the leaves lift the fact to `Step` with `Step/pure` or `Step/read`. Those leaves
state only the lifted `Step` fact, so the bodies are copied here instead of being reused.

The typing facts are the proved ones: `Typing.typingFacts_simEnv`, `Typing.ctrlTyping_simEnv`,
`Typing.stateTyping_simEnv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Fwd30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}
variable (B : Builtins) (hn : H → String)
include hn

/-! ## `Step_pure`: the parametric family -/

/-- `drop`. -/
theorem spure_dropH (v : Val)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [v.toAdmin, .plain .drop]))) :
    SPure (simEnv B) (adminsToV [v.toAdmin, .plain .drop]) (adminsToV []) := by
  have T := Typing.typingFacts_simEnv B hn
  have hv : HasTyp (simEnv B) (VarEnv.empty.bindVals [("val", valV v)]) (.varT "val" [])
      (valV v) :=
    IntNumeric.typedV_val T ((T.append (adminsToV (vals [v])) [instrToV .drop]).1 h).1
      (List.mem_singleton_self v) ⟨rfl, rfl, rfl⟩
  show SPure (simEnv B) [adminToV v.toAdmin, .case "DROP" (.tuple [])] []
  rw [IntNumeric.adminToV_toAdmin]
  exact IntNumeric.spure_drop (IntNumeric.hasPureRules_simEnv B).drop hv

/-- `select` at a non-zero condition. -/
theorem spure_selectTrueH {v₁ v₂ : Val} {c : BitVec 32} {ts : Option (List ValType)} (hc0 : c ≠ 0)
    (h : TypedV (simEnv B) instrsT
      (.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)]))) :
    SPure (simEnv B) (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 c, .plain (.select ts)])
      (adminsToV [v₁.toAdmin]) := by
  have hty := IntNumeric.selTyped (Typing.typingFacts_simEnv B hn) (v₁ := v₁) (v₂ := v₂) (c := c)
    (ts := ts) h
  have hn0 : c.toNat ≠ 0 := fun h0 => hc0 (BitVec.eq_of_toNat_eq (by simpa using h0))
  show SPure (simEnv B) [adminToV v₁.toAdmin, adminToV v₂.toAdmin, adminToV (constI32 c),
    instrToV (.select ts)] [adminToV v₁.toAdmin]
  rw [IntNumeric.adminToV_toAdmin, IntNumeric.adminToV_toAdmin, IntNumeric.instrToV_select]
  exact IntNumeric.spure_selectTrue (IntNumeric.hasPureRules_simEnv B).selectTrue hty hn0

/-- `select` at a zero condition. -/
theorem spure_selectFalseH (v₁ v₂ : Val) (ts : Option (List ValType))
    (h : TypedV (simEnv B) instrsT
      (.list (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)]))) :
    SPure (simEnv B) (adminsToV [v₁.toAdmin, v₂.toAdmin, constI32 0, .plain (.select ts)])
      (adminsToV [v₂.toAdmin]) := by
  have hty := IntNumeric.selTyped (Typing.typingFacts_simEnv B hn) (v₁ := v₁) (v₂ := v₂) (c := 0)
    (ts := ts) h
  show SPure (simEnv B) [adminToV v₁.toAdmin, adminToV v₂.toAdmin, adminToV (constI32 0),
    instrToV (.select ts)] [adminToV v₂.toAdmin]
  rw [IntNumeric.adminToV_toAdmin, IntNumeric.adminToV_toAdmin, IntNumeric.instrToV_select]
  exact IntNumeric.spure_selectFalse (IntNumeric.hasPureRules_simEnv B).selectFalse hty

/-- **The parametric family**, as `Step_pure` facts. -/
theorem spure_parametric {is is' : List Admin} (hp : ParametricStep is is')
    (h : TypedV (simEnv B) instrsT (.list (adminsToV is))) :
    SPure (simEnv B) (adminsToV is) (adminsToV is') := by
  cases hp with
  | unreachable => exact IntNumeric.spure_unreachable (IntNumeric.hasPureRules_simEnv B).unreachable
  | nop => exact IntNumeric.spure_nopRule (IntNumeric.hasPureRules_simEnv B).nop
  | drop v => exact spure_dropH B hn v h
  | selectTrue hc0 => exact spure_selectTrueH B hn hc0 h
  | selectFalse v₁ v₂ ts => exact spure_selectFalseH B hn v₁ v₂ ts h

/-! ## `Step_pure`: control -/

omit hn in
/-- `if` at a non-zero condition. -/
theorem spure_ifTrueH {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr} (hc : c ≠ 0)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)]))) :
    SPure (simEnv B) (adminsToV [constI32 c, .plain (.if_ bt b₁ b₂)])
      (adminsToV [.plain (.block bt b₁)]) := by
  have Ty := Typing.ctrlTyping_simEnv B
  obtain ⟨hbt, h₁, h₂⟩ := Ty.ifInv _ _ _ (typedV_code h (.plain (.if_ bt b₁ b₂)) (by simp))
  exact spure_ifTrue (simEnv_execRules B).ifTrue (toNat_ne_zero hc) (Ty.i32 c) hbt h₁ h₂

omit hn in
/-- `if` at a zero condition. -/
theorem spure_ifFalseH {bt : BlockType} {b₁ b₂ : List Instr}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [constI32 0, .plain (.if_ bt b₁ b₂)]))) :
    SPure (simEnv B) (adminsToV [constI32 0, .plain (.if_ bt b₁ b₂)])
      (adminsToV [.plain (.block bt b₂)]) := by
  have Ty := Typing.ctrlTyping_simEnv B
  obtain ⟨hbt, h₁, h₂⟩ := Ty.ifInv _ _ _ (typedV_code h (.plain (.if_ bt b₁ b₂)) (by simp))
  exact spure_ifFalse (simEnv_execRules B).ifFalse (Ty.i32 0) hbt h₁ h₂

/-- A label with values. -/
theorem spure_labelValsH {n : Nat} {cont : List Instr} {vs : List Val}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [.label n cont (vals vs)]))) :
    SPure (simEnv B) (adminsToV [.label n cont (vals vs)]) (adminsToV (vals vs)) := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hn₀, hc, hb⟩ := T.label n cont (vals vs) h
  exact spure_labelVals (simEnv_execRules B).labelVals hn₀ hc (T.vals vs hb)

/-- `br 0` at a label. -/
theorem spure_brLabelZeroH {n : Nat} {cont : List Instr} {vs' vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : l.toNat = 0) (hlen : vs.length = n)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ expression cont)) := by
  subst hlen
  have T := Typing.typingFacts_simEnv B hn
  have Ty := Typing.ctrlTyping_simEnv B
  obtain ⟨-, hc, hb⟩ := T.label _ cont _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs') ++ adminsToV (vals vs) ++
      adminsToV [.plain (.br l)] ++ adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨habc, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have hl₀ : Encode.toValue l = pctV 0 := by rw [toValue_idx, hl]
  have key := spure_brLabelZero (simEnv_execRules B).brLabelZero (cont := instrsToV cont)
    (ws' := adminsToV (vals vs')) (ws := adminsToV (vals vs)) (is := adminsToV rest) hl₀
    (Ty.nat _) hc (T.vals vs' hv') (T.vals vs hv) (Ty.labelidx l) hrest
  have e₁ : (adminsToV (vals vs)).length = vs.length := by simp [adminsToV_length]
  rw [e₁] at key
  simpa [adminsToV_append, adminsToV_expression, toValue_idx] using key

/-- `br (l+1)` at a label. -/
theorem spure_brLabelSuccH {n : Nat} {cont : List Instr} {vs : List Val} {l : LabelIdx}
    {rest : List Admin} (hl : 0 < l.toNat)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ [.plain (.br (labelPred l))])) := by
  have T := Typing.typingFacts_simEnv B hn
  have Ty := Typing.ctrlTyping_simEnv B
  obtain ⟨hn₀, hc, hb⟩ := T.label _ cont _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs) ++ adminsToV [.plain (.br l)] ++
      adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_brLabelSucc (simEnv_execRules B).brLabelSucc hl (n := .num (.natN n))
    (cont := instrsToV cont) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) (Ty.labelidx l) hrest
  simpa [adminsToV_append, toValue_idx] using key

/-- `br` at a handler. -/
theorem spure_brHandlerH {n : Nat} {cs : List Catch} {vs : List Val} {l : LabelIdx}
    {rest : List Admin}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)])
      (adminsToV (vals vs ++ [.plain (.br l)])) := by
  have T := Typing.typingFacts_simEnv B hn
  have Ty := Typing.ctrlTyping_simEnv B
  obtain ⟨hn₀, hc, hb⟩ := T.handler _ cs _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs) ++ adminsToV [.plain (.br l)] ++
      adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_brHandler (simEnv_execRules B).brHandler (n := .num (.natN n))
    (cs := cs.map Encode.toValue) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    (l := Encode.toValue l) hn₀ hc (T.vals vs hv) (Ty.labelidx l) hrest
  simpa [adminsToV_append, toValue_idx] using key

/-- `br_on_null` at `null`. -/
theorem spure_brOnNullNullH {l : LabelIdx}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [.ref .null, .plain (.brOnNull l)]))) :
    SPure (simEnv B) (adminsToV [.ref .null, .plain (.brOnNull l)]) (adminsToV [.plain (.br l)]) := by
  have hv := typedV_vals_prefix (Typing.typingFacts_simEnv B hn) (vs := [.ref .null])
    (b := [.plain (.brOnNull l)]) h
  exact spure_brOnNullNull (simEnv_refRules B).brOnNullNull
    (typedV_list_single.1 hv) ((Typing.ctrlTyping_simEnv B).labelidx l)

/-- `br_on_non_null` at `null`. -/
theorem spure_brOnNonNullNullH {l : LabelIdx}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [.ref .null, .plain (.brOnNonNull l)]))) :
    SPure (simEnv B) (adminsToV [.ref .null, .plain (.brOnNonNull l)]) (adminsToV []) := by
  have hv := typedV_vals_prefix (Typing.typingFacts_simEnv B hn) (vs := [.ref .null])
    (b := [.plain (.brOnNonNull l)]) h
  exact spure_brOnNonNullNull (simEnv_refRules B).brOnNonNullNull
    (typedV_list_single.1 hv) ((Typing.ctrlTyping_simEnv B).labelidx l)

/-! ## `Step_pure`: frames, `return` and `trap` -/

/-- A frame with values. -/
theorem spure_frameValsH {fi : Frame} {n : Nat} {vs : List Val} (hlen : vs.length = n)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV [.frame n fi (vals vs)]))) :
    SPure (simEnv B) (adminsToV [.frame n fi (vals vs)]) (adminsToV (vals vs)) := by
  subst hlen
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hn₀, hfi, hb⟩ := T.frame _ fi _ h
  have key := spure_frameVals (simEnv_execRules B).frameVals (f := frameV fi)
    (ws := adminsToV (vals vs)) (by simpa [adminsToV_length] using hn₀) hfi (T.vals vs hb)
  simpa [adminsToV_length] using key

/-- `return` at a frame. -/
theorem spure_returnFrameH {fi : Frame} {n : Nat} {vs' vs : List Val} {rest : List Admin}
    (hlen : vs.length = n)
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs)) := by
  subst hlen
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨-, hfi, hb⟩ := T.frame _ fi _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs') ++ adminsToV (vals vs) ++
      adminsToV [.plain .return_] ++ adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨habc, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have key := spure_returnFrame (simEnv_execRules B).returnFrame (f := frameV fi)
    (ws' := adminsToV (vals vs')) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    ((Typing.ctrlTyping_simEnv B).nat _) hfi (T.vals vs' hv') (T.vals vs hv) hrest
  simpa [adminsToV_append, adminsToV_length] using key

/-- `return` at a label. -/
theorem spure_returnLabelH {n : Nat} {cont : List Instr} {vs : List Val} {rest : List Admin}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.label n cont (vals vs ++ [.plain .return_] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.label n cont (vals vs ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs ++ [.plain .return_])) := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hn₀, hc, hb⟩ := T.label _ cont _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs) ++ adminsToV [.plain .return_] ++
      adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_returnLabel (simEnv_execRules B).returnLabel (n := .num (.natN n))
    (cont := instrsToV cont) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) hrest
  simpa [adminsToV_append, toValue_idx] using key

/-- `return` at a handler. -/
theorem spure_returnHandlerH {n : Nat} {cs : List Catch} {vs : List Val} {rest : List Admin}
    (h : TypedV (simEnv B) instrsT (.list (adminsToV
      [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]))) :
    SPure (simEnv B) (adminsToV [.handler n cs (vals vs ++ [.plain .return_] ++ rest)])
      (adminsToV (vals vs ++ [.plain .return_])) := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hn₀, hc, hb⟩ := T.handler _ cs _ h
  have hb' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs) ++ adminsToV [.plain .return_] ++
      adminsToV rest)) := by simpa only [adminsToV_append] using hb
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_returnHandler (simEnv_execRules B).returnHandler (n := .num (.natN n))
    (cs := cs.map Encode.toValue) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) hrest
  simpa [adminsToV_append, toValue_idx] using key

/-- `trap` in a sequence. -/
theorem spure_trapInstrsH {vs : List Val} {rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (h : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs ++ [.trap] ++ rest)))) :
    SPure (simEnv B) (adminsToV (vals vs ++ [.trap] ++ rest)) (adminsToV [.trap]) := by
  have T := Typing.typingFacts_simEnv B hn
  have hv := typedV_vals_prefix T (b := [.trap] ++ rest) (by simpa using h)
  have h' : TypedV (simEnv B) instrsT (.list (adminsToV (vals vs) ++ adminsToV [.trap] ++
      adminsToV rest)) := by simpa only [adminsToV_append] using h
  obtain ⟨-, hrest⟩ := typedV_list_append.1 h'
  have hne' : adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (adminsToV_ne_nil (by simpa [vals] using h))
    · exact .inr (adminsToV_ne_nil h)
  have key := spure_trapInstrs (simEnv_execRules B).trapInstrs hne' hv hrest
  simpa [adminsToV_append, toValue_idx] using key

/-- **`PureHead` steps are `Step_pure` facts** of the declarative reading, at typed code. -/
theorem spure_of_pureHead {is is' : List Admin} (hp : PureHead is is')
    (h : TypedV (simEnv B) instrsT (.list (adminsToV is))) :
    SPure (simEnv B) (adminsToV is) (adminsToV is') := by
  have T : TypingFacts (simEnv B) hn := Typing.typingFacts_simEnv B hn
  have Ty : CtrlTyping (simEnv B) := Typing.ctrlTyping_simEnv B
  cases hp with
  | parametric hp => exact spure_parametric B hn hp h
  | ifTrue hc => exact spure_ifTrueH B hc h
  | ifFalse => exact spure_ifFalseH B h
  | labelVals => exact spure_labelValsH B hn h
  | brLabelZero hl hlen => exact spure_brLabelZeroH B hn hl hlen h
  | brLabelSucc hl => exact spure_brLabelSuccH B hn hl h
  | brHandler => exact spure_brHandlerH B hn h
  | @brIfTrue c l hc =>
    exact spure_brIfTrue (simEnv_execRules B).brIfTrue (toNat_ne_zero hc) (Ty.i32 c) (Ty.labelidx l)
  | @brIfFalse l => exact spure_brIfFalse (simEnv_execRules B).brIfFalse (Ty.i32 0) (Ty.labelidx l)
  | @brTableLt i ls l' l hl =>
    exact spure_brTableLt (simEnv_brTableRules B).brTableLt (k := i.toNat)
      (ls := ls.map Encode.toValue) (l := Encode.toValue l) (by rw [List.getElem?_map, hl]; rfl)
      (Ty.i32 i) (typedV_labels B Ty ls) (Ty.labelidx l')
  | @brTableGe i ls l' hl =>
    exact spure_brTableGe (simEnv_brTableRules B).brTableGe (k := i.toNat)
      (ls := ls.map Encode.toValue) (by rw [List.length_map]; exact hl) (Ty.i32 i)
      (typedV_labels B Ty ls) (Ty.labelidx l')
  | brOnNullNull => exact spure_brOnNullNullH B hn h
  | brOnNonNullNull => exact spure_brOnNonNullNullH B hn h
  | @callIndirect x y =>
    exact spure_callIndirect (simEnv_refRules B).callIndirect (Ty.idx x) (Ty.typeuseIdx y)
  | @returnCallIndirect x y =>
    exact spure_returnCallIndirect (simEnv_refRules B).returnCallIndirect (Ty.idx x)
      (Ty.typeuseIdx y)
  | frameVals hlen => exact spure_frameValsH B hn hlen h
  | returnFrame hlen => exact spure_returnFrameH B hn hlen h
  | returnLabel => exact spure_returnLabelH B hn h
  | returnHandler => exact spure_returnHandlerH B hn h
  | trapInstrs hne => exact spure_trapInstrsH B hn hne h
  | @trapLabel n cont =>
    obtain ⟨hn₀, hc, -⟩ := T.label _ cont _ h
    exact spure_trapLabel (simEnv_execRules B).trapLabel hn₀ hc
  | @trapHandler n cs =>
    obtain ⟨hn₀, hc, -⟩ := T.handler _ cs _ h
    exact spure_trapHandler (simEnv_execRules B).trapHandler hn₀ hc
  | @trapFrame fi n =>
    obtain ⟨hn₀, hfi, -⟩ := T.frame _ fi _ h
    exact spure_trapFrame (simEnv_execRules B).trapFrame hn₀ hfi

/-! ## `Step_read` -/

/-- `local.get`. -/
theorem sread_localGetH {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    (h : f.local? x = some (some v)) (hc : Typed (simEnv B) hn ⟨s, f, [.plain (.localGet x)]⟩)
    (hc' : Typed (simEnv B) hn ⟨s, f, [v.toAdmin]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.localGet x)]⟩) (adminsToV [v.toAdmin]) := by
  have T := Typing.typingFacts_simEnv B hn
  have hv : TypedV (simEnv B) valT (valV v) := State.typedV_val_of_mem T hc' (by simp)
  have hr : (Value.list (f.locals.map fun o => .opt (o.map valV))).idx? x.toNat =
      some (.opt (some (valV v))) := by
    simp only [Frame.local?] at h
    simp [Value.idx?, h]
  show SRead _ (cfgV _ [_]) [adminToV v.toAdmin]
  rw [IntNumeric.adminToV_toAdmin]
  exact State.sread_localGet (State.hasReadRules_simEnv B).localGet (State.stateDefs_simEnv B)
    (State.typedV_state T hc) ((Typing.stateTyping_simEnv B).idx _ x.value.isLt) hv
    (State.frameV_LOCALS f) hr

/-- `global.get`. -/
theorem sread_globalGetH {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    (h : s.global? f x = some (a, g)) (hc : Typed (simEnv B) hn ⟨s, f, [.plain (.globalGet x)]⟩)
    (hc' : Typed (simEnv B) hn ⟨s, f, [g.value.toAdmin]⟩) :
    SRead (simEnv B) (configV hn ⟨s, f, [.plain (.globalGet x)]⟩) (adminsToV [g.value.toAdmin]) := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨ha, hg⟩ := State.Store.global?_eq_some h
  have hv : TypedV (simEnv B) valT (valV g.value) := State.typedV_val_of_mem T hc' (by simp)
  show SRead _ (cfgV _ [_]) [adminToV g.value.toAdmin]
  rw [IntNumeric.adminToV_toAdmin]
  exact State.sread_globalGet (State.hasReadRules_simEnv B).globalGet (State.stateDefs_simEnv B)
    (State.typedV_state T hc) ((Typing.stateTyping_simEnv B).idx _ x.value.isLt) hv
    (State.storeV_GLOBALS hn s) (State.frameV_MODULE f) (State.moduleV_GLOBALS _)
    (State.getElem?_map_natN ha) (by simp [hg]) (State.globalInstV_VALUE g)

/-- **`ReadHead` steps are `Step_read` facts** of the declarative reading, between typed
configurations. -/
theorem sread_of_readHead {c : Config H} {is' : List Admin} (hr : ReadHead c is')
    (hc : Typed (simEnv B) hn c) (hc' : Typed (simEnv B) hn ⟨c.store, c.frame, is'⟩) :
    SRead (simEnv B) (configV hn c) (adminsToV is') := by
  cases hr with
  | localGet h => exact sread_localGetH B hn h hc hc'
  | globalGet h => exact sread_globalGetH B hn h hc hc'

end Silmaril.Wasm.SpecTec.Institution.Fwd30
