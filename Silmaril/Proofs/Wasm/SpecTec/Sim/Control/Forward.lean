module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.Pure

/-!
# Family C: forward obligations discharged through `Step_pure`

Each `fwd_*` below has exactly the type of the `Forward` field of the same name at
`env := simEnv B`, under the encoding's `TypingFacts` and the family's `CtrlTyping`. The proof
builds the `Step_pure` derivation of `Pure.lean` on the images and lifts it with `Step/pure`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type} {hn : H → String}

/-! ## Encoding facts -/

/-- A source body as administrative code is encoded as the body. -/
theorem adminsToV_expression (es : List Instr) : adminsToV (expression es) = instrsToV es := by
  induction es with
  | nil => rfl
  | cons i es ih =>
      show adminToV (.plain i) :: adminsToV (expression es) = _
      rw [ih]
      rfl

@[simp] theorem adminsToV_nil' : adminsToV ([] : List Admin) = [] := rfl
@[simp] theorem adminsToV_cons' (a : Admin) (l : List Admin) :
    adminsToV (a :: l) = adminToV a :: adminsToV l := rfl
@[simp] theorem adminToV_label (n : Nat) (cont : List Instr) (body : List Admin) :
    adminToV (.label n cont body) =
      .case "LABEL_%{%}%" (.tuple [.num (.natN n), .list (instrsToV cont), .list (adminsToV body)]) :=
  rfl
@[simp] theorem adminToV_handler (n : Nat) (cs : List Catch) (body : List Admin) :
    adminToV (.handler n cs body) = .case "HANDLER_%{%}%" (.tuple [.num (.natN n),
      .list (cs.map Encode.toValue), .list (adminsToV body)]) := rfl
@[simp] theorem adminToV_frame (n : Nat) (fi : Frame) (body : List Admin) :
    adminToV (.frame n fi body) =
      .case "FRAME_%{%}%" (.tuple [.num (.natN n), frameV fi, .list (adminsToV body)]) := rfl
@[simp] theorem adminToV_br (l : LabelIdx) :
    adminToV (.plain (.br l)) = .case "BR" (pctV l.toNat) := rfl
@[simp] theorem adminToV_return : adminToV (.plain .return_) = caseNilV "RETURN" := rfl
@[simp] theorem adminToV_refNull : adminToV (.ref .null) = caseNilV "REF.NULL_ADDR" := rfl
@[simp] theorem adminToV_refFunc (a : Nat) :
    adminToV (.ref (.func a)) = .case "REF.FUNC_ADDR" (.num (.natN a)) := rfl
@[simp] theorem adminToV_trap : adminToV .trap = caseNilV "TRAP" := rfl
@[simp] theorem labelPred_toNat (l : LabelIdx) : (labelPred l).toNat = l.toNat - 1 := rfl

/-- An index is encoded as `%` of its value. -/
theorem toValue_idx {k : IndexKind} (x : Idx k) : Encode.toValue x = pctV x.toNat := rfl

/-- The image of typed code is typed elementwise. -/
theorem typedV_code {env : Env} {is : List Admin}
    (h : TypedV env instrsT (.list (adminsToV is))) : ∀ a ∈ is, TypedV env instrT (adminToV a) := by
  rw [adminsToV_eq_map, typedV_list_iff] at h
  exact fun a ha => h _ (List.mem_map_of_mem ha)

/-- The image of typed code splits over `++`. -/
theorem typedV_code_append {env : Env} {a b : List Admin}
    (h : TypedV env instrsT (.list (adminsToV (a ++ b)))) :
    TypedV env instrsT (.list (adminsToV a)) ∧ TypedV env instrsT (.list (adminsToV b)) := by
  rw [adminsToV_append] at h
  exact typedV_list_append.1 h

/-- A value prefix of typed code is typed as `val*`. -/
theorem typedV_vals_prefix {env : Env} (T : TypingFacts env hn) {vs : List Val} {b : List Admin}
    (h : TypedV env instrsT (.list (adminsToV (vals vs ++ b)))) :
    TypedV env valsT (.list (adminsToV (vals vs))) :=
  T.vals vs (typedV_code_append h).1

/-- `Step/pure`, with access to the typing of both code sequences. -/
theorem fwd_of_spure' {env : Env} (T : TypingFacts env hn)
    (hr : Equiv.Validation.HasRuleAt env "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule)
    {s : Store H} {f : Frame} {is is' : List Admin}
    (h : TypedV env instrsT (.list (adminsToV is)) → TypedV env instrsT (.list (adminsToV is')) →
      SPure env (adminsToV is) (adminsToV is')) : FwdP env hn ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro hc hc'
  obtain ⟨hz, his⟩ := (T.config _).1 hc
  obtain ⟨-, his'⟩ := (T.config _).1 hc'
  exact sstep_pure hr hz his his' (h his his')

/-- `c ≠ 0` on the encoding. -/
theorem toNat_ne_zero {c : BitVec 32} (h : c ≠ 0) : c.toNat ≠ 0 :=
  fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))

section Fwd

variable (B : Builtins) (T : TypingFacts (simEnv B) hn) (Ty : CtrlTyping (simEnv B))

/-- The `Step/pure` rule of `simEnv B`. -/
theorem simEnv_pureRule (B : Builtins) :
    Equiv.Validation.HasRuleAt (simEnv B) "Step" "%~>%" 0 Equiv.ExecStepRules.pureRule :=
  (hasStepRules_simEnv B).pure

/-- The `Step_pure` rules of `simEnv B` this family uses. -/
theorem simEnv_execRules (B : Builtins) : Equiv.Execution.HasStepRules (simEnv B) := by
  have h := Equiv.Execution.hasStepRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The `br_table` rules of `simEnv B`. -/
theorem simEnv_brTableRules (B : Builtins) : Equiv.ExecDefault.HasBrTableRules (simEnv B) := by
  have h := Equiv.ExecDefault.hasBrTableRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

/-- The reference rules of `simEnv B`. -/
theorem simEnv_refRules (B : Builtins) : Equiv.ExecRef.HasRefRules (simEnv B) := by
  have h := Equiv.ExecRef.hasRefRules_wasm30
  cases h
  constructor <;> (apply hasRuleAt_simEnv; assumption)

include T Ty in
/-- `Forward.ifTrue`. -/
theorem fwd_ifTrue : ∀ {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType}
    {b₁ b₂ : List Instr} (_ : c ≠ 0),
    FwdP (simEnv B) hn ⟨s, f, [constI32 c, .plain (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.plain (.block bt b₁)]⟩ := by
  intro s f c bt b₁ b₂ hc
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hbt, h₁, h₂⟩ := Ty.ifInv _ _ _ (typedV_code h (.plain (.if_ bt b₁ b₂)) (by simp))
  exact spure_ifTrue (simEnv_execRules B).ifTrue (toNat_ne_zero hc) (Ty.i32 c) hbt h₁ h₂

include T Ty in
/-- `Forward.ifFalse`. -/
theorem fwd_ifFalse : ∀ {s : Store H} {f : Frame} {bt : BlockType} {b₁ b₂ : List Instr},
    FwdP (simEnv B) hn ⟨s, f, [constI32 0, .plain (.if_ bt b₁ b₂)]⟩
      ⟨s, f, [.plain (.block bt b₂)]⟩ := by
  intro s f bt b₁ b₂
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hbt, h₁, h₂⟩ := Ty.ifInv _ _ _ (typedV_code h (.plain (.if_ bt b₁ b₂)) (by simp))
  exact spure_ifFalse (simEnv_execRules B).ifFalse (Ty.i32 0) hbt h₁ h₂

include T in
/-- `Forward.labelVals`. -/
theorem fwd_labelVals : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val},
    FwdP (simEnv B) hn ⟨s, f, [.label n cont (vals vs)]⟩ ⟨s, f, vals vs⟩ := by
  intro s f n cont vs
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, hb⟩ := T.label n cont (vals vs) h
  exact spure_labelVals (simEnv_execRules B).labelVals hn₀ hc (T.vals vs hb)

include T Ty in
/-- `Forward.brLabelZero`. -/
theorem fwd_brLabelZero : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs' vs : List Val} {l : LabelIdx} {rest : List Admin} (_ : l.toNat = 0)
    (_ : vs.length = n),
    FwdP (simEnv B) hn ⟨s, f, [.label n cont (vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ expression cont⟩ := by
  intro s f n cont vs' vs l rest hl hlen
  subst hlen
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨-, hc, hb⟩ := T.label _ cont _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
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

include T Ty in
/-- `Forward.brLabelSucc`. -/
theorem fwd_brLabelSucc : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {l : LabelIdx} {rest : List Admin} (_ : 0 < l.toNat),
    FwdP (simEnv B) hn ⟨s, f, [.label n cont (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩ := by
  intro s f n cont vs l rest hl
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, hb⟩ := T.label _ cont _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_brLabelSucc (simEnv_execRules B).brLabelSucc hl (n := .num (.natN n))
    (cont := instrsToV cont) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) (Ty.labelidx l) hrest
  simpa [adminsToV_append, toValue_idx] using key

include T Ty in
/-- `Forward.brHandler`. -/
theorem fwd_brHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {l : LabelIdx} {rest : List Admin},
    FwdP (simEnv B) hn ⟨s, f, [.handler n cs (vals vs ++ [.plain (.br l)] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain (.br l)]⟩ := by
  intro s f n cs vs l rest
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, hb⟩ := T.handler _ cs _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_brHandler (simEnv_execRules B).brHandler (n := .num (.natN n))
    (cs := cs.map Encode.toValue) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    (l := Encode.toValue l) hn₀ hc (T.vals vs hv) (Ty.labelidx l) hrest
  simpa [adminsToV_append, toValue_idx] using key

include T Ty in
/-- `Forward.brIfTrue`. -/
theorem fwd_brIfTrue : ∀ {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (_ : c ≠ 0),
    FwdP (simEnv B) hn ⟨s, f, [constI32 c, .plain (.brIf l)]⟩ ⟨s, f, [.plain (.br l)]⟩ := by
  intro s f c l hc
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_brIfTrue (simEnv_execRules B).brIfTrue (toNat_ne_zero hc) (Ty.i32 c) (Ty.labelidx l)

include T Ty in
/-- `Forward.brIfFalse`. -/
theorem fwd_brIfFalse : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP (simEnv B) hn ⟨s, f, [constI32 0, .plain (.brIf l)]⟩ ⟨s, f, []⟩ := by
  intro s f l
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_brIfFalse (simEnv_execRules B).brIfFalse (Ty.i32 0) (Ty.labelidx l)

/-- The encoding of a label table is typed. -/
theorem typedV_labels (Ty : CtrlTyping (simEnv B)) (ls : List LabelIdx) :
    TypedV (simEnv B) labelidxsT (.list (ls.map Encode.toValue)) := by
  rw [typedV_list_iff]
  intro v hv
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hv
  exact Ty.labelidx l

include T Ty in
/-- `Forward.brTableLt`. -/
theorem fwd_brTableLt : ∀ {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx}
    {l' l : LabelIdx} (_ : ls[i.toNat]? = some l),
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l)]⟩ := by
  intro s f i ls l' l hl
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_brTableLt (simEnv_brTableRules B).brTableLt (k := i.toNat) (ls := ls.map Encode.toValue)
      (l := Encode.toValue l) (by rw [List.getElem?_map, hl]; rfl) (Ty.i32 i) (typedV_labels B Ty ls) (Ty.labelidx l')

include T Ty in
/-- `Forward.brTableGe`. -/
theorem fwd_brTableGe : ∀ {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx}
    {l' : LabelIdx} (_ : ls.length ≤ i.toNat),
    FwdP (simEnv B) hn ⟨s, f, [constI32 i, .plain (.brTable ls l')]⟩ ⟨s, f, [.plain (.br l')]⟩ := by
  intro s f i ls l' hl
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_brTableGe (simEnv_brTableRules B).brTableGe (k := i.toNat) (ls := ls.map Encode.toValue)
      (by rw [List.length_map]; exact hl) (Ty.i32 i) (typedV_labels B Ty ls) (Ty.labelidx l')

include T Ty in
/-- `Forward.brOnNullNull`. -/
theorem fwd_brOnNullNull : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, .plain (.brOnNull l)]⟩ ⟨s, f, [.plain (.br l)]⟩ := by
  intro s f l
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  have hv := typedV_vals_prefix T (vs := [.ref .null]) (b := [.plain (.brOnNull l)]) h
  exact spure_brOnNullNull (simEnv_refRules B).brOnNullNull
    (typedV_list_single.1 hv) (Ty.labelidx l)

include T Ty in
/-- `Forward.brOnNonNullNull`. -/
theorem fwd_brOnNonNullNull : ∀ {s : Store H} {f : Frame} {l : LabelIdx},
    FwdP (simEnv B) hn ⟨s, f, [.ref .null, .plain (.brOnNonNull l)]⟩ ⟨s, f, []⟩ := by
  intro s f l
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  have hv := typedV_vals_prefix T (vs := [.ref .null]) (b := [.plain (.brOnNonNull l)]) h
  exact spure_brOnNonNullNull (simEnv_refRules B).brOnNonNullNull
    (typedV_list_single.1 hv) (Ty.labelidx l)

include T Ty in
/-- `Forward.callIndirect`. -/
theorem fwd_callIndirect : ∀ {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx},
    FwdP (simEnv B) hn ⟨s, f, [.plain (.callIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]⟩ := by
  intro s f x y
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_callIndirect (simEnv_refRules B).callIndirect (Ty.idx x) (Ty.typeuseIdx y)

include T Ty in
/-- `Forward.returnCallIndirect`. -/
theorem fwd_returnCallIndirect : ∀ {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx},
    FwdP (simEnv B) hn ⟨s, f, [.plain (.returnCallIndirect x y)]⟩
      ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
        .plain (.returnCallRef y)]⟩ := by
  intro s f x y
  exact fwd_of_spure' T (simEnv_pureRule B) fun _ _ =>
    spure_returnCallIndirect (simEnv_refRules B).returnCallIndirect (Ty.idx x) (Ty.typeuseIdx y)

include T in
/-- `Forward.frameVals`. -/
theorem fwd_frameVals : ∀ {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val}
    (_ : vs.length = n),
    FwdP (simEnv B) hn ⟨s, f, [.frame n fi (vals vs)]⟩ ⟨s, f, vals vs⟩ := by
  intro s f fi n vs hlen
  subst hlen
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hfi, hb⟩ := T.frame _ fi _ h
  have key := spure_frameVals (simEnv_execRules B).frameVals (f := frameV fi)
    (ws := adminsToV (vals vs)) (by simpa [adminsToV_length] using hn₀) hfi (T.vals vs hb)
  simpa [adminsToV_length] using key

include T Ty in
/-- `Forward.returnFrame`. -/
theorem fwd_returnFrame : ∀ {s : Store H} {f fi : Frame} {n : Nat} {vs' vs : List Val}
    {rest : List Admin} (_ : vs.length = n),
    FwdP (simEnv B) hn ⟨s, f, [.frame n fi (vals vs' ++ vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs⟩ := by
  intro s f fi n vs' vs rest hlen
  subst hlen
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨-, hfi, hb⟩ := T.frame _ fi _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
  obtain ⟨habc, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hab, -⟩ := typedV_list_append.1 habc
  obtain ⟨hv', hv⟩ := typedV_list_append.1 hab
  have key := spure_returnFrame (simEnv_execRules B).returnFrame (f := frameV fi)
    (ws' := adminsToV (vals vs')) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    (Ty.nat _) hfi (T.vals vs' hv') (T.vals vs hv) hrest
  simpa [adminsToV_append, adminsToV_length] using key

include T in
/-- `Forward.returnLabel`. -/
theorem fwd_returnLabel : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr}
    {vs : List Val} {rest : List Admin},
    FwdP (simEnv B) hn ⟨s, f, [.label n cont (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
  intro s f n cont vs rest
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, hb⟩ := T.label _ cont _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_returnLabel (simEnv_execRules B).returnLabel (n := .num (.natN n))
    (cont := instrsToV cont) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) hrest
  simpa [adminsToV_append, toValue_idx] using key

include T in
/-- `Forward.returnHandler`. -/
theorem fwd_returnHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch}
    {vs : List Val} {rest : List Admin},
    FwdP (simEnv B) hn ⟨s, f, [.handler n cs (vals vs ++ [.plain .return_] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
  intro s f n cs vs rest
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, hb⟩ := T.handler _ cs _ h
  have hb' := hb
  simp only [adminsToV_append] at hb'
  obtain ⟨hab, hrest⟩ := typedV_list_append.1 hb'
  obtain ⟨hv, -⟩ := typedV_list_append.1 hab
  have key := spure_returnHandler (simEnv_execRules B).returnHandler (n := .num (.natN n))
    (cs := cs.map Encode.toValue) (ws := adminsToV (vals vs)) (is := adminsToV rest)
    hn₀ hc (T.vals vs hv) hrest
  simpa [adminsToV_append, toValue_idx] using key

include T in
/-- `Forward.trapInstrs`. -/
theorem fwd_trapInstrs : ∀ {s : Store H} {f : Frame} {vs : List Val} {rest : List Admin}
    (_ : vs ≠ [] ∨ rest ≠ []),
    FwdP (simEnv B) hn ⟨s, f, vals vs ++ [.trap] ++ rest⟩ ⟨s, f, [.trap]⟩ := by
  intro s f vs rest hne
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  have hv := typedV_vals_prefix T (b := [.trap] ++ rest) (by simpa using h)
  have h' := h
  simp only [adminsToV_append] at h'
  obtain ⟨-, hrest⟩ := typedV_list_append.1 h'
  have hne' : adminsToV (vals vs) ≠ [] ∨ adminsToV rest ≠ [] := by
    rcases hne with h | h
    · exact .inl (adminsToV_ne_nil (by simpa [vals] using h))
    · exact .inr (adminsToV_ne_nil h)
  have key := spure_trapInstrs (simEnv_execRules B).trapInstrs hne' hv hrest
  simpa [adminsToV_append, toValue_idx] using key

include T in
/-- `Forward.trapLabel`. -/
theorem fwd_trapLabel : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr},
    FwdP (simEnv B) hn ⟨s, f, [.label n cont [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  intro s f n cont
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, -⟩ := T.label _ cont _ h
  exact spure_trapLabel (simEnv_execRules B).trapLabel hn₀ hc

include T in
/-- `Forward.trapHandler`. -/
theorem fwd_trapHandler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch},
    FwdP (simEnv B) hn ⟨s, f, [.handler n cs [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  intro s f n cs
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hc, -⟩ := T.handler _ cs _ h
  exact spure_trapHandler (simEnv_execRules B).trapHandler hn₀ hc

include T in
/-- `Forward.trapFrame`. -/
theorem fwd_trapFrame : ∀ {s : Store H} {f fi : Frame} {n : Nat},
    FwdP (simEnv B) hn ⟨s, f, [.frame n fi [.trap]]⟩ ⟨s, f, [.trap]⟩ := by
  intro s f fi n
  refine fwd_of_spure' T (simEnv_pureRule B) fun h _ => ?_
  obtain ⟨hn₀, hfi, -⟩ := T.frame _ fi _ h
  exact spure_trapFrame (simEnv_execRules B).trapFrame hn₀ hfi

end Fwd

end Silmaril.Wasm.SpecTec.Sim
