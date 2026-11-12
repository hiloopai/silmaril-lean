module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Multi.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Thms
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Multi.Eq

/-!
# Round 5: SpecTec's successors keep their `CALL_REF`s typed

`SuccCallsTyped B hn` holds for every `B` and encoding (`succCallsTyped`), so `SuccTyped` does
too (`succTyped`). The proof inverts every one of the 36 rules of SpecTec's `Step` at once.

* The declarative reading types every quantifier of a rule (`QuantsOk`). So whenever a rule's
  right-hand code is assembled from quantified `instr*` and `val*` variables, from contexts
  (`LABEL_`, `HANDLER_`, `FRAME_`) around such code, from constructors other than `CALL_REF`
  and the contexts, and from `$lift_result(result)` with `result : result`, the `CALL_REF`s of
  the successor are typed `instr`s. `chk` checks that shape syntactically; `chk_sound` is its
  soundness.
* `stepRules_checked` runs the check on the 36 rules of the fixed script, by `rfl`. Every rule
  passes except `call_ref-hostfunc-div`, whose right-hand code is its left-hand code, which the
  check recognises separately (`isHostDivCode`): its successor's code is the source's, which is
  typed.

Rules 0 and 1 (`pure`, `read`) need no inversion of `Step_pure` or `Step_read`: their
right-hand code is the quantifier `instr'* : instr*`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Multi

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## Elements of a successor's code -/

/-- Every administrative instruction with image `x` has typed `CALL_REF`s. -/
def ElemOk (env : Env) (x : Value) : Prop :=
  ∀ a : Admin, adminToV a = x → AdminCallsTyped env a

/-- The heads `AdminCallsTyped` looks at. -/
def specialHeads : List MixopS := ["CALL_REF", "LABEL_%{%}%", "HANDLER_%{%}%", "FRAME_%{%}%"]

/-- The context heads. -/
def ctxHeads : List MixopS := ["LABEL_%{%}%", "HANDLER_%{%}%", "FRAME_%{%}%"]

theorem codeCallsTyped_of_elems {env : Env} :
    ∀ {l : List Admin}, (∀ x ∈ adminsToV l, ElemOk env x) → CodeCallsTyped env l
  | [], _ => trivial
  | a :: _, h => ⟨h _ (List.mem_cons_self ..) a rfl,
      codeCallsTyped_of_elems fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

/-- An instruction that is neither a context nor a `CALL_REF` has no `CALL_REF` to check. -/
theorem adminCallsTyped_of_head {env : Env} {a : Admin} (h : Typing.adminHead a ∉ specialHeads) :
    AdminCallsTyped env a := by
  cases a with
  | label n c b => exact absurd (by simp [specialHeads, Typing.adminHead]) h
  | handler n c b => exact absurd (by simp [specialHeads, Typing.adminHead]) h
  | frame n f b => exact absurd (by simp [specialHeads, Typing.adminHead]) h
  | plain i =>
    intro hc
    obtain ⟨y, hy⟩ | ⟨d, hd⟩ := Bwd.isCallRef_cases hc
    · cases hy
      exact absurd (by simp [specialHeads, Typing.adminHead, Typing.instrHead]) h
    · cases hd
  | ref r =>
    intro hc
    rcases Bwd.isCallRef_cases hc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  | callRefType d => exact absurd (by simp [specialHeads, Typing.adminHead]) h
  | returnCallRefType d =>
    intro hc
    rcases Bwd.isCallRef_cases hc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  | trap =>
    intro hc
    rcases Bwd.isCallRef_cases hc with ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'

/-- **A constructor other than `CALL_REF` and the contexts** is fine. -/
theorem elemOk_case {env : Env} {op : MixopS} {w : Value} (h : op ∉ specialHeads) :
    ElemOk env (.case op w) := fun _ ha =>
  adminCallsTyped_of_head ((Typing.adminToV_case ha) ▸ h)

/-- A value head is not special. -/
theorem not_special_of_val {op : MixopS} (h : op ∈ Typing.valHeads) : op ∉ specialHeads := by
  simp only [Typing.valHeads, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

section Typed

variable {env : Env} {hn : H → String}

mutual
/-- **A typed instruction has typed `CALL_REF`s**, at every depth of contexts. -/
theorem adminCallsTyped_of_typedV (T : TypingFacts env hn) :
    ∀ {a : Admin}, TypedV env instrT (adminToV a) → AdminCallsTyped env a
  | .label _ _ _, h => codeCallsTyped_of_typedV T (T.label _ _ _ (typedV_list_single.2 h)).2.2
  | .handler _ _ _, h =>
    codeCallsTyped_of_typedV T (T.handler _ _ _ (typedV_list_single.2 h)).2.2
  | .frame _ _ _, h => codeCallsTyped_of_typedV T (T.frame _ _ _ (typedV_list_single.2 h)).2.2
  | .plain _, h => fun _ => h
  | .ref _, h => fun _ => h
  | .callRefType _, h => fun _ => h
  | .returnCallRefType _, h => fun _ => h
  | .trap, h => fun _ => h

/-- **Typed code has typed `CALL_REF`s.** -/
theorem codeCallsTyped_of_typedV (T : TypingFacts env hn) :
    ∀ {l : List Admin}, TypedV env instrsT (.list (adminsToV l)) → CodeCallsTyped env l
  | [], _ => trivial
  | a :: l, h => by
    rw [adminsToV_eq_map, List.map_cons, typedV_list_cons_iff, ← adminsToV_eq_map] at h
    exact ⟨adminCallsTyped_of_typedV T h.1, codeCallsTyped_of_typedV T h.2⟩
end

/-- A typed instruction is fine. -/
theorem elemOk_of_typedV (T : TypingFacts env hn) {x : Value} (h : TypedV env instrT x) :
    ElemOk env x := fun _ ha => adminCallsTyped_of_typedV T (ha ▸ h)

end Typed

/-- **A label around fine code is fine.** -/
theorem elemOk_label {env : Env} {nv cv : Value} {xs : List Value}
    (h : ∀ x ∈ xs, ElemOk env x) : ElemOk env (.case "LABEL_%{%}%" (.tuple [nv, cv, .list xs])) := by
  intro a ha
  obtain ⟨n, c, b, rfl⟩ := Typing.head_label (Typing.adminToV_case ha).symm
  simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and] at ha
  exact codeCallsTyped_of_elems (ha.2.2.1 ▸ h)

/-- **A handler around fine code is fine.** -/
theorem elemOk_handler {env : Env} {nv cv : Value} {xs : List Value}
    (h : ∀ x ∈ xs, ElemOk env x) :
    ElemOk env (.case "HANDLER_%{%}%" (.tuple [nv, cv, .list xs])) := by
  intro a ha
  obtain ⟨n, c, b, rfl⟩ := Typing.head_handler (Typing.adminToV_case ha).symm
  simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and] at ha
  exact codeCallsTyped_of_elems (ha.2.2.1 ▸ h)

/-- **A frame around fine code is fine.** -/
theorem elemOk_frame {env : Env} {nv fv : Value} {xs : List Value}
    (h : ∀ x ∈ xs, ElemOk env x) :
    ElemOk env (.case "FRAME_%{%}%" (.tuple [nv, fv, .list xs])) := by
  intro a ha
  obtain ⟨n, c, b, rfl⟩ := Typing.head_frame (Typing.adminToV_case ha).symm
  simp only [adminToV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and] at ha
  exact codeCallsTyped_of_elems (ha.2.2.1 ▸ h)

/-! ## `$lift_result` of a typed `result` -/

theorem findDef_none_of_valsOnly {ρ : VarEnv} (hρ : ValsOnly ρ) (x : IL.Id) :
    ρ.findDef? x = none := by
  simp [VarEnv.findDef?, hρ.2.1]

/-- A call answered by `Applies`, in a scope of term variables. -/
theorem evalExp_call_of_applies {env : Env} {ρ : VarEnv} (hρ : ValsOnly ρ) {x r : IL.Id}
    {rv v : Value} (hr : ρ.findVal? r = some rv) (h : Applies env x [.val rv] v) :
    EvalExp env ρ (.callE x [.expA (.varE r)]) v :=
  evalExp_callE_iff.2 ((Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef
    (findDef_none_of_valsOnly hρ x) (Equiv.evalArgs_cons (evalExp_var hr) (evalArgs_nil _ ρ))).1 h)

/-- The three shapes of a typed `result`. -/
def ResultShape (rv : Value) : Prop :=
  (∃ l, rv = .case "_VALS" (.list l) ∧ ∀ x ∈ l, ∃ op w, x = .case op w ∧ op ∈ Typing.valHeads) ∨
    (∃ w, rv = .case "(REF.EXN_ADDR%)THROW_REF" w) ∨ rv = .case "TRAP" (.tuple [])

/-- A case of `result` with its payload type, read to its shape. -/
theorem resultShape_of_case {B : Builtins} {op : MixopS} {t : Typ} {w : Value}
    (hm : t = .iterT (.varT "val" []) .list ∧ op = "_VALS" ∨
      op = "(REF.EXN_ADDR%)THROW_REF" ∨ t = .tupT [] ∧ op = "TRAP")
    (hw : HasTyp (simEnv B) VarEnv.empty t w) : ResultShape (.case op w) := by
  rcases hm with ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩
  · obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 hw
    exact .inl ⟨l, hl ▸ rfl, fun x hx =>
      Typing.head_of_typed_val ⟨rfl, rfl, rfl⟩ (hasTypList_iff.1 hall x hx)⟩
  · exact .inr (.inl ⟨w, rfl⟩)
  · obtain ⟨vs, hvs, htup⟩ := hasTyp_tupT_iff.1 hw
    have e : vs = [] := hasTypTup_nil_iff.1 htup
    exact .inr (.inr (by rw [hvs, e]))

/-- **A typed `result` has one of three shapes.** -/
theorem resultShape_of_hasTyp {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {rv : Value}
    (ht : HasTyp (simEnv B) ρ (.varT "result" []) rv) : ResultShape rv := by
  have hl : localTyp? ρ "result" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 ht
  have htd' : td = _ := (Option.some.inj (ConfigOk.findTyp_result.symm.trans htd)).symm
  rw [htd'] at hi
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · have hσ : σ = VarEnv.empty := IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, hv, hc⟩ := hasTypDef_variantT_iff.1 hd
    obtain ⟨t, qs, prems, hmem, hw, -⟩ := hasTypCase_mem hc
    have hm' : t = .iterT (.varT "val" []) .list ∧ op = "_VALS" ∨
        op = "(REF.EXN_ADDR%)THROW_REF" ∨ t = .tupT [] ∧ op = "TRAP" := by
      simp only [List.mem_cons, TypCase.mk.injEq, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h
      · exact .inl ⟨h.2.1, h.1⟩
      · exact .inr (.inl h.1)
      · exact .inr (.inr ⟨h.2.1, h.1⟩)
    exact hv ▸ resultShape_of_case hm' (hσ ▸ hw)
  · exact absurd hrest not_hasTypInsts_nil

/-- `$lift_result(_VALS val*)` is `val*`. -/
theorem applies_lift_vals (B : Builtins) (l : List Value) :
    Applies (simEnv B) "lift_result" [.val (.case "_VALS" (.list l))] (.list l) := by
  obtain ⟨ps, t', q₁, q₂, q₃, hdef⟩ := Prims.liftResultDef B
  exact ⟨ps, t', _, hdef, Or.inl (tryClauses_hit (matchArgs_cons (matchArg_expA
    (matchExp_caseE (State.matchExp_iterVar (ρ₀ := VarEnv.empty) (l := l) rfl (by decide)
      rfl))) matchArgs_nil) premsHold_nil (Equiv.Execution.evalExp_valsPat (by decide) rfl))⟩

/-- `$lift_result((REF.EXN_ADDR a) THROW_REF)` is `(REF.EXN_ADDR a) THROW_REF`. -/
theorem applies_lift_throw (B : Builtins) (w : Value) :
    Applies (simEnv B) "lift_result" [.val (.case "(REF.EXN_ADDR%)THROW_REF" w)]
      (.list [.case "REF.EXN_ADDR" w, .case "THROW_REF" (.tuple [])]) := by
  obtain ⟨ps, t', q₁, q₂, q₃, hdef⟩ := Prims.liftResultDef B
  exact ⟨ps, t', _, hdef, Or.inl (tryClauses_skip_match (Prims.matchArgsUndef_case (by decide))
    (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl)))
      matchArgs_nil) premsHold_nil (evalExp_listE_iff.2 ⟨_, evalExps_cons
        (evalExp_case (evalExp_var rfl)) (evalExps_cons (evalExp_case
          (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil), rfl⟩)))⟩

/-- **`$lift_result` of a typed `result` is fine code**, whatever `B` answers elsewhere. -/
theorem elems_liftResult {B : Builtins} {ρ : VarEnv} (hρ : ValsOnly ρ) {r : IL.Id}
    {rv v : Value} (hr : ρ.findVal? r = some rv)
    (ht : HasTyp (simEnv B) ρ (.varT "result" []) rv)
    (he : EvalExp (simEnv B) ρ (.callE "lift_result" [.expA (.varE r)]) v) :
    ∃ xs, v = .list xs ∧ ∀ x ∈ xs, ElemOk (simEnv B) x := by
  rcases resultShape_of_hasTyp hρ ht with ⟨l, rfl, hl⟩ | ⟨w, rfl⟩ | rfl
  · refine ⟨l, EvalExp.unique he (evalExp_call_of_applies hρ hr (applies_lift_vals B l)),
      fun x hx => ?_⟩
    obtain ⟨op, w, hx', hop⟩ := hl x hx
    exact hx' ▸ elemOk_case (not_special_of_val hop)
  · refine ⟨_, EvalExp.unique he (evalExp_call_of_applies hρ hr (applies_lift_throw B w)),
      fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact elemOk_case (by decide)
    · exact (List.mem_singleton.1 hx) ▸ elemOk_case (by decide)
  · refine ⟨_, EvalExp.unique he
      (evalExp_call_of_applies hρ hr (Prims.applies_liftResult B .trap)), fun x hx => ?_⟩
    have hx' : x = .case "TRAP" (.tuple []) := by
      simpa [Result.toAdmin, adminsToV, Equiv.Execution.caseNilV] using hx
    exact hx' ▸ elemOk_case (by decide)

/-! ## The syntactic check -/

/-- `x : t*`. -/
def isListParam (t xs : IL.Id) : Param → Bool
  | .expP y (.iterT (.varT t' []) .list) => y == xs && t' == t
  | _ => false

/-- `r : result`. -/
def isResultParam (r : IL.Id) : Param → Bool
  | .expP y (.varT "result" []) => y == r
  | _ => false

/-- **The shape check** (fuel `k`; `true` checks code, `false` an element of code): code is a
concatenation of lists of fine elements, quantified `instr*` and `val*` iterations, and
`$lift_result(result)`; an element is a context around fine code or a constructor that is
neither `CALL_REF` nor a context. -/
def chk : Nat → List Param → Bool → Exp → Bool
  | 0, _, _, _ => false
  | k + 1, qs, true, .listE es => es.all (chk k qs false)
  | k + 1, qs, true, .catE a b => chk k qs true a && chk k qs true b
  | _ + 1, qs, true, .iterE (.varE x) (.mk .list [.mk x' (.varE xs)]) =>
      x == x' && x != "_" && qs.any (isListParam "instr" xs)
  | _ + 1, qs, true,
      .iterE (.subE (.varE x) (.varT "val" []) (.varT "instr" [])) (.mk .list [.mk x' (.varE xs)]) =>
      x == x' && x != "_" && qs.any (isListParam "val" xs)
  | _ + 1, qs, true, .callE "lift_result" [.expA (.varE r)] => qs.any (isResultParam r)
  | k + 1, qs, false, .caseE op (.tupE [_, _, b]) =>
      if ctxHeads.contains op then chk k qs true b else !specialHeads.contains op
  | _ + 1, _, false, .caseE op _ => !specialHeads.contains op
  | _, _, _, _ => false

/-- What `chk` guarantees of a value. -/
def ChkGood (env : Env) : Bool → Value → Prop
  | true, v => ∃ xs, v = .list xs ∧ ∀ x ∈ xs, ElemOk env x
  | false, v => ElemOk env v

/-- Each value of an evaluated list comes from one of its expressions. -/
theorem mem_of_evalExps {env : Env} {ρ : VarEnv} :
    ∀ {es : List Exp} {vs : List Value}, EvalExps env ρ es vs →
      ∀ x ∈ vs, ∃ e ∈ es, EvalExp env ρ e x
  | [], _, h, x, hx => by
    obtain rfl := evalExps_nil_iff.1 h
    cases hx
  | e :: es, _, h, x, hx => by
    obtain ⟨w, ws, hw, hws, rfl⟩ := evalExps_cons_iff.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨e, List.mem_cons_self .., hw⟩
    · obtain ⟨e', he', hx'⟩ := mem_of_evalExps hws x hx
      exact ⟨e', List.mem_cons_of_mem _ he', hx'⟩

/-- A parameter test, as a member. -/
theorem mem_of_any_isList {qs : List Param} {t xs : IL.Id}
    (h : qs.any (isListParam t xs) = true) : Param.expP xs (.iterT (.varT t []) .list) ∈ qs := by
  obtain ⟨q, hq, hz⟩ := List.any_eq_true.1 h
  unfold isListParam at hz
  split at hz
  · obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.1 hz
    obtain rfl := beq_iff_eq.1 h₁
    obtain rfl := beq_iff_eq.1 h₂
    exact hq
  · cases hz

/-- A parameter test, as a member. -/
theorem mem_of_any_isResult {qs : List Param} {r : IL.Id}
    (h : qs.any (isResultParam r) = true) : Param.expP r (.varT "result" []) ∈ qs := by
  obtain ⟨q, hq, hz⟩ := List.any_eq_true.1 h
  unfold isResultParam at hz
  split at hz
  · obtain rfl := beq_iff_eq.1 hz
    exact hq
  · cases hz

/-- The three conjuncts of an iteration test. -/
theorem iter_test {x x' : IL.Id} {b : Bool} (h : (x == x' && x != "_" && b) = true) :
    x' = x ∧ x ≠ "_" ∧ b = true := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.symm, h.1.2, h.2⟩

/-- The three components of an evaluated triple. -/
theorem evalExp_tup3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {w : Value}
    (h : EvalExp env ρ (.tupE [e₁, e₂, e₃]) w) :
    ∃ w₁ w₂ w₃, w = .tuple [w₁, w₂, w₃] ∧ EvalExp env ρ e₃ w₃ := by
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 h
  obtain ⟨w₁, vs₁, -, hvs₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨w₂, vs₂, -, hvs₂, rfl⟩ := evalExps_cons_iff.1 hvs₁
  obtain ⟨w₃, vs₃, h₃, hvs₃, rfl⟩ := evalExps_cons_iff.1 hvs₂
  obtain rfl := evalExps_nil_iff.1 hvs₃
  exact ⟨w₁, w₂, w₃, rfl, h₃⟩

section Sound

variable {B : Builtins} {hn : H → String} {ρ : VarEnv} {qs : List Param}

/-- A quantified `instr*` iteration is fine code. -/
theorem good_instrs (T : TypingFacts (simEnv B) hn) (hρ : ValsOnly ρ)
    (hq : QuantsOk (simEnv B) ρ qs) {x xs : IL.Id} (hx : x ≠ "_")
    (hm : Param.expP xs (.iterT (.varT "instr" []) .list) ∈ qs) {v : Value}
    (he : EvalExp (simEnv B) ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) v) :
    ChkGood (simEnv B) true v := by
  obtain ⟨l, fl, hl⟩ := quant_list hq hm
  obtain rfl := EvalExp.unique he (Equiv.Execution.evalExp_iterPat hx fl)
  obtain ⟨l', hl', hall⟩ := hasTyp_iterT_list_iff.1 hl
  rw [← Value.list.inj hl'] at hall
  exact ⟨l, rfl, fun y hy =>
    elemOk_of_typedV T (Typing.typedV_of_hasTyp hρ (hasTypList_iff.1 hall y hy))⟩

/-- A quantified `val*` iteration is fine code. -/
theorem good_vals (hρ : ValsOnly ρ) (hq : QuantsOk (simEnv B) ρ qs) {x xs : IL.Id}
    (hx : x ≠ "_") (hm : Param.expP xs (.iterT (.varT "val" []) .list) ∈ qs) {v : Value}
    (he : EvalExp (simEnv B) ρ
      (.iterE (.subE (.varE x) (.varT "val" []) (.varT "instr" [])) (.mk .list [.mk x (.varE xs)]))
      v) :
    ChkGood (simEnv B) true v := by
  obtain ⟨l, fl, hl⟩ := quant_list hq hm
  obtain rfl := EvalExp.unique he (Equiv.Execution.evalExp_valsPat hx fl)
  obtain ⟨l', hl', hall⟩ := hasTyp_iterT_list_iff.1 hl
  rw [← Value.list.inj hl'] at hall
  refine ⟨l, rfl, fun y hy => ?_⟩
  obtain ⟨op, w, rfl, hop⟩ := Typing.head_of_typed_val hρ (hasTypList_iff.1 hall y hy)
  exact elemOk_case (not_special_of_val hop)

/-- A context around fine code is fine. -/
theorem good_ctx {op : MixopS} (hop : op ∈ ctxHeads) {w₁ w₂ w₃ : Value}
    (h : ChkGood (simEnv B) true w₃) : ElemOk (simEnv B) (.case op (.tuple [w₁, w₂, w₃])) := by
  obtain ⟨xs, rfl, hxs⟩ := h
  simp only [ctxHeads, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl
  · exact elemOk_label hxs
  · exact elemOk_handler hxs
  · exact elemOk_frame hxs

/-- The induction hypothesis of `chk_sound`, at fuel `k`. -/
def ChkIH (B : Builtins) (ρ : VarEnv) (qs : List Param) (k : Nat) : Prop :=
  ∀ (m : Bool) (e : Exp) (v : Value), chk k qs m e = true → EvalExp (simEnv B) ρ e v →
    ChkGood (simEnv B) m v

/-- A list of fine elements is fine code. -/
theorem good_list {k : Nat} (ih : ChkIH B ρ qs k) {es : List Exp} {v : Value}
    (h : es.all (chk k qs false) = true) (he : EvalExp (simEnv B) ρ (.listE es) v) :
    ChkGood (simEnv B) true v := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_listE_iff.1 he
  refine ⟨vs, hv, fun x hx => ?_⟩
  obtain ⟨e', he', hx'⟩ := mem_of_evalExps hvs x hx
  exact ih false e' x (List.all_eq_true.1 h e' he') hx'

/-- A concatenation of fine code is fine code. -/
theorem good_cat {k : Nat} (ih : ChkIH B ρ qs k) {a b : Exp} {v : Value}
    (h : (chk k qs true a && chk k qs true b) = true)
    (he : EvalExp (simEnv B) ρ (.catE a b) v) : ChkGood (simEnv B) true v := by
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 he
  obtain ⟨xs₁, e₁, hx₁⟩ := ih true a v₁ ha h₁
  obtain ⟨xs₂, e₂, hx₂⟩ := ih true b v₂ hb h₂
  have hv : v = .list (xs₁ ++ xs₂) := by
    rw [e₁, e₂] at hc
    simpa [Value.cat?] using hc.symm
  exact ⟨_, hv, fun x hx => (List.mem_append.1 hx).elim (hx₁ x) (hx₂ x)⟩

/-- A triple-payload constructor that passes is fine. -/
theorem good_case3 {k : Nat} (ih : ChkIH B ρ qs k) {op : MixopS} {e₁ e₂ b : Exp} {v : Value}
    (h : (if ctxHeads.contains op then chk k qs true b else !specialHeads.contains op) = true)
    (he : EvalExp (simEnv B) ρ (.caseE op (.tupE [e₁, e₂, b])) v) :
    ChkGood (simEnv B) false v := by
  obtain ⟨w, hw, hv⟩ := evalExp_caseE_iff.1 he
  obtain ⟨w₁, w₂, w₃, hw', h₃⟩ := evalExp_tup3_inv hw
  rw [hv, hw']
  split at h
  · exact good_ctx (List.contains_iff_mem.1 ‹_›) (ih true b w₃ h h₃)
  · exact elemOk_case (by simpa using h)

/-- Another constructor that passes is fine. -/
theorem good_case {op : MixopS} {e : Exp} {v : Value} (h : (!specialHeads.contains op) = true)
    (he : EvalExp (simEnv B) ρ (.caseE op e) v) : ChkGood (simEnv B) false v := by
  obtain ⟨w, -, hv⟩ := evalExp_caseE_iff.1 he
  exact hv ▸ elemOk_case (by simpa using h)

/-- **`chk` is sound**: an expression that passes evaluates, under well-typed quantifiers, to
fine code (or a fine element). -/
theorem chk_sound (T : TypingFacts (simEnv B) hn) (hρ : ValsOnly ρ)
    (hq : QuantsOk (simEnv B) ρ qs) : ∀ k, ChkIH B ρ qs k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m e v h he
    unfold chk at h
    split at h
    · cases h
    · exact good_list (ih _ (Nat.lt_succ_self _)) h he
    · exact good_cat (ih _ (Nat.lt_succ_self _)) h he
    · exact good_instrs T hρ hq (iter_test h).2.1 (mem_of_any_isList (iter_test h).2.2)
        ((iter_test h).1 ▸ he)
    · exact good_vals hρ hq (iter_test h).2.1 (mem_of_any_isList (iter_test h).2.2)
        ((iter_test h).1 ▸ he)
    · obtain ⟨rv, fr, hr⟩ := quant_of hq (mem_of_any_isResult h)
      exact elems_liftResult hρ fr hr he
    · exact good_case3 (ih _ (Nat.lt_succ_self _)) h he
    · exact good_case h he
    · cases h

end Sound

/-! ## The 36 rules of `Step` -/

/-- The code `val^n (REF.FUNC_ADDR a) (CALL_REF yy)` of `call_ref-hostfunc-div`'s two sides. -/
def hostDivCode : Exp :=
  .catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
    (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")])

/-- `hostDivCode`, recognised. -/
def isHostDivCode : Exp → Bool
  | .catE (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
      (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))
    (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")]) => true
  | _ => false

theorem eq_of_isHostDivCode {e : Exp} (h : isHostDivCode e = true) : e = hostDivCode := by
  unfold isHostDivCode at h
  split at h
  · rfl
  · cases h

/-- **The check on one `Step` rule**: its right-hand code passes `chk`, or both sides have the
code of `call_ref-hostfunc-div`. -/
def succRule : Rule → Bool
  | .ruleD _ qs _ (.tupE [.caseE "%;%" (.tupE [_, lc]), .caseE "%;%" (.tupE [_, rc])]) _ =>
      chk 8 qs true rc || (isHostDivCode lc && isHostDivCode rc)
  | _ => false

/-- A rule that passes, unpacked. -/
theorem succRule_inv {r : Rule} (h : succRule r = true) :
    ∃ nm qs op S lc S' rc prems,
      r = .ruleD nm qs op (.tupE [.caseE "%;%" (.tupE [S, lc]), .caseE "%;%" (.tupE [S', rc])])
        prems ∧ (chk 8 qs true rc || (isHostDivCode lc && isHostDivCode rc)) = true := by
  unfold succRule at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, _, rfl, h⟩
  · cases h

set_option maxRecDepth 100000 in
/-- **Every rule of `Step` passes the check**, in every `simEnv B`. -/
theorem stepRules_checked (B : Builtins) : ∃ t rules,
    (simEnv B).findRel? "Step" = some ([], "%~>%", t, rules) ∧ rules.all succRule = true :=
  ⟨_, _, rfl, rfl⟩

/-- The code of a configuration's image, read off a `z; instr*` conclusion. -/
theorem code_of_cfg {env : Env} {ρ : VarEnv} {hn : H → String} {S c : Exp} {d : Config H}
    (h : EvalExp env ρ (.caseE "%;%" (.tupE [S, c])) (configV hn d)) :
    EvalExp env ρ c (.list (adminsToV d.code)) := by
  obtain ⟨w, hw, hwe⟩ := evalExp_caseE_iff.1 h
  rw [Bwd.configV_eq] at hwe
  obtain ⟨-, rfl⟩ := Value.case.inj hwe
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 hw
  obtain ⟨x, xs, -, hxs, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨y, ys, hy, hys, rfl⟩ := evalExps_cons_iff.1 hxs
  obtain rfl := evalExps_nil_iff.1 hys
  obtain ⟨-, hyv⟩ := List.cons.inj (Value.tuple.inj hv)
  obtain ⟨rfl, -⟩ := List.cons.inj hyv
  exact hy

/-- Both codes of a `Step` conclusion between two configurations' images. -/
theorem codes_of_pair {env : Env} {ρ : VarEnv} {hn : H → String} {S lc S' rc : Exp}
    {d d' : Config H}
    (h : EvalExp env ρ (.tupE [.caseE "%;%" (.tupE [S, lc]), .caseE "%;%" (.tupE [S', rc])])
      (.tuple [configV hn d, configV hn d'])) :
    EvalExp env ρ lc (.list (adminsToV d.code)) ∧ EvalExp env ρ rc (.list (adminsToV d'.code)) := by
  obtain ⟨vs, hvs, hv⟩ := evalExp_tupE_iff.1 h
  obtain ⟨x, xs, hx, hxs, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨y, ys, hy, hys, rfl⟩ := evalExps_cons_iff.1 hxs
  obtain rfl := evalExps_nil_iff.1 hys
  obtain ⟨rfl, hyv⟩ := List.cons.inj (Value.tuple.inj hv)
  obtain ⟨rfl, -⟩ := List.cons.inj hyv
  exact ⟨code_of_cfg hx, code_of_cfg hy⟩

/-- **One rule that passes the check**, at a typed source: the successor's `CALL_REF`s are
typed. -/
theorem calls_of_rule {B : Builtins} {hn : H → String} {σ : List (IL.Id × Value)}
    {qs : List Param} {S lc S' rc : Exp} {d d' : Config H} (hd : Typed (simEnv B) hn d)
    (hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp (simEnv B) (VarEnv.empty.bindVals σ)
      (.tupE [.caseE "%;%" (.tupE [S, lc]), .caseE "%;%" (.tupE [S', rc])])
      (.tuple [configV hn d, configV hn d']))
    (hg : (chk 8 qs true rc || (isHostDivCode lc && isHostDivCode rc)) = true) :
    CodeCallsTyped (simEnv B) d'.code := by
  have T := Typing.typingFacts_simEnv B hn
  obtain ⟨hl, hr⟩ := codes_of_pair he
  rcases Bool.or_eq_true_iff.1 hg with hc | hc
  · obtain ⟨xs, hxs, hok⟩ := chk_sound T (IntNumeric.valsOnly_bindVals _) hq 8 true _ _ hc hr
    exact codeCallsTyped_of_elems ((Value.list.inj hxs) ▸ hok)
  · obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.1 hc
    have e : adminsToV d'.code = adminsToV d.code := Value.list.inj (EvalExp.unique
      (eq_of_isHostDivCode h₂ ▸ hr) (eq_of_isHostDivCode h₁ ▸ hl))
    exact codeCallsTyped_of_typedV T (e ▸ ((T.config d).1 hd).2)

/-- **The `CALL_REF`s of SpecTec's successors of typed witnesses are typed**, for every `B` and
encoding: `Round5.Multi.SuccCallsTyped` holds. -/
theorem succCallsTyped (B : Builtins) (hn : H → String) : SuccCallsTyped B hn := by
  intro d d' hd hs
  cases hs with
  | rule hrel hrule hps hq he _ =>
    obtain ⟨t', rules', hrel', hall⟩ := stepRules_checked B
    rw [hrel'] at hrel
    obtain ⟨rfl, -, -, rfl⟩ : [] = _ ∧ _ ∧ _ ∧ rules' = _ := by
      simpa only [Option.some.injEq, Prod.mk.injEq] using hrel
    obtain rfl : _ = VarEnv.empty := (Option.some.inj hps).symm
    obtain ⟨_, _, _, S, lc, S', rc, _, hr, hg⟩ :=
      succRule_inv (List.all_eq_true.1 hall _ (List.mem_of_getElem? hrule))
    cases hr
    exact calls_of_rule hd hq he hg

/-- **`SuccTyped` holds**, for every `B` and encoding. -/
theorem succTyped (B : Builtins) (hn : H → String) : SuccTyped B hn :=
  succTyped_of_calls (succCallsTyped B hn)

end Silmaril.Wasm.SpecTec.Sim.Round5.Multi
