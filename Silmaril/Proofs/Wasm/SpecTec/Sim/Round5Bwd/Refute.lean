module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5Bwd.AggOob

/-!
# Round 5: `RemainingV` is false (`array.fill-zero` at a dangling array)

`Step_read/array.fill-zero` (rule 84) has the premises `otherwise` and `n = 0`. Its `otherwise`
reads "no earlier rule fires": `array.fill-null` (82) needs a null reference and
`array.fill-oob` (83) evaluates `|$arrayinst(z)[a].FIELDS|`, which has no value when the array
`a` does not exist. So at a dangling `REF.ARRAY_ADDR 0`, on the empty store, rule 84 fires.
Core's `arrayFillZero` needs `s.arrays[a]?`, and nothing else steps (`step_stuck`).

`Round4Read.ReadValid` (store bounds and index resolution) does not exclude dangling references,
and `Typed` is syntactic, so the configuration satisfies both. Hence
`Round4Read.RemainingV` fails for every `B` (`not_remainingV`), `Round4Int.Parts` is
unsatisfiable (`not_parts`), and the reduction `Round4Int.wholeStepValid_of_parts` is vacuous.
Core validity rules the configuration out (`ConfigOk` types `REF.ARRAY_ADDR a` only for an
allocated `a`), so the frozen target is not refuted.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Bwd

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.ExecRead (arrayFillOobRule)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Round4Read (ReadValid RemainingV)

variable {H : Type}

/-- The administrative instructions of the counterexample. -/
def FillOk : Admin → Bool
  | .plain (.intConst ..) => true
  | .ref (.array _) => true
  | .plain (.arrayFill _) => true
  | _ => false

set_option linter.unusedSimpArgs false in
/-- **Core is stuck** on code made of integer constants, array references and `array.fill`
when the store has no array. -/
theorem step_stuck {P : Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') (ha : c.store.arrays = []) (hall : c.code.all FillOk = true) :
    False := by
  induction h with
  | parametric h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | numeric h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | vector h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | «variable» h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | table h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | memory h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | reference h => cases h <;> simp [List.all_append, FillOk, vals] at hall
  | aggregate h => cases h <;> simp_all [List.all_append, FillOk, vals]
  | ctxtInstrs _ _ ih =>
    simp only [List.all_append, Bool.and_eq_true] at hall
    exact ih ha hall.1.2
  | _ => simp [List.all_append, FillOk, vals] at hall

/-- The encoding of the empty host type. -/
def hnE : Empty → String := fun e => e.elim

/-- Type index `0`. -/
def type0 : TypeIdx := ⟨0⟩

/-- `i32.const 0`. -/
def zero32 : Val := .num ⟨.int .i32, 0⟩

/-- `(ref.array 0) (i32.const 0) (i32.const 0) (i32.const 0) array.fill 0` on the empty store,
with the empty module instance: the array `0` does not exist. -/
def fillConfig : Config Empty :=
  ⟨{}, ⟨[], {}⟩, [arrRef 0, constI32 0, zero32.toAdmin, constI32 0, .plain (.arrayFill type0)]⟩

/-- `array.fill 0` is a typed `instr`. -/
theorem typedV_arrayFill (B : Builtins) :
    TypedV (simEnv B) (.varT "instr" []) (instrToV (.arrayFill type0)) :=
  FwdMem.typedV_instrCase rfl rfl
    (Typing.typedV_alias Typing.findTyp_typeidx (Typing.typedV_idx _) _ ⟨rfl, rfl, rfl⟩)

/-- **The counterexample is `Typed`**, in every `simEnv B`. -/
theorem typed_fillConfig (B : Builtins) : Typed (simEnv B) hnE fillConfig := by
  have T := Typing.typingFacts_simEnv B hnE
  obtain ⟨hst, hv⟩ := (T.config _).1 (Typing.typed_vals (B := B) hnE []
    [.ref (.array 0), zero32, zero32, zero32])
  refine (T.config _).2 ⟨hst, ?_⟩
  show TypedV (simEnv B) instrsT (.list (adminsToV (vals [.ref (.array 0), zero32, zero32,
    zero32] ++ [.plain (.arrayFill type0)])))
  rw [adminsToV_append]
  exact (T.append _ _).2 ⟨hv, typedV_list_single.2 (typedV_arrayFill B)⟩

/-- **The counterexample is `ReadValid`**: the empty store is bounded, and `array.fill` names no
table, memory or segment index. -/
theorem readValid_fillConfig : ReadValid fillConfig :=
  ⟨Integrate.storeOk_empty, by
    simp [fillConfig, zero32, constI32, Val.i32, Val.toAdmin, Round4Read.codeIdx,
      Round4Read.adminIdx, Round4Read.Instr.IdxOk]⟩

/-- **Core is stuck on it.** -/
theorem not_step_fillConfig {P : Profile} {host : HostSemantics Empty} {c' : Config Empty} :
    ¬ Step P host fillConfig c' := fun h =>
  step_stuck h rfl (by decide)

/-- A rule instance whose premises hold under `otherwise`, at a rule the relation lists, fires. -/
theorem fires_of_ruleAt {env : Env} {x : IL.Id} {k : Nat} {nm : IL.Id} {qs : List Param}
    {e : Exp} {prems : List Prem} (h : HasRuleAt env x "%~>%" k (.ruleD nm qs "%~>%" e prems))
    (σ : List (IL.Id × Value)) {v : Value} (hq : QuantsOk env (VarEnv.empty.bindVals σ) qs)
    (he : EvalExp env (VarEnv.empty.bindVals σ) e v)
    (hp : ∀ pr ∈ prems, DPrem env (otherwise env) (otherwise env x [] k v)
      (VarEnv.empty.bindVals σ) pr) :
    Fires env x k v := by
  obtain ⟨ps, t, rules, hrel, rfl, hk⟩ := h
  exact ⟨t, rules, _, hrel, hk, ⟨rfl, VarEnv.empty, σ, rfl, hq, he,
    fun pr hpr => dprem_toPremW (hp pr hpr)⟩⟩

/-- **`array.fill-oob` does not fire at the dangling array**: its premise evaluates
`|$arrayinst(z)[0].FIELDS|` on the empty store. -/
theorem not_arrayFillOob_fill (B : Builtins) {D : Interp} {els : Prop} {c : Value} :
    ¬ RuleBody (simEnv B) D els [] [] "%~>%" arrayFillOobRule
      (.tuple [configV hnE fillConfig, c]) := by
  intro hb
  obtain ⟨σ, -, he, hp⟩ := ruleBody_scope hb
  obtain ⟨hz, hl⟩ := RefsGC.cfgz_inv (RefsGC.lhs_of_concl he)
  obtain ⟨ha, -, -⟩ := RefsGC.binds_arrayFill hl
  obtain ⟨-, v₂, -, e₂, -⟩ := evalExp_cmpE_iff.1 (RefsGC.premW_if (hp _ List.mem_cons_self))
  obtain ⟨ai, hai, -⟩ := arrayLen_inv B (evalExp_varE_iff.1 hz) (evalExp_varE_iff.1 ha) e₂
  simp [fillConfig] at hai

/-- **No rule before `array.fill-zero` fires at the dangling array**: `array.fill-null` needs a
null reference, `array.fill-oob` a live array, and the tag table rules out the rest. -/
theorem otherwise_fillConfig (B : Builtins) :
    otherwise (simEnv B) "Step_read" [] 84 (.tuple [configV hnE fillConfig, .list (adminsToV [])]) :=
  RefsGC.otherwise_of_ruleAt (State.hasReadRules_simEnv B).arrayFillZero
    (RefsGC.readTable_simEnv B) (i := 84) (a := configV hnE fillConfig)
    (b := .list (adminsToV [])) (by decide) (exc := [82, 83])
    (RefsGC.lhsIn_arrayFill (hn := hnE) (s := {}) (f := ⟨[], {}⟩) (a := 0) (i := 0) (n := 0)
      (v := zero32) (x := type0)) (by decide) (by
      intro j hj _ r' hr' w hw
      obtain ⟨c, rfl⟩ := RefsGC.sameLhs_inv hw
      rcases (by simpa using hj : j = 82 ∨ j = 83) with rfl | rfl
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).arrayFillNull hr']
        exact RefsGC.not_arrayFillNull (hn := hnE) (s := {}) (f := ⟨[], {}⟩) (a := 0)
      · rw [RefsGC.relRules_of_ruleAt (State.hasReadRules_simEnv B).arrayFillOob hr']
        exact not_arrayFillOob_fill B)

/-- **`array.fill-zero` fires at the dangling array**, to the empty sequence. -/
theorem fires_fillConfig (B : Builtins) :
    Fires (simEnv B) "Step_read" 84 (.tuple [configV hnE fillConfig, .list (adminsToV [])]) := by
  have T : TypingFacts (simEnv B) hnE := Typing.typingFacts_simEnv B hnE
  have R : RefsGC.RTyping (simEnv B) := Typing.rTyping_simEnv B
  have hc : Typed (simEnv B) hnE fillConfig := typed_fillConfig B
  let σ : List (IL.Id × Value) := [("z", stateV hnE {} ⟨[], {}⟩), ("a", .num (.natN 0)),
    ("i", pctV (0 : BitVec 32).toNat), ("val", adminToV zero32.toAdmin), ("n", .num (.natN 0)),
    ("x", Encode.toValue type0)]
  have hρ : ValsOnly (VarEnv.empty.bindVals σ) := ⟨rfl, rfl, rfl⟩
  have hv : TypedV (simEnv B) State.valT (adminToV zero32.toAdmin) :=
    RefsGC.typed_toAdmin R zero32 (RefsGC.typed_head T (RefsGC.typed_tail T (RefsGC.typed_tail T
      ((T.config _).1 hc).2)))
  exact fires_of_ruleAt (State.hasReadRules_simEnv B).arrayFillZero σ
    (QuantsOk.cons rfl (((T.config _).1 hc).1 _ hρ) (QuantsOk.cons rfl (R.addr _ _ hρ)
      (QuantsOk.cons rfl (R.i32 _ _ hρ) (QuantsOk.cons rfl (hv _ hρ)
      (QuantsOk.cons rfl (R.nat _ _ hρ) (QuantsOk.cons rfl (R.idx _ type0.value.isLt _ hρ)
        QuantsOk.nil)))))) (by eval_tac) (prems_two (.elsePr (otherwise_fillConfig B))
      (.ifPr (RefsGC.evalExp_eq_true (by eval_tac) RefsGC.evalExp_num')))

/-- **`Round4Read.RemainingV` is false**, for every `B`, at the empty host type, the empty host
and every profile: its `read` field fails at rule 84 on `fillConfig`. -/
theorem not_remainingV (B : Builtins) (P : Profile) :
    ¬ RemainingV (simEnv B) hnE P Integrate.emptyHost := fun R => by
  obtain ⟨is', -, -, -, hs⟩ := R.read 84 (by decide) (by decide) (by decide) fillConfig _
    readValid_fillConfig (typed_fillConfig B) (fires_fillConfig B)
  exact not_step_fillConfig hs

/-- **`Round4Int.Parts` is unsatisfiable** at the empty host: its `rem` field is
`RemainingV`. -/
theorem not_parts (P : Profile) : ¬ Round4Int.Parts hnE P Integrate.emptyHost := fun Pa =>
  not_remainingV _ P Pa.rem

/-- **The hypothesis of `Round4Int.wholeStepValid_of_parts` is false**, so that reduction is
vacuous. -/
theorem not_parts_hyp :
    ¬ (∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : Numerics.RelaxedChoice),
        Round4Int.Parts hn (Profile.spec nd r) host) := fun h =>
  not_parts _ (h Empty hnE (fun e => e.elim) Integrate.emptyHost Integrate.hostFinite_emptyHost
    false {})

end Silmaril.Wasm.SpecTec.Sim.Round5.Bwd
