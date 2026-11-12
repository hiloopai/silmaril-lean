module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Undef

/-!
# The concrete `B`: `$unrolldt` and SpecTec's `Expand`

`Expand: deftype ~~ comptype -- if $unrolldt(deftype) = SUB final? typeuse* comptype`.
`$unrolldt(_DEF rectype i) = subtype*[i] -- if $unrollrt(rectype) = REC subtype*` binds `subtype*`
only in its `if` premise, and so does `$unrollrt`'s clause; under the evaluator both definitely
fail, `$unrollrt` has no builtin, and `$unrolldt` falls back to `B`, which answers with the image of
Core's `unrolldt` (`applies_unrolldt`). So `Expand` holds of the images exactly where Core's does
(`dderives_expand`, `dderives_expand_inv`), given that the images of closed types are typed
(`TypeTyping`, a typing fact).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

variable {prof : Silmaril.Wasm.Numerics.Profile}

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef
  applies_iff_callDef)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj tyV_list HasRuleAt)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## `tyInv` -/

/-- `tyInv` inverts `tyV`. -/
theorem tyInv_tyV {k : TKind} (t : Ty k) : tyInv k (tyV t) = some t := by
  classical
  have hex : ∃ t' : Ty k, tyV t' = tyV t := ⟨t, rfl⟩
  rw [tyInv]
  split
  · rename_i h
    exact congrArg some (tyV_inj _ _ h.choose_spec)
  · contradiction

/-- `tyInv` answers only on images. -/
theorem tyInv_eq_some {k : TKind} {v : Value} {t : Ty k} (h : tyInv k v = some t) : tyV t = v := by
  classical
  unfold tyInv at h
  split at h
  · rename_i hex
    cases h
    exact hex.choose_spec
  · cases h

/-! ## What `B` answers -/

/-- `B` answers `$unrolldt` by `unrolldtCall`. -/
theorem call_unrolldt (hn : H → String) (host : HostSemantics H) (v : Value) :
    (builtins prof hn host).call "unrolldt" [.val v] = unrolldtCall v := by
  simp [builtins, call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `B` has no entry for `$unrollrt`. -/
theorem call_unrollrt (hn : H → String) (host : HostSemantics H) (v : Value) :
    (builtins prof hn host).call "unrollrt" [.val v] = none := by
  simp [builtins, call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- On an image, `unrolldtCall` is Core's `unrolldt`. -/
theorem unrolldtCall_tyV (d : DefType) : unrolldtCall (tyV d) = (unrolldt d).map tyV := by
  unfold unrolldtCall
  rw [tyInv_tyV]
  cases h : unrolldt d <;> simp [h]

/-! ## The clauses -/

/-- `$unrollrt`'s single clause. -/
def unrollrtPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.varE "rectype") (.caseE "REC" (.caseE "%" (.tupE
    [.iterE (.varE "subtype") (.mk (.listN (.varE "n") none) [.mk "subtype" (.varE "subtype*")])]))))

/-- `$unrolldt`'s single clause's premise. -/
def unrolldtPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.callE "unrollrt" [.expA (.varE "rectype")]) (.caseE "REC"
    (.caseE "%" (.tupE [.iterE (.varE "subtype") (.mk .list [.mk "subtype" (.varE "subtype*")])]))))

/-- The two definitions, as the script has them. -/
structure UnrollDefs (env : Env) : Prop where
  unrollrt : ∃ ps t q body, env.findDef? "unrollrt" =
    some (ps, t, [.defD q [.expA (.varE "rectype")] body [unrollrtPrem]])
  unrolldt : ∃ ps t q body, env.findDef? "unrolldt" =
    some (ps, t, [.defD q [.expA (.caseE "_DEF" (.tupE [.varE "rectype", .varE "i"]))] body
      [unrolldtPrem]])

set_option maxRecDepth 100000 in
/-- `simEnv B` has them. -/
theorem unrollDefs_simEnv (B : Builtins) : UnrollDefs (simEnv B) :=
  ⟨⟨_, _, _, _, rfl⟩, ⟨_, _, _, _, rfl⟩⟩

/-- `$unrollrt`'s clause definitely fails on every argument. -/
theorem unrollrt_undef {env : Env} (D : UnrollDefs env) (R : Value) :
    ∃ ps t cs, env.findDef? "unrollrt" = some (ps, t, cs) ∧ TryClausesUndef env cs [.val R] := by
  obtain ⟨ps, t, q, body, hd⟩ := D.unrollrt
  refine ⟨ps, t, _, hd, IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil) ?_
    IntNumeric.tryClausesUndef_nil⟩
  exact premsUndef_if (evalExpUndef_cmpR (evalExp_var rfl) (evalExpUndef_case (evalExpUndef_case
    (evalExpUndef_tup (pre := []) (post := []) evalExps_nil
      (evalExpUndef_iterListN (evalExpUndef_var rfl))))))

/-- `_DEF rectype i` matches every image of a defined type. -/
theorem matchArgs_def (g : CRecType) (i : Nat) {env : Env} :
    MatchArgs env VarEnv.empty [.expA (.caseE "_DEF" (.tupE [.varE "rectype", .varE "i"]))]
      [.val (tyV (Ty.defn g i : DefType))]
      ((VarEnv.empty.bindVal "rectype" (tyV g)).bindVal "i" (Silmaril.SpecTec.Equiv.natV i)) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2 ⟨_, rfl,
    Equiv.Execution.matchExps_two_iff.2 ⟨_, _, _, rfl, matchExp_varE rfl, matchExp_varE rfl⟩⟩)))
    matchArgs_nil

/-- **`$unrolldt` on an image is `B`'s answer**: the image of Core's `unrolldt`. -/
theorem applies_unrolldt (hn : H → String) (host : HostSemantics H) (d : DefType) (w : Value) :
    Applies (simEnv (builtins prof hn host)) "unrolldt" [.val (tyV d)] w ↔
      (unrolldt d).map tyV = some w := by
  have D := unrollDefs_simEnv (builtins prof hn host)
  obtain ⟨g, i, rfl⟩ : ∃ g i, d = Ty.defn g i := by cases d; exact ⟨_, _, rfl⟩
  obtain ⟨ps, t, q, body, hd⟩ := D.unrolldt
  obtain ⟨ps', t', cs', hd', hu'⟩ := unrollrt_undef D (tyV g)
  have hu : TryClausesUndef (simEnv (builtins prof hn host)) [.defD q [.expA (.caseE "_DEF"
      (.tupE [.varE "rectype", .varE "i"]))] body [unrolldtPrem]] [.val (tyV (Ty.defn g i))] :=
    IntNumeric.tryClausesUndef_skip_prem (matchArgs_def g i) (premsUndef_if (evalExpUndef_cmpL
      (evalExpUndef_call rfl (Equiv.evalArgs_cons (evalExp_var rfl) Equiv.evalArgs_nil) hd' hu'
        (call_unrollrt hn host _)))) IntNumeric.tryClausesUndef_nil
  have hb : (simEnv (builtins prof hn host)).builtins.call "unrolldt" [.val (tyV (Ty.defn g i))] =
      (unrolldt (Ty.defn g i)).map tyV := by
    rw [simEnv, Env.builtins_withBuiltins, call_unrolldt, unrolldtCall_tyV]
  constructor
  · rintro ⟨ps₁, t₁, cs₁, hf, hc⟩
    rw [hd] at hf
    cases hf
    rcases hc with hc | ⟨_, hc⟩
    · exact absurd hu (fun h => not_tryClauses_and_undef hc h)
    · rw [← hb, hc]
  · intro h
    exact ⟨ps, t, _, hd, Or.inr ⟨hu, hb.trans h⟩⟩

/-! ## `Expand` -/

/-- The premise of `Expand`: `$unrolldt(deftype) = SUB final? typeuse* comptype`. -/
def expandPrem : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.callE "unrolldt" [.expA (.varE "deftype")])
    (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
      .iterE (.varE "typeuse") (.mk .list [.mk "typeuse" (.varE "typeuse*")]),
      .varE "comptype"])))

/-- The single rule of `Expand`. -/
def expandRule : Rule :=
  .ruleD "" [.expP "deftype" (.varT "deftype" []), .expP "comptype" (.varT "comptype" []),
      .expP "final?" (.iterT (.varT "final" []) .opt),
      .expP "typeuse*" (.iterT (.varT "typeuse" []) .list)] "%~~%"
    (.tupE [.varE "deftype", .varE "comptype"]) [expandPrem]

set_option maxRecDepth 100000 in
/-- `Expand` has exactly that rule. -/
theorem findRel_expand (B : Builtins) :
    ∃ t, (simEnv B).findRel? "Expand" = some ([], "%~~%", t, [expandRule]) :=
  ⟨_, rfl⟩

/-- The rule, as a `HasRuleAt` fact. -/
theorem hasRuleAt_expand (B : Builtins) : HasRuleAt (simEnv B) "Expand" "%~~%" 0 expandRule := by
  obtain ⟨t, h⟩ := findRel_expand B
  exact ⟨_, _, _, h, rfl, rfl⟩

/-- The assignment of `Expand`'s variables for `unrolldt d = SUB fin sups ct`. -/
def expandσ (d : DefType) (fin : Bool) (sups : Ty (.list .use)) (ct : CCompType) :
    List (IL.Id × Value) :=
  [("deftype", tyV d), ("comptype", tyV ct),
    ("final?", Silmaril.SpecTec.Equiv.Validation.finalV fin), ("typeuse*", tyV sups)]

/-- `SUB final? typeuse* comptype`, evaluated under `expandσ`. -/
theorem evalExp_expandSub {env : Env} (d : DefType) (fin : Bool) (sups : Ty (.list .use))
    (ct : CCompType) :
    EvalExp env (VarEnv.empty.bindVals (expandσ d fin sups ct))
      (.caseE "SUB" (.tupE [.iterE (.varE "final") (.mk .opt [.mk "final" (.varE "final?")]),
        .iterE (.varE "typeuse") (.mk .list [.mk "typeuse" (.varE "typeuse*")]),
        .varE "comptype"])) (tyV (Ty.sub fin sups ct)) := by
  have hf := IntNumeric.evalExp_iterOpt (env := env)
    (ρ := VarEnv.empty.bindVals (expandσ d fin sups ct)) (b := .varE "final") (x := "final") (y := "final?")
    (o := if fin then some (.case "FINAL" (.tuple [])) else none)
    (v := if fin then some (.case "FINAL" (.tuple [])) else none) rfl
    (fun w hw => ⟨w, hw, evalExp_var rfl⟩) id
  have hu := evalExp_iterMap (env := env) (ρ := VarEnv.empty.bindVals (expandσ d fin sups ct))
    (b := .varE "typeuse") (x := "typeuse") (y := "typeuse*") (ws := sups.toList.map tyV)
    (g := fun w => w) (by rw [← tyV_list]; rfl) (fun w _ => evalExp_var rfl)
  rw [List.map_id', ← tyV_list] at hu
  exact evalExp_case (evalExp_tup3 hf hu (evalExp_var rfl))

/-- **SpecTec's `Expand` holds of the images of Core's `Expand`**, for the concrete `B`, given the
typing of the images (`TypeTyping`). -/
theorem dderives_expand {hn : H → String} {host : HostSemantics H}
    (T : TypeTyping (simEnv (builtins prof hn host))) (O : ElseI) {d : DefType} {ct : CCompType}
    (h : Expand d ct) :
    DDerives (simEnv (builtins prof hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, tyV ct]) := by
  obtain ⟨hu⟩ := h
  rename_i fin sups
  have hρ : ValsOnly (VarEnv.empty.bindVals (expandσ d fin sups ct)) := ⟨rfl, rfl, rfl⟩
  refine dderives_of_ruleAt (hasRuleAt_expand _) (expandσ d fin sups ct)
    (QuantsOk.cons rfl (T.deftype d _ hρ) (QuantsOk.cons rfl (T.comptype ct _ hρ)
      (QuantsOk.cons rfl (T.final fin _ hρ) (QuantsOk.cons rfl (T.typeuses sups _ hρ)
        QuantsOk.nil))))
    (evalExp_tup2 (evalExp_var rfl) (evalExp_var rfl)) ?_
  intro pr hpr
  simp only [List.mem_singleton] at hpr
  subst hpr
  refine .ifPr (evalExp_cmpE_iff.2 ⟨_, _, evalExp_callArgs rfl
    (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))
    ((applies_unrolldt hn host d _).2 (by rw [hu]; rfl)), evalExp_expandSub d fin sups ct,
    by simp [cmpValues]⟩)

/-- The third component of an evaluated `SUB` injection. -/
theorem evalExp_sub3_inv {env : Env} {ρ : VarEnv} {e₁ e₂ e₃ : Exp} {v : Value}
    (h : EvalExp env ρ (.caseE "SUB" (.tupE [e₁, e₂, e₃])) v) :
    ∃ a b c, EvalExp env ρ e₃ c ∧ v = .case "SUB" (.tuple [a, b, c]) := by
  obtain ⟨x, hx, rfl⟩ := evalExp_caseE_iff.1 h
  obtain ⟨vs, hvs, rfl⟩ := evalExp_tupE_iff.1 hx
  obtain ⟨a, vs₁, -, hvs₁, rfl⟩ := evalExps_cons_iff.1 hvs
  obtain ⟨b, vs₂, -, hvs₂, rfl⟩ := evalExps_cons_iff.1 hvs₁
  obtain ⟨c, vs₃, hc, hvs₃, rfl⟩ := evalExps_cons_iff.1 hvs₂
  obtain rfl := evalExps_nil_iff.1 hvs₃
  exact ⟨a, b, c, hc, rfl⟩

/-- The comptype of an unrolled subtype, read off its image. -/
theorem expand_of_sub {d : DefType} {st : CSubType} {a b c : Value} (hst : unrolldt d = some st)
    (heq : tyV st = .case "SUB" (.tuple [a, b, c])) : ∃ ct, Expand d ct ∧ c = tyV ct :=
  match st, hst, heq with
  | .sub _ _ ct, hst, heq => by
    simp only [tyV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, and_true,
      true_and] at heq
    exact ⟨ct, .mk hst, heq.2.2.symm⟩

/-- A derivation of `Expand` is an instance of its one rule. -/
theorem expand_inst {hn : H → String} {host : HostSemantics H} {O : ElseI} {v : Value}
    (h : DDerives (simEnv (builtins prof hn host)) O "Expand" "%~~%" [] v) :
    ∃ ρ₀ σ, bindParams VarEnv.empty [] [] = some ρ₀ ∧
      EvalExp (simEnv (builtins prof hn host)) (ρ₀.bindVals σ)
        (.tupE [.varE "deftype", .varE "comptype"]) v ∧
      PremW (simEnv (builtins prof hn host)) (DDerives (simEnv (builtins prof hn host)) O)
        (O "Expand" [] 0 v) (ρ₀.bindVals σ) expandPrem := by
  obtain ⟨ps, t, rules, i, r, hrel, hrule, hb⟩ := dderives_iff.1 h
  obtain ⟨t', hrel'⟩ := findRel_expand (builtins prof hn host)
  rw [hrel'] at hrel
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hrel
  obtain ⟨rfl, -, rfl⟩ := hrel
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ r = expandRule := by
    rcases i with _ | i <;> simp at hrule
    exact ⟨rfl, hrule.symm⟩
  obtain ⟨-, ρ₀, σ, hb₀, -, he, hp⟩ := hb
  exact ⟨ρ₀, σ, hb₀, he, hp _ (List.mem_singleton_self _)⟩

/-- **…and conversely**: SpecTec's `Expand` of an image is the image of Core's `Expand`, for the
concrete `B` and under any reading of `otherwise`. -/
theorem expand_of_dderives {hn : H → String} {host : HostSemantics H} {O : ElseI} {d : DefType}
    {w : Value}
    (h : DDerives (simEnv (builtins prof hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, w])) :
    ∃ ct, Expand d ct ∧ w = tyV ct := by
  obtain ⟨ρ₀, σ, hb₀, he, hp⟩ := expand_inst h
  obtain ⟨_, _, h₁, h₂, hw⟩ := State.evalExp_tup2_inv he
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hw
  have hif := RefsGC.premW_if hp
  obtain ⟨v₁, v₂, hv₁, hv₂, -⟩ := evalExp_cmpE_iff.1 hif
  have happ : Applies (simEnv (builtins prof hn host)) "unrolldt" [.val (tyV d)] v₁ :=
    (applies_iff_callDef (RefsGC.findDef_bindVals_of_bindParams hb₀)
      (Equiv.evalArgs_cons h₁ (evalArgs_nil _ _))).2 (evalExp_callE_iff.1 hv₁)
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 ((applies_unrolldt hn host d v₁).1 happ)
  obtain ⟨a, b, c, hc, rfl⟩ := evalExp_sub3_inv hv₂
  obtain rfl := EvalExp.unique hc h₂
  exact expand_of_sub hst (RefsGC.eq_of_evalExp_eq hif hv₁ hv₂)

end Silmaril.Wasm.SpecTec.Sim.Prims
