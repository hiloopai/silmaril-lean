module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Blocktype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Store
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Misc
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.RefOkB.Derive

/-!
# Round 6: the functions the validation group calls, on the concrete `B`

* `not_applies_closDeftype`: `$clos_deftype(C, dt)` binds `dt'*` only in its `if` premise, so its
  clause definitely fails and `B` has no entry: **it never has a value**. So `Deftype_sub/refl`
  never fires under `DDerivesB` (`Heaptype_sub/refl` covers equal types).
* `applies_unrollht_rec`: `$unrollht_(C, REC k)` is `C.RECS[k]`, in a context `ctxR L`;
* `applies_unrollht_def`: `$unrollht_(C, dt)` at the image of a defined type is the image of
  Core's `unrolldt`;
* `applies_before_rec`: `$before(REC k, j)` is `k < j`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.TyElim

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef
  tryClauses_unique)
open Silmaril.SpecTec.Equiv.ExecBuiltins (matchExp_caseE_undef_of_ne matchArg_expA_undef_of_sub)
open Silmaril.SpecTec.Equiv.Validation (tyV tyV_inj natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Round6.RefOkB (ctxR)

variable {prof : Silmaril.Wasm.Numerics.Profile} {H : Type}

/-! ## What `B` does not answer -/

theorem call_unrollht (hn : H → String) (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (ws : List ArgV) : (Prims.builtins prof hn host).call "unrollht_" ws = none := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

theorem call_closDeftype (hn : H → String) (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (ws : List ArgV) : (Prims.builtins prof hn host).call "clos_deftype" ws = none := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

theorem call_before (hn : H → String) (host : Silmaril.Wasm.Execution.Core.HostSemantics H)
    (ws : List ArgV) : (Prims.builtins prof hn host).call "before" ws = none := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-! ## The clauses -/

/-- `$before`'s clauses. -/
def beforeClauses : List Clause :=
  [(Clause.defD [(Param.expP "j" (Typ.varT "n" [])), (Param.expP "i" (Typ.numT NumTyp.natT))] [(Arg.expA
  (Exp.caseE "REC" (Exp.varE "j"))), (Arg.expA (Exp.varE "i"))] (Exp.cmpE CmpOp.ltOp (OpTyp.numT NumTyp.natT)
  (Exp.varE "j") (Exp.varE "i")) []), (Clause.defD [(Param.expP "typeuse" (Typ.varT "typeuse" [])),
  (Param.expP "i" (Typ.numT NumTyp.natT))] [(Arg.expA (Exp.varE "typeuse")), (Arg.expA (Exp.varE "i"))]
  (Exp.boolE true) [Prem.elsePr])]

/-- `$unrollht_`'s clauses. -/
def unrollhtClauses : List Clause :=
  [(Clause.defD [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "deftype"
  (Typ.varT "deftype" []))] [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.subE (Exp.varE "deftype")
  (Typ.varT "deftype" []) (Typ.varT "heaptype" [])))] (Exp.callE "unrolldt" [(Arg.expA (Exp.varE "deftype"))])
  []), (Clause.defD [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "typeidx" (Typ.varT "typeidx"
  []))] [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.caseE "_IDX" (Exp.varE "typeidx")))] (Exp.callE "unrolldt"
  [(Arg.expA (Exp.idxE (Exp.dotE (Exp.varE "C") "TYPES") (Exp.projE (Exp.uncaseE (Exp.varE "typeidx") "%")
  (0 : Int))))]) []), (Clause.defD [(Param.expP "C" (Typ.varT "context" [])), (Param.expP "i" (Typ.varT "n"
  []))] [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.caseE "REC" (Exp.varE "i")))] (Exp.idxE (Exp.dotE
  (Exp.varE "C") "RECS") (Exp.varE "i")) [])]

/-- `$clos_deftype`'s clause. -/
def closClauses : List Clause :=
  [(Clause.defD [(Param.expP "C" (Typ.varT "context"
  [])), (Param.expP "dt" (Typ.varT "deftype" [])), (Param.expP "dt'*" (Typ.iterT (Typ.varT "deftype"
  []) Iter.list))] [(Arg.expA (Exp.varE "C")), (Arg.expA (Exp.varE "dt"))] (Exp.callE "subst_all_deftype"
  [(Arg.expA (Exp.varE "dt")), (Arg.expA (Exp.iterE (Exp.subE (Exp.varE "dt'") (Typ.varT "deftype"
  []) (Typ.varT "typeuse" [])) (IterExp.mk Iter.list [(Dom.mk "dt'" (Exp.varE "dt'*"))])))]) [(Prem.ifPr
  (Exp.cmpE CmpOp.eqOp OpTyp.boolT (Exp.iterE (Exp.varE "dt'") (IterExp.mk Iter.list [(Dom.mk "dt'"
  (Exp.varE "dt'*"))])) (Exp.callE "clos_deftypes" [(Arg.expA (Exp.dotE (Exp.varE "C") "TYPES"))])))])]

variable {B : Builtins}

set_option maxRecDepth 100000 in
theorem findDef_before : ∃ ps t, (simEnv B).findDef? "before" = some (ps, t, beforeClauses) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_unrollht : ∃ ps t, (simEnv B).findDef? "unrollht_" = some (ps, t, unrollhtClauses) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
theorem findDef_clos : ∃ ps t, (simEnv B).findDef? "clos_deftype" = some (ps, t, closClauses) :=
  ⟨_, _, rfl⟩

/-- The clauses of an applied definition, by its known clause list. -/
theorem applies_inv {env : Env} {x : IL.Id} {ws : List ArgV} {v : Value} {cs : List Clause}
    (hd : ∃ ps t, env.findDef? x = some (ps, t, cs)) (h : Applies env x ws v) :
    TryClauses env cs ws v ∨ (TryClausesUndef env cs ws ∧ env.builtins.call x ws = some v) := by
  obtain ⟨ps, t, hd⟩ := hd
  obtain ⟨ps', t', cs', hf, hc⟩ := h
  rw [hd] at hf
  cases hf
  exact hc

/-! ## `$clos_deftype` never has a value -/

/-- **`$clos_deftype` has no value**, on the concrete `B`. -/
theorem not_applies_closDeftype (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) (c d w : Value) :
    ¬ Applies (simEnv (Prims.builtins prof hn host)) "clos_deftype" [.val c, .val d] w := by
  intro h
  have hu : TryClausesUndef (simEnv (Prims.builtins prof hn host)) closClauses [.val c, .val d] :=
    IntNumeric.tryClausesUndef_skip_prem (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
      (Prims.premsUndef_if (Prims.evalExpUndef_cmpL (Prims.evalExpUndef_iterList
        (Prims.evalExpUndef_var rfl)))) IntNumeric.tryClausesUndef_nil
  rcases applies_inv findDef_clos h with hc | ⟨-, hb⟩
  · exact not_tryClauses_and_undef hc hu
  · rw [simEnv, Env.builtins_withBuiltins, call_closDeftype] at hb
    cases hb

/-! ## `$unrollht_` -/

/-- `C`, matched. -/
theorem matchArg_C {env : Env} (c : Value) :
    MatchArg env VarEnv.empty (.expA (.varE "C")) (.val c) (VarEnv.empty.bindVal "C" c) :=
  matchArg_expA (matchExp_varE rfl)

/-- The patterns of `$unrollht_`'s three clauses. -/
abbrev unrollhtPats₁ : List Arg :=
  [.expA (.varE "C"), .expA (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))]
abbrev unrollhtPats₂ : List Arg := [.expA (.varE "C"), .expA (.caseE "_IDX" (.varE "typeidx"))]
abbrev unrollhtPats₃ : List Arg := [.expA (.varE "C"), .expA (.caseE "REC" (.varE "i"))]

/-- A second argument with operator `op ≠ op'` does not match the pattern `(C, op' x)`. -/
theorem matchArgsUndef_op {env : Env} {c w : Value} {op op' : MixopS} {x : IL.Id}
    (h : ¬ op = op') : MatchArgsUndef env VarEnv.empty [.expA (.varE "C"), .expA (.caseE op' (.varE x))]
      [.val c, .val (.case op w)] :=
  matchArgs_cons_undef_tail (matchArg_C _) (matchArgs_cons_undef
    (matchArg_expA_undef (matchExp_caseE_undef_of_ne h)))

set_option maxRecDepth 100000 in
/-- `REC k` is not a `deftype`. -/
theorem matchArgsUndef_recDef {hn : H → String}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} {c : Value} {k : Nat} :
    MatchArgsUndef (simEnv (Prims.builtins prof hn host)) VarEnv.empty unrollhtPats₁
      [.val c, .val (.case "REC" (natV k))] :=
  matchArgs_cons_undef_tail (matchArg_C _) (matchArgs_cons_undef
    (matchArg_expA_undef_of_sub (by rfl)))

/-- `C.RECS[i]`, in `C = ctxR L`, `i = k`. -/
theorem evalExp_recsBody {env : Env} {L : List Value} {k : Nat} {w : Value}
    (he : EvalExp env ((VarEnv.empty.bindVal "C" (ctxR L)).bindVal "i" (natV k))
      (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) w) : L[k]? = some w := by
  obtain ⟨lv, i, hl, hi, hidx⟩ := evalExp_idxE_iff.1 he
  obtain ⟨cv, hc, hf⟩ := evalExp_dotE_iff.1 hl
  have ec : cv = ctxR L := Option.some.inj ((evalExp_varE_iff.1 hc).symm.trans rfl)
  have el : lv = .list L := by rw [ec] at hf; exact (Option.some.inj hf).symm
  have ei : i = k := by
    have := (evalExp_varE_iff.1 hi).symm.trans (rfl : _ = some (natV k))
    simpa [natV] using this
  simpa [el, ei] using hidx

/-- **`$unrollht_(C, REC k)`'s clauses give `C.RECS[k]`**, in a context `ctxR L`. -/
theorem tryClauses_unrollht_rec {hn : H → String}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics H} {L : List Value} {k : Nat} {w : Value}
    (hc : TryClauses (simEnv (Prims.builtins prof hn host)) unrollhtClauses
      [.val (ctxR L), .val (.case "REC" (natV k))] w) : L[k]? = some w := by
  have hc₃ := (Silmaril.SpecTec.Equiv.ExecBuiltins.tryClauses_cons_iff_of_skip
    (matchArgsUndef_op (by decide))).1
      ((Silmaril.SpecTec.Equiv.ExecBuiltins.tryClauses_cons_iff_of_skip matchArgsUndef_recDef).1 hc)
  obtain ⟨ρ₀, ⟨n, hm⟩, he⟩ := BwdRead.tryClauses_one_inv hc₃
  have hm₀ : MatchArgs (simEnv (Prims.builtins prof hn host)) VarEnv.empty unrollhtPats₃
      [.val (ctxR L), .val (.case "REC" (natV k))]
      ((VarEnv.empty.bindVal "C" (ctxR L)).bindVal "i" (natV k)) :=
    matchArgs_cons (matchArg_C _) (matchArgs_cons (matchArg_expA (matchExp_caseE
      (matchExp_varE rfl))) matchArgs_nil)
  have e := IntNumeric.matchArgs_det hm₀ hm
  exact evalExp_recsBody (e ▸ he)

/-- **`$unrollht_(C, REC k)` is `C.RECS[k]`**, in a context `ctxR L`. -/
theorem applies_unrollht_rec (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {L : List Value} {k : Nat} {w : Value}
    (h : Applies (simEnv (Prims.builtins prof hn host)) "unrollht_"
      [.val (ctxR L), .val (.case "REC" (natV k))] w) : L[k]? = some w := by
  rcases applies_inv findDef_unrollht h with hc | ⟨-, hb⟩
  · exact tryClauses_unrollht_rec hc
  · rw [simEnv, Env.builtins_withBuiltins, call_unrollht] at hb
    cases hb

set_option maxRecDepth 100000 in
/-- `$unrollht_`'s first clause at the image of a defined type: Core's `unrolldt`. -/
theorem unrollht_clause₁ {hn : H → String} {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
    {c : Value} {d : DefType} {w : Value} {ρ₀ ρ₁ : VarEnv} {n : Nat}
    (hm : matchArgs n (simEnv (Prims.builtins prof hn host)) VarEnv.empty unrollhtPats₁
      [.val c, .val (tyV d)] = .ok ρ₀)
    (hp : PremsHold (simEnv (Prims.builtins prof hn host)) ρ₀ [] ρ₁)
    (he : EvalExp (simEnv (Prims.builtins prof hn host)) ρ₁
      (.callE "unrolldt" [.expA (.varE "deftype")]) w) :
    ∃ st, unrolldt d = some st ∧ w = tyV st := by
  obtain ⟨g, i, rfl⟩ : ∃ g i, d = Ty.defn g i := by cases d; exact ⟨_, _, rfl⟩
  have hm₀ : MatchArgs (simEnv (Prims.builtins prof hn host)) VarEnv.empty unrollhtPats₁
      [.val c, .val (tyV (Ty.defn g i))]
      ((VarEnv.empty.bindVal "C" c).bindVal "deftype" (tyV (Ty.defn g i))) :=
    matchArgs_cons (matchArg_C _) (matchArgs_cons (matchArg_expA (Prims.matchExp_subE
      (matchExp_varE rfl)) (by rfl)) matchArgs_nil)
  have e₀ := IntNumeric.matchArgs_det hm₀ hm
  have e₁ := Silmaril.SpecTec.Equiv.Validation.premsHold_nil_iff.1 hp
  have ha : Applies (simEnv (Prims.builtins prof hn host)) "unrolldt" [.val (tyV (Ty.defn g i))] w :=
    (Silmaril.SpecTec.Equiv.ExecNumeric.applies_iff_callDef
      (Prims.findDef_none_of_valsOnly ⟨rfl, rfl, rfl⟩ _)
      (Equiv.evalArgs_cons (evalExp_var rfl) Equiv.evalArgs_nil)).2
      (evalExp_callE_iff.1 (e₀ ▸ e₁ ▸ he))
  exact Option.map_eq_some_iff.1 ((Prims.applies_unrolldt hn host _ w).1 ha)
    |>.imp fun st h => ⟨h.1, h.2.symm⟩

/-- **`$unrollht_(C, dt)` at the image of a defined type is the image of Core's `unrolldt`.** -/
theorem applies_unrollht_def (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {c : Value} {d : DefType} {w : Value}
    (h : Applies (simEnv (Prims.builtins prof hn host)) "unrollht_" [.val c, .val (tyV d)] w) :
    ∃ st, unrolldt d = some st ∧ w = tyV st := by
  obtain ⟨g, i, rfl⟩ : ∃ g i, d = Ty.defn g i := by cases d; exact ⟨_, _, rfl⟩
  rcases applies_inv findDef_unrollht h with ⟨n, hn'⟩ | ⟨-, hb⟩
  · rcases Prims.tryClauses_cons_elim hn' with ⟨ρ₀, ρ₁, ⟨m, hm⟩, hp, he⟩ | hrest
    · exact unrollht_clause₁ hm hp he
    · have hrest' := (Silmaril.SpecTec.Equiv.ExecBuiltins.tryClauses_cons_iff_of_skip
        (matchArgsUndef_op (by decide))).1 ((Silmaril.SpecTec.Equiv.ExecBuiltins.tryClauses_cons_iff_of_skip
          (matchArgsUndef_op (by decide))).1 hrest)
      exact absurd hrest' Silmaril.SpecTec.Equiv.ExecBuiltins.not_tryClauses_nil
  · rw [simEnv, Env.builtins_withBuiltins, call_unrollht] at hb
    cases hb

/-! ## `$before` -/

/-- **`$before(REC k, j)` is `k < j`.** -/
theorem applies_before_rec (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) {k j : Nat}
    (h : Applies (simEnv (Prims.builtins prof hn host)) "before"
      [.val (.case "REC" (natV k)), .val (natV j)] (.bool true)) : k < j := by
  have hm : MatchArgs (simEnv (Prims.builtins prof hn host)) VarEnv.empty
      [.expA (.caseE "REC" (.varE "j")), .expA (.varE "i")]
      [.val (.case "REC" (natV k)), .val (natV j)]
      ((VarEnv.empty.bindVal "j" (natV k)).bindVal "i" (natV j)) :=
    matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl)))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
  have hv : TryClauses (simEnv (Prims.builtins prof hn host)) beforeClauses
      [.val (.case "REC" (natV k)), .val (natV j)] (.bool (decide (k < j))) :=
    tryClauses_hit hm (Silmaril.SpecTec.Equiv.Validation.premsHold_nil_iff.2 rfl)
      (evalExp_cmpNum (evalExp_var rfl) (evalExp_var rfl) (by simp [Num.cmp]))
  rcases applies_inv findDef_before h with hc | ⟨hu, -⟩
  · have := tryClauses_unique hc hv
    simpa using this
  · exact absurd hv fun hv => not_tryClauses_and_undef hv hu

end Silmaril.Wasm.SpecTec.Sim.Round6.TyElim
