module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round6.AgreeOk.DSub

/-!
# Round 6: `$before` and `$unrollht_` on images

`Subtype_ok2` calls two functions of the pinned script (definitions 332 and 333):

* `$before(typeuse, i)`: `REC j` is before `i` when `j < i`, every other type use is (an
  `otherwise` clause); `applies_before`: **it is Core's `before`**, for every `B`.
* `$unrollht_(C, heaptype)`: a defined type unrolls by `$unrolldt` (answered by the concrete `B`,
  `Prims.applies_unrolldt`), `REC i` to `C.RECS[i]`; `applies_unrollht_rec`,
  `applies_unrollht_dt`: **it is Core's `TypeCtx.unrollUse`** in `RefOkB.ctxR l`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Validation (tyV natV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core (HostSemantics)
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)

variable {B : Builtins} {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `$before` -/

/-- `$before`'s two clauses. -/
def beforeClauses : List Clause :=
  [.defD [.expP "j" (.varT "n" []), .expP "i" (.numT .natT)]
      [.expA (.caseE "REC" (.varE "j")), .expA (.varE "i")]
      (.cmpE .ltOp (.numT .natT) (.varE "j") (.varE "i")) [],
   .defD [.expP "typeuse" (.varT "typeuse" []), .expP "i" (.numT .natT)]
      [.expA (.varE "typeuse"), .expA (.varE "i")] (.boolE true) [.elsePr]]

set_option maxRecDepth 100000 in
theorem findDef_before : ∃ ps t, (simEnv B).findDef? "before" = some (ps, t, beforeClauses) :=
  ⟨_, _, rfl⟩

/-- `$before`'s fallback clause, at any type use. -/
theorem tryClauses_beforeElse {env : Env} (w : Value) (i : Nat) :
    TryClauses env [beforeClauses[1]] [.val w, .val (natV i)] (.bool true) :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_elsePr
    (evalExp_boolE_iff.2 rfl)

/-- `REC j` against a non-`REC` injection fails `$before`'s first clause. -/
theorem matchArgsUndef_beforeRec {env : Env} {op : MixopS} {w v : Value} (h : op ≠ "REC") :
    MatchArgsUndef env VarEnv.empty [.expA (.caseE "REC" (.varE "j")), .expA (.varE "i")]
      [.val (.case op w), .val v] :=
  matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef
    (Silmaril.SpecTec.Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (Ne.symm h).symm))

/-- **`$before` is Core's `before`** on images, for every `B`. -/
theorem applies_before {u : CTypeUse} {i : Nat} (h : before u i = true) :
    Applies (simEnv B) "before" [.val (tyV u), .val (natV i)] (.bool true) := by
  obtain ⟨ps, t, hd⟩ := findDef_before (B := B)
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  cases u with
  | recv j =>
    have hj : j < i := by simpa [before] using h
    exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl)))
      (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)) premsHold_nil
      (evalExp_cmpE_iff.2 ⟨_, _, evalExp_var rfl, evalExp_var rfl, by
        simp [cmpValues, natV, Num.cmp, hj]⟩)
  | idx x =>
    exact tryClauses_skip_match (matchArgsUndef_beforeRec (op := "_IDX") (by decide))
      (tryClauses_beforeElse _ i)
  | dt d =>
    cases d with
    | defn g k =>
      exact tryClauses_skip_match (matchArgsUndef_beforeRec (op := "_DEF") (by decide))
        (tryClauses_beforeElse _ i)

/-! ## `$unrollht_` -/

/-- `$unrollht_`'s three clauses. -/
def unrollhtClauses : List Clause :=
  [.defD [.expP "C" (.varT "context" []), .expP "deftype" (.varT "deftype" [])]
      [.expA (.varE "C"), .expA (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))]
      (.callE "unrolldt" [.expA (.varE "deftype")]) [],
   .defD [.expP "C" (.varT "context" []), .expP "typeidx" (.varT "typeidx" [])]
      [.expA (.varE "C"), .expA (.caseE "_IDX" (.varE "typeidx"))]
      (.callE "unrolldt" [.expA (.idxE (.dotE (.varE "C") "TYPES")
        (.projE (.uncaseE (.varE "typeidx") "%") (0 : Int)))]) [],
   .defD [.expP "C" (.varT "context" []), .expP "i" (.varT "n" [])]
      [.expA (.varE "C"), .expA (.caseE "REC" (.varE "i"))]
      (.idxE (.dotE (.varE "C") "RECS") (.varE "i")) []]

set_option maxRecDepth 100000 in
theorem findDef_unrollht :
    ∃ ps t, (simEnv B).findDef? "unrollht_" = some (ps, t, unrollhtClauses) :=
  ⟨_, _, rfl⟩

set_option maxRecDepth 100000 in
/-- `REC i` is not a `deftype`. -/
theorem argSubOk_rec (l : List Value) (i : Nat) :
    argSubOk (simEnv B) (VarEnv.empty.bindVal "C" (RefOkB.ctxR l))
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (.case "REC" (natV i)) = false := by
  simp only [argSubOk, subCaseOk, VarEnv.findTyp?, VarEnv.bindVal]
  rw [Round5.Pos.findTyp_deftype]
  rfl

/-- **`$unrollht_(C, REC i) = C.RECS[i]`**, in `RefOkB.ctxR l`. -/
theorem applies_unrollht_rec {l : List Value} {i : Nat} {w : Value} (hi : l[i]? = some w) :
    Applies (simEnv B) "unrollht_" [.val (RefOkB.ctxR l), .val (tyV (Ty.recv i : CTypeUse))] w := by
  obtain ⟨ps, t, hd⟩ := findDef_unrollht (B := B)
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  have hs : argSubOk (simEnv B) (VarEnv.empty.bindVal "C" (RefOkB.ctxR l))
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (.case "REC" (natV i)) = false := argSubOk_rec (B := B) l i
  refine tryClauses_skip_match (matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef_of_sub hs)))
    (tryClauses_skip_match (matchArgs_cons_undef_tail (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef
        (Silmaril.SpecTec.Equiv.ExecBuiltins.matchExp_caseE_undef_of_ne (by decide)))))
      (tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil))
        premsHold_nil (evalExp_idxE_iff.2 ⟨.list l, i, evalExp_dotE_iff.2 ⟨RefOkB.ctxR l,
          evalExp_var rfl, rfl⟩, evalExp_var rfl, hi⟩)))

set_option maxRecDepth 100000 in
/-- A defined type is a `deftype`. -/
theorem argSubOk_def (l : List Value) (g : CRecType) (k : Nat) :
    argSubOk (simEnv B) (VarEnv.empty.bindVal "C" (RefOkB.ctxR l))
      (.subE (.varE "deftype") (.varT "deftype" []) (.varT "heaptype" []))
      (tyV (Ty.defn g k : DefType)) = true := by
  simp only [argSubOk, subCaseOk, VarEnv.findTyp?, VarEnv.bindVal, tyV]
  rw [Round5.Pos.findTyp_deftype]
  rfl

/-- **`$unrollht_(C, deftype) = $unrolldt(deftype)`**, for the concrete `B`. -/
theorem applies_unrollht_dt {l : List Value} {d : DefType} {st : CSubType}
    (h : unrolldt d = some st) :
    Applies (simEnv (BI P hn host)) "unrollht_" [.val (RefOkB.ctxR l), .val (tyV d)] (tyV st) := by
  obtain ⟨ps, t, hd⟩ := findDef_unrollht (B := BI P hn host)
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  cases d with
  | defn g k =>
  exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
    (matchArgs_cons (matchArg_expA (Aggregates.matchExp_subE (matchExp_varE rfl))
      (argSubOk_def l g k)) matchArgs_nil)) premsHold_nil
    (evalExp_callArgs rfl (Equiv.evalArgs_cons (evalExp_var rfl) (evalArgs_nil _ _))
      ((Prims.applies_unrolldt (prof := P) hn host _ _).2 (by rw [h]; rfl)))

end Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk
