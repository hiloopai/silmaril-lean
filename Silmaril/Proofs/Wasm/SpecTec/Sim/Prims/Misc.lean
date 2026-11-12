module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Blocktype
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Prims.Host

/-!
# The concrete `B`: the remaining helpers

`$tag` (both ways), `$add_exninst`, `$as_deftype`, `$elem`, `$lift_result`, and the two `i31`
primitives `$wrap__`/`$extend__` (no clause; answered by `B`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

variable {prof : Silmaril.Wasm.Numerics.Profile}

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef)
open Silmaril.SpecTec.Equiv.ExecBuiltins (matchExp_caseE_undef_of_ne asBits?)
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.Execution (pctV)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tagInstToValue elemInstToValue moduleInstToValue)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core

variable {H : Type}

/-! ## `$tag` -/

/-- `$tag(z, x)` on an encoded state, in range. -/
theorem applies_tag {env : Env} (P : ProjDefs env) (S : State.StateDefs env) (hn : H → String)
    (s : Store H) (f : Frame) (x : TagIdx) (ta : Nat) (ti : TagInst)
    (h : s.tag? f x = some (ta, ti)) :
    Applies env "tag" [.val (stateV hn s f), .val (Encode.toValue x)] (tagInstToValue CT ti) := by
  have h' : f.module.tags[x.toNat]? = some ta ∧ s.tags[ta]? = some ti := by
    simpa [Store.tag?, Option.bind_eq_some_iff] using h
  exact applies_of_clause1 P.tag State.matchArgs_zxPat (State.evalExp_storeAccBody S
    (n := x.toNat) (a := ta) rfl rfl rfl (by rw [List.getElem?_map, h'.1]; rfl)
    (by rw [List.getElem?_map, h'.2]; rfl))

/-- The value of `$tag`'s body on an encoded state determines Core's `Store.tag?`. -/
theorem tag_of_body {env : Env} (S : State.StateDefs env) (hn : H → String) (s : Store H)
    (f : Frame) (x : TagIdx) {w : Value}
    (h : EvalExp env (State.accScope (stateV hn s f) (Encode.toValue x)) (State.storeAccBody "TAGS")
      w) :
    ∃ ta ti, s.tag? f x = some (ta, ti) ∧ w = tagInstToValue CT ti := by
  obtain ⟨L, i, hL, hi, hw⟩ := evalExp_idxE_iff.1 h
  have hL' : L = .list (s.tags.map (tagInstToValue CT)) :=
    EvalExp.unique hL (evalExp_dotE_iff.2 ⟨_, State.evalExp_sof S rfl (evalExp_var rfl), rfl⟩)
  obtain ⟨M, j, hM, hj, hi'⟩ := evalExp_idxE_iff.1 hi
  have hM' : M = .list (f.module.tags.map fun a => .num (.natN a)) :=
    EvalExp.unique hM (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_,
      State.evalExp_fof S rfl (evalExp_var rfl), rfl⟩, rfl⟩)
  have hj' : Value.num (.natN j) = .num (.natN x.toNat) :=
    EvalExp.unique hj (State.evalExp_idxPayload rfl)
  have ha : f.module.tags[x.toNat]? = some i := by
    simpa [hM', Value.idx?, ← (by simpa using hj' : j = x.toNat)] using hi'
  obtain ⟨ti, hti, rfl⟩ : ∃ ti, s.tags[i]? = some ti ∧ w = tagInstToValue CT ti := by
    simpa [hL', Value.idx?, eq_comm] using hw
  exact ⟨i, ti, by simp [Store.tag?, ha, hti], rfl⟩

/-- **`$tag` reads back**, for the concrete `B` (which has no entry for `$tag`). -/
theorem tag_inv (hn : H → String) (host : HostSemantics H) (s : Store H) (f : Frame) (x : TagIdx)
    (w : Value)
    (h : Applies (simEnv (builtins prof hn host)) "tag" [.val (stateV hn s f), .val (Encode.toValue x)]
      w) :
    ∃ ta ti, s.tag? f x = some (ta, ti) ∧ w = tagInstToValue CT ti := by
  rcases applies_clause1_inv (projDefs_simEnv _).tag State.matchArgs_zxPat h with hb | hb
  · exact tag_of_body (State.stateDefs_simEnv _) hn s f x hb
  · simp [simEnv, builtins, call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames] at hb

/-! ## `$add_exninst` -/

/-- Appending to the `EXNS` field of an encoded store encodes `Store.addExn`. -/
theorem storeV_addExn (hn : H → String) (s : Store H) (e : ExnInst) :
    (storeV hn s).setField "EXNS" (.list (s.exns.map exnInstV ++ [exnInstV e])) =
      some (storeV hn (s.addExn e)) := by
  simp [storeV, Store.addExn]

/-- `$add_exninst(z, [exn])` appends `exn`. -/
theorem applies_addExn {env : Env} (P : ProjDefs env) (S : State.StateDefs env)
    (hn : H → String) (s : Store H) (f : Frame) (e : ExnInst) :
    Applies env "add_exninst" [.val (stateV hn s f), .val (.list [exnInstV e])]
      (stateV hn (s.addExn e) f) := by
  have hm := matchArgs_cons (matchArg_expA (matchExp_varE (env := env) (ρ := VarEnv.empty)
    (x := "z") (v := stateV hn s f) rfl)) (matchArgs_cons (matchArg_expA
      (State.matchExp_iterVar (y := "exn") (ys := "exn*") (l := [exnInstV e]) rfl (by decide) rfl))
      matchArgs_nil)
  refine applies_of_clause1 P.addExn hm (evalExp_case (evalExp_tup2 ?_
    (State.evalExp_fof S rfl (evalExp_var rfl))))
  have hl : EvalExp env ((VarEnv.empty.bindVal "z" (stateV hn s f)).bindVal "exn*"
      (.list [exnInstV e])) (.iterE (.varE "exn") (.mk .list [.mk "exn" (.varE "exn*")]))
      (.list [exnInstV e]) := by
    simpa using evalExp_iterMap (g := fun w => w) rfl (fun w _ => evalExp_var rfl)
  exact evalExp_extE_iff.2 ⟨_, _, _, _, State.evalExp_sof S rfl (evalExp_var rfl), hl,
    State.pathGet_dot State.pathGet_root rfl, rfl,
    State.pathSet_dot State.pathGet_root (storeV_addExn hn s e) State.pathSet_root⟩

/-! ## `$as_deftype` -/

/-- A `SubE` pattern matches as its operand does. -/
theorem matchExp_subE {env : Env} {ρ ρ' : VarEnv} {e : Exp} {t₁ t₂ : Typ} {v : Value}
    (h : MatchExp env ρ e v ρ') : MatchExp env ρ (.subE e t₁ t₂) v ρ' := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 1, by simp [matchExp, h]⟩

set_option maxRecDepth 100000 in
/-- `$as_deftype(dt) = dt`. -/
theorem asDeftypeDef (B : Builtins) : State.HasClause1 (simEnv B) "as_deftype"
    [.expA (.subE (.varE "dt") (.varT "deftype" []) (.varT "typeuse" []))] (.varE "dt") :=
  ⟨_, _, _, rfl⟩

set_option maxRecDepth 100000 in
/-- The image of a defined type passes `deftype`'s subtype test. -/
theorem argSubOk_deftype (B : Builtins) (d : DefType) :
    argSubOk (simEnv B) VarEnv.empty (.subE (.varE "dt") (.varT "deftype" []) (.varT "typeuse" []))
      (CT.defType d) = true := by
  cases d
  rfl

/-- `$as_deftype` is the identity on the images of defined types. -/
theorem applies_asDeftype (B : Builtins) (d : DefType) :
    Applies (simEnv B) "as_deftype" [.val (CT.defType d)] (CT.defType d) :=
  applies_of_clause1 (asDeftypeDef B)
    (matchArgs_cons (matchArg_expA (matchExp_subE (matchExp_varE rfl)) (argSubOk_deftype B d))
      matchArgs_nil)
    (evalExp_var rfl)

/-! ## `$elem` -/

/-- `$elem(z, y)` on an encoded state, in range. -/
theorem evalExp_elem_stateV {env : Env} (S : State.StateDefs env) (hn : H → String)
    (ρ : VarEnv) (ez ey : Exp) (s : Store H) (f : Frame) (y : ElemIdx) (ea : Nat) (ei : ElemInst)
    (h : s.elem? f y = some (ea, ei)) (hρ : ρ.findDef? "elem" = none)
    (hz : EvalExp env ρ ez (stateV hn s f)) (hy : EvalExp env ρ ey (Encode.toValue y)) :
    EvalExp env ρ (.callE "elem" [.expA ez, .expA ey]) (elemInstToValue CT ei) := by
  have h' : f.module.elems[y.toNat]? = some ea ∧ s.elems[ea]? = some ei := by
    simpa [Store.elem?, Option.bind_eq_some_iff] using h
  exact State.evalExp_elem S (n := y.toNat) (a := ea) hρ hz hy rfl rfl rfl
    (by rw [List.getElem?_map, h'.1]; rfl) (by rw [List.getElem?_map, h'.2]; rfl)

/-! ## `$lift_result` -/

set_option maxRecDepth 100000 in
/-- `$lift_result`'s three clauses. -/
theorem liftResultDef (B : Builtins) : ∃ ps t q₁ q₂ q₃,
    (simEnv B).findDef? "lift_result" = some (ps, t,
      [.defD q₁ [.expA (.caseE "_VALS" (State.iterVar "val" "val*"))]
        (.iterE (.subE (.varE "val") (.varT "val" []) (.varT "instr" []))
          (.mk .list [.mk "val" (.varE "val*")])) [],
       .defD q₂ [.expA (.caseE "(REF.EXN_ADDR%)THROW_REF" (.varE "a"))]
        (.listE [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]) [],
       .defD q₃ [.expA (.caseE "TRAP" (.tupE []))] (.listE [.caseE "TRAP" (.tupE [])]) []]) :=
  ⟨_, _, _, _, _, rfl⟩

/-- A pattern for another injection is skipped. -/
theorem matchArgsUndef_case {env : Env} {op op' : MixopS} {e : Exp} {w : Value} (h : ¬ op' = op) :
    MatchArgsUndef env VarEnv.empty [.expA (.caseE op e)] [.val (.case op' w)] :=
  matchArgs_cons_undef (Silmaril.SpecTec.Equiv.ExecBuiltins.matchArg_expA_undef
    (matchExp_caseE_undef_of_ne h))

/-- **`$lift_result` on images** is `Result.toAdmin`, for every `B`. -/
theorem applies_liftResult (B : Builtins) (r : Result) :
    Applies (simEnv B) "lift_result" [.val (resultV r)] (.list (adminsToV r.toAdmin)) := by
  obtain ⟨ps, t, q₁, q₂, q₃, hd⟩ := liftResultDef B
  refine ⟨ps, t, _, hd, Or.inl ?_⟩
  cases r with
  | values vs =>
    refine tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE (State.matchExp_iterVar
      (ρ₀ := VarEnv.empty) (l := vs.map valV) rfl (by decide) rfl))) matchArgs_nil) premsHold_nil ?_
    simpa [Result.toAdmin, adminsToV_vals] using evalExp_iterMap (g := fun w => w) rfl
      (fun w _ => evalExp_subE_iff.2 (evalExp_var rfl))
  | throw a =>
    refine tryClauses_skip_match (matchArgsUndef_case (by decide)) (tryClauses_hit
      (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil)
      premsHold_nil (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_var rfl))
        (evalExps_cons (evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)) evalExps_nil),
        rfl⟩))
  | trap =>
    refine tryClauses_skip_match (matchArgsUndef_case (by decide))
      (tryClauses_skip_match (matchArgsUndef_case (by decide)) (tryClauses_hit
        (matchArgs_cons (matchArg_expA (matchExp_caseE (Equiv.Validation.matchExp_tup_iff.2
          ⟨[], rfl, (⟨1, by simp [matchExps]⟩ : Equiv.Validation.MatchExps _ VarEnv.empty [] [] VarEnv.empty)⟩))) matchArgs_nil) premsHold_nil
        (evalExp_listE_iff.2 ⟨_, evalExps_cons (evalExp_case (evalExp_tupE_iff.2
          ⟨[], evalExps_nil, rfl⟩)) evalExps_nil, rfl⟩)))

end Silmaril.Wasm.SpecTec.Sim.Prims
