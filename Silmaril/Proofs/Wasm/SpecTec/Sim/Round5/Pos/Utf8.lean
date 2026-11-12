module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round5.Pos.SuccTyped

/-!
# Round 5: `$utf8` never evaluates, so no export name is typed

SpecTec's `name` is `% char*` with the premise `|$utf8(char*)| < 2^32`. The first clause of
`$utf8` (definition 52, unchanged by erratum #656) is

```
def $utf8(ch*) = $concat_(byte, $utf8(ch)*)
```

Its argument pattern `ch*` matches *every* list, the singleton `[ch]` included, and the
evaluator tries clauses in order (`tryClauses`). So `$utf8([ch])` calls `$utf8([ch])` again,
eleven fuel levels lower, and never returns: at every fuel it is `outOfFuel`
(`tryClauses_utf8`). `outOfFuel` is not `undef`, so `callDef` never falls back to the
primitives `B`: **no `B` can give `$utf8` a value**, and the round-4 plan of answering it in
`Prims.builtins` (upstream item U7) cannot work as stated. (The four single-character clauses,
which bind their bytes through `if` premises, are never reached.)

Consequences, for every `B`:

* `not_hasTyp_name_single`: a one-character name is not a `name`;
* `not_hasTyp_exportinst_single`, `not_typedV_moduleinst_of_export`: no export instance with a
  one-character name, and no module instance holding one, is typed;
* `not_posTyping`: `Round4.PosTyping B hn` is uninhabited (its `moduleinst` field fails at the
  valid, bounded `ConfigOk.exportModule`, which exports global `0` as `"g"`), so
  `Round4.typed_of_configOk` and every reduction through `PosTyping` is vacuous;
* `not_typed_expNopCfg`: the valid, bounded configuration `nop` over that module is not `Typed`.

The empty name *is* a `name` (`$utf8([]) = []`), which this file does not need.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-! ## The first clause of `$utf8` loops -/

/-- `(ch <- ch*)*`. -/
def chsDom : IterExp := .mk .list [.mk "ch" (.varE "ch*")]

/-- `$concat_(byte, $utf8([ch])*)`, the body of `$utf8`'s first clause. -/
def utf8Body : Exp := .callE "concat_" [.typA (.varT "byte" []),
  .expA (.iterE (.callE "utf8" [.expA (.listE [.varE "ch"])]) chsDom)]

/-- `def $utf8(ch*) = $concat_(byte, $utf8(ch)*)`. -/
def utf8Clause1 : Clause :=
  .defD [.expP "ch*" (.iterT (.varT "char" []) .list)] [.expA (.iterE (.varE "ch") chsDom)]
    utf8Body []

set_option maxRecDepth 100000 in
/-- `$utf8`'s first clause, in every `simEnv B`. -/
theorem findDef_utf8 (B : Builtins) :
    ∃ ps t rest, (simEnv B).findDef? "utf8" = some (ps, t, utf8Clause1 :: rest) :=
  ⟨_, _, _, rfl⟩

@[simp] theorem ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] theorem err_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

/-- `[ch]` evaluates to `[u]` once there is fuel. -/
theorem evalArg_ch (B : Builtins) (m : Nat) (u : Value) (ρ : VarEnv)
    (hρ : ρ.findVal? "ch" = some u) :
    evalArg m (simEnv B) ρ (.expA (.listE [.varE "ch"])) = .ok (.val (.list [u])) ∨
      evalArg m (simEnv B) ρ (.expA (.listE [.varE "ch"])) = .error .outOfFuel := by
  rcases m with _ | _ | _ | _ | m
  · simp [evalArg]
  · simp [evalArg, evalExp]
  · simp [evalArg, evalExp, evalExps]
  · simp [evalArg, evalExp, evalExps]
  · simp [evalArg, evalExp, evalExps, hρ, Res.ofOption]

set_option maxRecDepth 100000 in
/-- **The fuel shift.** If `$utf8([u])`'s clauses run out of fuel at `n + 1`, they do at
`n + 12`: the first clause's body calls them again at `n + 1`. -/
theorem utf8_step (B : Builtins) (n : Nat) (u : Value) (ps : List Param) (t : Typ)
    (rest : List Clause) (hd : (simEnv B).findDef? "utf8" = some (ps, t, utf8Clause1 :: rest))
    (hT : tryClauses (n + 1) (simEnv B) (utf8Clause1 :: rest) [.val (.list [u])] =
      .error .outOfFuel) :
    tryClauses (n + 12) (simEnv B) (utf8Clause1 :: rest) [.val (.list [u])] =
      .error .outOfFuel := by
  simp only [tryClauses, utf8Clause1]
  rcases evalArg_ch B n u
    { vals := [("ch", u), ("ch*", Value.list [u])], typs := [], defs := [], grams := [] } rfl
    with he | he <;>
  simp [matchArgs, matchArg, argSubOk, matchExp, chsDom, matchIterE, matchIterList, matchRounds,
    matchExps, premsHold, utf8Body, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, iterCols, iterRows, Res.assert, hd,
    VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, iterCol,
    VarEnv.findVal?, VarEnv.findVals?, Map.empty, he, hT, Res.elimUndef, iterRow, Map.binds]

set_option maxRecDepth 100000 in
/-- Below fuel `12` the clauses run out of fuel outright. -/
theorem utf8_small (B : Builtins) (k : Nat) (hk : k < 12) (u : Value) (ps : List Param)
    (t : Typ) (rest : List Clause)
    (hd : (simEnv B).findDef? "utf8" = some (ps, t, utf8Clause1 :: rest)) :
    tryClauses k (simEnv B) (utf8Clause1 :: rest) [.val (.list [u])] = .error .outOfFuel := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> try omega
  all_goals simp [tryClauses, utf8Clause1, matchArgs, matchArg, argSubOk, matchExp, chsDom,
    matchIterE, matchIterList, matchRounds, matchExps, premsHold, utf8Body, evalExp, callDef,
    evalArgs, evalArg, evalIterE, evalDoms, evalIterList, evalRounds, Res.ofOption, domVar, domSrc,
    iterCols, iterRows, Res.assert, hd, VarEnv.findDef?, VarEnv.bindVal, VarEnv.bindVals,
    VarEnv.empty, Map.bind, Map.find?, iterCol, VarEnv.findVal?, VarEnv.findVals?,
    Map.empty, premHolds, Res.elimUndef]

/-- **`$utf8` on a one-element list never returns**: its clauses are `outOfFuel` at every fuel,
in every `simEnv B`. -/
theorem tryClauses_utf8 (B : Builtins) (u : Value) (ps : List Param) (t : Typ)
    (rest : List Clause) (hd : (simEnv B).findDef? "utf8" = some (ps, t, utf8Clause1 :: rest)) :
    ∀ n, tryClauses n (simEnv B) (utf8Clause1 :: rest) [.val (.list [u])] = .error .outOfFuel := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 12
    · exact utf8_small B n hn u ps t rest hd
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
      exact utf8_step B m u ps t rest hd (ih (m + 1) (by omega))

/-! ## `name` -/

/-- `(char <- char*)*`. -/
def charDom : IterExp := .mk .list [.mk "char" (.varE "char*")]

/-- `|$utf8(char*)|`, the left side of `name`'s premise. -/
def namePremLhs : Exp := .lenE (.callE "utf8" [.expA (.iterE (.varE "char") charDom)])

set_option maxRecDepth 100000 in
/-- `|$utf8([u])|` has no value, at any fuel. -/
theorem evalExp_namePremLhs (B : Builtins) (u : Value) (n : Nat) (v : Value) :
    evalExp n (simEnv B) (VarEnv.empty.bindVal "char*" (.list [u])) namePremLhs ≠ .ok v := by
  obtain ⟨ps, t, rest, hd⟩ := findDef_utf8 B
  have hT := tryClauses_utf8 B u ps t rest hd
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;>
  simp [namePremLhs, charDom, evalExp, callDef, evalArgs, evalArg, evalIterE, evalDoms,
    evalIterList, evalRounds, Res.ofOption, domVar, domSrc, Res.assert, hd, VarEnv.findDef?,
    VarEnv.bindVal, VarEnv.bindVals, VarEnv.empty, Map.bind, Map.find?, iterRow, iterRows,
    VarEnv.findVal?, Map.empty, Res.elimUndef, hT, Map.binds]

/-- `name`'s premise. -/
def namePrem : Exp :=
  .cmpE .ltOp (.numT .natT) namePremLhs
    (.binE .powOp (.numT .natT) (.numE (.natN 2)) (.numE (.natN 32)))

set_option maxRecDepth 100000 in
theorem findTyp_name (B : Builtins) : (simEnv B).findTyp? "name" = some ([], [.instD [] []
    (.variantT [.mk "%" (.tupT [.mk "char*" (.iterT (.varT "char" []) .list)]) []
      [.ifPr namePrem]])]) := rfl

/-- `name`'s premise fails on a one-character list. -/
theorem not_evalExp_namePrem (B : Builtins) (u : Value) (v : Value) :
    ¬ EvalExp (simEnv B) (VarEnv.empty.bindVal "char*" (.list [u])) namePrem v := by
  rintro ⟨n, hn⟩
  rcases n with _ | n
  · simp [evalExp] at hn
  · simp only [namePrem, evalExp] at hn
    cases he : evalExp n (simEnv B) (VarEnv.empty.bindVal "char*" (.list [u])) namePremLhs with
    | ok w => exact evalExp_namePremLhs B u n w he
    | error e => rw [he] at hn; cases hn

/-- **A one-character name is not a `name`**, in any `simEnv B` and term-only scope. -/
theorem not_hasTyp_name_single (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ) (u : Value) :
    ¬ HasTyp (simEnv B) ρ (.varT "name" []) (.case "%" (.tuple [.list [u]])) := by
  intro h
  have hl : localTyp? ρ "name" [] = none := by simp [localTyp?, VarEnv.findTyp?, hρ.1]
  obtain ⟨td, ws, htd, -, hi⟩ := (hasTyp_varT_global_iff hl).1 h
  rw [findTyp_name B] at htd
  obtain rfl := (Option.some.inj htd).symm
  rcases hasTypInsts_cons_inv hi with ⟨σ, hm, hd⟩ | hrest
  · obtain rfl := IntNumeric.matchArgs_nil_scope hm
    obtain ⟨op, w, he, hc⟩ := hasTypDef_variantT_iff.1 hd
    cases he
    obtain ⟨-, hp⟩ := (hasTypCase_cons_hit_iff rfl).1 hc
    exact not_evalExp_namePrem B u _ (ConfigOk.evalExp_of_premsOk_if hp)
  · exact absurd hrest not_hasTypInsts_nil

/-- The name `"g"` has one character. -/
theorem nameToValue_g :
    Silmaril.SpecTec.Equiv.RuntimeBridge.nameToValue "g" =
      .case "%" (.tuple [.list [Silmaril.SpecTec.Equiv.RuntimeBridge.charToValue 'g']]) := rfl

/-- An export instance named `[c]` is not an `exportinst`. -/
theorem not_hasTyp_exportinst_single (B : Builtins) {ρ : VarEnv} (hρ : ValsOnly ρ)
    (e : ExportInst) (c : Char) (hc : e.name.toList = [c]) :
    ¬ HasTyp (simEnv B) ρ (.varT "exportinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.exportInstToValue e) := by
  intro h
  have hF := ConfigOk.hasTypFields_of_closedStruct hρ ConfigOk.findTyp_exportinst h
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  have hn := hF.1
  simp only [Silmaril.SpecTec.Equiv.RuntimeBridge.nameToValue, hc, List.map_cons,
    List.map_nil] at hn
  exact not_hasTyp_name_single B ConfigOk.valsOnly_empty _ hn

/-- **No module instance exporting a one-character name is a typed `moduleinst`.** -/
theorem not_typedV_moduleinst_of_export (B : Builtins) (m : ModuleInst) (e : ExportInst)
    (he : e ∈ m.exports) (c : Char) (hc : e.name.toList = [c]) :
    ¬ TypedV (simEnv B) (.varT "moduleinst" [])
      (Silmaril.SpecTec.Equiv.RuntimeBridge.moduleInstToValue CT m) := by
  intro h
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_moduleinst' (h _ ConfigOk.valsOnly_empty)
  simp only [List.forall₂_cons, ConfigOk.fieldTyp] at hF
  obtain ⟨l, hl, hall⟩ := hasTyp_iterT_list_iff.1 hF.2.2.2.2.2.2.2.2.1
  cases hl
  exact not_hasTyp_exportinst_single B ConfigOk.valsOnly_empty e c hc
    (hasTypList_iff.1 hall _ (List.mem_map_of_mem he))

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
