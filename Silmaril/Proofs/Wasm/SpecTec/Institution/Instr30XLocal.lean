module

public import Silmaril.Wasm.SpecTec.Institution.Instr30.Thms

/-!
# Instruction typing of the wasm-3.0 script, extended: `local.get` and `local.set`

`Instr30` works in the empty context `{}`. The local-variable rules need a context with locals:

* `ctxL ls`: the context value `{LOCALS ls}` (every other field empty), the image of Core's
  `{locals := L}` at `ls = L.map localV` (`localV ⟨i, t⟩ = %%(i, t)`); `ctxT_ctxL`: it is a typed
  `context` when the local types are bounded;
* `Instr_ok/local.get` (rule 52) and `Instr_ok/local.set` (rule 53), located in `simEnv B` by a
  kernel `rfl` (copied from `Raw/…/Scripts/Wasm30/Original/Part2.lean`), each with one premise
  `C.LOCALS[x] = %%(init, t)`;
* `dd_localGet`, `dd_localSet`: they fire in `ctxL ls` at the images of Core's typings
  (`VariableInstrOk.localGet`, `localSet`), under every reading of `otherwise`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30X

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt tyV idxV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (ctxP CtxT)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (itV evalExp_nil evalExp_resNil)

variable {B : Builtins}

/-! ## Contexts with locals -/

/-- The image of an initialisation status. -/
def initV : Init → Value
  | .set => .case "SET" (.tuple [])
  | .unset => .case "UNSET" (.tuple [])

/-- The image of a local type, `%%(init, t)`. -/
def localV (lt : LocalType) : Value := .case "%%" (.tuple [initV lt.init, tyV lt.type])

/-- `{LOCALS ls}`. -/
def ctxL (ls : List Value) : Value :=
  .struct [("TYPES", .list []), ("TAGS", .list []), ("GLOBALS", .list []), ("MEMS", .list []),
    ("TABLES", .list []), ("FUNCS", .list []), ("DATAS", .list []), ("ELEMS", .list []),
    ("LOCALS", .list ls), ("LABELS", .list []), ("RETURN", .opt none), ("REFS", .list []),
    ("RECS", .list [])]

/-- A local type is bounded when its value type is. -/
def LocalBnd (lt : LocalType) : Prop := Round4.tyBnd lt.type = true

set_option maxRecDepth 100000 in
/-- `init`'s definition. -/
theorem findTyp_init : (simEnv B).findTyp? "init" = some ([], [.instD [] [] (.variantT
    [.mk "SET" (.tupT []) [] [], .mk "UNSET" (.tupT []) [] []])]) := rfl

set_option maxRecDepth 100000 in
/-- `localtype`'s definition. -/
theorem findTyp_localtype : (simEnv B).findTyp? "localtype" = some ([], [.instD [] [] (.variantT
    [.mk "%%" (.tupT [.mk "init" (.varT "init" []), .mk "valtype" (.varT "valtype" [])]) [] []])]) :=
  rfl

/-- Every initialisation status is an `init`. -/
theorem typedV_initV (i : Init) : TypedV (simEnv B) (.varT "init" []) (initV i) := by
  cases i
  · exact Typing.typedV_closedCase findTyp_init rfl hasTyp_tupT_nil
  · exact Typing.typedV_closedCase findTyp_init rfl hasTyp_tupT_nil

/-- A bounded local type is a `localtype`. -/
theorem typedV_localV {lt : LocalType} (hb : LocalBnd lt) :
    TypedV (simEnv B) (.varT "localtype" []) (localV lt) :=
  Typing.typedV_closedCase findTyp_localtype rfl
    (Round5.Pos.hasTyp_tup2 (typedV_initV lt.init) (Instr30.typedV_val hb))

/-- **`{LOCALS ls}` is a typed context** when its local types are. -/
theorem ctxT_ctxL {ls : List Value} (hl : ∀ u ∈ ls, TypedV (simEnv B) (.varT "localtype" []) u) :
    CtxT B (ctxL ls) :=
  have hn : TypedV (simEnv B) (.iterT (.varT "resulttype" []) .opt) (.opt none) :=
    fun _ _ => hasTyp_iterT_opt_iff.2 (.inl rfl)
  have h0 {t : Typ} : TypedV (simEnv B) (.iterT t .list) (.list []) := Round5.RefOk.typedV_listNil
  Round5.Pos.typedV_struct Round6.Reading.findTyp_context <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of h0 <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of (typedV_list_iff.2 hl) <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_cons_of hn <| Round5.Pos.hasTypFields_cons_of h0 <|
    Round5.Pos.hasTypFields_one h0

/-- The image of Core's `{locals := L}` is a typed context when `L` is bounded. -/
theorem ctxT_locals {L : List LocalType} (hL : ∀ lt ∈ L, LocalBnd lt) : CtxT B (ctxL (L.map localV)) :=
  ctxT_ctxL fun u hu => by
    obtain ⟨lt, hlt, rfl⟩ := List.mem_map.1 hu
    exact typedV_localV (hL lt hlt)

/-! ## The rules -/

/-- `C.LOCALS[x.0]`. -/
def localsAtE : Exp :=
  .idxE (.dotE (.varE "C") "LOCALS") (.projE (.uncaseE (.varE "x") "%") (0 : Int))

/-- `%(ps) ->_xs %(rs)` with explicit lists. -/
def itLXE (ps xs rs : List Exp) : Exp :=
  .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.listE ps]), .listE xs, .caseE "%" (.tupE [.listE rs])])

set_option maxRecDepth 100000 in
/-- `Instr_ok/local.get`. -/
theorem ruleAt_localGet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 52
    (.ruleD "local.get" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "LOCAL.GET" (.varE "x"), itLXE [] [] [.varE "t"]])
      [.ifPr (.cmpE .eqOp .boolT localsAtE
        (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- `Instr_ok/local.set`. -/
theorem ruleAt_localSet : HasRuleAt (simEnv B) "Instr_ok" "%|-%:%" 53
    (.ruleD "local.set" [ctxP, .expP "x" (.varT "idx" []), .expP "t" (.varT "valtype" []),
      .expP "init" (.varT "init" [])] "%|-%:%"
      (.tupE [.varE "C", .caseE "LOCAL.SET" (.varE "x"), itLXE [.varE "t"] [.varE "x"] []])
      [.ifPr (.cmpE .eqOp .boolT localsAtE (.caseE "%%" (.tupE [.varE "init", .varE "t"])))]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Firing them -/

/-- `C.LOCALS[x.0]` reads the local at `x`. -/
theorem evalExp_localsAt {env : Env} {ρ : VarEnv} {ls : List Value} {n : Nat} {u : Value}
    (hC : ρ.findVal? "C" = some (ctxL ls)) (hx : ρ.findVal? "x" = some (idxV n))
    (hu : ls[n]? = some u) : EvalExp env ρ localsAtE u :=
  evalExp_idxE_iff.2 ⟨_, n, evalExp_dotE_iff.2 ⟨_, Sim.evalExp_var hC, rfl⟩,
    evalExp_projE_iff.2 ⟨_, evalExp_uncaseE_iff.2 (Sim.evalExp_var hx), le_refl _, rfl⟩,
    by simpa [Value.idx?] using hu⟩

/-- An equation whose sides evaluate alike holds. -/
theorem evalExp_eqTrue {env : Env} {ρ : VarEnv} {e₁ e₂ : Exp} {v : Value}
    (h₁ : EvalExp env ρ e₁ v) (h₂ : EvalExp env ρ e₂ v) :
    EvalExp env ρ (.cmpE .eqOp .boolT e₁ e₂) (.bool true) :=
  evalExp_cmpE_iff.2 ⟨v, v, h₁, h₂, Equiv.ExecNumeric.cmpValues_eq_true_iff.2 rfl⟩

/-- **`Instr_ok/local.get`** in `{LOCALS ls}`, at a set local. -/
theorem dd_localGet (O : ElseI) {ls : List Value} (hc : CtxT B (ctxL ls)) (x : LocalIdx)
    {t : CValType} (hb : Round4.tyBnd t = true) (hl : ls[x.toNat]? = some (localV ⟨.set, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxL ls, instrToV (.localGet x), itV [] [] [tyV t]]) :=
  dderivesB_of_ruleAt ruleAt_localGet (self_mem_conclAlts _)
    [("C", ctxL ls), ("x", idxV x.toNat), ("t", tyV t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3 evalExp_resNil evalExp_nil
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var rfl))
          evalExps_nil, rfl⟩)))))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_localsAt rfl rfl hl)
      (evalExp_case (evalExp_tup2 (Round6.AgreeSub.evalExp_atomE "SET") (Sim.evalExp_var rfl))))))

/-- **`Instr_ok/local.set`** in `{LOCALS ls}`, at any local. -/
theorem dd_localSet (O : ElseI) {ls : List Value} (hc : CtxT B (ctxL ls)) (x : LocalIdx)
    {i : Init} {t : CValType} (hb : Round4.tyBnd t = true)
    (hl : ls[x.toNat]? = some (localV ⟨i, t⟩)) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxL ls, instrToV (.localSet x), itV [tyV t] [idxV x.toNat] []]) :=
  dderivesB_of_ruleAt ruleAt_localSet (self_mem_conclAlts _)
    [("C", ctxL ls), ("x", idxV x.toNat), ("t", tyV t), ("init", initV i)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Typing.typedV_idx x _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (Instr30.typedV_val hb _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_initV i _ (valsOnly_bind _)) QuantsOk.nil))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_case (Sim.evalExp_var rfl))
      (evalExp_case (evalExp_tup3
        (evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var rfl))
          evalExps_nil, rfl⟩))
        (evalExp_list1 (Sim.evalExp_var rfl)) evalExp_resNil)))
    (premsB_one (.ifPr (evalExp_eqTrue (evalExp_localsAt rfl rfl hl)
      (evalExp_case (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl))))))

/-! ## Core's local typings, preserved -/

/-- The Core context with locals only, `{locals := L}`. -/
def ctxLoc (L : List LocalType) : Context := { locals := L }

/-- The sentence `{LOCALS L} ⊢ i : it`, a fact of `Instr_ok`. -/
def localSen (L : List LocalType) (i : Instr) (it : InstrType) : SSen :=
  .fact "Instr_ok" "%|-%:%" [] (.tuple [ctxL (L.map localV), instrToV i,
    Silmaril.SpecTec.Equiv.Validation.instrtypeV it])

/-- The local at `x` of `L`, read through the image. -/
theorem getElem?_localV {L : List LocalType} {n : Nat} {lt : LocalType} (h : L[n]? = some lt) :
    (L.map localV)[n]? = some (localV lt) := by
  rw [List.getElem?_map, h]
  rfl

/-- **`local.get` and `local.set` are preserved**: in a bounded context `{locals := L}`, a Core
typing of `local.get x` or `local.set x` is an `Instr_ok` fact of `simEnv B` in `ctxL`. -/
theorem local_preserves (O : ElseI) {L : List LocalType} (hL : ∀ lt ∈ L, LocalBnd lt)
    {i : Instr} {it : InstrType} (hi : (∃ x, i = .localGet x) ∨ (∃ x, i = .localSet x))
    (h : InstrOk (ctxLoc L) i it) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [ctxL (L.map localV), instrToV i, Silmaril.SpecTec.Equiv.Validation.instrtypeV it]) := by
  have hv : VariableInstrOk (ctxLoc L) i it := by
    rcases hi with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      cases h <;> first | assumption | (rename_i h; nomatch h)
  rcases hi with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · cases hv with
    | localGet hl =>
      exact dd_localGet O (ctxT_locals hL) x (hL _ (List.mem_of_getElem? hl)) (getElem?_localV hl)
  · cases hv with
    | localSet hl =>
      exact dd_localSet O (ctxT_locals hL) x (hL _ (List.mem_of_getElem? hl)) (getElem?_localV hl)

end Silmaril.Wasm.SpecTec.Institution.Instr30X
