module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Derive

/-!
# Instruction typing of the wasm-3.0 script: `Instrs_ok/seq` and `Instrs_ok/frame`

The two structural rules of `Instrs_ok` that compose and frame typings, located in `simEnv B` by
a kernel `rfl` (copied from `Raw/…/Scripts/Wasm30/Original/Part2.lean`), and fired under
`DDerivesB` at instruction types without initialised locals:

* `evalExp_withLocalsNil`: `$with_locals(C, [], [])` evaluates to `C` (its first clause);
* `dd_instrsSeq`: `Instrs_ok/seq` with `x_1* = x_2* = []` (so `init* = t* = []`, and the locals
  premise is an empty iteration);
* `dd_instrsFrame`: `Instrs_ok/frame` with `x* = []`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (listIterE ctxP CtxT)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (resE listP varP evalExp_resE evalExp_listIterV)

variable {B : Builtins}

/-! ## The rules -/

/-- The locals premise of `Instrs_ok/seq`. -/
def seqLocalsPrem : Prem :=
  .iterPr (.ifPr (.cmpE .eqOp .boolT (.idxE (.dotE (.varE "C") "LOCALS")
      (.projE (.uncaseE (.varE "x_1") "%") (0 : Int))) (.caseE "%%" (.tupE [.varE "init", .varE "t"]))))
    (.mk .list [.mk "init" (.varE "init*"), .mk "t" (.varE "t*"), .mk "x_1" (.varE "x_1*")])

/-- `$with_locals(C, x_1*, (SET t)*)`. -/
def withLocalsE : Exp :=
  .callE "with_locals" [.expA (.varE "C"), .expA (listIterE "x_1"),
    .expA (.iterE (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"]))
      (.mk .list [.mk "t" (.varE "t*")]))]

/-- The conclusion type of `Instrs_ok/seq`. -/
def itSeqE : Exp :=
  .caseE "%->_%%" (.tupE [resE "t_1", .catE (listIterE "x_1") (listIterE "x_2"), resE "t_3"])

set_option maxRecDepth 100000 in
/-- `Instrs_ok/seq`. -/
theorem ruleAt_instrsSeq : HasRuleAt (simEnv B) "Instrs_ok" "%|-%:%" 2
    (.ruleD "seq" [ctxP, listP "instr_1*" "instr", listP "instr_2*" "instr",
      listP "t_1*" "valtype", listP "x_1*" "idx", listP "x_2*" "idx", listP "t_3*" "valtype",
      listP "t_2*" "valtype", listP "init*" "init", listP "t*" "valtype"] "%|-%:%"
      (.tupE [.varE "C", .catE (listIterE "instr_1") (listIterE "instr_2"), itSeqE])
      [.rulePr "Instrs_ok" [] "%|-%:%" (.tupE [.varE "C", listIterE "instr_1", itE "t_1" "x_1" "t_2"]),
       seqLocalsPrem,
       .rulePr "Instrs_ok" [] "%|-%:%" (.tupE [withLocalsE, listIterE "instr_2", itE "t_2" "x_2" "t_3"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- `%(t* ++ t_1*) ->_x* %(t* ++ t_2*)`, the conclusion type of `Instrs_ok/frame`. -/
def itFrameE : Exp :=
  .caseE "%->_%%" (.tupE [.caseE "%" (.tupE [.catE (listIterE "t") (listIterE "t_1")]),
    listIterE "x", .caseE "%" (.tupE [.catE (listIterE "t") (listIterE "t_2")])])

set_option maxRecDepth 100000 in
/-- `Instrs_ok/frame`. -/
theorem ruleAt_instrsFrame : HasRuleAt (simEnv B) "Instrs_ok" "%|-%:%" 4
    (.ruleD "frame" [ctxP, listP "instr*" "instr", listP "t*" "valtype", listP "t_1*" "valtype",
      listP "x*" "idx", listP "t_2*" "valtype"] "%|-%:%"
      (.tupE [.varE "C", listIterE "instr", itFrameE])
      [.rulePr "Instrs_ok" [] "%|-%:%" (.tupE [.varE "C", listIterE "instr", itE "t_1" "x" "t_2"]),
       .rulePr "Resulttype_ok" [] "%|-%:OK" (.tupE [.varE "C", resE "t"])]) :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## `$with_locals(C, [], [])` -/

set_option maxRecDepth 100000 in
/-- `$with_locals`'s two clauses, the first one at `(C, [], [])`. -/
theorem findDef_withLocals : ∃ ps t c₂, (simEnv B).findDef? "with_locals" = some (ps, t,
    [.defD [ctxP] [.expA (.varE "C"), .expA (.listE []), .expA (.listE [])] (.varE "C") [], c₂]) :=
  ⟨_, _, _, rfl⟩

/-- **`$with_locals(C, [], [])` is `C`.** -/
theorem evalExp_withLocalsNil {ρ : VarEnv} {c : Value} (hρ : ρ.findDef? "with_locals" = none)
    (hC : EvalExp (simEnv B) ρ (.varE "C") c) (hx : EvalExp (simEnv B) ρ (listIterE "x_1") (.list []))
    (ht : EvalExp (simEnv B) ρ (.iterE (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"]))
      (.mk .list [.mk "t" (.varE "t*")])) (.list [])) :
    EvalExp (simEnv B) ρ withLocalsE c := by
  obtain ⟨ps, t, c₂, hd⟩ := findDef_withLocals (B := B)
  have ha : EvalArgs (simEnv B) ρ [.expA (.varE "C"), .expA (listIterE "x_1"),
      .expA (.iterE (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"]))
        (.mk .list [.mk "t" (.varE "t*")]))] [.val c, .val (.list []), .val (.list [])] :=
    Equiv.evalArgs_cons hC (Equiv.evalArgs_cons hx (Equiv.evalArgs_cons ht Equiv.evalArgs_nil))
  have hm : MatchArgs (simEnv B) VarEnv.empty
      [.expA (.varE "C"), .expA (.listE []), .expA (.listE [])]
      [.val c, .val (.list []), .val (.list [])] (VarEnv.empty.bindVal "C" c) :=
    matchArgs_cons (matchArg_expA (matchExp_varE rfl))
      (matchArgs_cons (matchArg_expA (Equiv.Execution.matchExp_listNil_iff.2 ⟨rfl, rfl⟩))
        (matchArgs_cons (matchArg_expA (Equiv.Execution.matchExp_listNil_iff.2 ⟨rfl, rfl⟩))
          matchArgs_nil))
  have hb : EvalExp (simEnv B) (VarEnv.empty.bindVal "C" c) (.varE "C") c := Sim.evalExp_var rfl
  exact evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd ha
    (tryClauses_hit hm (Equiv.Validation.premsHold_nil_iff.2 rfl) hb))

/-! ## Firing the rules -/

/-- The scope of `Instrs_ok/seq` without locals. -/
def seqσ (c : Value) (is₁ is₂ ts₁ ts₂ ts₃ : List Value) : List (IL.Id × Value) :=
  [("C", c), ("instr_1*", .list is₁), ("instr_2*", .list is₂), ("t_1*", .list ts₁),
    ("x_1*", .list []), ("x_2*", .list []), ("t_3*", .list ts₃), ("t_2*", .list ts₂),
    ("init*", .list []), ("t*", .list [])]

/-- A list of typed values is typed. -/
theorem typedV_nilList {s : IL.Id} : TypedV (simEnv B) (.iterT (.varT s []) .list) (.list []) :=
  typedV_list_iff.2 fun _ h => absurd h List.not_mem_nil

/-- The locals premise of `Instrs_ok/seq` holds when there are no locals to initialise. -/
theorem dpremB_seqLocals {O : ElseI} {els : Prop} {ρ : VarEnv}
    (h₁ : ρ.findVal? "init*" = some (.list [])) (h₂ : ρ.findVal? "t*" = some (.list []))
    (h₃ : ρ.findVal? "x_1*" = some (.list [])) : DPremB (simEnv B) O els ρ seqLocalsPrem :=
  .iterList (k := 0) (xvs := [("init", .list []), ("t", .list []), ("x_1", .list [])])
    (dls := [("init", []), ("t", []), ("x_1", [])]) (.inl rfl)
    ⟨2, by simp [evalDoms, domVar, domSrc, evalExp, h₁, h₂, h₃, Res.ofOption]⟩ (by simp)
    (by simp [domLists, Value.asList?]) (by simp) (by simp [iterRows])

/-- `t*` maps to the empty list in the scope of `Instrs_ok/seq`. -/
theorem evalExp_setsNil {ρ : VarEnv} (h : ρ.findVal? "t*" = some (.list [])) :
    EvalExp (simEnv B) ρ (.iterE (.caseE "%%" (.tupE [.caseE "SET" (.tupE []), .varE "t"]))
      (.mk .list [.mk "t" (.varE "t*")])) (.list []) := by
  have hm := Sim.evalExp_iterMap (env := simEnv B) (b := .caseE "%%"
    (.tupE [.caseE "SET" (.tupE []), .varE "t"])) (x := "t") (y := "t*") (ws := [])
    (g := fun w => w) h (fun _ hw => absurd hw List.not_mem_nil)
  simpa only [List.map_nil] using hm

/-- **`Instrs_ok/seq`** without locals, from `Instrs_ok` at both parts. -/
theorem dd_instrsSeq (O : ElseI) {c : Value} (hc : CtxT B c) {is₁ is₂ ts₁ ts₂ ts₃ : List Value}
    (hi₁ : ∀ i ∈ is₁, TypedV (simEnv B) (.varT "instr" []) i)
    (hi₂ : ∀ i ∈ is₂, TypedV (simEnv B) (.varT "instr" []) i)
    (ht₁ : ∀ t ∈ ts₁, TypedV (simEnv B) (.varT "valtype" []) t)
    (ht₂ : ∀ t ∈ ts₂, TypedV (simEnv B) (.varT "valtype" []) t)
    (ht₃ : ∀ t ∈ ts₃, TypedV (simEnv B) (.varT "valtype" []) t)
    (h₁ : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is₁, itV ts₁ [] ts₂]))
    (h₂ : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is₂, itV ts₂ [] ts₃])) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list (is₁ ++ is₂), itV ts₁ [] ts₃]) := by
  have hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃))
      [ctxP, listP "instr_1*" "instr", listP "instr_2*" "instr", listP "t_1*" "valtype",
        listP "x_1*" "idx", listP "x_2*" "idx", listP "t_3*" "valtype", listP "t_2*" "valtype",
        listP "init*" "init", listP "t*" "valtype"] :=
    QuantsOk.cons rfl (hc _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hi₁ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hi₂ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht₁ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht₃ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht₂ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_nilList _ (valsOnly_bind _)) QuantsOk.nil
  have hlist {x : IL.Id} {ws : List Value} (hx : x ≠ "_")
      (h : (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃)).findVal? (x ++ "*") = some (.list ws)) :
      EvalExp (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃)) (listIterE x) (.list ws) :=
    evalExp_listIterV h (findVal_bind1 hx)
  have hconcl : EvalExp (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃))
      (.tupE [.varE "C", .catE (listIterE "instr_1") (listIterE "instr_2"), itSeqE])
      (.tuple [c, .list (is₁ ++ is₂), itV ts₁ [] ts₃]) :=
    evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_cat (hlist (by decide) rfl) (hlist (by decide) rfl))
      (evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide)))
        (evalExp_cat (a := []) (b := []) (hlist (by decide) rfl) (hlist (by decide) rfl))
        (evalExp_resE rfl (findVal_bind1 (by decide)))))
  have hit₁ : EvalExp (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃))
      (itE "t_1" "x_1" "t_2") (itV ts₁ [] ts₂) :=
    evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide)))
      (hlist (by decide) rfl) (evalExp_resE rfl (findVal_bind1 (by decide))))
  have hit₂ : EvalExp (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃))
      (itE "t_2" "x_2" "t_3") (itV ts₂ [] ts₃) :=
    evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide)))
      (hlist (by decide) rfl) (evalExp_resE rfl (findVal_bind1 (by decide))))
  have hwl : EvalExp (simEnv B) (VarEnv.empty.bindVals (seqσ c is₁ is₂ ts₁ ts₂ ts₃)) withLocalsE c :=
    evalExp_withLocalsNil (Memory.findDef_bindVals_empty _ _) (Sim.evalExp_var rfl)
      (hlist (by decide) rfl) (evalExp_setsNil rfl)
  refine dderivesB_of_ruleAt ruleAt_instrsSeq (self_mem_conclAlts _) (seqσ c is₁ is₂ ts₁ ts₂ ts₃)
    hq hconcl ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (hlist (by decide) rfl) hit₁) h₁
  · exact dpremB_seqLocals rfl rfl rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 hwl (hlist (by decide) rfl) hit₂) h₂

/-- The scope of `Instrs_ok/frame` without locals. -/
def frameσ (c : Value) (is ts ts₁ ts₂ : List Value) : List (IL.Id × Value) :=
  [("C", c), ("instr*", .list is), ("t*", .list ts), ("t_1*", .list ts₁), ("x*", .list []),
    ("t_2*", .list ts₂)]

/-- **`Instrs_ok/frame`** without locals, from `Instrs_ok` and `Resulttype_ok` at the frame. -/
theorem dd_instrsFrame (O : ElseI) {c : Value} (hc : CtxT B c) {is ts ts₁ ts₂ : List Value}
    (hi : ∀ i ∈ is, TypedV (simEnv B) (.varT "instr" []) i)
    (ht : ∀ t ∈ ts, TypedV (simEnv B) (.varT "valtype" []) t)
    (ht₁ : ∀ t ∈ ts₁, TypedV (simEnv B) (.varT "valtype" []) t)
    (ht₂ : ∀ t ∈ ts₂, TypedV (simEnv B) (.varT "valtype" []) t)
    (h : DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, itV ts₁ [] ts₂]))
    (hr : DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" [] (.tuple [c, .case "%" (.tuple [.list ts])])) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list is, itV (ts ++ ts₁) [] (ts ++ ts₂)]) := by
  have hq : QuantsOk (simEnv B) (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂))
      [ctxP, listP "instr*" "instr", listP "t*" "valtype", listP "t_1*" "valtype",
        listP "x*" "idx", listP "t_2*" "valtype"] :=
    QuantsOk.cons rfl (hc _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 hi _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht₁ _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_nilList _ (valsOnly_bind _)) <|
    QuantsOk.cons rfl (typedV_list_iff.2 ht₂ _ (valsOnly_bind _)) QuantsOk.nil
  have hlist {x : IL.Id} {ws : List Value} (hx : x ≠ "_")
      (h : (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂)).findVal? (x ++ "*") = some (.list ws)) :
      EvalExp (simEnv B) (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂)) (listIterE x) (.list ws) :=
    evalExp_listIterV h (findVal_bind1 hx)
  have hres {ws : List Value} {e : Exp} (h : EvalExp (simEnv B)
      (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂)) e (.list ws)) :
      EvalExp (simEnv B) (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂)) (.caseE "%" (.tupE [e]))
        (.case "%" (.tuple [.list ws])) :=
    evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons h evalExps_nil, rfl⟩)
  have hconcl : EvalExp (simEnv B) (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂))
      (.tupE [.varE "C", listIterE "instr", itFrameE])
      (.tuple [c, .list is, itV (ts ++ ts₁) [] (ts ++ ts₂)]) :=
    evalExp_tup3 (Sim.evalExp_var rfl) (hlist (by decide) rfl)
      (evalExp_case (evalExp_tup3 (hres (evalExp_cat (hlist (by decide) rfl) (hlist (by decide) rfl)))
        (hlist (by decide) rfl) (hres (evalExp_cat (hlist (by decide) rfl) (hlist (by decide) rfl)))))
  have hit : EvalExp (simEnv B) (VarEnv.empty.bindVals (frameσ c is ts ts₁ ts₂))
      (itE "t_1" "x" "t_2") (itV ts₁ [] ts₂) :=
    evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide)))
      (hlist (by decide) rfl) (evalExp_resE rfl (findVal_bind1 (by decide))))
  refine dderivesB_of_ruleAt ruleAt_instrsFrame (self_mem_conclAlts _) (frameσ c is ts ts₁ ts₂)
    hq hconcl ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup3 (Sim.evalExp_var rfl) (hlist (by decide) rfl) hit) h
  · exact .rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl)
      (evalExp_resE rfl (findVal_bind1 (by decide)))) hr

end Silmaril.Wasm.SpecTec.Institution.Instr30
