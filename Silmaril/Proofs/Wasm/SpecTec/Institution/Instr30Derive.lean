module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30Rules

/-!
# Instruction typing of the wasm-3.0 script: firing the rules under `DDerivesB`

One lemma per rule of `Instr30Rules`, in any typed context `c` and under every reading `O` of
`otherwise`, from typed arguments and derivations of the premises:

* `dd_nop`, `dd_unreachable`, `dd_drop`: `Instr_ok`;
* `dd_instrtypeOk`: `Instrtype_ok` at an instruction type without initialised locals;
* `dd_instrsEmpty`, `dd_instrsInstr`: `Instrs_ok`.

Instruction types are written `itV ps xs rs` (`%(ps) ->_xs %(rs)`); `instrtypeV it` is
`itV` of its three components (`instrtypeV_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt instrtypeV tyV idxV)
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeSub (CtxT evalExp_atomE)
open Silmaril.Wasm.SpecTec.Sim.Round6.AgreeOk (evalExp_resE dpremB_iter2)

variable {B : Builtins}

/-- `%(ps) ->_xs %(rs)`, an instruction type value. -/
def itV (ps xs rs : List Value) : Value :=
  .case "%->_%%" (.tuple [.case "%" (.tuple [.list ps]), .list xs, .case "%" (.tuple [.list rs])])

/-- The encoding of a Core instruction type is an `itV`. -/
theorem instrtypeV_eq (it : InstrType) :
    instrtypeV it = itV (it.params.map tyV) (it.inits.map idxV) (it.results.map tyV) := rfl

/-- `[]` evaluates to the empty list. -/
theorem evalExp_nil {env : Env} {ρ : VarEnv} : EvalExp env ρ (.listE []) (.list []) :=
  evalExp_listE_iff.2 ⟨[], evalExps_nil, rfl⟩

/-- `%([])` evaluates to the empty result type. -/
theorem evalExp_resNil {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.listE []])) (.case "%" (.tuple [.list []])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons evalExp_nil evalExps_nil, rfl⟩)

/-- `%([]) ->_[] %([])` evaluates to `itV [] [] []`. -/
theorem evalExp_itNil {env : Env} {ρ : VarEnv} : EvalExp env ρ itNilE (itV [] [] []) :=
  evalExp_case (evalExp_tup3 evalExp_resNil evalExp_nil evalExp_resNil)

/-- A variable bound in front of a scope is found. -/
theorem findVal_bind1 {ρ : VarEnv} {x : IL.Id} (hx : x ≠ "_") (w : Value) :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.findVal?, VarEnv.bindVals, Map.binds, Map.bind, hx]

/-! ## `Instr_ok` -/

/-- **`Instr_ok/nop`.** -/
theorem dd_nop (O : ElseI) {c : Value} (hc : CtxT B c) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, .case "NOP" (.tuple []), itV [] [] []]) :=
  dderivesB_of_ruleAt ruleAt_nop (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_atomE "NOP") evalExp_itNil) premsB_nil

/-- The scope of `Instr_ok/unreachable`. -/
def unreachσ (c : Value) (ps rs : List Value) : List (IL.Id × Value) :=
  [("C", c), ("t_1*", .list ps), ("t_2*", .list rs)]

/-- `itUnreachE` evaluates to `itV ps [] rs` in its scope. -/
theorem evalExp_itUnreach {c : Value} {ps rs : List Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (unreachσ c ps rs)) itUnreachE (itV ps [] rs) :=
  evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide))) evalExp_nil
    (evalExp_resE rfl (findVal_bind1 (by decide))))

/-- **`Instr_ok/unreachable`**, from `Instrtype_ok` at its type. -/
theorem dd_unreachable (O : ElseI) {c : Value} (hc : CtxT B c) {ps rs : List Value}
    (hps : ∀ t ∈ ps, TypedV (simEnv B) (.varT "valtype" []) t)
    (hrs : ∀ t ∈ rs, TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Instrtype_ok" "%|-%:OK" [] (.tuple [c, itV ps [] rs])) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case "UNREACHABLE" (.tuple []), itV ps [] rs]) :=
  dderivesB_of_ruleAt ruleAt_unreachable (self_mem_conclAlts _) (unreachσ c ps rs)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hps _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hrs _ (valsOnly_bind _)) QuantsOk.nil)))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_atomE "UNREACHABLE") evalExp_itUnreach)
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) evalExp_itUnreach) hd))

/-- **`Instr_ok/drop`**, from `Valtype_ok` at the dropped type. -/
theorem dd_drop (O : ElseI) {c t : Value} (hc : CtxT B c)
    (ht : TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Valtype_ok" "%|-%:OK" [] (.tuple [c, t])) :
    DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" []
      (.tuple [c, .case "DROP" (.tuple []), itV [t] [] []]) :=
  dderivesB_of_ruleAt ruleAt_drop (self_mem_conclAlts _) [("C", c), ("t", t)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (ht _ (valsOnly_bind _))
      QuantsOk.nil))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_atomE "DROP")
      (evalExp_case (evalExp_tup3 (evalExp_case (evalExp_tupE_iff.2
        ⟨_, evalExps_cons (evalExp_list1 (Sim.evalExp_var rfl)) evalExps_nil, rfl⟩)) evalExp_nil
        evalExp_resNil)))
    (premsB_one (.rulePr (evalArgs_nil _ _) (evalExp_tup2 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl)) hd))

/-! ## `Instrtype_ok` -/

/-- The scope of `Instrtype_ok` without locals. -/
def itσ (c : Value) (ps rs : List Value) : List (IL.Id × Value) :=
  [("C", c), ("t_1*", .list ps), ("x*", .list []), ("t_2*", .list rs), ("lct*", .list [])]

/-- **`Instrtype_ok`** at a type without initialised locals, from `Resulttype_ok` at both sides. -/
theorem dd_instrtypeOk (O : ElseI) {c : Value} (hc : CtxT B c) {ps rs : List Value}
    (hps : ∀ t ∈ ps, TypedV (simEnv B) (.varT "valtype" []) t)
    (hrs : ∀ t ∈ rs, TypedV (simEnv B) (.varT "valtype" []) t)
    (h₁ : DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" [] (.tuple [c, .case "%" (.tuple [.list ps])]))
    (h₂ : DDerivesB (simEnv B) O "Resulttype_ok" "%|-%:OK" [] (.tuple [c, .case "%" (.tuple [.list rs])])) :
    DDerivesB (simEnv B) O "Instrtype_ok" "%|-%:OK" [] (.tuple [c, itV ps [] rs]) := by
  have h0 {s : IL.Id} : TypedV (simEnv B) (.iterT (.varT s []) .list) (.list []) :=
    typedV_list_iff.2 fun _ h => absurd h List.not_mem_nil
  refine dderivesB_of_ruleAt ruleAt_instrtypeOk (self_mem_conclAlts _) (itσ c ps rs)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hps _ (valsOnly_bind _)) (QuantsOk.cons rfl (h0 _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_list_iff.2 hrs _ (valsOnly_bind _))
      (QuantsOk.cons rfl (h0 _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_case (evalExp_tup3
      (evalExp_resE rfl (findVal_bind1 (by decide)))
      (Round6.AgreeOk.evalExp_listIterV (x := "x") rfl (findVal_bind1 (by decide)))
      (evalExp_resE rfl (findVal_bind1 (by decide)))))) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact .rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_resE rfl (findVal_bind1 (by decide)))) h₁
  · exact .rulePr (evalArgs_nil _ _)
      (evalExp_tup2 (Sim.evalExp_var rfl) (evalExp_resE rfl (findVal_bind1 (by decide)))) h₂
  · exact dpremB_iter2 (ps := []) rfl rfl fun _ h => absurd h List.not_mem_nil

/-! ## `Instrs_ok` -/

/-- **`Instrs_ok/empty`.** -/
theorem dd_instrsEmpty (O : ElseI) {c : Value} (hc : CtxT B c) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list [], itV [] [] []]) :=
  dderivesB_of_ruleAt ruleAt_instrsEmpty (self_mem_conclAlts _) [("C", c)]
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) QuantsOk.nil)
    (evalExp_tup3 (Sim.evalExp_var rfl) evalExp_nil evalExp_itNil) premsB_nil

/-- The scope of `Instrs_ok/instr`. -/
def instrσ (c i : Value) (ps xs rs : List Value) : List (IL.Id × Value) :=
  [("C", c), ("instr", i), ("t_1*", .list ps), ("x*", .list xs), ("t_2*", .list rs)]

/-- `itE "t_1" "x" "t_2"` evaluates to `itV ps xs rs` in the scope of `Instrs_ok/instr`. -/
theorem evalExp_itInstr {c i : Value} {ps xs rs : List Value} :
    EvalExp (simEnv B) (VarEnv.empty.bindVals (instrσ c i ps xs rs)) (itE "t_1" "x" "t_2")
      (itV ps xs rs) :=
  evalExp_case (evalExp_tup3 (evalExp_resE rfl (findVal_bind1 (by decide)))
    (Round6.AgreeOk.evalExp_listIterV (x := "x") rfl (findVal_bind1 (by decide)))
    (evalExp_resE rfl (findVal_bind1 (by decide))))

/-- **`Instrs_ok/instr`**, from `Instr_ok`. -/
theorem dd_instrsInstr (O : ElseI) {c i : Value} (hc : CtxT B c)
    (hi : TypedV (simEnv B) (.varT "instr" []) i) {ps xs rs : List Value}
    (hps : ∀ t ∈ ps, TypedV (simEnv B) (.varT "valtype" []) t)
    (hxs : ∀ x ∈ xs, TypedV (simEnv B) (.varT "idx" []) x)
    (hrs : ∀ t ∈ rs, TypedV (simEnv B) (.varT "valtype" []) t)
    (hd : DDerivesB (simEnv B) O "Instr_ok" "%|-%:%" [] (.tuple [c, i, itV ps xs rs])) :
    DDerivesB (simEnv B) O "Instrs_ok" "%|-%:%" [] (.tuple [c, .list [i], itV ps xs rs]) :=
  dderivesB_of_ruleAt ruleAt_instrsInstr (self_mem_conclAlts _) (instrσ c i ps xs rs)
    (QuantsOk.cons rfl (hc _ (valsOnly_bind _)) (QuantsOk.cons rfl (hi _ (valsOnly_bind _))
      (QuantsOk.cons rfl (typedV_list_iff.2 hps _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hxs _ (valsOnly_bind _)) (QuantsOk.cons rfl
      (typedV_list_iff.2 hrs _ (valsOnly_bind _)) QuantsOk.nil)))))
    (evalExp_tup3 (Sim.evalExp_var rfl) (evalExp_list1 (Sim.evalExp_var rfl)) evalExp_itInstr)
    (premsB_one (.rulePr (evalArgs_nil _ _)
      (evalExp_tup3 (Sim.evalExp_var rfl) (Sim.evalExp_var rfl) evalExp_itInstr) hd))

end Silmaril.Wasm.SpecTec.Institution.Instr30
