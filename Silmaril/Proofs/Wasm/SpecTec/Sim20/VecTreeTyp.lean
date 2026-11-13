module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecTreeExit

/-!
# Instruction typing from `admininstr` typing, in `simEnv20V`

`trap-vals`, `br-zero`, `br-succ`, `return-frame` and `return-label` quantify the code after the
redex as `instr*`, while the forward invariant `VecWhole.TypV` types code as `admininstr*`. In the
corrected script the cases of `instr` are a prefix of the cases of `admininstr`
(`take_adminCasesV`, kernel `rfl`), and a variant case is typed by the first case of its name.
So a case typed as an `admininstr` whose name is a case of `instr` is typed as an `instr`
(`typedV_instr_of_admin`).

* `hasTypCase_of_append`: a case typed in `l ++ m` whose name occurs in `l` is typed in `l`.
* **`typedV_instr_of_admin`**, and for the instructions of straight-line vector code
  (`VecWhole.vecOkI`) **`typedV_instrV_of_vecOk`**, `typedV_instrsV_of_vecOk` (lists, as
  `expression is`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)
open Silmaril.Wasm.SpecTec.Sim20.VecFix (simEnv20V variantCases instrFixV20 adminFixV20
  findTyp_admin20V)

variable {B : Builtins}

/-! ## Variant cases in a prefix -/

/-- The case names of a variant. -/
def caseOps (cs : List TypCase) : List MixopS := cs.map fun | .mk o _ _ _ => o

/-- **A case typed in `l ++ m` whose name occurs in `l` is typed in `l`.** -/
theorem hasTypCase_of_append {env : Env} {ρ : VarEnv} {m : List TypCase} {op : MixopS}
    {w : Value} : ∀ {l : List TypCase}, op ∈ caseOps l →
      HasTypCase env ρ (l ++ m) op w → HasTypCase env ρ l op w
  | [], hop, _ => by simp [caseOps] at hop
  | .mk o t qs prems :: l, hop, h => by
    by_cases ho : o = op
    · exact (hasTypCase_cons_hit_iffQ ho).2 ((hasTypCase_cons_hit_iffQ ho).1 h)
    · have hop' : op ∈ caseOps l := by
        simp only [caseOps, List.map_cons, List.mem_cons] at hop
        rcases hop with h' | h'
        · exact absurd h'.symm ho
        · exact h'
      exact (hasTypCase_cons_miss_iff ho).2
        (hasTypCase_of_append hop' ((hasTypCase_cons_miss_iff ho).1 h))

/-! ## `instr` and `admininstr` in `simEnv20V` -/

set_option maxRecDepth 100000 in
theorem findTyp_instrV : (simEnv20V B).findTyp? "instr" =
    some ([], [.instD [] [] (.variantT (variantCases instrFixV20))]) := rfl

set_option maxRecDepth 100000 in
/-- **The cases of `instr` are a prefix of those of `admininstr`** (kernel `rfl`). -/
theorem take_adminCasesV : (variantCases adminFixV20).take (variantCases instrFixV20).length =
    variantCases instrFixV20 := by
  with_unfolding_all rfl

theorem adminCasesV_eq : variantCases adminFixV20 = variantCases instrFixV20 ++
    (variantCases adminFixV20).drop (variantCases instrFixV20).length := by
  conv_lhs => rw [← List.take_append_drop (variantCases instrFixV20).length
    (variantCases adminFixV20), take_adminCasesV]

/-- **A case typed as an `admininstr` of `simEnv20V`, named as a case of `instr`, is an
`instr`.** -/
theorem typedV_instr_of_admin {op : MixopS} {w : Value}
    (hop : op ∈ caseOps (variantCases instrFixV20))
    (h : TypedV (simEnv20V B) (.varT "admininstr" []) (.case op w)) :
    TypedV (simEnv20V B) (.varT "instr" []) (.case op w) := by
  obtain ⟨op', w', he, hc⟩ := hasTypDef_variantT_iff.1
    (Whole.hasTypDef_of_closed findTyp_admin20V (h _ Whole.valsOnly_empty))
  obtain ⟨rfl, rfl⟩ : op = op' ∧ w = w' := by simpa using he
  rw [adminCasesV_eq] at hc
  have hc' := hasTypCase_of_append hop hc
  exact fun _ hρ => hasTyp_varT_case (by simp [localTyp?, VarEnv.findTyp?, hρ.1]) findTyp_instrV
    Equiv.evalArgs_nil matchArgs_nil hc'

/-! ## The instructions of straight-line vector code -/

/-- The case names of the instructions of straight-line vector code. -/
def vecOps : List MixopS :=
  ["CONST", "VCONST", "REF.NULL", "VUNOP", "VBINOP", "VRELOP", "VEXTRACT_LANE"]

set_option maxRecDepth 100000 in
theorem vecOps_sub : ∀ op ∈ vecOps, op ∈ caseOps (variantCases instrFixV20) := by
  intro op hop
  simp only [vecOps, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_unfolding_all decide

/-- Each instruction of straight-line vector code is a case named in `vecOps`. -/
theorem instrToV_vecOk {i : V2.Instr} (h : VecWhole.vecOkI i = true) :
    ∃ op ∈ vecOps, ∃ w, instrToV i = .case op w := by
  cases i <;> simp only [VecWhole.vecOkI, Bool.false_eq_true] at h <;>
    exact ⟨_, by simp [vecOps], _, rfl⟩

/-- **An instruction of straight-line vector code typed as an `admininstr` of `simEnv20V` is an
`instr` there.** -/
theorem typedV_instrV_of_vecOk {i : V2.Instr} (hi : VecWhole.vecOkI i = true)
    (h : TypedV (simEnv20V B) (.varT "admininstr" []) (instrToV i)) :
    TypedV (simEnv20V B) (.varT "instr" []) (instrToV i) := by
  obtain ⟨op, hop, w, he⟩ := instrToV_vecOk hi
  rw [he] at h ⊢
  exact typedV_instr_of_admin (vecOps_sub op hop) h

/-- **The same for a list of instructions**, as the code `expression is`. -/
theorem typedV_instrsV_of_vecOk {is : List V2.Instr} (hi : is.all VecWhole.vecOkI = true)
    (h : TypedV (simEnv20V B) adminsTy (.list (adminsToV (expression is)))) :
    TypedV (simEnv20V B) Pure.instrsT (.list (adminsToV (expression is))) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  have hu' : u ∈ is.map instrToV := by
    simpa [expression, Pure.adminsToV_eq_map, adminToV] using hu
  obtain ⟨i, hm, rfl⟩ := List.mem_map.1 hu'
  exact typedV_instrV_of_vecOk (List.all_eq_true.1 hi i hm)
    (Sim.typedV_list_iff.1 h _ (by simpa [expression, Pure.adminsToV_eq_map, adminToV] using ⟨i, hm, rfl⟩))

end Silmaril.Wasm.SpecTec.Sim20.VecTree
