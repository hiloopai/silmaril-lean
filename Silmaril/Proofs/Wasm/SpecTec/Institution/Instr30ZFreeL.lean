module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZFree

/-!
# Module typing of the wasm-3.0 script, `$funcidx_nonfuncs` at any list of memories

`Instr30ZFree` evaluated `$free_module` and `$funcidx_nonfuncs` at one memory. Its pieces are
already generic in the list (`evalExp_flistIter`, `tc_flistRep`); here the pattern match, the body
and the argument of `$funcidx_module` are built for `memModuleV mts`, any `mts`, from per-shape
lemmas: `evalExp_star` (an iteration `x*` evaluates to the list `x*` is bound to) and
`evalExp_pctStar` (`%(x*)`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d310 Original.d311 Original.d384)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (defClauses free0 matchExp_tupE' matchExps_cons'
  matchExps_nil' matchExp_pctList matchExp_optVar fmBody fmPats fm_clauses fd_fmod fd_fm fnf_clauses
  fmod_clauses matchExp_listVar)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil)

variable {B : Builtins}

/-! ## Iterations over a bound list -/

/-- The newest binding of `x` is found. -/
theorem findVal_bindVals_one (ρ : VarEnv) {x : IL.Id} (hx : x ≠ "_") (w : Value) :
    (ρ.bindVals [(x, w)]).findVal? x = some w := by
  simp [VarEnv.bindVals, VarEnv.findVal?, Map.binds, Map.bind, hx]

/-- **`x*` evaluates to the list `x*` is bound to.** -/
theorem evalExp_star {env : Env} {ρ : VarEnv} {x xs : IL.Id} {ws : List Value} (hx : x ≠ "_")
    (h : ρ.findVal? xs = some (.list ws)) :
    EvalExp env ρ (.iterE (.varE x) (.mk .list [.mk x (.varE xs)])) (.list ws) := by
  have := Sim.evalExp_iterMap (env := env) (g := id) (b := .varE x) (x := x) h
    (fun w _ => Sim.evalExp_var (findVal_bindVals_one ρ hx w))
  simpa using this

/-- **`%(x*)` evaluates to `%(ws)`** where `x*` is bound to `ws`. -/
theorem evalExp_pctStar {env : Env} {ρ : VarEnv} {x xs : IL.Id} {ws : List Value} (hx : x ≠ "_")
    (h : ρ.findVal? xs = some (.list ws)) :
    EvalExp env ρ (.caseE "%" (.tupE [.iterE (.varE x) (.mk .list [.mk x (.varE xs)])]))
      (.case "%" (.tuple [.list ws])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_star hx h) evalExps_nil, rfl⟩)

/-- `%([])`, written as a literal. -/
theorem evalExp_pctNilE {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.listE []])) pctNil :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons Instr30.evalExp_nil evalExps_nil, rfl⟩)

/-! ## `$free_module` -/

/-- The scope `$free_module`'s pattern binds at `memModuleV mts`. -/
def fmρL (mts : List Silmaril.Wasm.MemoryType) : VarEnv :=
  (((((((((((VarEnv.empty.bindVal "type*" (.list [])).bindVal "import*" (.list [])).bindVal
    "tag*" (.list [])).bindVal "global*" (.list [])).bindVal "mem*" (.list (mts.map memV))).bindVal
    "table*" (.list [])).bindVal "func*" (.list [])).bindVal "data*" (.list [])).bindVal
    "elem*" (.list [])).bindVal "start?" (.opt none)).bindVal "export*" (.list []))

set_option maxRecDepth 100000 in
/-- **`$free_module`'s pattern matches `memModuleV mts`.** -/
theorem fm_matchL (mts : List Silmaril.Wasm.MemoryType) :
    MatchArgs (simEnv B) VarEnv.empty fmPats [.val (memModuleV mts)] (fmρL mts) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
    (matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_caseE (matchExp_tupE' (matchExps_cons'
      (RefOk.matchExp_star (by rfl) (by rfl) (by decide)) matchExps_nil'))) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_optVar (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) matchExps_nil')))) matchArgs_nil

/-- **`$free_module`'s body is `free0`** at `memModuleV mts`. -/
theorem fm_bodyL (mts : List Silmaril.Wasm.MemoryType) :
    EvalExp (simEnv B) (fmρL mts) fmBody free0 :=
  evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0
    (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0
      (evalExp_flistIter rfl rfl forall_mem_nil') (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl fun w hw => by
        obtain ⟨mt, -, rfl⟩ := List.mem_map.1 hw
        exact evalExp_fmem mt rfl (findVal_bindVals_one _ (by decide) _)))
      (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_foptNone rfl rfl))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_flistIter rfl rfl forall_mem_nil')

/-- **`$funcidx_module(memModuleV mts) = []`.** -/
theorem tc_funcidxModuleL (mts : List Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d311) [.val (memModuleV mts)] (.list []) :=
  fmod_clauses ▸ tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_dotE_iff.2 ⟨free0, evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (Sim.evalExp_var rfl) Equiv.evalArgs_nil, fd_fmod,
      .inl (fm_clauses ▸ tryClauses_hit (fm_matchL mts) (Equiv.Validation.premsHold_nil_iff.2 rfl)
        (fm_bodyL mts))⟩), rfl⟩)

/-! ## `$funcidx_nonfuncs` -/

/-- The scope `$funcidx_nonfuncs`'s pattern binds at `([], MEMORY mt*, [], [], [])`. -/
def fnfρL (mts : List Silmaril.Wasm.MemoryType) : VarEnv :=
  ((((VarEnv.empty.bindVal "global*" (.list [])).bindVal "mem*" (.list (mts.map memV))).bindVal
    "table*" (.list [])).bindVal "elem*" (.list [])).bindVal "export*" (.list [])

/-- `$funcidx_nonfuncs`'s body builds `memModuleV mts` in that scope. -/
theorem evalExp_fnfModuleL (mts : List Silmaril.Wasm.MemoryType) :
    EvalExp (simEnv B) (fnfρL mts) (match Instr30X.fnfBody with
      | .callE _ [.expA e] => e | e => e) (memModuleV mts) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_,
    evalExps_cons evalExp_pctNilE <| evalExps_cons evalExp_pctNilE <|
    evalExps_cons evalExp_pctNilE <| evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <| evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons evalExp_pctNilE <| evalExps_cons evalExp_pctNilE <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) <|
    evalExps_cons (evalExp_optE_none_iff.2 rfl) <|
    evalExps_cons (evalExp_pctStar (by decide) rfl) evalExps_nil, rfl⟩)

/-- **`$funcidx_nonfuncs(%%%%%([], MEMORY mt*, [], [], [])) = []`**, at every list of memory
types. -/
theorem tc_funcidxNonfuncsL (mts : List Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d384)
      [.val (.case "%%%%%" (.tuple [.list [], .list (mts.map memV), .list [], .list [], .list []]))]
      (.list []) :=
  fnf_clauses ▸ tryClauses_hit (ρ₀ := fnfρL mts)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
      (matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (RefOk.matchExp_star (by rfl) (by rfl) (by decide)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) <| matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) matchExps_nil')))) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (evalExp_fnfModuleL mts) Equiv.evalArgs_nil, fd_fm,
      .inl (tc_funcidxModuleL mts)⟩))

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
