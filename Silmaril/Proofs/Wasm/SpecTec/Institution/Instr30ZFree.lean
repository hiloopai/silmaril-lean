module

public import Silmaril.Wasm.SpecTec.Institution.Instr30X.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Institution.Instr30Z.Defs

/-!
# Module typing of the wasm-3.0 script, `$free_mem` and `$free_list` at one memory
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (callDef_iff)
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Scripts.Wasm30 (Original.d74 Original.d75 Original.d193 Original.d204 Original.d299
  Original.d310 Original.d311 Original.d384)
open Silmaril.Wasm.SpecTec.Institution.Instr30X (defClauses defSig free0 fd_flist fd_fopt matchExp_tupE'
  matchExps_cons' matchExps_nil' matchExp_pctList matchExp_optVar fmBody fmPats fm_clauses fd_fmod fd_fm
  fnfPats fnfBody fnf_clauses fmod_clauses matchExp_listVar)
open Silmaril.Wasm.SpecTec.Institution.Instr30 (pctNil)

variable {B : Builtins}

set_option maxRecDepth 100000 in
/-- `$free_mem`'s clauses. -/
theorem fd_fmem : (simEnv B).findDef? "free_mem" =
    some ((defSig Original.d299).1, (defSig Original.d299).2, defClauses Original.d299) := rfl

set_option maxRecDepth 100000 in
/-- `$free_memtype`'s clauses. -/
theorem fd_fmemtype : (simEnv B).findDef? "free_memtype" =
    some ((defSig Original.d204).1, (defSig Original.d204).2, defClauses Original.d204) := rfl

set_option maxRecDepth 100000 in
/-- `$free_addrtype`'s clauses. -/
theorem fd_faddr : (simEnv B).findDef? "free_addrtype" =
    some ((defSig Original.d193).1, (defSig Original.d193).2, defClauses Original.d193) := rfl

/-- `$free_list([]) = free0`. -/
theorem tc_flistNil : TryClauses (simEnv B) (defClauses Original.d75) [.val (.list [])] free0 :=
  ⟨20, by
    simp [free0, tryClauses, matchArg, matchExp, premsHold, VarEnv.empty,
      Res.elimUndef, Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure, matchArgs.eq_def,
      argSubOk, matchExps, defClauses, Original.d75, evalExp, evalExps, evalExpFields, Value.asList?, Functor.map, Except.map]⟩

/-- `free0 ⊕ free0 = free0`. -/
theorem comp_free0 : Value.comp? free0 free0 = some free0 := rfl

/-- `$free_list([free0]) = free0`, by its second clause `[free] ++ free'*`. -/
theorem tc_flistOne : TryClauses (simEnv B) (defClauses Original.d75) [.val (.list [free0])] free0 := by
  obtain ⟨n, hn⟩ := RefOk.matchArg_nil_undef (env := simEnv B) (ρ := VarEnv.empty) (a := free0)
    (al := [])
  refine tryClauses_skip_match (matchArgs_cons_undef ⟨n, hn⟩) (tryClauses_hit (ρ₀ :=
    ((VarEnv.empty.bindVal "free" free0).bindVal "free'*" (.list [])))
    (matchArgs_cons (matchArg_expA (RefOk.matchExp_consPat rfl rfl rfl (by decide)))
      matchArgs_nil) (Equiv.Validation.premsHold_nil_iff.2 rfl) ?_)
  refine evalExp_compE_iff.2 ⟨free0, free0, Sim.evalExp_var rfl, evalExp_callE_iff.2
    (callDef_iff.2 ⟨_, _, _, _, ⟨10, ?_⟩, fd_flist, .inl tc_flistNil⟩), comp_free0⟩
  simp [evalArgs, evalArg, evalExp, evalIterE, evalIterList, evalRounds, iterRows, Value.asList?,
    evalDoms, domSrc, domVar, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?, Bind.bind,
    Except.bind, Res.ofOption, Pure.pure, Except.pure, Functor.map, Except.map]

/-- `$free_list(free0 :: ws) = free0` when `$free_list(ws) = free0`, by the clause
`[free] ++ free'*`. -/
theorem tc_flistCons {ws : List Value}
    (ih : TryClauses (simEnv B) (defClauses Original.d75) [.val (.list ws)] free0) :
    TryClauses (simEnv B) (defClauses Original.d75) [.val (.list (free0 :: ws))] free0 := by
  obtain ⟨n, hn⟩ := RefOk.matchArg_nil_undef (env := simEnv B) (ρ := VarEnv.empty) (a := free0)
    (al := ws)
  have hl : EvalExp (simEnv B) ((VarEnv.empty.bindVal "free" free0).bindVal "free'*" (.list ws))
      (.iterE (.varE "free'") (.mk .list [.mk "free'" (.varE "free'*")])) (.list ws) := by
    have h := Sim.evalExp_iterMap (env := simEnv B) (b := .varE "free'") (x := "free'")
      (g := id) (ws := ws) (y := "free'*")
      (ρ := (VarEnv.empty.bindVal "free" free0).bindVal "free'*" (.list ws))
      rfl (fun w _ => Sim.evalExp_var (by simp [VarEnv.bindVals, VarEnv.findVal?, VarEnv.bindVal,
        Map.binds, Map.bind]))
    simpa using h
  exact tryClauses_skip_match (matchArgs_cons_undef ⟨n, hn⟩) (tryClauses_hit
    (ρ₀ := ((VarEnv.empty.bindVal "free" free0).bindVal "free'*" (.list ws)))
    (matchArgs_cons (matchArg_expA (RefOk.matchExp_consPat rfl rfl rfl (by decide)))
      matchArgs_nil) (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_compE_iff.2 ⟨free0, free0, Sim.evalExp_var rfl, evalExp_callE_iff.2
      (callDef_iff.2 ⟨_, _, _, _, Equiv.evalArgs_cons hl Equiv.evalArgs_nil, fd_flist, .inl ih⟩),
      comp_free0⟩))

/-- **`$free_list` of `k` copies of `free0` is `free0`.** -/
theorem tc_flistRep (k : Nat) :
    TryClauses (simEnv B) (defClauses Original.d75) [.val (.list (List.replicate k free0))] free0 :=
  match k with
  | 0 => tc_flistNil
  | k + 1 => tc_flistCons (tc_flistRep k)

/-- `$free_opt(eps) = free0`. -/
theorem tc_foptNone : TryClauses (simEnv B) (defClauses Original.d74) [.val (.opt none)] free0 :=
  ⟨20, by
    simp [free0, tryClauses, matchArg, matchExp, premsHold, VarEnv.empty,
      Res.elimUndef, Bind.bind, Except.bind, Pure.pure, Except.pure, matchArgs.eq_def,
      argSubOk, defClauses, Original.d74, evalExp, evalExps, evalExpFields,
      Functor.map, Except.map]⟩

/-- `$free_addrtype(at) = free0`, at every value. -/
theorem tc_faddr (a : Value) : TryClauses (simEnv B) (defClauses Original.d193) [.val a] free0 :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl) ⟨20, by
      simp [free0, evalExp, evalExps, evalExpFields, Bind.bind, Except.bind, Pure.pure,
        Except.pure, Functor.map, Except.map]⟩

/-- `$free_memtype(%%PAGE(at, l)) = free0`. -/
theorem tc_fmemtype (a l : Value) :
    TryClauses (simEnv B) (defClauses Original.d204) [.val (.case "%%PAGE" (.tuple [a, l]))] free0 :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
      (matchExps_cons' (matchExp_varE rfl) (matchExps_cons' (matchExp_varE rfl) matchExps_nil')))))
      matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (Sim.evalExp_var rfl) Equiv.evalArgs_nil, fd_faddr, .inl (tc_faddr a)⟩))

/-- **`$free_mem(MEMORY mt) = free0`**, at the image of every memory type. -/
theorem tc_fmem (mt : Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d299) [.val (.case "MEMORY" (Encode.toValue mt))]
      free0 :=
  tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_varE rfl))) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (Sim.evalExp_var rfl) Equiv.evalArgs_nil, fd_fmemtype,
      .inl (tc_fmemtype _ _)⟩))

/-! ## `$free_module` at a module with one memory -/

/-- **`$free_list(f(x)*)` is `free0`** when `f` gives `free0` on every element of `x*`. -/
theorem evalExp_flistIter {ρ : VarEnv} {f x xs : IL.Id} {ws : List Value}
    (hd : ρ.findDef? "free_list" = none) (hxs : ρ.findVal? xs = some (.list ws))
    (hb : ∀ w ∈ ws, EvalExp (simEnv B) (ρ.bindVals [(x, w)]) (.callE f [.expA (.varE x)]) free0) :
    EvalExp (simEnv B) ρ (.callE "free_list" [.expA (.iterE (.callE f [.expA (.varE x)])
      (.mk .list [.mk x (.varE xs)]))]) free0 := by
  have hl := Sim.evalExp_iterMap (g := fun _ => free0) hxs hb
  rw [List.map_const'] at hl
  exact evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _, Equiv.evalArgs_cons hl Equiv.evalArgs_nil,
    by rw [hd]; exact fd_flist, .inl (tc_flistRep _)⟩)

/-- `$free_opt(f(x)?)` is `free0` when `x?` is absent. -/
theorem evalExp_foptNone {ρ : VarEnv} {f x xs : IL.Id} (hd : ρ.findDef? "free_opt" = none)
    (hxs : ρ.findVal? xs = some (.opt none)) :
    EvalExp (simEnv B) ρ (.callE "free_opt" [.expA (.iterE (.callE f [.expA (.varE x)])
      (.mk .opt [.mk x (.varE xs)]))]) free0 :=
  evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _, ⟨10, by
    simp [evalArgs, evalArg, evalExp, evalIterE, evalDoms, domSrc, domVar, hxs, Value.asOpt?,
      Bind.bind, Except.bind, Res.ofOption, Pure.pure, Except.pure, Functor.map, Except.map]⟩,
    by rw [hd]; exact fd_fopt, .inl tc_foptNone⟩)

/-- The scope `$free_module`'s pattern binds at `memModuleV [mt]`. -/
def fmρ1 (mt : Silmaril.Wasm.MemoryType) : VarEnv :=
  (((((((((((VarEnv.empty.bindVal "type*" (.list [])).bindVal "import*" (.list [])).bindVal
    "tag*" (.list [])).bindVal "global*" (.list [])).bindVal "mem*" (.list [memV mt])).bindVal
    "table*" (.list [])).bindVal "func*" (.list [])).bindVal "data*" (.list [])).bindVal
    "elem*" (.list [])).bindVal "start?" (.opt none)).bindVal "export*" (.list []))

set_option maxRecDepth 100000 in
/-- **`$free_module`'s pattern matches `memModuleV [mt]`.** -/
theorem fm_match1 (mt : Silmaril.Wasm.MemoryType) :
    MatchArgs (simEnv B) VarEnv.empty fmPats [.val (memModuleV [mt])] (fmρ1 mt) :=
  matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
    (matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_caseE (matchExp_tupE' (matchExps_cons'
      (RefOk.matchExp_star (by rfl) (by rfl) (by decide)) matchExps_nil'))) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_pctList (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) <| matchExps_cons' (matchExp_optVar (by rfl)) <|
    matchExps_cons' (matchExp_pctList (by rfl)) matchExps_nil')))) matchArgs_nil

/-- `$free_mem(mem)` is `free0` at `mem = MEMORY mt`, in every scope. -/
theorem evalExp_fmem {ρ : VarEnv} (mt : Silmaril.Wasm.MemoryType)
    (hd : ρ.findDef? "free_mem" = none) (hm : ρ.findVal? "mem" = some (memV mt)) :
    EvalExp (simEnv B) ρ (.callE "free_mem" [.expA (.varE "mem")]) free0 :=
  evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
    Equiv.evalArgs_cons (Sim.evalExp_var hm) Equiv.evalArgs_nil, by rw [hd]; exact fd_fmem,
    .inl (tc_fmem mt)⟩)

/-- `free0 ⊕ free0`, as an evaluation step. -/
theorem evalExp_comp0 {ρ : VarEnv} {e₁ e₂ : Exp} (h₁ : EvalExp (simEnv B) ρ e₁ free0)
    (h₂ : EvalExp (simEnv B) ρ e₂ free0) : EvalExp (simEnv B) ρ (.compE e₁ e₂) free0 :=
  evalExp_compE_iff.2 ⟨_, _, h₁, h₂, comp_free0⟩

/-- An iteration over an empty list holds of every element. -/
theorem forall_mem_nil' {P : Value → Prop} : ∀ w ∈ ([] : List Value), P w := fun _ h => nomatch h

/-- **`$free_module`'s body is `free0`** at `memModuleV [mt]`: ten compositions, each of
`$free_list` over an empty list, of `$free_mem` over `[MEMORY mt]`, or of `$free_opt(eps)`. -/
theorem fm_body1 (mt : Silmaril.Wasm.MemoryType) : EvalExp (simEnv B) (fmρ1 mt) fmBody free0 :=
  evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0
    (evalExp_comp0 (evalExp_comp0 (evalExp_comp0 (evalExp_comp0
      (evalExp_flistIter rfl rfl forall_mem_nil') (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl fun w hw => by
        obtain rfl := List.mem_singleton.1 hw
        exact evalExp_fmem mt rfl rfl))
      (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_flistIter rfl rfl forall_mem_nil'))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_foptNone rfl rfl))
      (evalExp_flistIter rfl rfl forall_mem_nil')) (evalExp_flistIter rfl rfl forall_mem_nil')

/-- **`$free_module(memModuleV [mt]) = free0`.** -/
theorem tc_freeModule1 (mt : Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d310) [.val (memModuleV [mt])] free0 :=
  fm_clauses ▸ tryClauses_hit (fm_match1 mt) (Equiv.Validation.premsHold_nil_iff.2 rfl) (fm_body1 mt)

/-- **`$funcidx_module(memModuleV [mt]) = []`.** -/
theorem tc_funcidxModule1 (mt : Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d311) [.val (memModuleV [mt])] (.list []) :=
  fmod_clauses ▸ tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_dotE_iff.2 ⟨free0, evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _,
      Equiv.evalArgs_cons (Sim.evalExp_var rfl) Equiv.evalArgs_nil, fd_fmod,
      .inl (tc_freeModule1 mt)⟩), rfl⟩)

/-- The scope `$funcidx_nonfuncs`'s pattern binds at `([], [MEMORY mt], [], [], [])`. -/
def fnfρ1 (mt : Silmaril.Wasm.MemoryType) : VarEnv :=
  ((((VarEnv.empty.bindVal "global*" (.list [])).bindVal "mem*" (.list [memV mt])).bindVal
    "table*" (.list [])).bindVal "elem*" (.list [])).bindVal "export*" (.list [])

/-- **`$funcidx_nonfuncs(%%%%%([], [MEMORY mt], [], [], [])) = []`.** -/
theorem tc_funcidxNonfuncs1 (mt : Silmaril.Wasm.MemoryType) :
    TryClauses (simEnv B) (defClauses Original.d384)
      [.val (.case "%%%%%" (.tuple [.list [], .list [memV mt], .list [], .list [], .list []]))]
      (.list []) :=
  fnf_clauses ▸ tryClauses_hit (ρ₀ := fnfρ1 mt)
    (matchArgs_cons (matchArg_expA (matchExp_caseE (matchExp_tupE'
      (matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (RefOk.matchExp_star (by rfl) (by rfl) (by decide)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) <| matchExps_cons' (matchExp_listVar (by rfl)) <|
      matchExps_cons' (matchExp_listVar (by rfl)) matchExps_nil')))) matchArgs_nil)
    (Equiv.Validation.premsHold_nil_iff.2 rfl)
    (evalExp_callE_iff.2 (callDef_iff.2 ⟨_, _, _, _, ⟨20, by
      simp [memModuleV, pctNil, fnfρ1, evalArgs, evalArg, evalExp, evalExps, evalIterE, evalDoms,
        domSrc, domVar, VarEnv.findVal?, VarEnv.bindVal, Map.bind, Map.find?, evalIterList,
        evalRounds, Value.asList?, iterRows, iterRow, Functor.map, Except.map, Bind.bind, Except.bind,
        Res.ofOption, Pure.pure, Except.pure, VarEnv.bindVals, Map.binds]⟩, fd_fm,
      .inl (tc_funcidxModule1 mt)⟩))

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
