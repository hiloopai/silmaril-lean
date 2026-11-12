module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.MemSize
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Control.CallFunc

/-!
# `Step_read/call_addr` of 1.0, backwards

1.0's `call_addr` (rule 5 of `Step_read`, transcribed as `callAddrRule10`, kernel `rfl`) is

  `z; val^k (CALL_ADDR a) ~> (FRAME_ n {f} (LABEL_ n {eps} instr*))`

under `$funcinst(z)[a] = {TYPE (t_1^k -> t_2^n), MODULE mm, CODE func}`,
`func = FUNC x (LOCAL t)* instr*` and `f = {LOCALS val^k ($default_(t))*, MODULE mm}`. It opens the
frame and the body's label in one step, as V1's `Step.invokeWasm` does.

Backwards: the first premise names a store function (`funcinst_of_eval10`); it is a Wasm function,
because a host function's image has `CODE = _HOSTFUNC …`, which the second premise rules out; its
type gives `k = |params|` and `n = |results|` (`funcType_of_eval10`). The second premise gives the
locals and body (`code_of_eval10`), and the third makes `f` the image of V1's new frame
`⟨args ++ locals.map Value.zero, module⟩` (`frame_of_eval10`, through `$default_` at every 1.0 value
type, `evalExp_default10`). V1's `resultArity` (at most one result) is `StoreOk10`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step value values expression)
open Silmaril.Wasm.Execution.Runtime (Frame FuncInst)
open Silmaril.SpecTec.Equiv.Validation (HasRuleAt)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.SpecTec.Equiv (evalArgs_cons evalArgs_nil)
open Silmaril.Wasm.SpecTec.Sim (Fires QuantsOk quant_list evalExp_tup2 evalExp_tup3 evalExp_case
  evalExp_list1 evalExp_cat evalExp_iterMap evalExp_iterNMap evalExp_str2 findVal_bind1)
open Silmaril.Wasm.SpecTec.Sim.State (HasClause1 evalExp_call1)
open Silmaril.Wasm.SpecTec.Sim20.Pure (quant_val quant_listT fires_inv evalExp_subIter
  evalExp_iter evalExp_valsN_inv)
open Silmaril.Wasm.SpecTec.Sim20.State (sfPat matchArgs_sf)
open Silmaril.Wasm.SpecTec.Sim.Bwd (eq_of_cmp)

set_option maxRecDepth 100000

variable {H : Type} {B : Builtins} {hn : H → String}

/-! ## The rule -/

/-- `val^k`, coerced to `admininstr`. -/
abbrev valsKE : Exp := .iterE (.subE (.varE "val") (.varT "val" []) (.varT "admininstr" []))
  (.mk (.listN (.varE "k") none) [.mk "val" (.varE "val*")])

/-- `t_1^k -> t_2^n`. -/
abbrev funcTypeE : Exp := .caseE "%->%" (.tupE [
  .iterE (.varE "t_1") (.mk (.listN (.varE "k") none) [.mk "t_1" (.varE "t_1*")]),
  .iterE (.varE "t_2") (.mk (.listN (.varE "n") none) [.mk "t_2" (.varE "t_2*")])])

/-- `FUNC x (LOCAL t)* instr*`. -/
abbrev funcE : Exp := .caseE "FUNC" (.tupE [.varE "x",
  .iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]),
  .iterE (.varE "instr") (.mk .list [.mk "instr" (.varE "instr*")])])

/-- `{LOCALS val^k ($default_(t))*, MODULE mm}`. -/
abbrev frameE : Exp := .strE [.mk "LOCALS" (.catE
    (.iterE (.varE "val") (.mk (.listN (.varE "k") none) [.mk "val" (.varE "val*")]))
    (.iterE (.callE "default_" [.expA (.varE "t")]) (.mk .list [.mk "t" (.varE "t*")]))),
  .mk "MODULE" (.varE "mm")]

/-- The quantifiers of `call_addr`. -/
abbrev callAddrRule10Qs : List Param :=
  [.expP "z" (.varT "state" []), .expP "k" (.numT .natT),
    .expP "val*" (.iterT (.varT "val" []) .list), .expP "a" (.varT "addr" []),
    .expP "n" (.varT "n" []), .expP "f" (.varT "frame" []),
    .expP "instr*" (.iterT (.varT "instr" []) .list),
    .expP "t_1*" (.iterT (.varT "valtype" []) .list), .expP "t_2*" (.iterT (.varT "valtype" []) .list),
    .expP "mm" (.varT "moduleinst" []), .expP "func" (.varT "func" []), .expP "x" (.varT "idx" []),
    .expP "t*" (.iterT (.varT "valtype" []) .list)]

/-- `Step_read/call_addr` of 1.0 (transcribed). -/
def callAddrRule10 : Rule :=
  .ruleD "call_addr" callAddrRule10Qs "%~>%"
    (.tupE [.caseE "%;%" (.tupE [.varE "z", .catE valsKE (.listE [.caseE "CALL_ADDR" (.varE "a")])]),
      .listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n", .varE "f", .listE [.caseE "LABEL_%{%}%"
        (.tupE [.varE "n", .listE [], .iterE (.subE (.varE "instr") (.varT "instr" [])
          (.varT "admininstr" [])) (.mk .list [.mk "instr" (.varE "instr*")])])]])]])
    [.ifPr (.cmpE .eqOp .boolT (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
        (.strE [.mk "TYPE" funcTypeE, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")])),
      .ifPr (.cmpE .eqOp .boolT (.varE "func") funcE),
      .ifPr (.cmpE .eqOp .boolT (.varE "f") frameE)]

variable (B) in
theorem hasRuleAt10_callAddr : HasRuleAt (simEnv10 B) "Step_read" "%~>%" 5 callAddrRule10 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-! ## Evaluation helpers -/

/-- Three record fields, read back. -/
theorem evalExpFields_inv3 {env : Env} {ρ : VarEnv} {a₁ a₂ a₃ b₁ b₂ b₃ : AtomS} {e₁ e₂ e₃ : Exp}
    {v₁ v₂ v₃ : Value}
    (h : EvalExpFields env ρ [.mk a₁ e₁, .mk a₂ e₂, .mk a₃ e₃] [(b₁, v₁), (b₂, v₂), (b₃, v₃)]) :
    EvalExp env ρ e₁ v₁ ∧ EvalExp env ρ e₂ v₂ ∧ EvalExp env ρ e₃ v₃ := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [evalExpFields] at hn
  | succ n =>
    simp only [evalExpFields, List.mapM_cons, List.mapM_nil] at hn
    cases h₁ : evalExp n env ρ e₁ <;> cases h₂ : evalExp n env ρ e₂ <;>
      cases h₃ : evalExp n env ρ e₃ <;>
      simp_all [Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
    exact ⟨⟨n, h₁⟩, ⟨n, h₂⟩, ⟨n, h₃⟩⟩

theorem hasClause_funcinst10 : HasClause1 (simEnv10 B) "funcinst" sfPat
    (.dotE (.varE "s") "FUNCS") := ⟨_, _, _, rfl⟩

/-- `$funcinst(z)` at the 1.0 encoding. -/
theorem evalExp_funcinst10 {ρ : VarEnv} {s : Store H} {f : Frame}
    (hρ : ρ.findDef? "funcinst" = none) (fz : ρ.findVal? "z" = some (stateV hn s f)) :
    EvalExp (simEnv10 B) ρ (.callE "funcinst" [.expA (.varE "z")])
      (.list (s.funcs.map (funcInstV hn))) :=
  evalExp_call1 hasClause_funcinst10 hρ (evalArgs_cons (evalExp_var fz) evalArgs_nil) matchArgs_sf
    (evalExp_dotE_iff.2 ⟨storeV hn s, evalExp_var rfl, rfl⟩)

/-- `$funcinst(z)[a]`, read back: a store function. -/
theorem funcinst_of_eval10 {ρ : VarEnv} {s : Store H} {f : Frame} {n : Nat} {v : Value}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN n)))
    (hρ : ρ.findDef? "funcinst" = none)
    (h : EvalExp (simEnv10 B) ρ (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a")) v) :
    ∃ fi, s.funcs[n]? = some fi ∧ v = funcInstV hn fi := by
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 h
  have ewl : wl = .list (s.funcs.map (funcInstV hn)) :=
    EvalExp.unique hwl (evalExp_funcinst10 hρ fz)
  have ei : i = n := Sim.Bwd.natN_inj (EvalExp.unique hi (evalExp_var fa))
  have hget : (s.funcs.map (funcInstV hn))[n]? = some v := by
    rw [← ei]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fi, hfi, hfv⟩ := Option.map_eq_some_iff.1 hget
  exact ⟨fi, hfi, hfv.symm⟩

/-- `t_1^k -> t_2^n` at a function type, read back: the counts are the arities. -/
theorem funcType_of_eval10 {ρ : VarEnv} {ft : V1.FuncType}
    (h : EvalExp (simEnv10 B) ρ funcTypeE (funcTypeV ft)) :
    ρ.findVal? "k" = some (.num (.natN ft.params.length)) ∧
      ρ.findVal? "n" = some (.num (.natN ft.results.length)) := by
  have hs := tup_of_caseV (op := "%->%") h
  obtain ⟨w₁, ws, h₁, hws, he⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hs
  obtain ⟨rfl, rfl⟩ := List.cons.inj he
  obtain ⟨w₂, ws', h₂, -, he'⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hws
  obtain ⟨rfl, -⟩ := List.cons.inj he'
  have hb : ∀ (x : IL.Id) (σ : VarEnv) (w u : Value), σ.findVal? x = some w →
      EvalExp (simEnv10 B) σ (.varE x) u → u = w := fun x σ w u hw hu => by
    rw [evalExp_varE_iff, hw] at hu
    exact (Option.some.inj hu).symm
  obtain ⟨l₁, -, fk, e₁⟩ := Sim.Exn.evalExp_iterN_inv (hb "t_1") (by decide) h₁
  obtain ⟨l₂, -, fn, e₂⟩ := Sim.Exn.evalExp_iterN_inv (hb "t_2") (by decide) h₂
  have hl₁ : l₁.length = ft.params.length := by
    rw [← List.length_map (f := valTypeV)]
    exact congrArg List.length (Value.list.inj e₁).symm
  have hl₂ : l₂.length = ft.results.length := by
    rw [← List.length_map (f := valTypeV)]
    exact congrArg List.length (Value.list.inj e₂).symm
  exact ⟨hl₁ ▸ fk, hl₂ ▸ fn⟩

/-- **The first premise, read back**: `a` names a Wasm function of the store, whose type gives the
counts, and `mm` and `func` are bound to its module and code. -/
theorem prem1_of_eval10 {ρ : VarEnv} {s : Store H} {f : Frame} {n : Nat}
    (fz : ρ.findVal? "z" = some (stateV hn s f)) (fa : ρ.findVal? "a" = some (.num (.natN n)))
    (hρ : ρ.findDef? "funcinst" = none)
    (hfunc : ∃ u, ρ.findVal? "func" = some (.case "FUNC" u))
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT
      (.idxE (.callE "funcinst" [.expA (.varE "z")]) (.varE "a"))
      (.strE [.mk "TYPE" funcTypeE, .mk "MODULE" (.varE "mm"), .mk "CODE" (.varE "func")]))
      (.bool true)) :
    ∃ ft m fn, s.funcs[n]? = some (.wasm ft m fn) ∧
      ρ.findVal? "k" = some (.num (.natN ft.params.length)) ∧
      ρ.findVal? "n" = some (.num (.natN ft.results.length)) ∧
      ρ.findVal? "mm" = some (moduleInstV m) ∧ ρ.findVal? "func" = some (funcV fn) := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  obtain ⟨fi, hfi, rfl⟩ := funcinst_of_eval10 fz fa hρ h₁
  obtain ⟨gs, hgs, hv⟩ := evalExp_strE_iff.1 h₂
  cases fi with
  | host ft hf =>
    obtain ⟨u, fu⟩ := hfunc
    simp only [funcInstV, Value.struct.injEq] at hv
    subst hv
    have := (evalExpFields_inv3 hgs).2.2
    rw [evalExp_varE_iff, fu] at this
    simp at this
  | wasm ft m fn =>
    simp only [funcInstV, Value.struct.injEq] at hv
    subst hv
    obtain ⟨hT, hM, hC⟩ := evalExpFields_inv3 hgs
    obtain ⟨fk, fn'⟩ := funcType_of_eval10 hT
    exact ⟨ft, m, fn, hfi, fk, fn', evalExp_varE_iff.1 hM, evalExp_varE_iff.1 hC⟩

/-- **The second premise, read back** at a function's image: `t*` and `instr*` are its locals and
body. -/
theorem code_of_eval10 {ρ : VarEnv} {fn : V1.Func} {xv : Value} {ts is : List Value}
    (ffn : ρ.findVal? "func" = some (funcV fn)) (fx : ρ.findVal? "x" = some xv)
    (ft : ρ.findVal? "t*" = some (.list ts)) (fi : ρ.findVal? "instr*" = some (.list is))
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT (.varE "func") funcE) (.bool true)) :
    ts = fn.locals.map valTypeV ∧ is = instrsToV fn.body := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have el : EvalExp (simEnv10 B) ρ (.iterE (.caseE "LOCAL" (.varE "t")) (.mk .list [.mk "t" (.varE "t*")]))
      (.list (ts.map (.case "LOCAL"))) :=
    evalExp_iterMap ft fun _ _ => evalExp_case (evalExp_var (findVal_bind1 (by decide)))
  have e₂ : v = .case "FUNC" (.tuple [xv, .list (ts.map (.case "LOCAL")), .list is]) :=
    EvalExp.unique h₂ (evalExp_case (evalExp_tup3 (evalExp_var fx) el (evalExp_iter (by decide) fi)))
  have e₁ : v = funcV fn := EvalExp.unique h₁ (evalExp_var ffn)
  have hf := e₂.symm.trans e₁
  simp only [funcV, Value.case.injEq, Value.tuple.injEq, List.cons.injEq, Value.list.injEq,
    true_and, and_true] at hf
  refine ⟨?_, hf.2.2⟩
  have hm : ts.map (Value.case "LOCAL") = (fn.locals.map valTypeV).map (Value.case "LOCAL") := by
    rw [hf.2.1, List.map_map]
    rfl
  exact List.map_injective_iff.2 (fun _ _ h => (Value.case.inj h).2) hm

/-! ## `$default_` -/

theorem findDef_fzero10 : ∃ ps t, (simEnv10 B).findDef? "fzero" = some (ps, t,
    [.defD [.expP "N" (.varT "N" [])] [.expA (.varE "N")]
      (.caseE "POS" (.caseE "SUBNORM" (.tupE [.numE (.natN 0)]))) []]) := ⟨_, _, rfl⟩

/-- `$fzero(N) = POS (SUBNORM 0)`. -/
theorem evalExp_fzero10 {ρ : VarEnv} (N : Nat) (hρ : ρ.findDef? "fzero" = none) :
    EvalExp (simEnv10 B) ρ (.callE "fzero" [.expA (.numE (.natN N))])
      (.case "POS" (.case "SUBNORM" (.tuple [.num (.natN 0)]))) := by
  obtain ⟨ps, t, hd⟩ := findDef_fzero10 (B := B)
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd
    (evalArgs_cons (evalExp_numE_iff.2 rfl) evalArgs_nil) ?_)
  exact tryClauses_hit (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) matchArgs_nil)
    premsHold_nil (evalExp_case (evalExp_tupE_iff.2
      ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩) |> evalExp_case)

theorem findDef_default10 : ∃ ps t, (simEnv10 B).findDef? "default_" = some (ps, t,
    [.defD [] [.expA (.caseE "I32" (.tupE []))] (.caseE "CONST" (.tupE [.caseE "I32" (.tupE []),
        .caseE "%" (.tupE [.numE (.natN 0)])])) [],
      .defD [] [.expA (.caseE "I64" (.tupE []))] (.caseE "CONST" (.tupE [.caseE "I64" (.tupE []),
        .caseE "%" (.tupE [.numE (.natN 0)])])) [],
      .defD [] [.expA (.caseE "F32" (.tupE []))] (.caseE "CONST" (.tupE [.caseE "F32" (.tupE []),
        .callE "fzero" [.expA (.numE (.natN 32))]])) [],
      .defD [] [.expA (.caseE "F64" (.tupE []))] (.caseE "CONST" (.tupE [.caseE "F64" (.tupE []),
        .callE "fzero" [.expA (.numE (.natN 64))]])) []]) := ⟨_, _, rfl⟩

/-- The nullary case `op`, evaluated. -/
theorem evalExp_nil0 {env : Env} {ρ : VarEnv} (op : MixopS) :
    EvalExp env ρ (.caseE op (.tupE [])) (.case op (.tuple [])) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨[], evalExps_nil, rfl⟩)

/-- `%0`, evaluated. -/
theorem evalExp_pct0 {env : Env} {ρ : VarEnv} :
    EvalExp env ρ (.caseE "%" (.tupE [.numE (.natN 0)])) (pctV 0) :=
  evalExp_case (evalExp_tupE_iff.2 ⟨_, evalExps_cons (evalExp_numE_iff.2 rfl) evalExps_nil, rfl⟩)

/-- **`$default_(t)`** is the image of V1's zero, at every 1.0 value type. -/
theorem evalExp_default10 (t : V1.ValType) {ρ : VarEnv} {e : Exp}
    (hρ : ρ.findDef? "default_" = none) (he : EvalExp (simEnv10 B) ρ e (valTypeV t)) :
    EvalExp (simEnv10 B) ρ (.callE "default_" [.expA e])
      (valV (Execution.Runtime.Value.zero t)) := by
  obtain ⟨ps, ty, hd⟩ := findDef_default10 (B := B)
  refine evalExp_callE_iff.2 (callDef_of_tryClauses hρ hd (evalArgs_cons he evalArgs_nil) ?_)
  rcases t with (_ | _) | (_ | _) <;>
  · repeat (refine tryClauses_skip_match (matchArgs_cons_undef (matchArg_expA_undef
      (matchExp_caseE_undef (by decide)))) ?_)
    refine tryClauses_hit (ρ₀ := VarEnv.empty)
      (matchArgs_cons (matchArg_expA (matchExp_caseE matchExp_tupE_nil)) matchArgs_nil)
      premsHold_nil ?_
    first
      | exact evalExp_case (evalExp_tup2 (evalExp_nil0 _) evalExp_pct0)
      | exact evalExp_case (evalExp_tup2 (evalExp_nil0 _) (evalExp_fzero10 _ rfl))

/-- A value type, read back from its image. -/
def vtOf : Value → V1.ValType
  | .case "I64" _ => .int .i64
  | .case "F32" _ => .float .f32
  | .case "F64" _ => .float .f64
  | _ => .int .i32

theorem vtOf_valTypeV (t : V1.ValType) : vtOf (valTypeV t) = t := by
  rcases t with (_ | _) | (_ | _) <;> rfl

/-- **The third premise, read back**: `f` is the image of V1's new frame. -/
theorem frame_of_eval10 {ρ : VarEnv} {args : List Execution.Runtime.Value} {locals : List V1.ValType}
    {m : Execution.Runtime.ModuleInst} {fv : Value} (hρ : ρ.findDef? "default_" = none)
    (ff : ρ.findVal? "f" = some fv) (fk : ρ.findVal? "k" = some (.num (.natN (args.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (args.map valV)))
    (ft : ρ.findVal? "t*" = some (.list (locals.map valTypeV)))
    (fm : ρ.findVal? "mm" = some (moduleInstV m))
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT (.varE "f") frameE) (.bool true)) :
    fv = frameV ⟨args ++ locals.map Execution.Runtime.Value.zero, m⟩ := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  have e₁ : EvalExp (simEnv10 B) ρ (.iterE (.varE "val")
      (.mk (.listN (.varE "k") none) [.mk "val" (.varE "val*")])) (.list ((args.map valV).map id)) :=
    evalExp_iterNMap fk fw fun _ _ => evalExp_var (findVal_bind1 (by decide))
  have e₂ : EvalExp (simEnv10 B) ρ (.iterE (.callE "default_" [.expA (.varE "t")])
      (.mk .list [.mk "t" (.varE "t*")]))
      (.list ((locals.map valTypeV).map fun w => valV (Execution.Runtime.Value.zero (vtOf w)))) :=
    evalExp_iterMap ft fun w hw => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hw
      rw [vtOf_valTypeV]
      exact evalExp_default10 t hρ (evalExp_var (findVal_bind1 (by decide)))
  have e₃ := evalExp_str2 (a₁ := "LOCALS") (a₂ := "MODULE") (evalExp_cat e₁ e₂) (evalExp_var fm)
  have ev : v = fv := EvalExp.unique h₁ (evalExp_var ff)
  rw [← ev, EvalExp.unique h₂ e₃]
  simp [frameV, List.map_map, Function.comp_def, vtOf_valTypeV]

/-! ## The left-hand side -/

theorem head10_callAddr {a : Admin} (h : adminHead10 a = "CALL_ADDR") : ∃ fa, a = .invoke fa := by
  revert h; admin_head_inv10

/-- A configuration pattern `z; e`, read back. -/
theorem cfg_split10 {ρ : VarEnv} {e : Exp} {s : Store H} {f : Frame} {code : List Admin}
    (h : EvalExp (simEnv10 B) ρ (.caseE "%;%" (.tupE [.varE "z", e])) (configV hn ⟨s, f, code⟩)) :
    ρ.findVal? "z" = some (stateV hn s f) ∧ EvalExp (simEnv10 B) ρ e (.list (adminsToV code)) := by
  obtain ⟨u, hu, hcu⟩ := evalExp_caseE_iff.1 h
  have hu' : u = .tuple [stateV hn s f, .list (adminsToV code)] := (Value.case.inj hcu.symm).2
  obtain ⟨u₁, u₂, hZ, hL, hU⟩ := Sim.State.evalExp_tup2_inv (hu' ▸ hu)
  have e₁₂ : stateV hn s f = u₁ ∧ Value.list (adminsToV code) = u₂ := by
    simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hU
  exact ⟨e₁₂.1 ▸ evalExp_varE_iff.1 hZ, e₁₂.2 ▸ hL⟩

/-- `val^k (CALL_ADDR a)`, read back at a list. -/
theorem valsCall_inv10 {ρ : VarEnv} {l : List Value}
    (h : EvalExp (simEnv10 B) ρ (.catE valsKE (.listE [.caseE "CALL_ADDR" (.varE "a")])) (.list l)) :
    ∃ vs A, ρ.findVal? "val*" = some (.list vs) ∧ ρ.findVal? "k" = some (.num (.natN vs.length)) ∧
      ρ.findVal? "a" = some A ∧ l = vs ++ [.case "CALL_ADDR" A] := by
  obtain ⟨v₁, v₂, h₁, h₂, hc⟩ := evalExp_catE_iff.1 h
  obtain ⟨vs, fv, fk, rfl⟩ := evalExp_valsN_inv (by decide) h₁
  obtain ⟨us, hus, rfl⟩ := evalExp_listE_iff.1 h₂
  obtain ⟨w, ws', hw, hws', rfl⟩ := Silmaril.SpecTec.Sem.evalExps_cons_iff.1 hus
  obtain rfl := Silmaril.SpecTec.Sem.evalExps_nil_iff.1 hws'
  obtain ⟨A, hA, rfl⟩ := evalExp_caseE_iff.1 hw
  exact ⟨vs, A, fv, fk, evalExp_varE_iff.1 hA, by simpa [Value.cat?] using hc.symm⟩

/-- Code whose image is a typed `val*` followed by `CALL_ADDR A` is `values args ++ [invoke fa]`. -/
theorem code_callAddr10 {σ : List (IL.Id × Value)} {code : List Admin} {vs : List Value} {A : Value}
    (ht : HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list vs))
    (hcode : adminsToV code = vs ++ [.case "CALL_ADDR" A]) :
    ∃ args fa, code = values args ++ [.invoke fa] ∧ vs = args.map valV ∧
      A = .num (.natN fa.value) := by
  obtain ⟨l₁, m, l₃, rfl, h₁', hm, h₃⟩ := split_marked10 hcode
  have hl₃ : l₃ = [] := by
    rw [adminsToV_map10] at h₃
    exact List.map_eq_nil_iff.1 h₃
  obtain ⟨fa, rfl⟩ := head10_callAddr (adminToV_case10 hm)
  obtain ⟨args, rfl⟩ := values_of_image h₁' (consts_of_typed10 (Sim.valsOnly_bindVals σ) ht)
  refine ⟨args, fa, by simp [hl₃], by rw [← h₁', adminsToV_values], (Value.case.inj hm).2.symm⟩

/-- **The left-hand side `z; val^k (CALL_ADDR a)`, read back** at a configuration. -/
theorem lhs_callAddr10 {σ : List (IL.Id × Value)} {s : Store H} {f : Frame} {code : List Admin}
    {ws : List Value} (fws : (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws))
    (ht : HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list ws))
    (h : EvalExp (simEnv10 B) (VarEnv.empty.bindVals σ)
      (.caseE "%;%" (.tupE [.varE "z", .catE valsKE (.listE [.caseE "CALL_ADDR" (.varE "a")])]))
      (configV hn ⟨s, f, code⟩)) :
    ∃ args fa, code = values args ++ [.invoke fa] ∧
      (VarEnv.empty.bindVals σ).findVal? "z" = some (stateV hn s f) ∧
      (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list (args.map valV)) ∧
      (VarEnv.empty.bindVals σ).findVal? "k" = some (.num (.natN (args.map valV).length)) ∧
      (VarEnv.empty.bindVals σ).findVal? "a" = some (.num (.natN fa.value)) := by
  obtain ⟨fz, hL⟩ := cfg_split10 h
  obtain ⟨vs, A, fv, fk, fA, hcode⟩ := valsCall_inv10 hL
  have ew : ws = vs := Value.list.inj (Option.some.inj (fws.symm.trans fv))
  obtain ⟨args, fa, hc, hvs, hA⟩ := code_callAddr10 (ew ▸ ht) hcode
  exact ⟨args, fa, hc, fz, hvs ▸ fv, hvs ▸ fk, hA ▸ fA⟩

/-! ## The rule backwards -/

/-- The second premise forces `func` to be a `FUNC`. -/
theorem func_of_prem2 {ρ : VarEnv}
    (h : EvalExp (simEnv10 B) ρ (.cmpE .eqOp .boolT (.varE "func") funcE) (.bool true)) :
    ∃ u, ρ.findVal? "func" = some (.case "FUNC" u) := by
  obtain ⟨v, h₁, h₂⟩ := eq_of_cmp h
  obtain ⟨u, -, rfl⟩ := evalExp_caseE_iff.1 h₂
  exact ⟨u, evalExp_varE_iff.1 h₁⟩

/-- The image of V1's call frame. -/
theorem adminsToV_callFrame10 (len : Nat) (F : Frame) (body : V1.Expr) :
    adminsToV [.frame len F [.label len [] (expression body)]] =
      [.case "FRAME_%{%}%" (.tuple [.num (.natN len), frameV F,
        .list [.case "LABEL_%{%}%" (.tuple [.num (.natN len), .list [], .list (instrsToV body)])]])] := by
  rw [adminsToV_frame10]
  simp only [adminsToV_label10, adminsToV_expression]
  rfl

/-- The right-hand side `FRAME_ n {f} (LABEL_ n {eps} instr*)`, evaluated. -/
theorem evalExp_callAddrRhs {ρ : VarEnv} {nv fv : Value} {is : List Value}
    (fn : ρ.findVal? "n" = some nv) (ff : ρ.findVal? "f" = some fv)
    (fi : ρ.findVal? "instr*" = some (.list is)) :
    EvalExp (simEnv10 B) ρ (.listE [.caseE "FRAME_%{%}%" (.tupE [.varE "n", .varE "f",
      .listE [.caseE "LABEL_%{%}%" (.tupE [.varE "n", .listE [], .iterE (.subE (.varE "instr")
        (.varT "instr" []) (.varT "admininstr" [])) (.mk .list [.mk "instr" (.varE "instr*")])])]])])
      (.list [.case "FRAME_%{%}%" (.tuple [nv, fv, .list [.case "LABEL_%{%}%" (.tuple [nv,
        .list [], .list is])]])]) :=
  evalExp_list1 (evalExp_case (evalExp_tup3 (evalExp_var fn) (evalExp_var ff) (evalExp_list1
    (evalExp_case (evalExp_tup3 (evalExp_var fn) Sim20.Pure.evalExp_list0
      (evalExp_subIter (by decide) fi))))))

/-- The quantifiers of `call_addr` the conclusion and premises read. -/
theorem callAddr_quants {σ : List (IL.Id × Value)} {qs : List Param}
    (hq : QuantsOk (simEnv10 B) (VarEnv.empty.bindVals σ) qs)
    (hm : ∀ p ∈ callAddrRule10Qs, p ∈ qs) :
    ∃ ws xv ts is fv₀, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) ∧
      HasTyp (simEnv10 B) (VarEnv.empty.bindVals σ) (.iterT (.varT "val" []) .list) (.list ws) ∧
      (VarEnv.empty.bindVals σ).findVal? "x" = some xv ∧
      (VarEnv.empty.bindVals σ).findVal? "t*" = some (.list ts) ∧
      (VarEnv.empty.bindVals σ).findVal? "instr*" = some (.list is) ∧
      (VarEnv.empty.bindVals σ).findVal? "f" = some fv₀ := by
  obtain ⟨ws, fws, ht⟩ := quant_listT (x := "val*") (t := .varT "val" []) hq (hm _ (by simp))
  obtain ⟨xv, fx⟩ := quant_val (x := "x") (t := .varT "idx" []) hq (hm _ (by simp))
  obtain ⟨ts, fts, -⟩ := quant_list (x := "t*") (t := .varT "valtype" []) hq (hm _ (by simp))
  obtain ⟨is, fis, -⟩ := quant_list (x := "instr*") (t := .varT "instr" []) hq (hm _ (by simp))
  obtain ⟨fv₀, ff⟩ := quant_val (x := "f") (t := .varT "frame" []) hq (hm _ (by simp))
  exact ⟨ws, xv, ts, is, fv₀, fws, ht, fx, fts, fis, ff⟩

/-- **`Step_read/call_addr` backwards**, at a `GoodV1` configuration: V1's `invokeWasm`. -/
theorem bwd10_callAddr {host : HostSemantics H} {c : Config H} {w : List Value} (hg : GoodV1 c)
    (hf : Fires (simEnv10 B) "Step_read" 5 (.tuple [configV hn c, .list w])) :
    ∃ code', w = adminsToV code' ∧ Step host c ⟨c.store, c.frame, code'⟩ := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨σ, hq, he, hp⟩ := fires_inv (hasRuleAt10_callAddr B) hf
  obtain ⟨ws, xv, ts, is, fv₀, fws, ht, fx, fts, fis, ff⟩ := callAddr_quants hq fun _ h => h
  obtain ⟨args, fa, rfl, fz, fv, fk, fA⟩ := lhs_callAddr10 fws ht (Sim.RefsGC.lhs_of_concl he)
  obtain ⟨ft, m, fn, hfi, fk', fn', fm, ffn⟩ := prem1_of_eval10 fz fA rfl
    (func_of_prem2 (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))) (Sim20.Pure.ifPrem (hp _ (.head _)))
  have hcode : ts = fn.locals.map valTypeV ∧ is = instrsToV fn.body :=
    code_of_eval10 ffn fx fts fis (Sim20.Pure.ifPrem (hp _ (.tail _ (.head _))))
  have hF : fv₀ = frameV ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩ :=
    frame_of_eval10 rfl ff fk fv (hcode.1 ▸ fts) fm
      (Sim20.Pure.ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have harity : args.length = ft.params.length := by
    simpa using Sim.Bwd.natN_inj (Option.some.inj (fk.symm.trans fk'))
  have hres : ft.results.length ≤ 1 := hg.2.1.1 _ (List.mem_of_getElem? hfi)
  have hw : w = adminsToV [.frame ft.results.length
      ⟨args ++ fn.locals.map Execution.Runtime.Value.zero, m⟩
      [.label ft.results.length [] (expression fn.body)]] := by
    rw [adminsToV_callFrame10, ← hF]
    exact Value.list.inj (EvalExp.unique (Sim.RefsGC.rhs_of_concl he)
      (evalExp_callAddrRhs fn' ff (hcode.2 ▸ fis)))
  exact ⟨_, hw, .invokeWasm s f fa ft m fn args hfi harity hres⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
