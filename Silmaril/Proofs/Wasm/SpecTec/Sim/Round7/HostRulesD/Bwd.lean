module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostRulesD.Fwd

/-!
# Round 7, `BD`: the host-call rules backward, at `configVD`

Round 5's `FwdRef.bwd_callRefHostT` reads a firing of `Step` rule 8 or 9 from a `configV` image
back as a Core host-call step, at `BI`. Here the same is done from a `configVD` image at `BD`,
for every store, memory SIMD code included:

* `expand_of_dderivesD`, `callInvD`: SpecTec's `Expand` on an image at `BD` is Core's (copies of
  `Prims.expand_of_dderives` and `Integrate.callInv_concrete`, through `applies_unrolldtD`);
* `hostLhsD_of`: the left-hand side `(s; f); val^n (REF.FUNC_ADDR a) (CALL_REF yy)` decoded from
  a `configVD` image, through round 7's `vals_of_typedD` and `adminToVD_case`;
* `funcinstD_of_eval`, `hostCodeD_of_eval`, `hostPremsD`: the premises on `$funcinst`, `Expand`
  and the `CODE` field, read back at `funcInstVD` images;
* `hostMemD_of_eval`: `o ∈ $hostcall(…)` read back through `HostD.hostInvD_typed`;
* `bwd_callRefHostD` (rule 8), `bwd_callRefHostDivD` (rule 9): every firing at `simEnv (BD …)`
  from the `configVD` image of a configuration with a typed image is the image of a Core step.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (valsNPat)
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies applies_iff_callDef)
open Silmaril.SpecTec.Equiv.ExecReadAggregate (evalExp_iterNVar)
open Silmaril.SpecTec.Equiv.Validation (tyV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round7.HostD (BD hostArgsD outcomeVD)
open Round7.MemSimd (storeVD stateVD configVD funcInstVD adminsToVD adminToVD TypedD BwdUpToD
  typingFactsD_simEnv adminsToVD_eq adminsToVD_eq_map adminToVD_case vals_of_typedD)
open Bwd (cfgSt_inv HostLhs valsTyped_of outcome_res outcome_bot)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

/-! ## `Expand` backward at `BD` -/

/-- A derivation of `Expand` at `BD` is an instance of its one rule. -/
theorem expand_instD {O : ElseI} {v : Value}
    (h : DDerives (simEnv (BD P hn host)) O "Expand" "%~~%" [] v) :
    ∃ ρ₀ σ, bindParams VarEnv.empty [] [] = some ρ₀ ∧
      EvalExp (simEnv (BD P hn host)) (ρ₀.bindVals σ)
        (.tupE [.varE "deftype", .varE "comptype"]) v ∧
      PremW (simEnv (BD P hn host)) (DDerives (simEnv (BD P hn host)) O)
        (O "Expand" [] 0 v) (ρ₀.bindVals σ) Prims.expandPrem := by
  obtain ⟨ps, t, rules, i, r, hrel, hrule, hb⟩ := dderives_iff.1 h
  obtain ⟨t', hrel'⟩ := Prims.findRel_expand (BD P hn host)
  rw [hrel'] at hrel
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hrel
  obtain ⟨rfl, -, rfl⟩ := hrel
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ r = Prims.expandRule := by
    rcases i with _ | i <;> simp at hrule
    exact ⟨rfl, hrule.symm⟩
  obtain ⟨-, ρ₀, σ, hb₀, -, he, hp⟩ := hb
  exact ⟨ρ₀, σ, hb₀, he, hp _ (List.mem_singleton_self _)⟩

/-- **SpecTec's `Expand` of an image at `BD` is the image of Core's `Expand`.** -/
theorem expand_of_dderivesD {O : ElseI} {d : DefType} {w : Value}
    (h : DDerives (simEnv (BD P hn host)) O "Expand" "%~~%" [] (.tuple [tyV d, w])) :
    ∃ ct, Expand d ct ∧ w = tyV ct := by
  obtain ⟨ρ₀, σ, hb₀, he, hp⟩ := expand_instD h
  obtain ⟨_, _, h₁, h₂, hw⟩ := State.evalExp_tup2_inv he
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa only [Value.tuple.injEq, List.cons.injEq, and_true] using hw
  have hif := RefsGC.premW_if hp
  obtain ⟨v₁, v₂, hv₁, hv₂, -⟩ := evalExp_cmpE_iff.1 hif
  have happ : Applies (simEnv (BD P hn host)) "unrolldt" [.val (tyV d)] v₁ :=
    (applies_iff_callDef (RefsGC.findDef_bindVals_of_bindParams hb₀)
      (Equiv.evalArgs_cons h₁ (evalArgs_nil _ _))).2 (evalExp_callE_iff.1 hv₁)
  obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.1 ((applies_unrolldtD d v₁).1 happ)
  obtain ⟨a, b, c, hc, rfl⟩ := Prims.evalExp_sub3_inv hv₂
  obtain rfl := EvalExp.unique hc h₂
  exact Prims.expand_of_sub hst (RefsGC.eq_of_evalExp_eq hif hv₁ hv₂)

/-- `Bwd.CallInv` at `BD`. -/
theorem callInvD : Bwd.CallInv (simEnv (BD P hn host)) := by
  refine ⟨fun d T₁ T₂ h => ?_⟩
  obtain ⟨ct, hct, he⟩ := expand_of_dderivesD h
  obtain ⟨ps, rs, rfl, h₁, h₂⟩ := Integrate.func2_of_tyV he
  exact ⟨ps, rs, hct, h₁, h₂⟩

/-! ## The left-hand side at `configVD` -/

/-- The parts of the host calls' left-hand side, read back from a `configVD` image. -/
structure HostLhsD (s : Store H) (f : Frame) (code : List Admin) (ρ : VarEnv) : Prop where
  /-- The code is `vals vs ++ [REF.FUNC_ADDR a, c]`. -/
  shape : ∃ vs addr c, code = vals vs ++ [.ref (.func addr), c] ∧ c.IsCallRef ∧
    ρ.findVal? "a" = some (.num (.natN addr)) ∧
    ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)) ∧
    ρ.findVal? "val*" = some (.list (vs.map valV))
  /-- The state variables. -/
  state : ρ.findVal? "s" = some (storeVD hn s) ∧ ρ.findVal? "f" = some (frameV f)

/-- An administrative instruction whose `adminToVD` image is a value head is a value, encoded
as by `adminToV`. -/
theorem adminToVD_val {a : Admin} {op : MixopS} {x : Value} (h : adminToVD a = .case op x)
    (hop : op ∈ Typing.valHeads) : ∃ v : Val, a = v.toAdmin ∧ adminToV a = .case op x := by
  obtain ⟨v, rfl⟩ := Typing.head_val ((adminToVD_case h) ▸ hop)
  exact ⟨v, rfl, (Round7.MemSimd.adminToVD_eq _ (adminMS_val v)) ▸ h⟩

/-- **The left-hand side `(s; f); val^n (REF.FUNC_ADDR a) (CALL_REF yy)` of the host-call rules,
decoded from a `configVD` image.** -/
theorem hostLhsD_of {B : Builtins} {σ : List (IL.Id × Value)} {s : Store H} {f : Frame}
    {code : List Admin} {sv fv av yy : Value}
    (fs : (VarEnv.empty.bindVals σ).findVal? "s" = some sv)
    (ff : (VarEnv.empty.bindVals σ).findVal? "f" = some fv)
    (fa : (VarEnv.empty.bindVals σ).findVal? "a" = some av)
    (fy : (VarEnv.empty.bindVals σ).findVal? "yy" = some yy)
    (htv : ∀ ws, (VarEnv.empty.bindVals σ).findVal? "val*" = some (.list ws) →
      HasTyp (simEnv B) (VarEnv.empty.bindVals σ) valsT (.list ws))
    (hl : EvalExp (simEnv B) (VarEnv.empty.bindVals σ) (.caseE "%;%" (.tupE [.caseE "%;%"
      (.tupE [.varE "s", .varE "f"]), .catE (valsNPat "val" "val*" "n")
        (.listE [.caseE "REF.FUNC_ADDR" (.varE "a"), .caseE "CALL_REF" (.varE "yy")])]))
      (configVD hn ⟨s, f, code⟩)) :
    HostLhsD (hn := hn) s f code (VarEnv.empty.bindVals σ) := by
  obtain ⟨x, hx, hc⟩ := cfgSt_inv hl fs ff
  have e₀ : stateVD hn s f = stV sv fv ∧ Value.list (adminsToVD code) = x :=
    Bwd.tuple2_inj (Value.case.inj hc).2
  have es : storeVD hn s = sv ∧ frameV f = fv := Bwd.stV_inj e₀.1
  obtain ⟨ws, fw, fn, hcode⟩ := Bwd.valsN_cat (e₀.2.symm ▸ hx)
    (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case (evalExp_var fy)))
  have hmap : code.map adminToVD = ws ++ [.case "REF.FUNC_ADDR" av, .case "CALL_REF" yy] := by
    rw [← adminsToVD_eq_map]; exact Value.list.inj hcode
  obtain ⟨l₀, rest, rfl, h₀, hrest⟩ := List.map_eq_append_iff.1 hmap
  have hws : adminsToVD l₀ = ws := by rw [adminsToVD_eq_map]; exact h₀
  obtain ⟨vs, rfl⟩ := vals_of_typedD (B := B) ⟨rfl, rfl, rfl⟩ (hws ▸ htv ws fw)
  obtain ⟨b, c₀, rfl, hb, hc₀⟩ : ∃ b c₀, rest = [b, c₀] ∧
      adminToVD b = .case "REF.FUNC_ADDR" av ∧ adminToVD c₀ = .case "CALL_REF" yy := by
    match rest, hrest with
    | [b, c₀], h =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
      exact ⟨b, c₀, rfl, h.1, h.2⟩
    | [], h => simp at h
    | [_], h => simp at h
    | _ :: _ :: _ :: _, h => simp at h
  obtain ⟨v, rfl, hbv⟩ := adminToVD_val hb (by simp [Typing.valHeads])
  obtain ⟨addr, hv, hav⟩ := Bwd.decode_refFuncAddr hbv
  have hcr : c₀.IsCallRef := Typing.head_callRef (adminToVD_case hc₀).symm
  have hws' : ws = vs.map valV := by
    rw [← hws, Round7.MemSimd.adminsToVD_vals, adminsToV_vals]
  exact ⟨⟨vs, addr, c₀, by rw [hv], hcr, hav ▸ fa, hws' ▸ fn, hws' ▸ fw⟩,
    es.1.symm ▸ fs, es.2.symm ▸ ff⟩

/-! ## The premises at `funcInstVD` images -/

/-- `$funcinst(e)[a] = fi`, read back at a `stateVD` image. -/
theorem funcinstD_of_eval {B : Builtins} {s : Store H} {f : Frame} {ρ : VarEnv}
    {ez : Exp} {addr : Nat} {fv : Value} (hd : ρ.findDef? "funcinst" = none)
    (hz : EvalExp (simEnv B) ρ ez (stateVD hn s f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr))) (ffi : ρ.findVal? "fi" = some fv)
    (h : EvalExp (simEnv B) ρ (.cmpE .eqOp .boolT
      (.idxE (.callE "funcinst" [.expA ez]) (.varE "a")) (.varE "fi")) (.bool true)) :
    ∃ fn, s.funcs[addr]? = some fn ∧ fv = funcInstVD hn fn := by
  obtain ⟨v, h₁, h₂⟩ := Bwd.eq_of_cmp h
  have ev : v = fv := EvalExp.unique h₂ (evalExp_var ffi)
  obtain ⟨wl, i, hwl, hi, hidx⟩ := evalExp_idxE_iff.1 h₁
  have hap : Applies (simEnv B) "funcinst" [.val (stateVD hn s f)] wl :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons hz (evalArgs_nil _ ρ))).2 (evalExp_callE_iff.1 hwl)
  have ewl : wl = .list (s.funcs.map (funcInstVD hn)) :=
    Equiv.ExecNumeric.Applies.unique hap (applies_funcinstD B s f)
  have ei : Value.num (.natN i) = .num (.natN addr) := EvalExp.unique hi (evalExp_var fa)
  have hget : (s.funcs.map (funcInstVD hn))[addr]? = some v := by
    rw [← Bwd.natN_inj ei]
    simpa [Value.idx?, ewl] using hidx
  rw [List.getElem?_map] at hget
  obtain ⟨fn, hfn, hfv⟩ := Option.map_eq_some_iff.1 hget
  exact ⟨fn, hfn, by rw [← ev, ← hfv]⟩

/-- `fi.CODE = _HOSTFUNC hf`, read back at a `funcInstVD` image. -/
theorem hostCodeD_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {hfv : Value}
    (ffi : ρ.findVal? "fi" = some (funcInstVD hn fn)) (fh : ρ.findVal? "hf" = some hfv)
    (h : EvalExp env ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE")
      (.caseE "_HOSTFUNC" (.varE "hf"))) (.bool true)) :
    ∃ hh, fn.code = .host hh ∧ hfv = .text (hn hh) := by
  obtain ⟨v, h₁, h₂⟩ := Bwd.eq_of_cmp h
  have e₂ : v = .case "_HOSTFUNC" hfv := EvalExp.unique h₂ (evalExp_case (evalExp_var fh))
  obtain ⟨fv, hfv', hfld⟩ := evalExp_dotE_iff.1 h₁
  have efv : fv = funcInstVD hn fn := EvalExp.unique hfv' (evalExp_var ffi)
  rw [efv, e₂] at hfld
  cases hc : fn.code with
  | wasm code => simp [funcInstVD, Value.field?, hc] at hfld
  | host hh =>
    simp only [funcInstVD, Value.field?, hc] at hfld
    simp only [List.find?] at hfld
    exact ⟨hh, rfl, (Value.case.inj (Option.some.inj hfld)).2.symm⟩

/-- The `TYPE` of a `funcInstVD` image. -/
theorem funcInstVD_type_of_eval {env : Env} {ρ : VarEnv} {fn : FuncInst H} {ty : Value}
    (ffi : ρ.findVal? "fi" = some (funcInstVD hn fn))
    (h : EvalExp env ρ (.dotE (.varE "fi") "TYPE") ty) : ty = CT.defType fn.type := by
  obtain ⟨fv, hfv, hfld⟩ := evalExp_dotE_iff.1 h
  have efv : fv = funcInstVD hn fn := EvalExp.unique hfv (evalExp_var ffi)
  rw [efv] at hfld
  simp [funcInstVD, Value.field?] at hfld
  exact hfld.symm

/-- **The three premises of the host-call rules on `fi`, read back at `BD`.** -/
theorem hostPremsD {D' : Interp} {els : Prop} {ρ : VarEnv} {s : Store H} {f : Frame}
    {addr : Nat} {vs : List Val} {fiv hfv : Value} (hd : ρ.findDef? "funcinst" = none)
    (fs : ρ.findVal? "s" = some (storeVD hn s)) (ff : ρ.findVal? "f" = some (frameV f))
    (fa : ρ.findVal? "a" = some (.num (.natN addr))) (ffi : ρ.findVal? "fi" = some fiv)
    (fh : ρ.findVal? "hf" = some hfv)
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (h₁ : EvalExp (simEnv (BD P hn host)) ρ (.cmpE .eqOp .boolT (.idxE (.callE "funcinst"
      [.expA (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))]) (.varE "a")) (.varE "fi")) (.bool true))
    (h₂ : PremW (simEnv (BD P hn host)) D' els ρ (.rulePr "Expand" [] "%~~%"
      (.tupE [.dotE (.varE "fi") "TYPE",
      .caseE "FUNC%->%" (.tupE [.caseE "%" (.tupE [.iterE (.varE "t_1")
        (.mk (.listN (.varE "n") none) [.mk "t_1" (.varE "t_1*")])]),
      .caseE "%" (.tupE [.iterE (.varE "t_2")
        (.mk (.listN (.varE "m") none) [.mk "t_2" (.varE "t_2*")])])])])))
    (hexp : ∀ w, D' "Expand" "%~~%" [] w → DDerives (simEnv (BD P hn host))
      (otherwise (simEnv (BD P hn host))) "Expand" "%~~%" [] w)
    (h₃ : EvalExp (simEnv (BD P hn host)) ρ (.cmpE .eqOp .boolT (.dotE (.varE "fi") "CODE")
      (.caseE "_HOSTFUNC" (.varE "hf"))) (.bool true)) :
    ∃ fn₀ ps rs hh, s.funcs[addr]? = some fn₀ ∧ fiv = funcInstVD hn fn₀ ∧
      Expand fn₀.type (.func ps rs) ∧ vs.length = ps.length ∧ fn₀.code = .host hh ∧
      hfv = .text (hn hh) := by
  have hz : EvalExp (simEnv (BD P hn host)) ρ (.caseE "%;%" (.tupE [.varE "s", .varE "f"]))
      (stateVD hn s f) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs) (evalExp_var ff))
  obtain ⟨fn₀, hfn, rfl⟩ := funcinstD_of_eval hd hz fa ffi h₁
  obtain ⟨w', hw', hd'⟩ := Bwd.rulePrem_inv h₂
  obtain ⟨ty, ftv, hty, hft, rfl⟩ := Bwd.tup2_inv hw'
  obtain ⟨T₁, T₂, fn₁, -, rfl⟩ := Bwd.funcTypePat_inv hft
  have hE : DDerives (simEnv (BD P hn host)) (otherwise (simEnv (BD P hn host))) "Expand" "%~~%"
      [] (.tuple [CT.defType fn₀.type, .case "FUNC%->%" (.tuple [.case "%" (.tuple [.list T₁]),
        .case "%" (.tuple [.list T₂])])]) := funcInstVD_type_of_eval ffi hty ▸ hexp _ hd'
  obtain ⟨ps, rs, hex, hl₁, -⟩ := callInvD.expand fn₀.type T₁ T₂ hE
  obtain ⟨hh, hcode₀, rfl⟩ := hostCodeD_of_eval ffi fh h₃
  have hnl : vs.length = ps.length := by
    rw [← hl₁, ← List.length_map (f := valV)]
    exact Bwd.natN_inj (Option.some.inj (fn.symm.trans fn₁))
  exact ⟨fn₀, ps, rs, hh, hfn, rfl, hex, hnl, hcode₀, rfl⟩

/-- `o ∈ $hostcall(_HOSTFUNC hf, s, val^n)` at `BD`, read back on a typed `storeVD` image. -/
theorem hostMemD_of_eval (hinj : Function.Injective hn) (hf : HostFinite host) {ρ : VarEnv}
    {s₀ : Store H} {hh : H} {vs : List Val} {oe : Exp} {o : Value}
    (hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s₀))
    (hd : ρ.findDef? "hostcall" = none)
    (fs : ρ.findVal? "s" = some (storeVD hn s₀)) (fh : ρ.findVal? "hf" = some (.text (hn hh)))
    (fn : ρ.findVal? "n" = some (.num (.natN (vs.map valV).length)))
    (fw : ρ.findVal? "val*" = some (.list (vs.map valV)))
    (ho : EvalExp (simEnv (BD P hn host)) ρ oe o)
    (h : EvalExp (simEnv (BD P hn host)) ρ (.memE oe (.callE "hostcall"
      [.expA (.caseE "_HOSTFUNC" (.varE "hf")), .expA (.varE "s"), .expA (.iterE (.varE "val")
        (.mk (.listN (.varE "n") none) [.mk "val" (.varE "val*")]))])) (.bool true)) :
    ∃ out, host hh s₀ vs out ∧ o = outcomeVD hn out := by
  obtain ⟨v₁, v₂, h₁, h₂, hm⟩ := evalExp_memE_iff.1 h
  have e₁ : v₁ = o := EvalExp.unique h₁ ho
  have hap : Applies (simEnv (BD P hn host)) "hostcall" (hostArgsD hn hh s₀ vs) v₂ :=
    (applies_iff_callDef hd (Equiv.evalArgs_cons (evalExp_case (evalExp_var fh))
      (Equiv.evalArgs_cons (evalExp_var fs) (Equiv.evalArgs_cons
        (evalExp_iterNVar (by decide) fn fw) (evalArgs_nil _ ρ))))).2 (evalExp_callE_iff.1 h₂)
  exact Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.HostD.hostInvD_typed hf
    (Round7.HostD.hostRespectsDT_all _ hinj host) hst hap (e₁ ▸ hm)

/-- An `outcomeVD` image headed `RES`. -/
theorem outcomeD_res {out : Execution.Host.Outcome (Store H) Result} {sv rv : Value}
    (h : Value.case "RES" (.tuple [sv, rv]) = outcomeVD hn out) :
    ∃ s₂ r, out = .returned s₂ r ∧ sv = storeVD hn s₂ ∧ rv = resultV r := by
  cases out with
  | returned s₂ r =>
    have e := Bwd.tuple2_inj (Value.case.inj h).2
    exact ⟨s₂, r, rfl, e.1, e.2⟩
  | diverged => exact absurd (Value.case.inj h).1 (by decide)

/-- An `outcomeVD` image headed `BOT`. -/
theorem outcomeD_bot {out : Execution.Host.Outcome (Store H) Result}
    (h : Equiv.Execution.caseNilV "BOT" = outcomeVD hn out) : out = .diverged := by
  cases out with
  | returned s₂ r => exact absurd (Value.case.inj h).1 (by decide)
  | diverged => rfl

/-! ## The two rules -/

/-- **`Step` rule 8 (`call_ref-hostfunc-res`) backward, at `configVD` and `BD`**: a firing from
the `configVD` image of a configuration with a typed image is the image of a Core host-call
step. The store may hold memory SIMD code. -/
theorem bwd_callRefHostD (hinj : Function.Injective hn) (hf : HostFinite host)
    (c : Config H) (w : Value) (ht : TypedD (simEnv (BD P hn host)) hn c)
    (hfi : Fires (simEnv (BD P hn host)) "Step" 8 (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w := by
  obtain ⟨s, f, code⟩ := c
  have TD := typingFactsD_simEnv (BD P hn host) hn
  have hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s) :=
    ((TD.state _ _).1 ((TD.config _).1 ht).1).1
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv _).callRefHostfuncRes hfi)
  obtain ⟨sv, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨fv, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hlr := Exn.evalExp_tup2_inv he
  have hL : HostLhsD (hn := hn) s f code (VarEnv.empty.bindVals σ) :=
    hostLhsD_of fs ff fa fy (valsTyped_of hq (.tail _ (.tail _ (.tail _ (.head _))))) hlr.1
  obtain ⟨⟨vs, addr, c₀, rfl, hcr, fa', fn, fw⟩, fs', ff'⟩ := hL
  obtain ⟨s'v, fs'', -⟩ := quant_of (x := "s'") (t := storeT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨rv, fr, -⟩ := quant_of (x := "result") (t := resultT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
  obtain ⟨hfv, fh, -⟩ := quant_of (x := "hf") (t := .textT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.tail _ (.tail _ (.head _)))))))))))))
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPremsD rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h)
    (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  have hres : EvalExp (simEnv (BD P hn host)) _ (.caseE "RES" (.tupE [.varE "s'", .varE "result"]))
      (.case "RES" (.tuple [s'v, rv])) :=
    evalExp_case (evalExp_tup2 (evalExp_var fs'') (evalExp_var fr))
  obtain ⟨out, hhost, hout⟩ := hostMemD_of_eval hinj hf hst rfl fs' (hhv ▸ fh) fn fw hres
    (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  obtain ⟨s₂, r, rfl, hs₂, hr₂⟩ := outcomeD_res hout
  obtain ⟨x, hx, hw⟩ := cfgSt_inv hlr.2 fs'' ff'
  have hx' : x = .list (adminsToVD r.toAdmin) := by
    rw [adminsToVD_eq _ (adminsMS_result r)]
    exact Equiv.ExecNumeric.Applies.unique (applies_of_call1 rfl fr hx)
      (hr₂ ▸ Prims.applies_liftResult _ r)
  have hw' : w = configVD hn ⟨s₂, f, r.toAdmin⟩ := by
    rw [hw, hx', hs₂]
    rfl
  exact ⟨_, _, Bwd.ConfigEq.refl _, hw', .callRefHost hcr hfn hex hnl hcode₀ hhost⟩

/-- **`Step` rule 9 (`call_ref-hostfunc-div`) backward, at `configVD` and `BD`.** -/
theorem bwd_callRefHostDivD (hinj : Function.Injective hn) (hf : HostFinite host)
    (c : Config H) (w : Value) (ht : TypedD (simEnv (BD P hn host)) hn c)
    (hfi : Fires (simEnv (BD P hn host)) "Step" 9 (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w := by
  obtain ⟨s, f, code⟩ := c
  have TD := typingFactsD_simEnv (BD P hn host) hn
  have hst : TypedV (simEnv (BD P hn host)) storeT (storeVD hn s) :=
    ((TD.state _ _).1 ((TD.config _).1 ht).1).1
  obtain ⟨σ, hq, he, hp⟩ :=
    ruleBody_scope (fires_body (hasStepRules_simEnv _).callRefHostfuncDiv hfi)
  obtain ⟨sv, fs, -⟩ := quant_of (x := "s") (t := storeT) hq (.head _)
  obtain ⟨fv, ff, -⟩ := quant_of (x := "f") (t := frameT) hq (.tail _ (.head _))
  obtain ⟨av, fa, -⟩ := quant_of (x := "a") (t := addrT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨yy, fy, -⟩ := quant_of (x := "yy") (t := typeuseT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hlr := Exn.evalExp_tup2_inv he
  have hw : w = configVD hn ⟨s, f, code⟩ := EvalExp.unique hlr.2 hlr.1
  have hL : HostLhsD (hn := hn) s f code (VarEnv.empty.bindVals σ) :=
    hostLhsD_of fs ff fa fy (valsTyped_of hq (.tail _ (.tail _ (.tail _ (.head _))))) hlr.1
  obtain ⟨⟨vs, addr, c₀, rfl, hcr, fa', fn, fw⟩, fs', ff'⟩ := hL
  obtain ⟨fiv, ffi, -⟩ := quant_of (x := "fi") (t := funcinstT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  obtain ⟨hfv, fh, -⟩ := quant_of (x := "hf") (t := .textT) hq
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
      (.head _)))))))))))
  obtain ⟨fn₀, ps, rs, hh, hfn, -, hex, hnl, hcode₀, hhv⟩ := hostPremsD rfl fs' ff' fa'
    ffi fh fn (ifPrem (hp _ (.head _))) (hp _ (.tail _ (.head _))) (fun _ h => h)
    (ifPrem (hp _ (.tail _ (.tail _ (.head _)))))
  obtain ⟨out, hhost, hout⟩ := hostMemD_of_eval hinj hf hst rfl fs' (hhv ▸ fh) fn fw
    evalExp_caseNil (ifPrem (hp _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hdiv : out = .diverged := outcomeD_bot hout
  exact ⟨_, _, Bwd.ConfigEq.refl _, hw, .callRefHostDiv hcr hfn hex hnl hcode₀ (hdiv ▸ hhost)⟩

/-- **The host-call obligations of round 7's dispatch at `BD`**: the fields for `Step` rules 8
and 9 of `MemSimd.BackwardUpToD` at `simEnv (BD …)`, under any predicate. -/
theorem hostStepsD (hinj : Function.Injective hn) (hf : HostFinite host) {i : Nat}
    (hi : i ∈ [8, 9]) (c : Config H) (w : Value) (ht : TypedD (simEnv (BD P hn host)) hn c)
    (hfi : Fires (simEnv (BD P hn host)) "Step" i (.tuple [configVD hn c, w])) :
    BwdUpToD hn P host c w := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact bwd_callRefHostD hinj hf c w ht hfi
  · exact bwd_callRefHostDivD hinj hf c w ht hfi

end Silmaril.Wasm.SpecTec.Sim.Round7.HostRulesD
