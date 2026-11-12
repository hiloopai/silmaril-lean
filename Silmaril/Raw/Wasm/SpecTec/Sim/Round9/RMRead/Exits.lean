module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round9.RMPure.Counted
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms

/-!
# Round 9, rm: the exit rules of `Step_read` backward at `configVD` (unrefined)

Round 6's leaves for the `Step_read` rules that move a `return_call_ref` or a thrown exception out
of a label, handler or frame, re-run at `configVD`: the code may hold memory SIMD instructions in
the parts the rule carries or discards. None reads the state. Rules 8, 9, 10
(`return_call_ref-label`, `-handler`, `-frame-null`), 13 (`throw_ref-instrs`), 14, 15, 16
(`throw_ref-label`, `-frame`, `-handler-empty`), 19, 20 (`throw_ref-handler-catch_all`,
`-catch_all_ref`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMRead

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV iterPat valsPat valsNPat evalExp_iterPat
  evalExp_valsPat)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round7.MemSimd (configVD adminsToVD adminToVD instrsToVD adminsToVD_eq_single
  adminsToVD_eq_pair adminsToVD_append adminsToVD_vals configVD_cfgV)
open RMPure (toV_of_atomD labelD_of handlerD_of frameD_of valsD_of splitD_of adminsToVD_eq_split)

variable {H : Type} {hn : H → String} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H}

/-- **The backward obligation of a `Step_read` rule at `configVD`.** -/
def LeafRD (B : Builtins) (hn : H → String) (P : Silmaril.Wasm.Numerics.Profile)
    (host : HostSemantics H) (i : Nat) : Prop :=
  ∀ (c : Config H) (w : Value), Fires (simEnv B) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is', w = .list (adminsToVD is') ∧ Step P host c ⟨c.store, c.frame, is'⟩

/-- `RETURN_CALL_REF` at `adminToVD`. -/
theorem retCallRefD_of {a : Admin} {x : Value} (h : adminToVD a = .case "RETURN_CALL_REF" x) :
    a.IsReturnCallRef ∧ adminToV a = .case "RETURN_CALL_REF" x := by
  have h' := toV_of_atomD h rfl
  exact ⟨Bwd.retDecode.returnCallRef a x h', h'⟩

/-- `(REF.EXN_ADDR a) THROW_REF` at `adminsToVD`: the code is `throwing k`. -/
theorem throwingD_of {l : List Admin} {v : Value}
    (h : adminsToVD l = [.case "REF.EXN_ADDR" v, .case "THROW_REF" (.tuple [])]) :
    ∃ k, l = throwing k ∧ v = .num (.natN k) := by
  obtain ⟨a, b, rfl, ha, hb⟩ := adminsToVD_eq_pair h
  have ha' := toV_of_atomD ha rfl
  have hb' := toV_of_atomD hb rfl
  exact Exn.adminsToV_eq_throwing (by simp only [adminsToV, ha', hb'])

/-- The image of `throwing k` at `adminsToVD`. -/
theorem adminsToVD_throwing (k : Nat) : adminsToVD (throwing k) = adminsToV (throwing k) := rfl

/-- A thrown exception in a rule's instruction pattern, at `adminsToVD`. -/
theorem throwExnD_decode {B : Builtins} {ρ : VarEnv} {body : List Admin} {w : Value}
    (h : EvalExp (simEnv B) ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"),
      .caseE "THROW_REF" (.tupE [])]) (.list (adminsToVD body)))
    (hw : EvalExp (simEnv B) ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"),
      .caseE "THROW_REF" (.tupE [])]) w) :
    ∃ k, body = throwing k ∧ ρ.findVal? "a" = some (.num (.natN k)) ∧
      w = .list (adminsToVD (throwing k)) := by
  obtain ⟨av, fa, hl⟩ := Exn.evalExp_throwExn_inv h
  obtain ⟨k, rfl, rfl⟩ := throwingD_of hl
  exact ⟨k, rfl, fa, EvalExp.unique hw (Exn.evalExp_throwExn fa)⟩

/-- A `LABEL_`, `HANDLER_` or `FRAME_` image at `adminToVD`, with an arbitrary payload. -/
theorem ctxD_of {a : Admin} {op : MixopS} {u : Value} (h : adminToVD a = .case op u)
    (hop : op = "LABEL_%{%}%" ∨ op = "HANDLER_%{%}%" ∨ op = "FRAME_%{%}%") :
    ∃ x y body, u = .tuple [x, y, .list (adminsToVD body)] := by
  have hh := Round7.MemSimd.adminToVD_case h
  cases a with
  | plain i =>
    rcases hop with rfl | rfl | rfl <;> cases i <;> simp [Typing.adminHead, Typing.instrHead] at hh
  | ref r =>
    rcases hop with rfl | rfl | rfl <;> cases r <;> simp [Typing.adminHead, Typing.refHead] at hh
  | label k cont body =>
    simp only [adminToVD, Value.case.injEq] at h
    exact ⟨_, _, body, h.2.symm⟩
  | handler k cs body =>
    simp only [adminToVD, Value.case.injEq] at h
    exact ⟨_, _, body, h.2.symm⟩
  | frame k fi body =>
    simp only [adminToVD, Value.case.injEq] at h
    exact ⟨_, _, body, h.2.symm⟩
  | _ => rcases hop with rfl | rfl | rfl <;> simp [Typing.adminHead] at hh

/-- The context rules' left-hand code `C{x y} (REF.EXN_ADDR a) THROW_REF`, at `adminsToVD`. -/
theorem throwCtxD {B : Builtins} {ρ : VarEnv} {op : MixopS} {e₁ e₂ : Exp} {code : List Admin}
    {w : Value} (hop : op = "LABEL_%{%}%" ∨ op = "HANDLER_%{%}%" ∨ op = "FRAME_%{%}%")
    (hce : EvalExp (simEnv B) ρ (.listE [.caseE op (.tupE [e₁, e₂, .listE
      [.caseE "REF.EXN_ADDR" (.varE "a"), .caseE "THROW_REF" (.tupE [])]])])
      (.list (adminsToVD code)))
    (hre : EvalExp (simEnv B) ρ (.listE [.caseE "REF.EXN_ADDR" (.varE "a"),
      .caseE "THROW_REF" (.tupE [])]) w) :
    ∃ a x y k, code = [a] ∧
      adminToVD a = .case op (.tuple [x, y, .list (adminsToVD (throwing k))]) ∧
      EvalExp (simEnv B) ρ e₂ y ∧ ρ.findVal? "a" = some (.num (.natN k)) ∧
      w = .list (adminsToVD (throwing k)) := by
  obtain ⟨x, hx, hxe⟩ := Exn.evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨x', y', body, rfl⟩ := ctxD_of ha hop
  obtain ⟨-, h₂, h₃⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨k, rfl, fa, hw⟩ := throwExnD_decode h₃ hre
  exact ⟨a, x', y', k, rfl, ha, h₂, fa, hw⟩

theorem bwdRD_throwRefLabel (B : Builtins) : LeafRD B hn P host 14 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefLabel hf
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨a, x, y, k, rfl, ha, -, -, rfl⟩ := throwCtxD (.inl rfl) hce hre
  obtain ⟨n, cont, body, rfl, -, -, hb⟩ := labelD_of ha
  obtain ⟨k', rfl, hk⟩ := throwingD_of (v := .num (.natN k)) ((Value.list.inj hb).symm.trans rfl)
  obtain rfl : k = k' := Bwd.natN_inj hk
  exact ⟨_, rfl, .throwRefLabel⟩

theorem bwdRD_throwRefFrame (B : Builtins) : LeafRD B hn P host 15 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ := Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefFrame hf
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨a, x, y, k, rfl, ha, -, -, rfl⟩ := throwCtxD (.inr (.inr rfl)) hce hre
  obtain ⟨n, fi, body, rfl, -, -, hb⟩ := frameD_of ha
  obtain ⟨k', rfl, hk⟩ := throwingD_of (v := .num (.natN k)) ((Value.list.inj hb).symm.trans rfl)
  obtain rfl : k = k' := Bwd.natN_inj hk
  exact ⟨_, rfl, .throwRefFrame⟩

theorem bwdRD_throwRefHandlerEmpty (B : Builtins) : LeafRD B hn P host 16 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerEmpty hf
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨a, x, y, k, rfl, ha, hy, -, rfl⟩ := throwCtxD (.inr (.inl rfl)) hce hre
  obtain ⟨n, cs, body, rfl, -, hcs, hb⟩ := handlerD_of ha
  obtain ⟨k', rfl, hk⟩ := throwingD_of (v := .num (.natN k)) ((Value.list.inj hb).symm.trans rfl)
  obtain rfl : k = k' := Bwd.natN_inj hk
  obtain rfl : cs = [] := by
    have h0 := evalExps_nil_iff.1 (Exn.evalExp_list_inv (hcs ▸ hy))
    simpa using h0
  exact ⟨_, rfl, .throwRefHandlerEmpty⟩

theorem bwdRD_throwRefHandlerCatchAll (B : Builtins) : LeafRD B hn P host 19 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerCatchAll hf
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨x, hx, hxe⟩ := Exn.evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨x', y', body, rfl⟩ := ctxD_of ha (.inr (.inl rfl))
  obtain ⟨n, cs, body', rfl, -, hcs, hb'⟩ := handlerD_of ha
  obtain ⟨-, h₂, h₃⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨c₀, cs₀, lw, rfl, hc₀, hlw⟩ := Exn.catch_head' (hcs ▸ h₂)
  obtain ⟨l, rfl, rfl⟩ := (Exn.catch_decode hc₀).2.2.1 rfl
  obtain ⟨av, -, hl⟩ := Exn.evalExp_throwExn_inv (hb' ▸ h₃)
  obtain ⟨k, rfl, -⟩ := throwingD_of hl
  refine ⟨[.plain (.br l)], ?_, .throwRefHandlerCatchAll⟩
  exact EvalExp.unique hre (evalExp_list1 (evalExp_case hlw))

theorem bwdRD_throwRefHandlerCatchAllRef (B : Builtins) : LeafRD B hn P host 20 := by
  rintro ⟨s, f, code⟩ w hf
  obtain ⟨-, ρ₀, σ, -, -, he, -⟩ :=
    Exn.fires_body (Exn.hasReadRules_simEnv B).throwRefHandlerCatchAllRef hf
  obtain ⟨-, hce, hre⟩ := Exn.evalExp_concl_inv (Round7.MemSimd.configVD_eq hn _ ▸ he)
  obtain ⟨x, hx, hxe⟩ := Exn.evalExp_list1_inv' hce
  obtain ⟨a, rfl, ha⟩ := adminsToVD_eq_single hx
  obtain ⟨u, hu, rfl⟩ := evalExp_caseE_iff.1 hxe
  obtain ⟨x', y', body, rfl⟩ := ctxD_of ha (.inr (.inl rfl))
  obtain ⟨n, cs, body', rfl, -, hcs, hb'⟩ := handlerD_of ha
  obtain ⟨-, h₂, h₃⟩ := Exn.evalExp_tup3_inv hu
  obtain ⟨c₀, cs₀, lw, rfl, hc₀, hlw⟩ := Exn.catch_head' (hcs ▸ h₂)
  obtain ⟨l, rfl, rfl⟩ := (Exn.catch_decode hc₀).2.2.2 rfl
  obtain ⟨av, fa, hl⟩ := Exn.evalExp_throwExn_inv (hb' ▸ h₃)
  obtain ⟨k, rfl, rfl⟩ := throwingD_of hl
  refine ⟨[.ref (.exn k), .plain (.br l)], ?_, .throwRefHandlerCatchAllRef⟩
  exact EvalExp.unique hre (evalExp_list2 (evalExp_case (evalExp_var fa)) (evalExp_case hlw))

end Silmaril.Wasm.SpecTec.Sim.Round9.RMRead
