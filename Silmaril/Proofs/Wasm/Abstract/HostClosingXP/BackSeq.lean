module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackTy
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackCall

/-!
# The logged backward simulation: sequences and operator sites (proofs)

* `seq_part`: a labelled run of `tcode stk A ++ B` splits at the end of `A`; `A`'s part is a
  resolved logged run (`BackG`); if it completes normally the run goes on from its values in
  front of `B`, otherwise the log ends with `A`'s part (read off later by `mkOut'`);
* `site_facts`: the facts at an operator's site after its arguments (the check, the arity
  invariant, typing in context, the tag invariants);
* `call_ret_facts`: a returning answer of the closure, at a checked call: the callee's result
  arity, the tag invariants and store check after it, and its logged Core run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

theorem vals_ne_trap' {ws : List Val} : vals ws ≠ [.trap] := by
  intro h
  have hm : Admin.trap ∈ vals ws := h ▸ List.mem_singleton_self _
  obtain ⟨v, -, hv⟩ := List.mem_map.1 hm
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv

theorem vals_ne_throwing {ws : List Val} {x : Nat} : vals ws ≠ throwing x := by
  intro h
  have hm : Admin.plain .throwRef ∈ vals ws := h ▸ (by simp [throwing])
  obtain ⟨v, -, hv⟩ := List.mem_map.1 hm
  rcases v with ⟨⟨_ | _⟩, _⟩ | _ | _ <;> simp [Val.toAdmin] at hv

/-- A typed problem, with no code after it. -/
theorem typedP_of {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {labels : List Nat} {ret : Nat} {out : Option Nat} (hS : StoreChkE (ehExt tags) s.funcs)
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length) es =
      some out)
    (hct : Sim.ContextTyped ⟨s, f, tcode stk es⟩) (hTM : Abstract.CallXT.TyTypes f.module)
    (hts : TagsOk tags s) : TypedP tags s f stk es :=
  ⟨[], labels, ret, out, hS, hc, by simpa using hct, hTM, hts⟩

theorem typedP_ctx {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (ht : TypedP tags s f stk es) : Sim.ContextTyped ⟨s, f, tcode stk es⟩ := by
  obtain ⟨rest, -, -, -, -, -, hct, -, -⟩ := ht
  exact Sim.ContextTyped.suffix (rest := rest) (by simpa only [List.append_assoc] using hct)

/-- **A labelled run of a sequence, split at the end of its first part.** -/
theorem seq_part {n : Nat} {s : Store H} {f : Frame} {stk : List Val} {A : List Binaryen.BExpr}
    {B : List Admin} {c : Config H} {cs : List (Call (wasmHostSig H))}
    (hA : TypedP tags s f stk A) (ihA : ∀ m ≤ n, BackG tags o host m A)
    (hrun : EvRunN (profile o) host n ⟨s, f, tcode stk A ++ B⟩ cs c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') (hnd : decompose? c.store c.code = none) :
    ∃ (l : List (OCall H)) (r : Store H × Frame × POut) (cs₁ cs₂ : List (Call (wasmHostSig H))),
      cs = cs₁ ++ cs₂ ∧ EvalLXPh s f stk A l r ∧ ResX l r cs₁ ∧
      (¬ r.2.2.IsNormal ∨
        ∃ (s₁ : Store H) (f₁ : Frame) (stk₁ : List Val) (m : Nat),
          r = (s₁, f₁, .flow (.normal stk₁)) ∧ Shape.SubstPre Cl (l.map OCall.lift) cs₁ ∧ m ≤ n ∧
          EvRunN (profile o) host m ⟨s₁, f₁, vals stk₁.reverse ++ B⟩ cs₂ c ∧
          Steps (profile o) host ⟨s, f, tcode stk A ++ B⟩ ⟨s₁, f₁, vals stk₁.reverse ++ B⟩) := by
  obtain ⟨c₁, n₁, cs₁, cs₂, rfl, h₁, hn₁, hend₁, hk⟩ := evRunN_seq_split hrun hend
  have hnd₁ : decompose? c₁.store c₁.code = none := by
    rcases hk with ⟨ws, hw, -⟩ | ⟨-, rfl, -⟩ | ⟨x, -, rfl, -⟩ | ⟨rfl, -⟩
    · rw [hw]; exact decompose?_vals_nil
    · exact hnd
    · exact hnd
    · cases hdc : decompose? c₁.store c₁.code with
      | none => rfl
      | some x =>
        exfalso
        have := decompose?_wrap_seq (ws := []) (rest := B)
          (show (decompose? c₁.store c₁.code).isSome by rw [hdc]; rfl)
        simp only [vals, List.map_nil, List.nil_append] at this
        rw [hnd] at this
        cases this
  obtain ⟨l, r, hd, hres, hok⟩ := ihA n₁ hn₁ s f stk c₁ cs₁ hA h₁ hend₁ hnd₁
  refine ⟨l, r, cs₁, cs₂, rfl, hd, hres, ?_⟩
  by_cases hn : r.2.2.IsNormal
  swap
  · exact .inl hn
  right
  obtain ⟨s₁, f₁, o₁⟩ := r
  obtain ⟨stk₁, rfl⟩ := POut.normal_of hn
  have hq : Shape.SubstPre Cl (l.map OCall.lift) cs₁ := by
    rcases hres with h | ⟨h, -⟩
    · exact h
    · cases h
  rcases hok with ⟨oc, he, hm⟩ | ⟨h, -⟩
  swap
  · cases h
  obtain ⟨hs₁, hf₁, hfm⟩ := match_of_matchP (fl := .normal stk₁) (by simp) hm
  have hc₁ : c₁.code = vals stk₁.reverse := ends_normal hfm he
  obtain ⟨cst, cfr, ccd⟩ := c₁
  simp only at hs₁ hf₁ hc₁
  subst hs₁ hf₁ hc₁
  rcases hk with ⟨ws, hw, hk⟩ | ⟨hw, -, -⟩ | ⟨x, hw, -, -⟩ | ⟨rfl, rfl⟩
  · obtain rfl : stk₁.reverse = ws := Sim.vals_injective hw
    exact ⟨cst, cfr, stk₁, n - n₁, rfl, hq, by omega, hk, Steps.append B (evRunN_steps h₁)⟩
  · exact (vals_ne_trap' hw).elim
  · exact (vals_ne_throwing hw).elim
  · exact ⟨cst, cfr, stk₁, 0, rfl, hq, by omega, .refl _, Steps.append B (evRunN_steps h₁)⟩

section Site

variable {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
  {args es : List Binaryen.BExpr} {l : List (OCall H)} {cs₁ cs₂ : List (Call (wasmHostSig H))}
  {c : Config H} {n : Nat}

/-- **The facts at an operator's site**, after its arguments completed normally. -/
theorem site_facts (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (ht : TypedP tags s f stk (.op i args :: es))
    (hrun : EvRunN (profile o) host n ⟨s, f, tcode stk (.op i args :: es)⟩ (cs₁ ++ cs₂) c)
    (hd : EvalLXPh s f stk args l (s₁, f₁, .flow (.normal stk₁)))
    (hq : Shape.SubstPre Cl (l.map OCall.lift) cs₁)
    (hst : Steps (profile o) host ⟨s, f, tcode stk (.op i args :: es)⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es)⟩) :
    ∃ (labels : List Nat) (ret : Nat) (out o₁ : Option Nat),
      StoreChkE (ehExt tags) s.funcs ∧
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
        (.op i args :: es) = some out ∧
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels o₁ es = some out ∧
      ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true ∧
      TagsOk tags s₁ ∧
      flatChkE (ehExt tags) s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o₁ ∧
      EvalInvE (ehExt tags) s f (s₁, f₁, .normal stk₁) ∧
      Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ ∧
      Abstract.CallXT.TyTypes f₁.module ∧ Abstract.CallXT.TyFuncs s₁ ∧
      StoreChkE (ehExt tags) s₁.funcs := by
  have hct := typedP_ctx ht
  obtain ⟨-, labels, ret, out, hS, hc, -, hTM, hts⟩ := ht
  have hcons : Cons host cs₁ := (cons_append.1 (evRun_consistent (evRunN_evRun hrun))).1
  obtain ⟨-, t₁, a₁, -⟩ := full_run (P := profile o) hH hE hd
    (substPre_mono (close_le_goodCX hH hE) hq) hcons hts
  obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
  have aha : ArityGoodE (ehExt tags) s f stk args (s₁, f₁, .normal stk₁) true :=
    arityE_of_arityP a₁
  obtain ⟨hf, inv1⟩ := arity_args hS aha h1
  have hsite := ContextTyped.steps_typed hT hct hst
  exact ⟨labels, ret, out, o₁, hS, hc, h2, aha, t₁, hf, inv1, hsite, by rw [inv1.2.1]; exact hTM,
    tyFuncs_of_ctx hsite, storeChk_inv inv1 hS⟩

end Site

/-- **A returning answer of the closure at a checked call**: the callee's result arity, the tag
invariants and the store check after it, and its logged Core run. -/
theorem call_ret_facts (hH : NativeHostSlice host) (hE : HostSliceE tags host) {s₁ s₃ : Store H}
    {a : Nat} {us ws : List Val} {q : List (Call (wasmHostSig H))} {fi : FuncInst H}
    {ps rs : List Validation.CValType}
    (hz : (q, .ret (.inl ws) s₃) ∈ Cl a s₁ us) (hc : Cons host q) (hts : TagsOk tags s₁)
    (hS : StoreChkE (ehExt tags) s₁.funcs) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length) :
    ws.length = rs.length ∧ TagsOk tags s₃ ∧ FuncsGoodE (ehExt tags) s₁.funcs s₃.funcs ∧
      CalleeRun (profile o) host s₁ a us q s₃ (.inl ws) := by
  have hm := close_le_goodCX (P := profile o) (tags := tags) hH hE a s₁ us hz
  obtain ⟨bfl, w, hC, hvs, hws, hlen, hrun⟩ := goodCX_inl hm hc hfi hty
  obtain ⟨⟨ob, hob, hok, hfuncs⟩, -, -⟩ := (oracleSoundTE_hostP (P := profile o) hH hE) s₁ s₃ {}
    a fi ps rs us bfl (.callRefType fi.type) hS hfi hty hn trivial ⟨hts, hC⟩
  have hrs : rs.length ≤ w.length := retVals_length hok hob hvs
  have hwl : ws.length = rs.length := by
    have := congrArg List.length hws
    simp only [List.length_reverse, List.length_take] at this
    omega
  exact ⟨hwl, tagsOk_hostCallXP hH hE hC hts, hfuncs, hrun hts hS hn⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
