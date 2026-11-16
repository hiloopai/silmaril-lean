module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackSeq

/-!
# The logged backward simulation of operators (proofs)

`case_op`: an operator tree `op i args :: es`. Its arguments are split off (`seq_part`); an
abrupt end of the arguments ends the tree (`argsAbort`). After values, the instruction:

* a flat instruction steps by `evalFlat` (`evalFlat_progressH` from typing), the trees after it
  going on, or ending the run abruptly;
* `call`, a resolved `call_indirect` and `call_ref` on a function reference reach a `call_ref`
  form on the callee, which `CallG` resolves: the callee returns (`callRet`, `indRet`, `refRet`)
  or throws (`callThrow`, `indThrow`, `refThrow`) in the closure, or traps there, which is read
  as a cut call (`callCut`, `indCut`, `refCut`), the closure resolving it by
  `Shape.Subst.intTrap`;
* an unresolved `call_indirect` and `call_ref` on null trap (`indRes`, `refNull`);
* the tail call forms end in a pending tail call (`tail`) or trap (`tailRes`);
* `throw` and `throw_ref` raise their exception or trap.

Every abrupt end is read off the forward simulation (`mkOut''`): the run's log ends there.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {host : HostSemantics H} {tags : List TagInst} {o : GrowOracle}

theorem res_one {a : Nat} {us : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    {q : List (Call (wasmHostSig H))} (hz : (q, .ret b s₂) ∈ Cl a s₁ us) :
    Shape.SubstPre Cl ([OCall.mk a us s₁ b s₂].map OCall.lift) q := by
  have := Shape.SubstPre.int (rest := []) hz (Shape.SubstPre.nil (c := Cl))
  rw [List.append_nil] at this
  exact this

/-- A tail check of `return_call_indirect` names a function type. -/
theorem typeArity_some_rci {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {h : Nat} {x : TableIdx} {y : TypeIdx} {o : Option Nat}
    (hc : flatChkE tExt F mi nl ret labels h (.returnCallIndirect x y) = some o) :
    ∃ p, Abstract.CallXT.typeArity mi y = some p := by
  cases hta : Abstract.CallXT.typeArity mi y with
  | none => simp [flatChkE, tExt, hta, extStep] at hc
  | some p => exact ⟨p, rfl⟩

section Op

variable {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ : List Val} {i : Instr}
  {args es : List Binaryen.BExpr} {l : List (OCall H)} {cs₁ cs₂ : List (Call (wasmHostSig H))}
  {c : Config H} {n m : Nat}

/-- The code of an operator's site, as a sequence. -/
theorem site_code (stk : List Val) (i : Instr) (E : List Admin) :
    vals stk.reverse ++ .plain i :: E = vals stk.reverse ++ [.plain i] ++ E := by simp

/-- **A call in its `call_ref` form, resolved by `CallG`**, for an operator whose arguments
completed normally: the answer read as the logged canonical rule (`hret`, `hthrow`, `hcut`). -/
theorem op_callee (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {pre us : List Val} {a : Nat} {cr : Admin} {fi : FuncInst H}
    {ps rs : List Validation.CValType}
    (ht : TypedP tags s f stk (.op i args :: es))
    (hrun : EvRunN (profile o) host n ⟨s, f, tcode stk (.op i args :: es)⟩ (cs₁ ++ cs₂) c)
    (hend : ∀ c', ¬ Step (profile o) Det.noHost c c') (hnd : decompose? c.store c.code = none)
    (hq : Shape.SubstPre Cl (l.map OCall.lift) cs₁)
    (ihk : ∀ m' ≤ n, BackG tags o host m' es) (ihC : ∀ m' ≤ n, CallG tags o host m')
    (hcr : cr.IsCallRef) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts₁ : TagsOk tags s₁) (hS₁ : StoreChkE (ehExt tags) s₁.funcs)
    (hm : m ≤ n)
    (hk : EvRunN (profile o) host m ⟨s₁, f₁, Interp.callCode pre us a cr
      (expression (Binaryen.BExpr.lowerList es))⟩ cs₂ c)
    (hctC : Sim.ContextTyped ⟨s₁, f₁, Interp.callCode pre us a cr
      (expression (Binaryen.BExpr.lowerList es))⟩)
    (hcont : ∀ (ws : List Val) (s₃ : Store H), ws.length = rs.length → TagsOk tags s₃ →
      FuncsGoodE (ehExt tags) s₁.funcs s₃.funcs →
      Sim.ContextTyped ⟨s₃, f₁, tcode (ws.reverse ++ pre.reverse) es⟩ →
      TypedP tags s₃ f₁ (ws.reverse ++ pre.reverse) es)
    (hret : ∀ (ws : List Val) (s₃ : Store H) (l₂ : List (OCall H)) (r : Store H × Frame × POut),
      EvalLXPh s₃ f₁ (ws.reverse ++ pre.reverse) es l₂ r →
      EvalLXPh s f stk (.op i args :: es) (l ++ OCall.mk a us s₁ (.inl ws) s₃ :: l₂) r)
    (hthrow : ∀ (t : Nat) (s₃ : Store H),
      EvalLXPh s f stk (.op i args :: es) (l ++ [OCall.mk a us s₁ (.inr t) s₃])
        (s₃, f₁, .flow (.throw t)))
    (hcut : ∀ (ws : List Val) (s₃ : Store H), rs.length < ws.length →
      EvalLXPh s f stk (.op i args :: es) (l ++ [OCall.mk a us s₁ (.inl ws) s₃])
        (s₃, f₁, .flow .trap)) :
    BackOut s f stk (.op i args :: es) (cs₁ ++ cs₂) c := by
  have hcons : Cons host (cs₁ ++ cs₂) := evRun_consistent (evRunN_evRun hrun)
  rcases ihC m hm s₁ f₁ pre us a cr _ c cs₂ hcr ⟨hS₁, hts₁, fi, ps, rs, hfi, hty, hn⟩ hctC hk
      hend hnd with ⟨q, b, s₃, m'', cs₃, hz, rfl, hm'', hk₃⟩ | hz
  · rw [cons_append, cons_append] at hcons
    rcases b with ws | t
    · obtain ⟨hwl, t₃, hfg, hrunC⟩ := call_ret_facts (o := o) hH hE hz hcons.2.1 hts₁ hS₁ hfi hty hn
      have hcode : vals pre ++ ansCode (.inl ws) ++ expression (Binaryen.BExpr.lowerList es) =
          tcode (ws.reverse ++ pre.reverse) es := by
        simp [tcode, ansCode, vals]
      have hst : Steps (profile o) host ⟨s₁, f₁, Interp.callCode pre us a cr
          (expression (Binaryen.BExpr.lowerList es))⟩
          ⟨s₃, f₁, tcode (ws.reverse ++ pre.reverse) es⟩ := by
        rw [← hcode]
        exact evRun_steps (evRun_ctx pre _ (hrunC f₁ cr hcr))
      have htk := hcont ws s₃ hwl t₃ hfg (ContextTyped.steps_typed hT hctC hst)
      rw [hcode] at hk₃
      obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihk m'' (by omega) s₃ f₁ _ c cs₃ htk hk₃ hend hnd
      have hres : ResX (l ++ OCall.mk a us s₁ (.inl ws) s₃ :: l₂) r₂ (cs₁ ++ (q ++ cs₃)) := by
        have := resX_prepend (resPre_append hq (res_one hz)) hres₂
        simpa [List.append_assoc] using this
      exact mkOut hH hE ht hrun hend (hret ws s₃ l₂ r₂ hd₂) hres
    · have hrun' : EvRunN (profile o) host n ⟨s, f, tcode stk (.op i args :: es)⟩
          ((cs₁ ++ q) ++ cs₃) c := by simpa [List.append_assoc] using hrun
      have := mkOut'' hH hE ht hrun' hend (hthrow t s₃) (.inl (resPre_append hq (res_one hz)))
      simpa [List.append_assoc] using this
  · let ws : List Val := List.replicate (rs.length + 1) (.ref .null)
    have hres : ResX (l ++ [OCall.mk a us s₁ (.inl ws) s₁]) (s₁, f₁, .flow .trap) (cs₁ ++ cs₂) :=
      .inr ⟨rfl, l, [], a, us, s₁, .inl ws, s₁, cs₁, cs₂, rfl, hq, hz, rfl⟩
    exact mkOut hH hE ht hrun hend (hcut ws s₁ (by simp [ws])) hres

/-- The continuation after a call answered by values is a typed problem. -/
theorem cont_typed {s₃ : Store H} {ws : List Val} {k : Nat} {rs : List Validation.CValType}
    {labels : List Nat} {ret : Nat} {out : Option Nat} {stk' : List Val}
    (hS : StoreChkE (ehExt tags) s.funcs) (inv1 : EvalInvE (ehExt tags) s f (s₁, f₁, .normal stk₁))
    (hTM : Abstract.CallXT.TyTypes f.module)
    (h2 : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels
      (some (stk'.length - k + rs.length)) es = some out)
    (hwl : ws.length = rs.length) (t₃ : TagsOk tags s₃)
    (hfg : FuncsGoodE (ehExt tags) s₁.funcs s₃.funcs)
    (hct : Sim.ContextTyped ⟨s₃, f₁, tcode (ws.reverse ++ stk'.drop k) es⟩) :
    TypedP tags s₃ f₁ (ws.reverse ++ stk'.drop k) es := by
  have inv2 : EvalInvE (ehExt tags) s f (s₃, f₁, .normal (ws.reverse ++ stk'.drop k)) :=
    ⟨inv1.1.trans hfg, inv1.2.1, inv1.2.2⟩
  have hlen : (ws.reverse ++ stk'.drop k).length = stk'.length - k + rs.length := by
    simp only [List.length_append, List.length_reverse, List.length_drop]
    omega
  refine typedP_of (storeChk_inv inv2 hS) (labels := labels) (ret := ret) (out := out) ?_ hct
    (by rw [inv2.2.1]; exact hTM) t₃
  rw [hlen]
  exact chk_inv inv2 h2

end Op

section Case

variable {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List Binaryen.BExpr}
  {c : Config H} {cs : List (Call (wasmHostSig H))} {n : Nat}

/-- **The operator case** of the logged backward simulation. -/
theorem case_op (hT : HostTyped host) (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    (ihA : ∀ m ≤ n, BackG tags o host m args) (ihk : ∀ m ≤ n, BackG tags o host m es)
    (ihC : ∀ m ≤ n, CallG tags o host m) :
    BackG tags o host n (.op i args :: es) := by
  intro s f stk c cs ht hrun hend hnd
  have hcode := code_op stk i args es
  have hrun₀ := hrun
  change EvRunN _ _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
    (.op i args :: es))⟩ _ _ at hrun
  rw [hcode] at hrun
  obtain ⟨l, r, cs₁, cs₂, rfl, hd, hres, hr⟩ := seq_part (args_typedP ht) ihA hrun hend hnd
  rcases hr with hn | ⟨s₁, f₁, stk₁, m, rfl, hq, hm, hk, hst⟩
  · exact mkOut'' hH hE ht hrun₀ hend (.argsAbort hd hn) hres
  have hst' : Steps (profile o) host ⟨s, f, tcode stk (.op i args :: es)⟩
      ⟨s₁, f₁, vals stk₁.reverse ++ .plain i :: expression (Binaryen.BExpr.lowerList es)⟩ := by
    change Steps _ _ ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList
      (.op i args :: es))⟩ _
    rw [hcode]
    exact hst
  obtain ⟨labels, ret, out, o₁, hS, hc, h2, aha, t₁, hf, inv1, hsite, hTM₁, hTF₁, hS₁⟩ :=
    site_facts hT hH hE ht hrun₀ hd hq hst'
  have hTM : Abstract.CallXT.TyTypes f.module := by rw [← inv1.2.1]; exact hTM₁
  let E := expression (Binaryen.BExpr.lowerList es)
  rcases instr_cases i with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ | ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨y, rfl⟩ |
    (⟨x, rfl⟩ | rfl) | ⟨hi, hx⟩
  · -- call
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call hf)
    obtain ⟨a, fi, ps, rs, hfi, hty, rfl, rfl⟩ := callArity_func? hpq
    have hst₁ : Steps (profile o) NH ⟨s₁, f₁, vals stk₁.reverse ++ .plain (.call x) :: E⟩
        ⟨s₁, f₁, Interp.callCode (stk₁.drop ps.length).reverse (stk₁.take ps.length).reverse a
          (.callRefType fi.type) E⟩ := by
      rw [site_code, ← callCode_split]
      exact .single (Silmaril.Wasm.Logic.Core.Step.ctx _ _
        (Step.call (module_of_func? hfi) (funcs_of_func? hfi)))
    obtain ⟨m', hm', hk'⟩ := through hst₁ hk hend
    obtain ⟨-, -, h2'⟩ := arity_call_pre hS aha hfi hty hc
    refine op_callee hT hH hE ht hrun₀ hend hnd hq ihk ihC (cr := .callRefType fi.type) trivial (funcs_of_func? hfi) hty
      (take_rev_length hp) t₁ hS₁ (by omega) hk'
      (ContextTyped.steps_typed hT hsite (steps_host hst₁)) ?_ ?_ ?_ ?_
    · intro ws s₃ hwl t₃ hfg hct
      rw [List.reverse_reverse] at hct ⊢
      exact cont_typed hS inv1 hTM h2' hwl t₃ hfg hct
    · intro ws s₃ l₂ r hd₂
      rw [List.reverse_reverse] at hd₂
      exact .callRet hd hfi hty hd₂
    · intro t s₃
      exact .callThrow hd hfi hty
    · intro ws s₃ hws
      exact .callCut hd hfi hty hws
  · -- call_indirect
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := indirect_res (.inl rfl) hsite
    cases o' with
    | none => exact mkOut'' hH hE ht hrun₀ hend (.indRes hd hres) (.inl hq)
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      have hf_t := hf
      rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
      have e : vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++
          .plain (.callIndirect x y) :: E =
          vals stk'.reverse ++ [aconst ad j, .plain (.callIndirect x y)] ++ E := by
        rw [List.reverse_cons, vals_append, Silmaril.Wasm.Abstract.CallRes.aconst_eq]; simp
      have hst₀ : Steps (profile o) NH ⟨s₁, f₁, vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++
          .plain (.callIndirect x y) :: E⟩
          ⟨s₁, f₁, vals stk'.reverse ++ [.ref (.func fa), .plain (.callRef y)] ++ E⟩ := by
        rw [e]
        exact Steps.ctx _ _ (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres)
      have hct₀ := ContextTyped.steps_typed hT hsite (steps_host hst₀)
      obtain ⟨ps, rs, hty⟩ := funcType_of_callRef_cfg (P := profile o)
        (by simpa only [List.append_assoc, List.cons_append, List.singleton_append] using hct₀)
        (cr := .plain (.callRef y)) trivial hfi
      have hy := Abstract.CallXT.typeArity_of_indRes hres hfi hty hTF₁ hTM₁
        (types_some_of_flatChkT hf_t)
      obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) hy hf_t
      simp only [List.length_cons] at hp
      have hst₁ : Steps (profile o) NH ⟨s₁, f₁, vals (Val.num ⟨.int ad.intType, j⟩ :: stk').reverse ++
          .plain (.callIndirect x y) :: E⟩
          ⟨s₁, f₁, Interp.callCode (stk'.drop ps.length).reverse (stk'.take ps.length).reverse fa
            (.plain (.callRef y)) E⟩ := by
        rw [← callCode_split]; exact hst₀
      obtain ⟨m', hm', hk'⟩ := through hst₁ hk hend
      obtain ⟨-, -, h2'⟩ := arity_ir_preP hS aha (.inl ⟨x, rfl⟩) hy hc
      refine op_callee hT hH hE ht hrun₀ hend hnd hq ihk ihC (cr := .plain (.callRef y)) trivial hfi hty
        (take_rev_length (by omega)) t₁ hS₁ (by omega) hk'
        (ContextTyped.steps_typed hT hsite (steps_host hst₁)) ?_ ?_ ?_ ?_
      · intro ws s₃ hwl t₃ hfg hct
        rw [List.reverse_reverse] at hct ⊢
        exact cont_typed hS inv1 hTM h2' hwl t₃ hfg hct
      · intro ws s₃ l₂ r hd₂
        rw [List.reverse_reverse] at hd₂
        exact .indRet hd hres hfi hty hy hd₂
      · intro t s₃
        exact .indThrow hd hres hfi hty hy
      · intro ws s₃ hws
        exact .indCut hd hres hfi hty hy hws
  · -- call_ref
    obtain ⟨r, stk', rfl, hr⟩ := callRef_top hsite hTM₁
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact mkOut'' hH hE ht hrun₀ hend (.refNull hd) (.inl hq)
    have e : vals (Val.ref (.func fa) :: stk').reverse ++ .plain (.callRef y) :: E =
        vals stk'.reverse ++ .ref (.func fa) :: .plain (.callRef y) :: E := by
      simp [vals, Val.toAdmin]
    obtain ⟨ps, rs, hty⟩ := funcType_of_callRef_cfg (P := profile o) (e ▸ hsite)
      (cr := .plain (.callRef y)) trivial hfi
    have hy := Abstract.CallXT.typeArity_of_callRef_site hsite hTM₁ hfi hty (hTF₁ _ _ hfi)
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) hy hf_t
    simp only [List.length_cons] at hp
    have e' : vals (Val.ref (.func fa) :: stk').reverse ++ .plain (.callRef y) :: E =
        Interp.callCode (stk'.drop ps.length).reverse (stk'.take ps.length).reverse fa
          (.plain (.callRef y)) E := by
      rw [← callCode_split]; simp [vals, Val.toAdmin]
    obtain ⟨-, -, h2'⟩ := arity_ir_preP hS aha (.inr rfl) hy hc
    refine op_callee hT hH hE ht hrun₀ hend hnd hq ihk ihC (cr := .plain (.callRef y)) trivial hfi hty
      (take_rev_length (by omega)) t₁ hS₁ hm (e' ▸ hk) (e' ▸ hsite) ?_ ?_ ?_ ?_
    · intro ws s₃ hwl t₃ hfg hct
      rw [List.reverse_reverse] at hct ⊢
      exact cont_typed hS inv1 hTM h2' hwl t₃ hfg hct
    · intro ws s₃ l₂ r hd₂
      rw [List.reverse_reverse] at hd₂
      exact .refRet hd hfi hty hy hd₂
    · intro t s₃
      exact .refThrow hd hfi hty hy
    · intro ws s₃ hws
      exact .refCut hd hfi hty hy hws
  · -- return_call
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    have hca : ∃ p, callArity s₁.funcs f₁.module x = some p := by
      cases h : callArity s₁.funcs f₁.module x with
      | none => simp [flatChkE, tExt, h, extStep] at hf_t
      | some p => exact ⟨p, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := hca
    obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := callArity_func? hpq
    exact mkOut'' hH hE ht hrun₀ hend (.tail hd (.direct hfi) (funcs_of_func? hfi) hty
      (tailAnn_typed (.direct hfi) hsite (funcs_of_func? hfi) hty hTF₁ hTM₁ hf_t)) (.inl hq)
  · -- return_call_indirect
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨ad, j, stk', o', rfl, hres⟩ := indirect_res (.inr rfl) hsite
    cases o' with
    | none => exact mkOut'' hH hE ht hrun₀ hend (.tailRes hd (.indirectTrap hres)) (.inl hq)
    | some fa =>
      obtain ⟨fi, hfi⟩ := fi_of_indRes hres
      obtain ⟨p, hy₀⟩ := typeArity_some_rci hf_t
      obtain ⟨ps, rs, hty⟩ := funcType_of_indRes hres hfi hTF₁ hTM₁ hy₀
      exact mkOut'' hH hE ht hrun₀ hend (.tail hd (.indirect hres) hfi hty
        (tailAnn_typed (.indirect hres) hsite hfi hty hTF₁ hTM₁ hf_t)) (.inl hq)
  · -- return_call_ref
    have hf_t := hf
    rw [flatChkE_ehExt_tExt (fun _ h => by cases h) (by intro h; cases h)] at hf_t
    obtain ⟨r, stk', rfl, hr⟩ := returnCallRef_top hsite hTM₁
    rcases hr with rfl | ⟨fa, fi, rfl, hfi⟩
    · exact mkOut'' hH hE ht hrun₀ hend (.tailRes hd .refNull) (.inl hq)
    · obtain ⟨ps, rs, hty⟩ := funcType_of_returnCallRef_site hsite hTM₁ hfi (hTF₁ _ _ hfi)
      exact mkOut'' hH hE ht hrun₀ hend (.tail hd .ref hfi hty
        (tailAnn_typed .ref hsite hfi hty hTF₁ hTM₁ hf_t)) (.inl hq)
  · -- throw
    obtain ⟨p, htf, hp⟩ := throw_chk hf
    obtain ⟨ta, ti, ts, ht', he, hlen⟩ := tag_of_tagFields t₁.1 htf
    exact mkOut'' hH hE ht hrun₀ hend (.throw hd ht' he (by omega)) (.inl hq)
  · -- throw_ref
    obtain ⟨r, stk', rfl, hr⟩ := throwRef_top hsite
    rcases hr with rfl | ⟨a, rfl⟩
    · exact mkOut'' hH hE ht hrun₀ hend (.throwRefNull hd) (.inl hq)
    · exact mkOut'' hH hE ht hrun₀ hend (.throwRefExn hd) (.inl hq)
  · -- a flat instruction
    have hf' : flatChk s₁.funcs f₁.module f₁.locals.length ret labels stk₁.length i = some o₁ := by
      rw [← flatChkE_eq_flatChk (ehExt tags) hx]; exact hf
    obtain ⟨⟨s₂, f₂, fl₂⟩, hflat⟩ := evalFlat_progressH hf' hi hsite
    by_cases hn₂ : fl₂.IsNormal
    swap
    · exact mkOut'' hH hE ht hrun₀ hend (.opStop hi hd hflat hn₂) (.inl hq)
    rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Binaryen.Flow.IsNormal] at hn₂
    have st := steps_flat_normal (P := profile o) (host := NH) hi hf' hflat E
    obtain ⟨m', hm', hk'⟩ := through st hk hend
    obtain ⟨ho, inv2⟩ := flat_normal (ext := ehExt tags) hflat hf'
    have inv12 : EvalInvE (ehExt tags) s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have hcons : Cons host (cs₁ ++ cs₂) := evRun_consistent (evRunN_evRun hrun₀)
    have hts : TagsOk tags s := by obtain ⟨-, -, -, -, -, -, -, -, h⟩ := ht; exact h
    obtain ⟨-, t₂, -, -⟩ := full_run (P := profile o) hH hE (.opOk (es := []) hi hd hflat .nil)
      (by simpa using substPre_mono (close_le_goodCX hH hE) hq) (cons_append.1 hcons).1 hts
    have htk : TypedP tags s₂ f₂ stk₂ es := by
      refine typedP_of (storeChk_inv inv12 hS) (labels := labels) (ret := ret) (out := out) ?_
        (ContextTyped.steps_typed hT hsite (steps_host st)) (by rw [inv12.2.1]; exact hTM) t₂
      rw [← ho]
      exact chk_inv inv12 h2
    obtain ⟨l₂, r₂, hd₂, hres₂, -⟩ := ihk m' (by omega) s₂ f₂ stk₂ c cs₂ htk hk' hend hnd
    exact mkOut hH hE ht hrun₀ hend (.opOk hi hd hflat hd₂) (resX_prepend hq hres₂)

end Case

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
