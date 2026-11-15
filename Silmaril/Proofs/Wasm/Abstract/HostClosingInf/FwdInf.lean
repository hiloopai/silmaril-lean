module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInf.Seg

/-!
# Productive native runs are productive Core runs (proofs)

The converse of `coreInf_wasmEvInfN`, every profile: a productive run of `wasmEvInfN` whose
answers the host allows is a productive Core run of the invocation with exactly those events.

* `infL_fwd`: a productive run of trees within their function (`InfL`), resolved by the closure
  to `ω'`, is a productive Core run of the lowered trees with the events `ω'`. By induction on
  `InfL`: the finite parts are logged Core runs (`prefix_glue`, `loopBack_glue`, `arm_glue`,
  from `evalL_fwd`), lifted through their contexts; a loop iterating forever (`loopInf`) is a
  chain of iterations (`coreInf_of_segments`), its stream regrouped by iteration
  (`substInf_regroup`);
* `reachL_fwd`: a logged reach (`ReachL`) with a consistent resolved prefix `q` is a Core run
  with the events `q` to the reached call, in a context (`Lifts`) of labels and values;
* `descends_fwd`, `descPath_fwd`: a descent of the module (path) is such a run from the
  caller's call into the callee's call, inside the callee frames entered on the way;
* `infChain_fwd`: an infinite chain of descents is a chain of such runs, nested ever deeper;
* `wasmEvInfN_coreInf`: **the converse bridge**.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInf

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp
open Shape (streamAppend StreamConcat SubstInf Res1 SubstPre)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Contexts -/

/-- A context lifting every labelled step, with its label. -/
def Lifts (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (W : Config H → Config H) : Prop :=
  ∀ c l c', HEvStep P host c l c' → HEvStep P host (W c) l (W c')

theorem lifts_id : Lifts P host (fun c : Config H => c) := fun _ _ _ h => h

theorem lifts_comp {V W : Config H → Config H} (hV : Lifts P host V) (hW : Lifts P host W) :
    Lifts P host (fun c => V (W c)) := fun _ _ _ h => hV _ _ _ (hW _ _ _ h)

theorem lifts_ctx (ws : List Val) (rest : List Admin) :
    Lifts P host (fun c : Config H => ⟨c.store, c.frame, vals ws ++ c.code ++ rest⟩) := by
  intro c l c' h
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_ctx ws rest h

theorem lifts_label (n : Nat) (cont : List Instr) :
    Lifts P host (fun c : Config H => ⟨c.store, c.frame, [.label n cont c.code]⟩) := by
  intro c l c' h
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_label n cont h

theorem lifts_frame (n : Nat) (g : Frame) :
    Lifts P host (fun c : Config H => ⟨c.store, g, [.frame n c.frame c.code]⟩) := by
  intro c l c' h
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  exact hEvStep_frame n h

/-- The call `y` about to be made, in the frame `F`: its arguments, `ref.func`, `call_ref`. -/
def callAt (y : (wasmOShape H).self.Op) (F : Frame) : Config H :=
  ⟨y.2.2, F, (invoke y.2.2 y.1 y.2.1).code⟩

theorem callAt_code {y : (wasmOShape H).self.Op} {F : Frame} {fi : FuncInst H}
    (hf : y.2.2.funcs[y.1]? = some fi) :
    callAt y F = ⟨y.2.2, F, vals y.2.1 ++ [.ref (.func y.1), .callRefType fi.type]⟩ := by
  simp [callAt, invoke, hf]

/-- A typed call of a checked store. -/
def InvC (y : (wasmOShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), y.2.2.funcs[y.1]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧ y.2.1.length = ps.length ∧
    StoreChk y.2.2.funcs

/-- **Entering a Wasm callee**: host-free, from the call to the callee's body in its frame and
label. -/
theorem enter_body {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hf : y.2.2.funcs[y.1]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : y.2.1.length = ps.length) (g : Frame) :
    Steps P NH (callAt y g) ⟨y.2.2, g, [.frame rs.length (Frame.forCall fi.module y.2.1 fn.locals)
      [.label rs.length [] (vals ([] : List Val).reverse ++
        expression (Binaryen.BExpr.lowerList (Binaryen.liftInstrs fn.body)))]]⟩ := by
  rw [callAt_code hf, Binaryen.lowerList_liftInstrs]
  obtain ⟨ps', rs', he', hpl, hrl⟩ := expand_of_funcType hty
  rw [← hrl]
  simpa [vals] using (Relation.ReflTransGen.single
    (Step.callRefFunc (P := P) (host := NH) (f := g)
      (show Admin.IsCallRef (.callRefType fi.type) from trivial) hf he' (hn.trans hpl.symm) hcode))

/-- The check of a callee body, from the store check. -/
theorem body_chk {y : (wasmOShape H).self.Op} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hS : StoreChk y.2.2.funcs)
    (hf : y.2.2.funcs[y.1]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : y.2.1.length = ps.length) :
    ∃ ob, chk y.2.2.funcs (Frame.forCall fi.module y.2.1 fn.locals).module
      (Frame.forCall fi.module y.2.1 fn.locals).locals.length rs.length [rs.length]
      (some ([] : List Val).length) (Binaryen.liftInstrs fn.body) = some ob := by
  obtain ⟨ob, hb, -⟩ := endsAt_eq (hS y.1 fi fn ps rs hf hcode hty)
  exact ⟨ob, by rw [forCall_length _ _ hn]; exact hb⟩

/-! ## Productive runs within a function -/

/-- **A productive run of trees within their function is a productive Core run** with the
events of its resolution. -/
theorem infL_fwd (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {ω : Nat → OCall H} (h : InfL s f stk es ω) :
    ∀ ω', SubstInf (Shape.close wasmHOpen) (fun i => (ω i).lift) ω' → ConsInf host ω' →
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
      chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      CoreInf P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ ω' := by
  induction h with
  | args _ ih =>
    intro ω' hs hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    rw [code_op]
    simpa [vals] using coreInf_ctx [] _ (ih ω' hs hc hS ha)
  | callK hargs hfi hty _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH (.callRet hargs hfi hty .nil) hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')
  | opK hi hargs hflat _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    have hE := EvalL.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')
  | @block s f stk bt body es np nr ω har _ ih =>
    intro ω' hs hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    have := coreInf_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (coreInf_label nr [] (ih ω' hs hc hS hbc))
    simpa [Shape.streamAppend_nil] using coreInf_prepend (evRun_of_free enter) this
  | blockK har hbody hvs _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    have hE := EvalL.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')
  | @loop s f stk bt body es np nr ω har _ ih =>
    intro ω' hs hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    have := coreInf_ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es))
      (coreInf_label np [.loop bt (Binaryen.BExpr.lowerList body)] (ih ω' hs hc hS hbc))
    simpa [Shape.streamAppend_nil] using coreInf_prepend (evRun_of_free enter) this
  | loopK har hbody _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    have hE := EvalL.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')
  | loopBack har hbody _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    obtain ⟨run, hS', hchk'⟩ := loopBack_glue (P := P) hH har hbody hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')
  | @loopInf s f stk bt body es np nr ω st l h0 har hit hω =>
    intro ω' hs hc labels ret out hS hchk
    obtain ⟨q, hq, hqc⟩ := substInf_regroup (Shape.streamConcat_map OCall.lift hω) hs
    have hcq := cons_of_concat hqc hc
    choose vs hit₁ hit₂ using hit
    let K : Nat → Config H := fun n => ⟨(st n).1, (st n).2.1, vals (st n).2.2.reverse ++
      expression (Binaryen.BExpr.lowerList (.loop bt body :: es))⟩
    have inv : ∀ n, StoreChk (st n).1.funcs ∧ chk (st n).1.funcs (st n).2.1.module
        (st n).2.1.locals.length ret labels (some (st n).2.2.length) (.loop bt body :: es) =
          some out := by
      intro n
      induction n with
      | zero => rw [h0]; exact ⟨hS, hchk⟩
      | succ n ih =>
        obtain ⟨-, hS', hchk'⟩ := loopBack_glue (P := P) hH (har n) (hit₁ n) (hq n) (hcq n)
          ih.1 ih.2
        rw [hit₂ n]
        exact ⟨hS', hchk'⟩
    have seg : ∀ n, EvRun P host (K n) (q n) (K (n + 1)) := by
      intro n
      obtain ⟨run, -, -⟩ := loopBack_glue (P := P) hH (har n) (hit₁ n) (hq n) (hcq n)
        (inv n).1 (inv n).2
      simp only [K]
      rw [hit₂ n]
      exact run
    have := coreInf_of_segments K q seg hqc
    simpa [K, h0] using this
  | cond _ ih =>
    intro ω' hs hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    rw [code_if]
    simpa [vals] using coreInf_ctx [] _ (ih ω' hs hc hS hco)
  | arm hcE hb har _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    obtain ⟨hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hcE hb har hq hcq hS hchk
    exact coreInf_prepend run (coreInf_ctx _ _ (coreInf_label _ [] (ih ω'' hs' hc' hS' hbc)))
  | ifK hcE hb har harm hvs _ ih =>
    intro ω' hs hc labels ret out hS hchk
    rw [streamAppend_map] at hs
    obtain ⟨q, ω'', rfl, hq, hs'⟩ := substInf_split hs
    obtain ⟨hcq, hc'⟩ := consInf_split hc
    have hE := EvalL.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE hq hcq hS hchk
    exact coreInf_prepend run (ih ω'' hs' hc' hS' hchk')

/-! ## Logged reaches -/

/-- **A logged reach is a Core run to the reached call** with exactly the events of its resolved
prefix, in a context of labels and values; the reached call is typed. -/
theorem reachL_fwd (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {l : List (OCall H)} {y : (wasmOShape H).self.Op}
    (h : ReachL s f stk es l y) :
    ∀ q, SubstPre (Shape.close wasmHOpen) (l.map OCall.lift) q → Cons host q →
      ∀ {labels : List Nat} {ret : Nat} {out : Option Nat}, StoreChk s.funcs →
      chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
      InvC y ∧ ∃ (W : Config H → Config H) (F' : Frame), Lifts P host W ∧
        EvRun P host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ q
          (W (callAt y F')) := by
  induction h with
  | @here s s₁ f f₁ stk stk₁ x args es a fi ps rs l hargs hfi hty =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨d, cl⟩ := evalL_fwd (P := P) hH hargs q (substPre_mono (close_le_goodC hH) hq) hc
    obtain ⟨inv1, hp, -⟩ := arity_call_pre hS (evalH_good (P := P) hH d).1 hfi hty hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨c', o', hrun, he, hm⟩ := cl hS ha
    have hc' : c' = vals stk₁.reverse := ends_normal hm he
    subst hc'
    have hfa := Silmaril.Wasm.Interp.funcs_of_func? hfi
    refine ⟨⟨fi, ps, rs, hfa, hty, take_rev_length hp, storeChk_inv inv1 hS⟩,
      fun c => ⟨c.store, c.frame, vals (stk₁.drop ps.length).reverse ++ c.code ++
        expression (Binaryen.BExpr.lowerList es)⟩, f₁, lifts_ctx _ _, ?_⟩
    rw [code_op]
    dsimp only
    rw [callAt_code (F := f₁) (y := ⟨a, ((stk₁.take ps.length).reverse, s₁)⟩) hfa]
    have r1 := evRun_append (rest := .plain (.call x) :: expression (Binaryen.BExpr.lowerList es))
      hrun
    have hsplit : vals stk₁.reverse =
        vals (stk₁.drop ps.length).reverse ++ vals (stk₁.take ps.length).reverse := by
      conv_lhs => rw [← List.take_append_drop ps.length stk₁]
      simp [vals]
    have h₁ := Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := NH)
      ((stk₁.drop ps.length).reverse ++ (stk₁.take ps.length).reverse)
      (expression (Binaryen.BExpr.lowerList es))
      (Step.call (s := s₁) (f := f₁) (module_of_func? hfi) hfa)
    rw [hsplit] at r1
    simp only [vals_append, List.append_assoc, List.singleton_append] at h₁ r1 ⊢
    simpa using evRun_trans r1 (evRun_of_free (.single h₁))
  | @args s f stk i args es l y _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨hy, W, F', hW, run⟩ := ih q hq hc hS ha
    let rest : List Admin := .plain i :: expression (Binaryen.BExpr.lowerList es)
    refine ⟨hy, _, F', lifts_comp (lifts_ctx [] rest) hW, ?_⟩
    rw [code_op]
    simpa [vals] using evRun_wrap _ (lifts_ctx (P := P) (host := host) [] rest) run
  | @callK s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ y hargs hfi hty _ ih =>
    intro q hq hc labels ret out hS hchk
    have e : (l₁ ++ OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂ :: l₂).map
        OCall.lift = (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂]).map
          OCall.lift ++ l₂.map OCall.lift := by simp
    rw [e] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH (.callRet hargs hfi hty .nil) h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩
  | opK hi hargs hflat _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.opOk hi hargs hflat (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩
  | @block s f stk bt body es np nr l y har _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := block_enter (P := P) har hchk
    obtain ⟨hy, W, F', hW, run⟩ := ih q hq hc hS hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    refine ⟨hy, _, F', lifts_comp (lifts_ctx (stk.drop np).reverse rest)
      (lifts_comp (lifts_label nr []) hW), ?_⟩
    have := evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) nr []) run)
    simpa using evRun_trans (evRun_of_free enter) this
  | blockK har hbody hvs _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.blockOk har hbody hvs (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩
  | @loop s f stk bt body es np nr l y har _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨⟨ob, hbc⟩, enter⟩ := loop_enter (P := P) har hchk
    obtain ⟨hy, W, F', hW, run⟩ := ih q hq hc hS hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    let cont : List Instr := [.loop bt (Binaryen.BExpr.lowerList body)]
    refine ⟨hy, _, F', lifts_comp (lifts_ctx (stk.drop np).reverse rest)
      (lifts_comp (lifts_label np cont) hW), ?_⟩
    have := evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) np cont) run)
    simpa using evRun_trans (evRun_of_free enter) this
  | loopK har hbody _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.loopOk har hbody (es := []) .nil
    rw [List.append_nil] at hE
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩
  | loopBack har hbody _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨run, hS', hchk'⟩ := loopBack_glue (P := P) hH har hbody h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩
  | @cond s f stk bt c t el es l y _ ih =>
    intro q hq hc labels ret out hS hchk
    obtain ⟨o, h1, -⟩ := chk_consE.mp hchk
    obtain ⟨oc, hco, -⟩ := chk1_ifE h1
    obtain ⟨hy, W, F', hW, run⟩ := ih q hq hc hS hco
    let rest : List Admin := .plain (.if_ bt (Binaryen.BExpr.lowerList t)
      (Binaryen.BExpr.lowerList el)) :: expression (Binaryen.BExpr.lowerList es)
    refine ⟨hy, _, F', lifts_comp (lifts_ctx [] rest) hW, ?_⟩
    rw [code_if]
    simpa [vals] using evRun_wrap _ (lifts_ctx (P := P) (host := host) [] rest) run
  | @arm s s₁ f f₁ stk stk₁ cv b bt c t el es np nr l₁ l₂ y hcE hb har _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨hS', ⟨ob, hbc⟩, run⟩ := arm_glue (P := P) hH hcE hb har h₁ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₂ h₂ hc.2 hS' hbc
    let rest : List Admin := expression (Binaryen.BExpr.lowerList es)
    refine ⟨hy, _, F', lifts_comp (lifts_ctx (stk₁.drop np).reverse rest)
      (lifts_comp (lifts_label nr []) hW), ?_⟩
    exact evRun_trans run (evRun_wrap _ (lifts_ctx (P := P) (host := host) (stk₁.drop np).reverse rest)
      (evRun_wrap _ (lifts_label (P := P) (host := host) nr []) run'))
  | ifK hcE hb har harm hvs _ ih =>
    intro q hq hc labels ret out hS hchk
    rw [List.map_append, List.map_append] at hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    have hE := EvalL.ifOk hcE hb har harm hvs (es := []) .nil
    rw [List.append_nil] at hE
    rw [← List.map_append] at h₁₂
    obtain ⟨run, hS', hchk'⟩ := prefix_glue (P := P) hH hE h₁₂ hc.1 hS hchk
    obtain ⟨hy, W, F', hW, run'⟩ := ih q₃ h₃ hc.2 hS' hchk'
    exact ⟨hy, W, F', hW, evRun_trans run run'⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingInf
