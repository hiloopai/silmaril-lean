module

public import Silmaril.Proofs.Wasm.Abstract.FullObsNative.Local
public import Silmaril.Wasm.Abstract.HostEval.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.FullObsNative.Thms`: **at the H2 oracle, silent paths of
checked typed trees are local divergence** (`silent_localDivO_host`).

A `.div` path of the exposed body `denListE` is silent divergence or a stuck configuration
(`stuck` is `diverge`). For trees passing the arity check, in a store whose functions pass it,
from a typed Core configuration, with every call answered by `hostCall host` (typed answers,
native host slice), no stuck configuration is reachable: the check rejects `try_table` and
unknown arities and resolves every callee and its type; typed progress
(`Interp.evalFlat_progressH`, `Interp.truthy_progressH`) rules out flat rejections and a
missing or non-`i32` condition; and a sound oracle (`Interp.hostCall_sound`) never answers a
branch past the callee's label, so `callAns` is never stuck.

The proof is by coinduction (`localDivO_of_coind`) on `SilHyp`: the hypotheses of
`back_whole` for the trees and an answered silent path of their tree. Each step decomposes the
path through the construct's bind (`path_bind_inv`): a silent prefix is the next problem; a
finished prefix is read as an `EvalH` run (`path_evalO`), the hypotheses carried past it as in
`div_whole` (`Interp.evalH_good` for the check and the Core run, `ContextTyped.steps_typed` for
typing); abrupt flows end the tree in a value, which has no silent path. A loop iteration
branching back is the `loopBack` step to the loop at its new state, so no well-founded
argument on silent iterations is needed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FullObsNative

open Silmaril.Wasm Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace Silmaril.Wasm.Binaryen
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
  Silmaril.Elgot.ITree
open Silmaril.Wasm.Interp (Problem)

variable {H : Type}

/-- A fixed deterministic profile for the Core runs used to carry typing. -/
abbrev sprof : Silmaril.Wasm.Numerics.Profile := Silmaril.Wasm.SingleThreaded.profile fun _ _ _ _ => false

/-- The hypotheses of `back_whole` for the trees. -/
def Hyp (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) : Prop :=
  ∃ (labels : List Nat) (ret : Nat) (out : Option Nat), Interp.StoreChk s.funcs ∧
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out ∧
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (BExpr.lowerList es)⟩

/-- The coinductive invariant: the hypotheses of `back_whole`, and an answered silent path. -/
def SilHyp (host : HostSemantics H) : Problem H := fun s f stk es =>
  Hyp s f stk es ∧ ∃ cs, Answered (hostCall host) cs ∧
    Path (tr (denListE es f stk : M (CallSig H) H Res) ⟨s⟩) cs .div

/-! ## Trees with no silent path -/

theorem not_path_ret_div {E : Sig.{0}} {Y : Type 1} {v : Y} {cs : List (Call E)} :
    ¬ Path (ret v : Silmaril.Elgot.ITree.Tree (SigEv E) Y) cs .div := by
  intro h
  cases h with
  | div h => exact ret_ne_diverge _ h
  | vis h => exact ret_ne_vis _ _ _ h

theorem not_path_ret_bind_pure {E : Sig.{0}} {Y : Type 1} {v : Y} {cs : List (Call E)} :
    ¬ Path ((ret v : Silmaril.Elgot.ITree.Tree (SigEv E) Y) >>= pure) cs .div := by
  rw [bind_pure]; exact not_path_ret_div

theorem not_path_pure_div {E : Sig.{0}} {Y : Type 1} {v : Y} {cs : List (Call E)} :
    ¬ Path (pure v : Silmaril.Elgot.ITree.Tree (SigEv E) Y) cs .div :=
  not_path_ret_div

theorem bc_error {X Y : Type 1} (g : X × St H → TT H (Ex H Y)) (e : PUnit.{2}) :
    bc g (.error e) = ret (.error e) := rfl

theorem thenK_pass (k : Frame → List Val → M (CallSig H) H Res) {f : Frame} {fl : Flow}
    (hn : ¬ fl.IsNormal) : thenK k ⟨(f, fl)⟩ = pure ⟨(f, fl)⟩ := by
  cases fl <;> first | exact absurd trivial hn | rfl

theorem endR_eq_ok {r : Store H × Frame × Flow} {s₁ : Store H} {f₁ : Frame} {fl : Flow}
    (h : endR r = .val (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩))) : r = (s₁, f₁, fl) := by
  obtain ⟨a, b, c⟩ := r
  cases c <;> simp_all [endR]

/-- A finished answered prefix is an `EvalH` run. -/
theorem evalH_of_path {host : HostSemantics H} {es : List BExpr} {s s₁ : Store H}
    {f f₁ : Frame} {stk : List Val} {fl : Flow} {cs : List (Call (CallSig H))}
    (hA : Answered (hostCall host) cs)
    (h : Path (tr (denListE es f stk : M (CallSig H) H Res) ⟨s⟩) cs
      (.val (.ok (⟨(f₁, fl)⟩, ⟨s₁⟩)))) :
    EvalH host s f stk es (s₁, f₁, fl) := by
  obtain ⟨r, hev, he⟩ := path_evalO hA h (by simp)
  rw [endR_eq_ok he] at hev
  exact hev

/-! ## Carrying the hypotheses -/

section
variable {host : HostSemantics H}

/-- Typing after a finished normal prefix, in place. -/
theorem typed_prefix (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val} {xs : List BExpr} {rest : List Admin}
    {labels : List Nat} {ret : Nat} {ox : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) xs = some ox)
    (ht : Sim.ContextTyped ⟨s, f, (vals stk.reverse ++ expression (BExpr.lowerList xs)) ++ rest⟩)
    (hev : EvalH host s f stk xs (s₁, f₁, .normal stk₁)) :
    Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ rest⟩ := by
  obtain ⟨c', o', hrun, he, hm⟩ :=
    Interp.run_of_wp ((Interp.evalH_good (P := sprof) hH hev).2 hS hc)
  rw [Interp.ends_normal hm he] at hrun
  exact ContextTyped.steps_typed hT ht (Silmaril.Wasm.Logic.Core.Steps.append rest hrun)

/-- **The hypotheses after the first tree**, when it falls through. -/
theorem hyp_after (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {s s₁ : Store H}
    {f f₁ : Frame} {stk stk₁ : List Val} {e : BExpr} {es : List BExpr}
    (h : Hyp s f stk (e :: es)) (hev : EvalH host s f stk [e] (s₁, f₁, .normal stk₁)) :
    Hyp s₁ f₁ stk₁ es := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  have hc1 : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) [e] =
      some o₁ := Interp.chk_consE.mpr ⟨o₁, h1, by cases o₁ <;> simp⟩
  obtain ⟨hok, inv⟩ := (Interp.evalH_good (P := sprof) hH hev).1 hS hc1
  simp only [Interp.FlowOkE] at hok
  subst hok
  refine ⟨labels, ret, out, Interp.storeChk_inv inv hS, Interp.chk_inv inv h2, ?_⟩
  have e1 : vals stk.reverse ++ expression (BExpr.lowerList (e :: es)) =
      (vals stk.reverse ++ expression (BExpr.lowerList [e])) ++
        expression (BExpr.lowerList es) := by
    simp [expression]
  rw [e1] at ht
  exact typed_prefix hT hH hS hc1 ht hev

/-- The hypotheses of the arguments of an operator. -/
theorem hyp_args {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
    (h : Hyp s f stk (.op i args :: es)) : Hyp s f stk args := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  exact ⟨labels, ret, oa, hS, ha, Sim.ContextTyped.suffix (Interp.code_op stk i args es ▸ ht)⟩

/-- The hypotheses of the condition of an `if`. -/
theorem hyp_cond {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {c t el es : List BExpr} (h : Hyp s f stk (.if_ bt c t el :: es)) : Hyp s f stk c := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, -⟩ := Interp.chk1_ifE h1
  exact ⟨labels, ret, oc, hS, hco, Sim.ContextTyped.suffix (Interp.code_if stk bt c t el es ▸ ht)⟩

/-- The arity and the hypotheses of the body of a block. -/
theorem hyp_block {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {body es : List BExpr} (h : Hyp s f stk (.block bt body :: es)) :
    ∃ np nr, arity f bt = some (np, nr) ∧ Hyp s f (stk.take np) body := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_blockE h1
  have har : arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (nr :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have henter := Interp.steps_enter (P := sprof) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) (s := s) (f := f)
    (B := BExpr.lowerList body) hp (Interp.step_block har) (expression (BExpr.lowerList es))
  have htK := (Interp.code_block (body := body) stk bt es ▸ ht).steps henter
  exact ⟨np, nr, har, nr :: labels, ret, ob, hS, hb', Sim.ContextTyped.label htK⟩

/-- The arity and the hypotheses of the body of a loop. -/
theorem hyp_loop {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType}
    {body es : List BExpr} (h : Hyp s f stk (.loop bt body :: es)) :
    ∃ np nr, arity f bt = some (np, nr) ∧ Hyp s f (stk.take np) body := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨np, nr, hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har : arity f bt = some (np, nr) := (Interp.arity_eq f bt).trans hba
  obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  have henter := Interp.steps_enter (P := sprof) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) (s := s) (f := f)
    (B := BExpr.lowerList body) hp (Interp.step_loop har) (expression (BExpr.lowerList es))
  have htK := (Interp.code_loop (body := body) stk bt es ▸ ht).steps henter
  exact ⟨np, nr, har, np :: labels, ret, ob, hS, hb', Sim.ContextTyped.label htK⟩

/-- **The hypotheses after a loop iteration branching back**, at the loop. -/
theorem hyp_loopBack (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s s₁ : Store H} {f f₁ : Frame} {stk vs : List Val} {bt : BlockType}
    {body es : List BExpr} {np nr : Nat} (har : arity f bt = some (np, nr))
    (h : Hyp s f stk (.loop bt body :: es))
    (hev : EvalH host s f (stk.take np) body (s₁, f₁, .brk 0 vs)) :
    Hyp s₁ f₁ (vs.take np ++ stk.drop np) (.loop bt body :: es) := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨np', nr', hba, hp, hbody, rfl⟩ := Interp.chk1_loopE h1
  have har' : arity f bt = some (np', nr') := (Interp.arity_eq f bt).trans hba
  rw [har] at har'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj har')
  obtain ⟨ob, hb, -⟩ := Interp.endsAt_eq hbody
  have hb' : Interp.chk s.funcs f.module f.locals.length ret (np :: labels)
      (some (stk.take np).length) body = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb
  set rest := expression (BExpr.lowerList es) with hrest
  have henter := Interp.steps_enter (P := sprof) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) (s := s) (f := f)
    (B := BExpr.lowerList body) hp (Interp.step_loop har) rest
  have htK := (Interp.code_loop (body := body) stk bt es ▸ ht).steps henter
  obtain ⟨hok, inv1⟩ := (Interp.evalH_good (P := sprof) hH hev).1 hS hb'
  obtain ⟨c', o', hrun, he, hm⟩ :=
    Interp.run_of_wp ((Interp.evalH_good (P := sprof) hH hev).2 hS hb')
  have htL := ContextTyped.steps_typed hT htK
    (Silmaril.Wasm.Logic.Core.Steps.ctx _ rest
      (Silmaril.Wasm.Logic.Core.Steps.label np [.loop bt (BExpr.lowerList body)] hrun))
  have hnp : np ≤ vs.length := by
    obtain ⟨k, hk, hkl⟩ := hok
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    omega
  have hx := Interp.exit_br0 (P := sprof) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) (s₁ := s₁) (f₁ := f₁)
    (n := np) (cont := [.loop bt (BExpr.lowerList body)]) he hm hnp (stk.drop np).reverse rest
  have hlen : (vs.take np ++ stk.drop np).length = stk.length := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  refine ⟨labels, ret, out, Interp.storeChk_inv inv1 hS, ?_, ?_⟩
  · rw [hlen]; exact Interp.chk_inv inv1 hc
  · rw [Interp.code_loop]
    simpa [List.reverse_append, List.append_assoc, expression, hrest] using htL.steps hx

/-- **The arm of an `if`**, once its condition has fallen through: the condition is an `i32`,
the block type resolves, and the arm satisfies the hypotheses. -/
theorem hyp_arm (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s s₁ : Store H} {f f₁ : Frame} {stk stk' : List Val} {bt : BlockType}
    {c t el es : List BExpr} (h : Hyp s f stk (.if_ bt c t el :: es))
    (hev : EvalH host s f stk c (s₁, f₁, .normal stk')) :
    ∃ cv stk₁ b np nr, stk' = cv :: stk₁ ∧ truthy cv = some b ∧ arity f₁ bt = some (np, nr) ∧
      Hyp s₁ f₁ (stk₁.take np) (if b then t else el) := by
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := h
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨oc, hco, hk1⟩ := Interp.chk1_ifE h1
  have hcode := Interp.code_if stk bt c t el es
  set rest := expression (BExpr.lowerList es) with hrest
  have ht₁ := typed_prefix hT hH hS hco (hcode ▸ ht) hev
  obtain ⟨hoc, inv0⟩ := (Interp.evalH_good (P := sprof) hH hev).1 hS hco
  obtain ⟨np, nr, ha, -⟩ := hk1 _ hoc
  have har : arity f₁ bt = some (np, nr) := by
    rw [Interp.arity_eq, inv0.2.1]; exact ha
  obtain ⟨cv, stk₁, b, rfl, hb⟩ := Interp.truthy_progressH ht₁
  obtain ⟨inv1, hp, hendArm, -⟩ :=
    Interp.arity_if_pre (b := b) hS (Interp.evalH_good (P := sprof) hH hev).1 har hc
  obtain ⟨ob, hb', -⟩ := Interp.endsAt_eq (Interp.chk_inv_endsAt inv1 hendArm)
  have hb'' : Interp.chk s₁.funcs f₁.module f₁.locals.length ret (nr :: labels)
      (some (stk₁.take np).length) (if b then t else el) = some ob := by
    rw [Interp.take_length_of_le hp]; exact hb'
  have hif := Interp.step_if_arm (o := fun _ _ _ _ => false) (s := s₁) (f := f₁) (stk := stk₁)
    (bt := bt) (t := t) (el := el) (rest := rest) hb
  have henter := Interp.steps_enter (P := sprof) (host := Silmaril.Wasm.SingleThreaded.Det.noHost) (s := s₁) (f := f₁)
    (B := BExpr.lowerList (if b then t else el)) hp (Interp.step_block har) rest
  have htK := ht₁.steps ((Relation.ReflTransGen.single hif).trans henter)
  exact ⟨cv, stk₁, b, np, nr, rfl, hb, har, nr :: labels, ret, ob, Interp.storeChk_inv inv1 hS,
    hb'', Sim.ContextTyped.label htK⟩

end

/-! ## Abrupt ends of the constructs -/

section
variable {host : HostSemantics H}

theorem nodiv_opRest_error {i : Instr} {es : List BExpr} {e : PUnit.{2}}
    {cs : List (Call (CallSig H))} : ¬ Path (opRest pure i es (.error e)) cs .div := by
  simp only [opRest, bc_error, ret_bind', contK_error]; exact not_path_pure_div

theorem nodiv_opRest_pass {i : Instr} {es : List BExpr} {f₁ : Frame} {fl : Flow} {σ : St H}
    {cs : List (Call (CallSig H))} (hn : ¬ fl.IsNormal) :
    ¬ Path (opRest pure i es (.ok (⟨(f₁, fl)⟩, σ))) cs .div := by
  simp only [opRest, bc_ok, thenK_pass _ hn, tr_pure, ret_bind', contK_pass es hn]
  exact not_path_pure_div

theorem nodiv_opRest_flat {i : Instr} {es : List BExpr} (hi : ∀ x, i ≠ .call x) {s₁ s₂ : Store H}
    {f₁ f₂ : Frame} {stk₁ : List Val} {fl : Flow}
    (hflat : evalFlat s₁ f₁ stk₁ i = some (s₂, f₂, fl)) (hn : ¬ fl.IsNormal)
    {cs : List (Call (CallSig H))} :
    ¬ Path (opRest pure i es (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩))) cs .div := by
  simp only [opRest, bc_ok]
  show ¬ Path (tr (opC callEv i f₁ stk₁) ⟨s₁⟩ >>= (fun x => contK es x >>= pure)) cs .div
  rw [opC_flat hi, tr, run_flatK, hflat]
  cases fl with
  | normal => exact absurd trivial hn
  | trap =>
    simp only [evalTree, ret_bind', contK_error]; exact not_path_pure_div
  | _ =>
    simp only [evalTree, ret_bind', contK_pass es hn]; exact not_path_pure_div

theorem nodiv_blockRest_error {np nr : Nat} {stk : List Val} {es : List BExpr} {e : PUnit.{2}}
    {cs : List (Call (CallSig H))} : ¬ Path (blockRest pure np nr stk es (.error e)) cs .div := by
  simp only [blockRest, bc_error, ret_bind', contK_error]; exact not_path_pure_div

theorem nodiv_blockRest_none {np nr : Nat} {stk : List Val} {es : List BExpr} {f₁ : Frame}
    {fl : Flow} {σ : St H} (hvs : fl.blockVals = none) {cs : List (Call (CallSig H))} :
    ¬ Path (blockRest pure np nr stk es (.ok (⟨(f₁, fl)⟩, σ))) cs .div := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;>
    simp only [Flow.blockVals, reduceCtorEq] at hvs <;>
    simp only [blockRest, bc_ok, blockK, tr_pure, ret_bind', contK, thenK] <;>
    exact not_path_pure_div

theorem nodiv_loopRest_error {bt : BlockType} {body : List BExpr} {np nr : Nat} {stk : List Val}
    {es : List BExpr} {e : PUnit.{2}} {cs : List (Call (CallSig H))} :
    ¬ Path (loopRest pure bt body np nr stk es (.error e)) cs .div := by
  simp only [loopRest, bc_error, ret_bind', contK_error]; exact not_path_pure_div

theorem nodiv_loopRest_pass {bt : BlockType} {body : List BExpr} {np nr : Nat} {stk : List Val}
    {es : List BExpr} {f₁ : Frame} {fl : Flow} {σ : St H} (hn : ¬ fl.IsNormal)
    (h0 : ∀ vs, fl ≠ .brk 0 vs) {cs : List (Call (CallSig H))} :
    ¬ Path (loopRest pure bt body np nr stk es (.ok (⟨(f₁, fl)⟩, σ))) cs .div := by
  rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | t
  · exact absurd trivial hn
  · exact absurd rfl (h0 ws)
  all_goals
    simp only [loopRest, bc_ok, loopK, tr_pure, ret_bind', Sum.elim_inl, contK, thenK]
    exact not_path_pure_div

/-- The tree of a call after its arguments: the call event, then the answer and the rest. -/
theorem opRest_call {x : FuncIdx} {es : List BExpr} {s₁ : Store H} {f₁ : Frame}
    {stk₁ : List Val} {a : Nat} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hfi : s₁.func? f₁ x = some (a, fi))
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    opRest pure (.call x) es (.ok (⟨(f₁, .normal stk₁)⟩, ⟨s₁⟩)) =
      vis (E := SigEv (CallSig H)) (R := Store H × Flow)
        ⟨(a, (stk₁.take ps.length).reverse, s₁), rfl⟩
        fun n => tr (callAns f₁ stk₁ ps rs n) ⟨s₁⟩ >>= fun x => contK es x >>= pure := by
  simp only [opRest, bc_ok]
  show tr (callEv x f₁ stk₁) ⟨s₁⟩ >>= (fun x => contK es x >>= pure) = _
  rw [tr_callEv, hfi]
  dsimp only
  rw [hty]
  dsimp only
  exact vis_bind _ _ _

end

/-! ## The coinductive step -/

section
variable {host : HostSemantics H}

/-- The callee facts after the arguments of a checked call. -/
theorem call_info (hH : Interp.NativeHostSlice host) {s : Store H} {f : Frame}
    {stk : List Val} {x : FuncIdx} {args es : List BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length)
      (.op (.call x) args :: es) = some out)
    {s₁ : Store H} {f₁ : Frame} {stk₁ : List Val}
    (hev : EvalH host s f stk args (s₁, f₁, .normal stk₁)) :
    ∃ a fi ps rs, s₁.func? f₁ x = some (a, fi) ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      Interp.EvalInv s f (s₁, f₁, .normal stk₁) ∧ ps.length ≤ stk₁.length := by
  obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
  obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := sprof) hH hev).1 h1
  obtain ⟨p, q, hpq, -, -⟩ := Interp.flatChk_call (Interp.flatChkE_call hf)
  obtain ⟨a, fi, ps, rs, hfi, hty, -, -⟩ := Interp.callArity_func? hpq
  obtain ⟨inv1, hp, -⟩ :=
    Interp.arity_call_pre hS (Interp.evalH_good (P := sprof) hH hev).1 hfi hty hc
  exact ⟨a, fi, ps, rs, hfi, hty, inv1, hp⟩

/-- **The operator case.** -/
theorem sil_op (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {i : Instr} {args es : List BExpr}
    (h : SilHyp host s f stk (.op i args :: es)) :
    DivStepO (hostCall host) (SilHyp host) ⊥ s f stk (.op i args :: es) := by
  obtain ⟨hy, cs, hA, hp⟩ := h
  have hy0 := hy
  obtain ⟨labels, ret, out, hS, hc, ht⟩ := hy
  rw [← bind_pure (tr _ _), tree_op] at hp
  rcases path_bind_inv cs hp with ⟨cs₁, cs₂, w, rfl, hp₁, hp₂⟩ | ⟨-, hp₁⟩
  swap
  · exact .args ⟨hyp_args hy0, cs, hA, hp₁⟩
  obtain ⟨hA₁, hA₂⟩ := answered_append.1 hA
  rcases w with e | ⟨⟨⟨f₁, fl⟩⟩, ⟨s₁⟩⟩
  · exact (nodiv_opRest_error hp₂).elim
  have hev := evalH_of_path hA₁ hp₁
  by_cases hn : fl.IsNormal
  swap
  · exact (nodiv_opRest_pass hn hp₂).elim
  rcases fl with stk₁ | _ | _ | _ | _ <;> simp only [Flow.IsNormal] at hn
  by_cases hcall : ∃ x, i = .call x
  · obtain ⟨x, rfl⟩ := hcall
    obtain ⟨a, fi, ps, rs, hfi, hty, inv1, hp⟩ := call_info hH hS hc hev
    have hS₁ := Interp.storeChk_inv inv1 hS
    rw [opRest_call hfi hty] at hp₂
    obtain ⟨n, cs', rfl, hp₃⟩ := path_vis_inv hp₂
    obtain ⟨hcall, hA₃⟩ := answered_cons.1 hA₂
    obtain ⟨s₂, fl⟩ := n
    change hostCall host s₁ a (stk₁.take ps.length).reverse (s₂, fl) at hcall
    have hlen : (stk₁.take ps.length).reverse.length = ps.length := by
      simp only [List.length_reverse, List.length_take]; omega
    obtain ⟨⟨ob, -, hok, -⟩, -, -⟩ :=
      Interp.hostCall_sound (P := sprof) hH s₁ s₂ f₁ a fi ps rs _ fl hS₁
        (Interp.funcs_of_func? hfi) hty hlen hcall
    cases hvs : fl.retVals with
    | some vs =>
      rw [tr_callAns_ok hvs, ret_bind', contK_normal, bind_pure] at hp₃
      exact .callRet hev hfi hty hcall hvs
        ⟨hyp_after hT hH hy0 (.callOk hev hfi hty hcall hvs .nil), cs', hA₃, hp₃⟩
    | none =>
      exfalso
      rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | t <;>
        simp only [Flow.retVals, reduceCtorEq] at hvs
      · obtain ⟨m, hm, -⟩ := hok
        simp at hm
      · rw [tr_callAns_trap, ret_bind', contK_error] at hp₃
        exact not_path_ret_bind_pure hp₃
      · exact hok
  · have hi : ∀ x, i ≠ .call x := fun x hx => hcall ⟨x, hx⟩
    obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
    obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := sprof) hH hev).1 h1
    have htyped := typed_prefix hT hH hS (Interp.chk1_opE h1).choose_spec.1
      (Interp.code_op stk i args es ▸ ht) hev
    obtain ⟨⟨s₂, f₂, fl₂⟩, hfl⟩ := Interp.evalFlat_progressH hf hi htyped
    by_cases hn₂ : fl₂.IsNormal
    swap
    · exact (nodiv_opRest_flat hi hfl hn₂ hp₂).elim
    rcases fl₂ with stk₂ | _ | _ | _ | _ <;> simp only [Flow.IsNormal] at hn₂
    rw [opRest_flat pure hi hfl, bind_pure] at hp₂
    exact .opK hi hev hfl ⟨hyp_after hT hH hy0 (.opOk hi hev hfl .nil), cs₂, hA₂, hp₂⟩

/-- **The block case.** -/
theorem sil_block (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
    (h : SilHyp host s f stk (.block bt body :: es)) :
    DivStepO (hostCall host) (SilHyp host) ⊥ s f stk (.block bt body :: es) := by
  obtain ⟨hy, cs, hA, hp⟩ := h
  obtain ⟨np, nr, har, hyb⟩ := hyp_block hy
  rw [← bind_pure (tr _ _), tree_block pure har] at hp
  rcases path_bind_inv cs hp with ⟨cs₁, cs₂, w, rfl, hp₁, hp₂⟩ | ⟨-, hp₁⟩
  swap
  · exact .block har ⟨hyb, cs, hA, hp₁⟩
  obtain ⟨hA₁, hA₂⟩ := answered_append.1 hA
  rcases w with e | ⟨⟨⟨f₁, fl⟩⟩, ⟨s₁⟩⟩
  · exact (nodiv_blockRest_error hp₂).elim
  have hev := evalH_of_path hA₁ hp₁
  cases hvs : fl.blockVals with
  | none => exact (nodiv_blockRest_none hvs hp₂).elim
  | some vs =>
    rw [blockRest_ok pure hvs, bind_pure] at hp₂
    exact .blockK har hev hvs ⟨hyp_after hT hH hy (.blockOk har hev hvs .nil), cs₂, hA₂, hp₂⟩

/-- **The loop case.** A branch back is the step to the loop at its new state. -/
theorem sil_loop (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {body es : List BExpr}
    (h : SilHyp host s f stk (.loop bt body :: es)) :
    DivStepO (hostCall host) (SilHyp host) ⊥ s f stk (.loop bt body :: es) := by
  obtain ⟨hy, cs, hA, hp⟩ := h
  obtain ⟨np, nr, har, hyb⟩ := hyp_loop hy
  rw [← bind_pure (tr _ _), tree_loop pure har] at hp
  rcases path_bind_inv cs hp with ⟨cs₁, cs₂, w, rfl, hp₁, hp₂⟩ | ⟨-, hp₁⟩
  swap
  · exact .loop har ⟨hyb, cs, hA, hp₁⟩
  obtain ⟨hA₁, hA₂⟩ := answered_append.1 hA
  rcases w with e | ⟨⟨⟨f₁, fl⟩⟩, ⟨s₁⟩⟩
  · exact (nodiv_loopRest_error hp₂).elim
  have hev := evalH_of_path hA₁ hp₁
  rcases fl with ws | ⟨_ | k, vs⟩ | ws | _ | t
  · rw [loopRest_normal, bind_pure] at hp₂
    exact .loopK har hev ⟨hyp_after hT hH hy (.loopOk har hev .nil), cs₂, hA₂, hp₂⟩
  · rw [loopRest_brk, bind_pure] at hp₂
    exact .loopBack har hev ⟨hyp_loopBack hT hH har hy hev, cs₂, hA₂, hp₂⟩
  all_goals exact (nodiv_loopRest_pass (by simp [Flow.IsNormal]) (by simp) hp₂).elim

/-- **The `if` case.** -/
theorem sil_if (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {bt : BlockType} {c t el es : List BExpr}
    (h : SilHyp host s f stk (.if_ bt c t el :: es)) :
    DivStepO (hostCall host) (SilHyp host) ⊥ s f stk (.if_ bt c t el :: es) := by
  obtain ⟨hy, cs, hA, hp⟩ := h
  rw [← bind_pure (tr _ _), tree_cons, denC, tr_bind, bind_assoc', bind_assoc'] at hp
  rcases path_bind_inv cs hp with ⟨cs₁, cs₂, w, rfl, hp₁, hp₂⟩ | ⟨-, hp₁⟩
  swap
  · exact .cond ⟨hyp_cond hy, cs, hA, hp₁⟩
  obtain ⟨hA₁, hA₂⟩ := answered_append.1 hA
  rcases w with e | ⟨⟨⟨f₁, fl⟩⟩, ⟨s₁⟩⟩
  · simp only [bc_error, ret_bind', contK_error] at hp₂
    exact (not_path_pure_div hp₂).elim
  have hev := evalH_of_path hA₁ hp₁
  by_cases hn : fl.IsNormal
  swap
  · exfalso
    rcases fl with ws | ⟨_ | k, ws⟩ | ws | _ | t
    · exact hn trivial
    all_goals
      simp only [bc_ok, tr_pure, ret_bind', contK, thenK] at hp₂
      exact not_path_pure_div hp₂
  rcases fl with stk' | _ | _ | _ | _ <;> simp only [Flow.IsNormal] at hn
  obtain ⟨cv, stk₁, b, np, nr, rfl, hb, har, hya⟩ := hyp_arm hT hH hy hev
  simp only [bc_ok] at hp₂
  rw [hb, har] at hp₂
  dsimp only at hp₂
  rw [tr_bind, bind_assoc'] at hp₂
  rcases path_bind_inv cs₂ hp₂ with ⟨cs₃, cs₄, w, rfl, hp₃, hp₄⟩ | ⟨-, hp₃⟩
  swap
  · exact .arm hev hb har ⟨hya, cs₂, hA₂, by cases b <;> exact hp₃⟩
  obtain ⟨hA₃, hA₄⟩ := answered_append.1 hA₂
  change Path (blockRest pure np nr stk₁ es w) cs₄ .div at hp₄
  rcases w with e | ⟨⟨⟨f₂, fl₂⟩⟩, ⟨s₂⟩⟩
  · exact (nodiv_blockRest_error hp₄).elim
  have hevb : EvalH host s₁ f₁ (stk₁.take np) (if b then t else el) (s₂, f₂, fl₂) := by
    cases b <;> exact evalH_of_path hA₃ hp₃
  cases hvs : fl₂.blockVals with
  | none => exact (nodiv_blockRest_none hvs hp₄).elim
  | some vs =>
    rw [blockRest_ok pure hvs, bind_pure] at hp₄
    exact .ifK hev hb har hevb hvs
      ⟨hyp_after hT hH hy (.ifOk hev hb har hevb hvs .nil), cs₄, hA₄, hp₄⟩

/-- One unfolding of local divergence, at every tree list satisfying the invariant. -/
theorem sil_step (hT : HostTyped host) (hH : Interp.NativeHostSlice host) :
    ∀ s f stk es, SilHyp host s f stk es → DivStepO (hostCall host) (SilHyp host) ⊥ s f stk es := by
  intro s f stk es h
  rcases es with _ | ⟨e, es⟩
  · exfalso
    obtain ⟨-, cs, -, hp⟩ := h
    exact not_path_ret_div (by simpa [denListC_nil, tr_pure] using hp)
  · rcases e with ⟨i, args⟩ | ⟨bt, body⟩ | ⟨bt, body⟩ | ⟨bt, cnd, t, el⟩ | ⟨bt, cs, body⟩
    · exact sil_op hT hH h
    · exact sil_block hT hH h
    · exact sil_loop hT hH h
    · exact sil_if hT hH h
    · exfalso
      obtain ⟨⟨labels, ret, out, -, hc, -⟩, -⟩ := h
      obtain ⟨o₁, h1, -⟩ := Interp.chk_consE.mp hc
      simp [Interp.chk1E, Interp.noExt] at h1

/-- **Silent paths of checked typed trees are local divergence**, at the H2 oracle. -/
theorem silent_localDivO_host (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out)
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (BExpr.lowerList es)⟩)
    (hsil : ∃ cs, Answered (hostCall host) cs ∧
      Path (tr (denListE es f stk : M (CallSig H) H Res) ⟨s⟩) cs .div) :
    LocalDivO (hostCall host) s f stk es :=
  localDivO_of_coind (sil_step hT hH) s f stk es ⟨⟨labels, ret, out, hS, hc, ht⟩, hsil⟩

end

end Silmaril.Proofs.Wasm.Abstract.FullObsNative
