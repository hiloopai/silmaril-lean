module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapCases
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Fwd

/-!
# The logged forward simulation of a run cut at a trapping callee (proofs)

`evalLXPh_trap`: if the log of an `EvalLXPh` run is `l₁ ++ z :: l₂`, the calls of `l₁` resolved by
`GoodCX` to `q₁` and the callee of `z` trapping with the host events `c₁` (`TrapAt`), with a
consistent `q₁ ++ c₁`, then the code has a logged Core run to a trap with exactly the host events
`q₁ ++ c₁` (`CoreLT`). The run is the full logged runs in front of the call (`evalLXPh_fwd`), the
callee's trap, and the trap leaving every context. Whatever the run does after the call
(including a cut, `callCut`) is not run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-- **The callee of an internal call traps**, with the host events `c₁`, on stores with the tag
invariants and the store check, for typed arguments. -/
def TrapAt (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H)
    (z : OCall H) (c₁ : List (Call (wasmHostSig H))) : Prop :=
  ∀ (a : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat) (s₂ : Store H),
    z = OCall.mk a args s₁ b s₂ → ∀ (fi : FuncInst H) (ps rs : List Validation.CValType),
    s₁.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
    TagsOk tags s₁ → StoreChkE (ehExt tags) s₁.funcs → args.length = ps.length →
    CalleeTrap P host s₁ a args c₁

section Split

variable {α : Type} {la lb l₁ l₂ : List α} {x z : α}

theorem split_two (h : la ++ lb = l₁ ++ z :: l₂) :
    (∃ m, la = l₁ ++ z :: m) ∨ ∃ m, l₁ = la ++ m ∧ lb = m ++ z :: l₂ := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h₁, h₂⟩ | ⟨c', h₁, h₂⟩
  · exact .inr ⟨a', h₁, h₂⟩
  · rcases c' with _ | ⟨z', m⟩
    · simp only [List.append_nil, List.nil_append] at h₁ h₂
      exact .inr ⟨[], by simp [h₁], by simp [h₂]⟩
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, -⟩ := h₂
      exact .inl ⟨m, h₁⟩

theorem split_mid (h : la ++ x :: lb = l₁ ++ z :: l₂) :
    (∃ m, la = l₁ ++ z :: m) ∨ (l₁ = la ∧ z = x) ∨ ∃ m, l₁ = la ++ x :: m ∧ lb = m ++ z :: l₂ := by
  rcases split_two h with h₁ | ⟨m, h₁, h₂⟩
  · exact .inl h₁
  · rcases m with _ | ⟨x', m⟩
    · simp only [List.append_nil, List.nil_append, List.cons.injEq] at h₁ h₂
      exact .inr (.inl ⟨h₁, h₂.1.symm⟩)
    · simp only [List.cons_append, List.cons.injEq] at h₂
      obtain ⟨rfl, h₂⟩ := h₂
      exact .inr (.inr ⟨m, h₁, h₂⟩)

theorem split_last (h : la ++ [x] = l₁ ++ z :: l₂) :
    (∃ m, la = l₁ ++ z :: m) ∨ (l₁ = la ∧ z = x) := by
  rcases split_mid (lb := []) h with h₁ | h₁ | ⟨m, -, h₂⟩
  · exact .inl h₁
  · exact .inr h₁
  · simp at h₂

end Split

/-- A full logged run, its resolved log consistent: an oracle run, the tag invariants after
it, its arity facts and its logged Core run. -/
theorem full_run {tags : List TagInst} (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr} {l : List (OCall H)}
    {r : Store H × Frame × POut} {q : List (Call (wasmHostSig H))}
    (hd : EvalLXPh s f stk es l r) (hq : Shape.SubstPre (GoodCX tags P host) (l.map OCall.lift) q)
    (hc : Cons host q) (hts : TagsOk tags s) :
    EvalOXP (hostCallXP host) s f stk es r ∧ TagsOk tags r.1 ∧
      ArityGoodP (ehExt tags) s f stk es r true ∧ CoreLP tags P host s f stk es r q := by
  obtain ⟨d, c⟩ := evalLXPh_fwd (P := P) hH hE hd q hq hc
  obtain ⟨t, a, -⟩ := evalOXP_host_good (P := P) hH hE d hts
  exact ⟨d, t, a, c hts⟩

/-- Splitting a resolved log and its consistency at an append. -/
theorem split_res {tags : List TagInst} {la m : List (OCall H)} {q c₁ : List (Call (wasmHostSig H))}
    (hq : Shape.SubstPre (GoodCX tags P host) ((la ++ m).map OCall.lift) q)
    (hc : Cons host (q ++ c₁)) :
    ∃ qa qm, q = qa ++ qm ∧ Shape.SubstPre (GoodCX tags P host) (la.map OCall.lift) qa ∧
      Shape.SubstPre (GoodCX tags P host) (m.map OCall.lift) qm ∧ Cons host qa ∧
      Cons host (qm ++ c₁) := by
  rw [List.map_append] at hq
  obtain ⟨qa, qm, rfl, h₁, h₂⟩ := substPre_append.1 hq
  rw [List.append_assoc, cons_append] at hc
  exact ⟨qa, qm, rfl, h₁, h₂, hc.1, hc.2⟩

/-- **The logged forward simulation of a run cut at a trapping callee**, every profile. -/
theorem evalLXPh_trap {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {l : List (OCall H)} {r : Store H × Frame × POut}
    (h : EvalLXPh s f stk es l r) :
    ∀ (l₁ : List (OCall H)) (z : OCall H) (l₂ : List (OCall H)), l = l₁ ++ z :: l₂ →
      ∀ q₁ c₁, Shape.SubstPre (GoodCX tags P host) (l₁.map OCall.lift) q₁ →
        TrapAt tags P host z c₁ → Cons host (q₁ ++ c₁) → TagsOk tags s →
        CoreLT tags P host s f stk es (q₁ ++ c₁) := by
  induction h with
  | nil =>
    intro l₁ z l₂ hl
    simp at hl
  | argsAbort _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs la lb r hargs hfi hty hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_mid hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_args (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_call (arityE_of_arityP a₁) cl₁ hfi hty
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ (funcs_of_func? hfi) hty t₁ hS hn)
    · obtain ⟨qa, qm', rfl, ha, hm', hca, hcm'⟩ := split_res hq hc
      obtain ⟨cx, qm, rfl, hmx, hm⟩ := substPre_mk hm'
      rw [List.append_assoc, cons_append] at hcm'
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs ha hca hts
      obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ :=
        goodCX_inl hmx hcm'.1 (funcs_of_func? hfi) hty
      simp only [List.append_assoc]
      exact coreLP_callRet hH hE (arityE_of_arityP a₁) cl₁ hfi hty ⟨t₁, hC⟩ hvs hws
        (fun hS hn => hrun t₁ hS hn) (ih₂ m z l₂ rfl qm c₁ hm hz hcm'.2 (tagsOk_hostCallXP hH hE hC t₁))
  | @callThrow s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs t la hargs hfi hty ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_call (arityE_of_arityP a₁) cl₁ hfi hty
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ (funcs_of_func? hfi) hty t₁ hS hn)
  | @callCut s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs la hargs hfi hty hws ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_call (arityE_of_arityP a₁) cl₁ hfi hty
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ (funcs_of_func? hfi) hty t₁ hS hn)
  | @opOk s s₁ s₂ f f₁ f₂ stk stk₁ stk₂ i args es la lb r hi hargs hflat hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_args (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs ha hca hts
      simp only [List.append_assoc]
      exact coreLP_opOk (arityE_of_arityP a₁) cl₁ hi hflat
        (ih₂ m z l₂ rfl qm c₁ hm hz hcm (t₁.evalFlat hflat))
  | opStop _ _ _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @blockOk s s₁ f f₁ stk vs bt body es np nr fl la lb r har hbody hvs hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_block har (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hbody ha hca hts
      simp only [List.append_assoc]
      exact coreLP_blockOk har (arityE_of_arityP a₁) cl₁ hvs (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | blockBrk har _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_block har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | blockEsc har _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_block har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @loopOk s s₁ f f₁ stk vs bt body es np nr la lb r har hbody hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_loop har (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hbody ha hca hts
      simp only [List.append_assoc]
      exact coreLP_loopOk har (arityE_of_arityP a₁) cl₁ (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | @loopBack s s₁ f f₁ stk vs bt body es np nr la lb r har hbody hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_loop har (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hbody ha hca hts
      simp only [List.append_assoc]
      exact coreLP_loopBack har (arityE_of_arityP a₁) cl₁ (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | loopBrk har _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_loop har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | loopEsc har _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_loop har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @ifOk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr fl la lb lc r hc' hb har harm hvs
      hk ih₁ ih₂ ih₃ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, hm₁⟩ | ⟨m, rfl, rfl⟩
    · rcases split_two hm₁ with ⟨m', rfl⟩ | ⟨m', rfl, rfl⟩
      · exact coreLT_ifCond (ih₁ l₁ z m' rfl q₁ c₁ hq hz hc hts)
      · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
        obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hc' ha hca hts
        simp only [List.append_assoc]
        exact coreLT_ifArm (arityE_of_arityP a₁) cl₁ hb har
          (ih₂ m' z m rfl qm c₁ hm hz hcm t₁)
    · obtain ⟨qab, qm, rfl, hab, hm, hcab, hcm⟩ := split_res hq hc
      rw [List.map_append] at hab
      obtain ⟨qa, qb, rfl, ha, hb'⟩ := substPre_append.1 hab
      rw [cons_append] at hcab
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hc' ha hcab.1 hts
      obtain ⟨-, t₂, a₂, cl₂⟩ := full_run hH hE harm hb' hcab.2 t₁
      rw [show qa ++ qb ++ qm ++ c₁ = qa ++ qb ++ (qm ++ c₁) by simp]
      exact coreLP_ifOk (arityE_of_arityP a₁) cl₁ hb har (arityE_of_arityP a₂) cl₂ hvs
        (ih₃ m z l₂ rfl qm c₁ hm hz hcm t₂)
  | @ifBrk s s₁ s₂ f f₁ f₂ stk stk₁ vs cv b bt c t el es np nr k la lb hc' hb har harm ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_ifCond (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hc' ha hca hts
      simp only [List.append_assoc]
      exact coreLT_ifArm (arityE_of_arityP a₁) cl₁ hb har (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | @ifEsc s s₁ s₂ f f₁ f₂ stk stk₁ cv b bt c t el es np nr o la lb hc' hb har harm ho ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_ifCond (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hc' ha hca hts
      simp only [List.append_assoc]
      exact coreLT_ifArm (arityE_of_arityP a₁) cl₁ hb har (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | ifAbort _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_ifCond (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @indRet s s₁ s₂ f f₁ stk stk₁ ws x y args es ad i fa fi ps rs la lb r hargs hres hfi hty hy hk
      ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_mid hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_args (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) cl₁
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
    · obtain ⟨qa, qm', rfl, ha, hm', hca, hcm'⟩ := split_res hq hc
      obtain ⟨cx, qm, rfl, hmx, hm⟩ := substPre_mk hm'
      rw [List.append_assoc, cons_append] at hcm'
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs ha hca hts
      obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ := goodCX_inl hmx hcm'.1 hfi hty
      simp only [List.append_assoc]
      exact coreLP_irRet hH hE (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) cl₁
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy ⟨t₁, hC⟩ hvs hws
        (fun hS hn => hrun t₁ hS hn) (ih₂ m z l₂ rfl qm c₁ hm hz hcm'.2 (tagsOk_hostCallXP hH hE hC t₁))
  | @indThrow s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs t la hargs hres hfi hty hy ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) cl₁
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
  | @indCut s s₁ s₂ f f₁ stk stk₁ ws x y args es ad i fa fi ps rs la hargs hres hfi hty hy hws ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) cl₁
        (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
  | indRes _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @refRet s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs la lb r hargs hfi hty hy hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_mid hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_args (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inr rfl) (arityE_of_arityP a₁) cl₁ .refl hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
    · obtain ⟨qa, qm', rfl, ha, hm', hca, hcm'⟩ := split_res hq hc
      obtain ⟨cx, qm, rfl, hmx, hm⟩ := substPre_mk hm'
      rw [List.append_assoc, cons_append] at hcm'
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs ha hca hts
      obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ := goodCX_inl hmx hcm'.1 hfi hty
      simp only [List.append_assoc]
      exact coreLP_irRet hH hE (.inr rfl) (arityE_of_arityP a₁) cl₁ .refl hfi hty hy ⟨t₁, hC⟩
        hvs hws (fun hS hn => hrun t₁ hS hn) (ih₂ m z l₂ rfl qm c₁ hm hz hcm'.2 (tagsOk_hostCallXP hH hE hC t₁))
  | @refThrow s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs t la hargs hfi hty hy ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inr rfl) (arityE_of_arityP a₁) cl₁ .refl hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
  | @refCut s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs la hargs hfi hty hy hws ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_last hl with ⟨m, rfl⟩ | ⟨rfl, rfl⟩
    · exact coreLT_args (ih l₁ z m rfl q₁ c₁ hq hz hc hts)
    · rw [cons_append] at hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hargs hq hc.1 hts
      exact coreLT_ir (.inr rfl) (arityE_of_arityP a₁) cl₁ .refl hy
        (fun hS hn => hz _ _ _ _ _ rfl _ _ _ hfi hty t₁ hS hn)
  | refNull _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | tail _ _ _ _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | tailRes _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | throw _ _ _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | throwRefNull _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | throwRefExn _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_args (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | @tryOk s s₁ f f₁ stk vs bt cs body es np nr fl la lb r har hbody hvs hk ih₁ ih₂ =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    rcases split_two hl with ⟨m, rfl⟩ | ⟨m, rfl, rfl⟩
    · exact coreLT_try har (ih₁ l₁ z m rfl q₁ c₁ hq hz hc hts)
    · obtain ⟨qa, qm, rfl, ha, hm, hca, hcm⟩ := split_res hq hc
      obtain ⟨-, t₁, a₁, cl₁⟩ := full_run hH hE hbody ha hca hts
      simp only [List.append_assoc]
      exact coreLP_tryOk har (arityE_of_arityP a₁) cl₁ hvs (ih₂ m z l₂ rfl qm c₁ hm hz hcm t₁)
  | tryBrk har _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_try har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | tryEsc har _ _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_try har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | tryCatch har _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_try har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)
  | tryRethrow har _ _ ih =>
    intro l₁ z l₂ hl q₁ c₁ hq hz hc hts
    exact coreLT_try har (ih l₁ z l₂ hl q₁ c₁ hq hz hc hts)

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
