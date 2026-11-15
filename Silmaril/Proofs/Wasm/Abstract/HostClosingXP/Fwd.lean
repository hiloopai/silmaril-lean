module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Calls
public import Silmaril.Games.Abstract.Module.Thms
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic

/-!
# The logged forward simulation of `EvalLXPh` (proofs)

* `GoodCX`: the returning closed behaviours whose consistent log is the event log of the Core run
  of the call, in any frame and any `call_ref` form (`CalleeRun`), with the answer a canonical
  host-oracle outcome (`hostCallXP`, read through the exit flow) for the arity facts;
* `evalLXPh_fwd`: a logged canonical run whose calls `GoodCX` resolves to a consistent `q` is an
  `EvalOXP (hostCallXP host)` run and, on a store with the tag invariants, a logged Core run with
  exactly the host events `q` (`CoreLP`). A cut call is never resolved by a returning behaviour
  (`GoodCX` returns at most the callee's result arity).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallX (tailPop TailRes)
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.HostEvalP (hostCallXP)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}

/-! ## Resolved logs -/

/-- The host answers of a log are allowed. -/
abbrev Cons (host : HostSemantics H) (q : List (Call (wasmHostSig H))) : Prop :=
  (coreHostRel host).Consistent q

theorem cons_append {q₁ q₂ : List (Call (wasmHostSig H))} :
    Cons host (q₁ ++ q₂) ↔ Cons host q₁ ∧ Cons host q₂ :=
  List.forall_mem_append

theorem substPre_append {sh : Silmaril.Games.Abstract.Shape} {c : sh.ClosedMod}
    {u v : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)} :
    Shape.SubstPre c (u ++ v) q ↔
      ∃ q₁ q₂, q = q₁ ++ q₂ ∧ Shape.SubstPre c u q₁ ∧ Shape.SubstPre c v q₂ := by
  induction u generalizing q with
  | nil => exact ⟨fun h => ⟨[], q, rfl, .nil, h⟩, fun ⟨q₁, q₂, e, h₁, h₂⟩ => by
      cases h₁; simpa [e] using h₂⟩
  | cons z u ih =>
    constructor
    · intro h
      cases h with
      | ext h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .ext h₁, h₂⟩
      | int hm h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .int hm h₁, h₂⟩
    · rintro ⟨q₁, q₂, rfl, h₁, h₂⟩
      cases h₁ with
      | ext h₁ => exact .ext (ih.2 ⟨_, _, rfl, h₁, h₂⟩)
      | int hm h₁ =>
        rw [List.append_assoc]
        exact Shape.SubstPre.int hm (ih.2 ⟨_, _, rfl, h₁, h₂⟩)

theorem substPre_mk {c : (wasmHShape H).ClosedMod} {a : Nat} {args : List Val} {s₁ s₂ : Store H}
    {b : List Val ⊕ Nat} {rest : List (HCall H)} {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre c ((OCall.mk a args s₁ b s₂).lift :: rest) q) :
    ∃ c₁ q', q = c₁ ++ q' ∧ (c₁, .ret b s₂) ∈ c a s₁ args ∧ Shape.SubstPre c rest q' := by
  change Shape.SubstPre c (⟨.inr ⟨a, (args, s₁)⟩, (b, s₂)⟩ :: rest) q at h
  cases h with
  | int hm h => exact ⟨_, _, rfl, hm, h⟩

/-- A resolved log ending in one call: the prefix and the call's returning callee behaviour. -/
theorem substPre_last {c : (wasmHShape H).ClosedMod} {l : List (OCall H)} {a : Nat}
    {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat} {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre c ((l ++ [OCall.mk a args s₁ b s₂]).map OCall.lift) q) :
    ∃ q₁ c₁, q = q₁ ++ c₁ ∧ Shape.SubstPre c (l.map OCall.lift) q₁ ∧
      (c₁, .ret b s₂) ∈ c a s₁ args := by
  rw [List.map_append, List.map_cons, List.map_nil] at h
  obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 h
  obtain ⟨c₁, q', rfl, hm, h₃⟩ := substPre_mk h₂
  cases h₃
  exact ⟨q₁, c₁, by simp, h₁, hm⟩

/-- A resolved log with one call in the middle. -/
theorem substPre_mid {c : (wasmHShape H).ClosedMod} {l₁ l₂ : List (OCall H)} {a : Nat}
    {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat} {q : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre c ((l₁ ++ OCall.mk a args s₁ b s₂ :: l₂).map OCall.lift) q) :
    ∃ q₁ c₁ q₂, q = q₁ ++ (c₁ ++ q₂) ∧ Shape.SubstPre c (l₁.map OCall.lift) q₁ ∧
      (c₁, .ret b s₂) ∈ c a s₁ args ∧ Shape.SubstPre c (l₂.map OCall.lift) q₂ := by
  rw [List.map_append, List.map_cons] at h
  obtain ⟨q₁, q₂', rfl, h₁, h₂⟩ := substPre_append.1 h
  obtain ⟨c₁, q₂, rfl, hm, h₃⟩ := substPre_mk h₂
  exact ⟨q₁, c₁, q₂, rfl, h₁, hm, h₃⟩

/-! ## The returning behaviours that are logged Core runs -/

/-- **Returning closed behaviours that are logged Core runs**: with a consistent log, a
canonical host-oracle outcome (read through the exit flow), and, on a store with the tag
invariants and the exception checker's store check, for typed arguments, the event log of the
Core run of the call in any frame and any `call_ref` form. -/
def GoodCX (tags : List TagInst) (P : Silmaril.Wasm.Numerics.Profile) (host : HostSemantics H) :
    (wasmHShape H).ClosedMod := fun a s us =>
  {y | ∀ b s', y.2 = .ret b s' → Cons host y.1 →
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (bfl fl : Binaryen.Flow),
      s.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      hostCallXP host s a us (s', bfl) ∧ exitFlow rs.length bfl = some fl ∧
      endOfFlow fl s' = .ret b s' ∧
      (TagsOk tags s → StoreChkE (ehExt tags) s.funcs → us.length = ps.length →
        CalleeRun P host s a us y.1 s' b)}

section Good

variable {tags : List TagInst} {a : Nat} {args : List Val} {s₁ s₂ : Store H}
  {c₁ : List (Call (wasmHostSig H))} {fi : FuncInst H} {ps rs : List Validation.CValType}

/-- A returned answer `inl ws` of `GoodCX`: at most the callee's result arity. -/
theorem goodCX_inl {ws : List Val} (hm : (c₁, .ret (.inl ws) s₂) ∈ GoodCX tags P host a s₁ args)
    (hc : Cons host c₁) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    ∃ bfl w, hostCallXP host s₁ a args (s₂, bfl) ∧ bfl.retVals = some w ∧
      ws.reverse = w.take rs.length ∧ ws.length ≤ rs.length ∧
      (TagsOk tags s₁ → StoreChkE (ehExt tags) s₁.funcs → args.length = ps.length →
        CalleeRun P host s₁ a args c₁ s₂ (.inl ws)) := by
  obtain ⟨fi', ps', rs', bfl, fl, hfi', hty', hC, hx, hend, hrun⟩ := hm _ _ rfl hc
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  have hlen : ws.length ≤ rs'.length := exitFlow_len hx hend
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inl.injEq, reduceCtorEq, and_true] at hend
  all_goals subst hend
  all_goals exact ⟨_, w, hC, rfl, by simp, hlen, hrun⟩

/-- A returned answer `inr t` of `GoodCX` is a thrown oracle outcome. -/
theorem goodCX_inr {t : Nat} (hm : (c₁, .ret (.inr t) s₂) ∈ GoodCX tags P host a s₁ args)
    (hc : Cons host c₁) (hfi : s₁.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    hostCallXP host s₁ a args (s₂, .throw t) ∧
      (TagsOk tags s₁ → StoreChkE (ehExt tags) s₁.funcs → args.length = ps.length →
        CalleeRun P host s₁ a args c₁ s₂ (.inr t)) := by
  obtain ⟨fi', ps', rs', bfl, fl, hfi', hty', hC, hx, hend, hrun⟩ := hm _ _ rfl hc
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
  rcases bfl with w | ⟨_ | k, w⟩ | w | _ | t' <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inr.injEq, reduceCtorEq, and_true] at hend
  subst hend
  exact ⟨hC, hrun⟩

end Good

/-! ## The simulation -/

/-- The tag invariants after an oracle answer. -/
theorem tagsOk_hostCallXP {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s' : Store H} {a : Nat} {us : List Val} {fl : Binaryen.Flow}
    (h : hostCallXP host s a us (s', fl)) (hts : TagsOk tags s) : TagsOk tags s' :=
  (hostCallXP_sound (P := Silmaril.Wasm.Numerics.Profile.spec) hH hE _ _ _ _ h hts).1

/-- **The logged forward simulation of `EvalLXPh`**, every profile: a logged run whose calls
`GoodCX` resolves to a consistent `q` is an `EvalOXP (hostCallXP host)` run and, on a store with
the tag invariants, a logged Core run with exactly the host events `q`. -/
theorem evalLXPh_fwd {tags : List TagInst} (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {l : List (OCall H)} {r : Store H × Frame × POut}
    (h : EvalLXPh s f stk es l r) :
    ∀ q, Shape.SubstPre (GoodCX tags P host) (l.map OCall.lift) q → Cons host q →
      EvalOXP (hostCallXP host) s f stk es r ∧
        (TagsOk tags s → CoreLP tags P host s f stk es r q) := by
  have AG := fun {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
      {r : Store H × Frame × POut} (d : EvalOXP (hostCallXP host) s f stk es r)
      (hts : TagsOk tags s) => evalOXP_host_good (P := P) hH hE d hts
  induction h with
  | nil =>
    intro q hq _
    cases hq
    exact ⟨.nil, fun _ => coreLP_nil⟩
  | argsAbort _ ho ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.argsAbort d ho, fun hts => coreLP_argsAbort (c hts) ho⟩
  | callRet _ hfi hty _ ih₁ ih₂ =>
    intro q hq hc
    obtain ⟨q₁, c₁, q₂, rfl, h₁, hm, h₃⟩ := substPre_mid hq
    rw [cons_append, cons_append] at hc
    obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ :=
      goodCX_inl hm hc.2.1 (funcs_of_func? hfi) hty
    obtain ⟨d₁, c₁'⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂'⟩ := ih₂ q₂ h₃ hc.2.2
    refine ⟨.callOk d₁ hfi hty hC hvs (hws ▸ d₂), fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_callRet hH hE (arityE_of_arityP a₁) (c₁' hts) hfi hty ⟨t₁, hC⟩ hvs hws
      (fun hS hn => hrun t₁ hS hn) (c₂' (tagsOk_hostCallXP hH hE hC t₁))
  | callThrow _ hfi hty ih =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, h₁, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨hC, hrun⟩ := goodCX_inr hm hc.2 (funcs_of_func? hfi) hty
    obtain ⟨d₁, c₁'⟩ := ih q₁ h₁ hc.1
    refine ⟨.callThrow d₁ hfi hty hC, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_callThrow (arityE_of_arityP a₁) (c₁' hts) hfi hty
      (fun hS hn => hrun t₁ hS hn)
  | callCut _ hfi hty hws =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, -, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨-, -, -, -, -, hle, -⟩ := goodCX_inl hm hc.2 (funcs_of_func? hfi) hty
    omega
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.opOk hi d₁ hflat d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_opOk (arityE_of_arityP a₁) (c₁ hts) hi hflat (c₂ (t₁.evalFlat hflat))
  | opStop hi _ hflat hfl ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    refine ⟨.opStop hi d hflat hfl, fun hts => ?_⟩
    obtain ⟨-, a₁, -⟩ := AG d hts
    exact coreLP_opStop (arityE_of_arityP a₁) (c hts) hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.blockOk har d₁ hvs d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_blockOk har (arityE_of_arityP a₁) (c₁ hts) hvs (c₂ t₁)
  | blockBrk har _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.blockBrk har d, fun hts => coreLP_blockBrk har (c hts)⟩
  | blockEsc har _ ho ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.blockEsc har d ho, fun hts => coreLP_blockEsc har (c hts) ho⟩
  | loopOk har _ _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.loopOk har d₁ d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_loopOk har (arityE_of_arityP a₁) (c₁ hts) (c₂ t₁)
  | loopBack har _ _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.loopBack har d₁ d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_loopBack har (arityE_of_arityP a₁) (c₁ hts) (c₂ t₁)
  | loopBrk har _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.loopBrk har d, fun hts => coreLP_loopBrk har (c hts)⟩
  | loopEsc har _ ho ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.loopEsc har d ho, fun hts => coreLP_loopEsc har (c hts) ho⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro q hq hc
    rw [List.map_append, List.map_append] at hq
    obtain ⟨q₁₂, q₃, rfl, h₁₂, h₃⟩ := substPre_append.1 hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 h₁₂
    rw [cons_append, cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.1.2
    obtain ⟨d₃, c₃⟩ := ih₃ q₃ h₃ hc.2
    refine ⟨.ifOk d₁ hb har d₂ hvs d₃, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    obtain ⟨t₂, a₂, -⟩ := AG d₂ t₁
    exact coreLP_ifOk (arityE_of_arityP a₁) (c₁ hts) hb har (arityE_of_arityP a₂) (c₂ t₁) hvs
      (c₃ t₂)
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.ifBrk d₁ hb har d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_ifBrk (arityE_of_arityP a₁) (c₁ hts) hb har (c₂ t₁)
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.ifEsc d₁ hb har d₂ ho, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_ifEsc (arityE_of_arityP a₁) (c₁ hts) hb har (c₂ t₁) ho
  | ifAbort _ ho ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.ifAbort d ho, fun hts => coreLP_ifAbort (c hts) ho⟩
  | indRet _ hres hfi hty hy _ ih₁ ih₂ =>
    intro q hq hc
    obtain ⟨q₁, c₁, q₂, rfl, h₁, hm, h₃⟩ := substPre_mid hq
    rw [cons_append, cons_append] at hc
    obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ := goodCX_inl hm hc.2.1 hfi hty
    obtain ⟨d₁, c₁'⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂'⟩ := ih₂ q₂ h₃ hc.2.2
    refine ⟨.callIndOk d₁ hres hfi hty hy hC hvs (hws ▸ d₂), fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_irRet hH hE (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) (c₁' hts)
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hfi hty hy ⟨t₁, hC⟩ hvs hws
      (fun hS hn => hrun t₁ hS hn) (c₂' (tagsOk_hostCallXP hH hE hC t₁))
  | indThrow _ hres hfi hty hy ih =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, h₁, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨hC, hrun⟩ := goodCX_inr hm hc.2 hfi hty
    obtain ⟨d₁, c₁'⟩ := ih q₁ h₁ hc.1
    refine ⟨.callIndStop d₁ hres hfi hty hy hC trivial, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_irThrow (.inl ⟨_, rfl⟩) (arityE_of_arityP a₁) (c₁' hts)
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_func hres) hy
      (fun hS hn => hrun t₁ hS hn)
  | indCut _ _ hfi hty _ hws =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, -, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨-, -, -, -, -, hle, -⟩ := goodCX_inl hm hc.2 hfi hty
    omega
  | indRes _ hres ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.callIndRes d hres, fun hts => coreLP_irTrap (c hts)
      (Silmaril.Wasm.Abstract.CallRes.steps_callIndirect_trap hres)⟩
  | refRet _ hfi hty hy _ ih₁ ih₂ =>
    intro q hq hc
    obtain ⟨q₁, c₁, q₂, rfl, h₁, hm, h₃⟩ := substPre_mid hq
    rw [cons_append, cons_append] at hc
    obtain ⟨bfl, w, hC, hvs, hws, -, hrun⟩ := goodCX_inl hm hc.2.1 hfi hty
    obtain ⟨d₁, c₁'⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂'⟩ := ih₂ q₂ h₃ hc.2.2
    refine ⟨.callRefOk d₁ hfi hty hy hC hvs (hws ▸ d₂), fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_irRet hH hE (.inr rfl) (arityE_of_arityP a₁) (c₁' hts) .refl hfi hty hy
      ⟨t₁, hC⟩ hvs hws (fun hS hn => hrun t₁ hS hn) (c₂' (tagsOk_hostCallXP hH hE hC t₁))
  | refThrow _ hfi hty hy ih =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, h₁, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨hC, hrun⟩ := goodCX_inr hm hc.2 hfi hty
    obtain ⟨d₁, c₁'⟩ := ih q₁ h₁ hc.1
    refine ⟨.callRefStop d₁ hfi hty hy hC trivial, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_irThrow (.inr rfl) (arityE_of_arityP a₁) (c₁' hts) .refl hy
      (fun hS hn => hrun t₁ hS hn)
  | refCut _ hfi hty _ hws =>
    intro q hq hc
    obtain ⟨q₁, c₁, rfl, -, hm⟩ := substPre_last hq
    rw [cons_append] at hc
    obtain ⟨-, -, -, -, -, hle, -⟩ := goodCX_inl hm hc.2 hfi hty
    omega
  | refNull _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.callRefNull d, fun hts => coreLP_irTrap (c hts)
      (.single (Step.callRefNull (c := .plain (.callRef _)) trivial))⟩
  | tail _ hres hfi hty hy ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tail d hres hfi hty hy, fun hts => coreLP_tail (c hts) hres⟩
  | tailRes _ hres ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tailRes d hres, fun hts => coreLP_tailRes (c hts) hres⟩
  | throw _ ht he hn ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.throw d ht he hn, fun hts => coreLP_throw (c hts) ht he hn⟩
  | throwRefNull _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.throwRefNull d, fun hts => coreLP_throwRefNull (c hts)⟩
  | throwRefExn _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.throwRefExn d, fun hts => coreLP_throwRefExn (c hts)⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    intro q hq hc
    rw [List.map_append] at hq
    obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := substPre_append.1 hq
    rw [cons_append] at hc
    obtain ⟨d₁, c₁⟩ := ih₁ q₁ h₁ hc.1
    obtain ⟨d₂, c₂⟩ := ih₂ q₂ h₂ hc.2
    refine ⟨.tryOk har d₁ hvs d₂, fun hts => ?_⟩
    obtain ⟨t₁, a₁, -⟩ := AG d₁ hts
    exact coreLP_tryOk har (arityE_of_arityP a₁) (c₁ hts) hvs (c₂ t₁)
  | tryBrk har _ ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tryBrk har d, fun hts => coreLP_tryBrk har (c hts)⟩
  | tryEsc har _ ho hnt ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tryEsc har d ho hnt, fun hts => coreLP_tryEsc har (c hts) ho hnt⟩
  | tryCatch har _ hcat ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tryCatch har d hcat, fun hts => coreLP_tryCatch har (c hts) hcat⟩
  | tryRethrow har _ hcat ih =>
    intro q hq hc
    obtain ⟨d, c⟩ := ih q hq hc
    exact ⟨.tryRethrow har d hcat, fun hts => coreLP_tryRethrow har (c hts) hcat⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
