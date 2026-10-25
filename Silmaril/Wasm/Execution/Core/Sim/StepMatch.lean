module

public import Silmaril.Wasm.Execution.Core.Sim.CodeRel
public import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

/-! # Matching a step of the same code on a related store

`Step.match_storeRel`: a step of a configuration is matched, in exactly one step,
by the *same code* on any `StoreRel F`-related store, provided `F` is contained in
`FuncRel BI` and the host respects `F`. The two results are related by the
closure `AdminsRel BI B` (for any runtime base relation `B`): they differ only
where a call entered a function body, which is `FuncRel`-related, so the bodies
are `InstrsRel BI`-related (`AdminsRel.src`).

This is the reflexive part of a code-relation simulation: the shared code of a
base pair (for example the prefix before a bottom instruction, `Sim/DeadSuffix`)
may contain labels, handlers and frames, and anything inside them may call. The
proof is by induction on the step: the four context rules by the induction
hypothesis; calls through `FuncRel`/`HostRespects`; the store-reading redexes by
`Step.transport_storeRel`; every other rule reads at most the exceptions of the
store, which related stores share.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Pointwise lookup in `Forall₂`-related lists. -/
theorem forall₂_getElem? {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {n : Nat} {a : α},
      l₁[n]? = some a → ∃ b, l₂[n]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hab _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, hab⟩
  | _, _, .cons _ ht, n + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact forall₂_getElem? ht h

/-- `CatchMatches` reads only the exceptions of the store. -/
theorem catchMatches_congr {s t : Store H} (hex : s.exns = t.exns) (f : Frame) (a : Nat)
    (c : Catch) : CatchMatches s f a c ↔ CatchMatches t f a c := by
  cases c <;> simp [CatchMatches, hex]

/-- A store-transportable redex: a step whose code is `val* a` with `a` neither a
context nor a call through a reference. -/
theorem transport_redex {F : FuncInst H → FuncInst H → Prop} {s s' t : Store H} {f f' : Frame}
    {code es' : List Admin} (hst : StoreRel F s t) (h : Step P host ⟨s, f, code⟩ ⟨s', f', es'⟩)
    (hr : lastRedex code = true)
    (hl : ∀ a, code.getLast? = some a → ¬ a.IsCtx ∧ ¬ a.IsCallRef) :
    ∃ t', Step P host ⟨t, f, code⟩ ⟨t', f', es'⟩ ∧ StoreRel F s' t' := by
  obtain ⟨us, b, -, rfl⟩ := eq_of_lastRedex hr
  obtain ⟨h1, h2⟩ := hl b (by simp)
  exact Step.transport_storeRel hst h1 h2 h

/-- The conclusion of `Step.match_storeRel` for a configuration step `c ~> c'`. -/
def MatchStore (P : Profile) (host : HostSemantics H) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c c' : Config H) : Prop :=
  ∀ t, StoreRel F c.store t → ∃ (t' : Store H) (es'' : List Admin),
    Step P host ⟨t, c.frame, c.code⟩ ⟨t', c'.frame, es''⟩ ∧ StoreRel F c'.store t' ∧
      AdminsRel BI B c'.code es''

section
variable {F : FuncInst H → FuncInst H → Prop} {BI : List Instr → List Instr → Prop}
  {B : List Admin → List Admin → Prop}

/-- A matched step whose code is unchanged. -/
theorem MatchStore.of_same {c c' : Config H}
    (h : ∀ t, StoreRel F c.store t → ∃ t', Step P host ⟨t, c.frame, c.code⟩ ⟨t', c'.frame, c'.code⟩ ∧
      StoreRel F c'.store t') : MatchStore P host F BI B c c' := by
  intro t hst
  obtain ⟨t', h1, h2⟩ := h t hst
  exact ⟨t', _, h1, h2, AdminsRel.refl _⟩

end

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- **Same code, related stores.** A step is matched by one step of the same code on
any `StoreRel F`-related store, with `AdminsRel BI B`-related results. -/
theorem Step.match_storeRel {F : FuncInst H → FuncInst H → Prop}
    {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}
    (hF : ∀ fi gi, F fi gi → FuncRel BI fi gi) (hhost : HostRespects F host)
    {c c' : Config H} (h : Step P host c c') : MatchStore P host F BI B c c' := by
  induction h with
  | parametric h => exact MatchStore.of_same fun t hst => ⟨t, .parametric h, hst⟩
  | numeric h => exact MatchStore.of_same fun t hst => ⟨t, .numeric h, hst⟩
  | vector h => exact MatchStore.of_same fun t hst => ⟨t, .vector h, hst⟩
  | «variable» h =>
    rename_i c c'
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', es'⟩ := c'
    refine MatchStore.of_same fun t hst => transport_redex hst (.variable h)
      (VariableStep.lastRedex_eq h) ?_
    intro a ha
    cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])
  | table h =>
    rename_i c c'
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', es'⟩ := c'
    refine MatchStore.of_same fun t hst => transport_redex hst (.table h)
      (TableStep.lastRedex_eq h) ?_
    intro a ha
    cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])
  | memory h =>
    rename_i c c'
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', es'⟩ := c'
    refine MatchStore.of_same fun t hst => transport_redex hst (.memory h)
      (MemoryStep.lastRedex_eq h) ?_
    intro a ha
    cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])
  | reference h =>
    rename_i c c'
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', es'⟩ := c'
    refine MatchStore.of_same fun t hst => transport_redex hst (.reference h)
      (RefStep.lastRedex_eq h) ?_
    intro a ha
    cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])
  | aggregate h =>
    rename_i c c'
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', es'⟩ := c'
    refine MatchStore.of_same fun t hst => transport_redex hst (.aggregate h)
      (AggregateStep.lastRedex_eq h) ?_
    intro a ha
    cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])
  | ctxtInstrs _ hne ih =>
    intro t hst
    obtain ⟨t', es'', h1, h2, h3⟩ := ih t hst
    exact ⟨t', _, .ctxtInstrs h1 hne, h2, .append (.append (.refl _) h3) (.refl _)⟩
  | ctxtLabel _ ih =>
    intro t hst
    obtain ⟨t', es'', h1, h2, h3⟩ := ih t hst
    exact ⟨t', _, .ctxtLabel h1, h2, .cons (.label _ (InstrsRel.refl _) h3) .nil⟩
  | ctxtHandler _ ih =>
    intro t hst
    obtain ⟨t', es'', h1, h2, h3⟩ := ih t hst
    exact ⟨t', _, .ctxtHandler h1, h2, .cons (.handler _ _ h3) .nil⟩
  | ctxtFrame _ ih =>
    intro t hst
    obtain ⟨t', es'', h1, h2, h3⟩ := ih t hst
    exact ⟨t', _, .ctxtFrame h1, h2, .cons (.frame _ _ h3) .nil⟩
  | block hbt hm => exact MatchStore.of_same fun t hst => ⟨t, .block hbt hm, hst⟩
  | loop hbt hm => exact MatchStore.of_same fun t hst => ⟨t, .loop hbt hm, hst⟩
  | ifTrue hc => exact MatchStore.of_same fun t hst => ⟨t, .ifTrue hc, hst⟩
  | ifFalse => exact MatchStore.of_same fun t hst => ⟨t, .ifFalse, hst⟩
  | labelVals => exact MatchStore.of_same fun t hst => ⟨t, .labelVals, hst⟩
  | brLabelZero hl hn => exact MatchStore.of_same fun t hst => ⟨t, .brLabelZero hl hn, hst⟩
  | brLabelSucc hl => exact MatchStore.of_same fun t hst => ⟨t, .brLabelSucc hl, hst⟩
  | brHandler => exact MatchStore.of_same fun t hst => ⟨t, .brHandler, hst⟩
  | brIfTrue hc => exact MatchStore.of_same fun t hst => ⟨t, .brIfTrue hc, hst⟩
  | brIfFalse => exact MatchStore.of_same fun t hst => ⟨t, .brIfFalse, hst⟩
  | brTableLt hi => exact MatchStore.of_same fun t hst => ⟨t, .brTableLt hi, hst⟩
  | brTableGe hi => exact MatchStore.of_same fun t hst => ⟨t, .brTableGe hi, hst⟩
  | brOnNullNull => exact MatchStore.of_same fun t hst => ⟨t, .brOnNullNull, hst⟩
  | brOnNullAddr hv => exact MatchStore.of_same fun t hst => ⟨t, .brOnNullAddr hv, hst⟩
  | brOnNonNullNull => exact MatchStore.of_same fun t hst => ⟨t, .brOnNonNullNull, hst⟩
  | brOnNonNullAddr hv => exact MatchStore.of_same fun t hst => ⟨t, .brOnNonNullAddr hv, hst⟩
  | brOnCastSucceed h =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.brOnCastSucceed h)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFail h =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.brOnCastFail h)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFailSucceed h =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.brOnCastFailSucceed h)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFailFail h =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.brOnCastFailFail h)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | call hx hf =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.call hx hf)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | callRefNull hc => exact MatchStore.of_same fun t hst => ⟨t, .callRefNull hc, hst⟩
  | callRefFunc hc hf he hn hcode =>
    intro t hst
    obtain ⟨gi, hg, hfg⟩ := forall₂_getElem? hst.funcs hf
    obtain ⟨hty, hmod, hcr⟩ := hF _ _ hfg
    rw [hcode] at hcr
    cases hgc : gi.code with
    | host h' => rw [hgc] at hcr; simp [FuncCodeRel] at hcr
    | wasm g =>
      rw [hgc] at hcr
      obtain ⟨-, hloc, hbody⟩ := hcr
      refine ⟨t, _, .callRefFunc hc hg (by rw [← hty]; exact he) hn hgc, hst, ?_⟩
      dsimp only
      rw [hmod, hloc]
      exact .cons (.frame _ _ (.cons (.label _ .nil (.src hbody)) .nil)) .nil
  | callRefHost hc hf he hn hcode hh =>
    intro t hst
    obtain ⟨gi, hg, hfg⟩ := forall₂_getElem? hst.funcs hf
    obtain ⟨hty, -, hcr⟩ := hF _ _ hfg
    rw [hcode] at hcr
    cases hgc : gi.code with
    | wasm g => rw [hgc] at hcr; simp [FuncCodeRel] at hcr
    | host h' =>
      rw [hgc] at hcr
      simp only [FuncCodeRel] at hcr
      subst hcr
      obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst hh
      cases out' with
      | diverged => simp [OutcomeRel] at hrel
      | returned t' r' =>
        simp only [OutcomeRel, Host.Outcome.Sim_returned_returned, id] at hrel
        obtain ⟨hs', rfl⟩ := hrel
        exact ⟨t', _, .callRefHost hc hg (by rw [← hty]; exact he) hn hgc hout', hs', AdminsRel.refl _⟩
  | callRefHostDiv hc hf he hn hcode hh =>
    intro t hst
    obtain ⟨gi, hg, hfg⟩ := forall₂_getElem? hst.funcs hf
    obtain ⟨hty, -, hcr⟩ := hF _ _ hfg
    rw [hcode] at hcr
    cases hgc : gi.code with
    | wasm g => rw [hgc] at hcr; simp [FuncCodeRel] at hcr
    | host h' =>
      rw [hgc] at hcr
      simp only [FuncCodeRel] at hcr
      subst hcr
      obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst hh
      cases out' with
      | diverged =>
        exact ⟨t, _, .callRefHostDiv hc hg (by rw [← hty]; exact he) hn hgc hout', hst, AdminsRel.refl _⟩
      | returned t' r' => simp [OutcomeRel] at hrel
  | returnCall hx hf =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.returnCall hx hf)
      (by simp [lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | returnCallRefLabel hc => exact MatchStore.of_same fun t hst => ⟨t, .returnCallRefLabel hc, hst⟩
  | returnCallRefHandler hc =>
    exact MatchStore.of_same fun t hst => ⟨t, .returnCallRefHandler hc, hst⟩
  | returnCallRefFrameNull hc =>
    exact MatchStore.of_same fun t hst => ⟨t, .returnCallRefFrameNull hc, hst⟩
  | returnCallRefFrameAddr hc hf he hn =>
    refine MatchStore.of_same fun t hst => ?_
    obtain ⟨gi, hg, hfg⟩ := forall₂_getElem? hst.funcs hf
    obtain ⟨hty, -, -⟩ := hF _ _ hfg
    exact ⟨t, .returnCallRefFrameAddr hc hg (by rw [← hty]; exact he) hn, hst⟩
  | callIndirect => exact MatchStore.of_same fun t hst => ⟨t, .callIndirect, hst⟩
  | returnCallIndirect => exact MatchStore.of_same fun t hst => ⟨t, .returnCallIndirect, hst⟩
  | frameVals hn => exact MatchStore.of_same fun t hst => ⟨t, .frameVals hn, hst⟩
  | returnFrame hn => exact MatchStore.of_same fun t hst => ⟨t, .returnFrame hn, hst⟩
  | returnLabel => exact MatchStore.of_same fun t hst => ⟨t, .returnLabel, hst⟩
  | returnHandler => exact MatchStore.of_same fun t hst => ⟨t, .returnHandler, hst⟩
  | throw ht he hn =>
    exact MatchStore.of_same fun t hst => transport_redex hst (.throw ht he hn)
      (by rw [lastRedex_vals_append _ (List.cons_ne_nil _ _)]; simp [lastRedex, Admin.val?])
      (by simp [Admin.IsCtx, Admin.IsCallRef])
  | throwRefNull => exact MatchStore.of_same fun t hst => ⟨t, .throwRefNull, hst⟩
  | throwRefInstrs hne => exact MatchStore.of_same fun t hst => ⟨t, .throwRefInstrs hne, hst⟩
  | throwRefLabel => exact MatchStore.of_same fun t hst => ⟨t, .throwRefLabel, hst⟩
  | throwRefFrame => exact MatchStore.of_same fun t hst => ⟨t, .throwRefFrame, hst⟩
  | throwRefHandlerEmpty => exact MatchStore.of_same fun t hst => ⟨t, .throwRefHandlerEmpty, hst⟩
  | throwRefHandlerCatch he ht =>
    exact MatchStore.of_same fun t hst =>
      ⟨t, .throwRefHandlerCatch (by rw [← hst.exns_eq]; exact he) ht, hst⟩
  | throwRefHandlerCatchRef he ht =>
    exact MatchStore.of_same fun t hst =>
      ⟨t, .throwRefHandlerCatchRef (by rw [← hst.exns_eq]; exact he) ht, hst⟩
  | throwRefHandlerCatchAll =>
    exact MatchStore.of_same fun t hst => ⟨t, .throwRefHandlerCatchAll, hst⟩
  | throwRefHandlerCatchAllRef =>
    exact MatchStore.of_same fun t hst => ⟨t, .throwRefHandlerCatchAllRef, hst⟩
  | throwRefHandlerNext h =>
    exact MatchStore.of_same fun t hst =>
      ⟨t, .throwRefHandlerNext ((catchMatches_congr hst.exns_eq _ _ _).not.mp h), hst⟩
  | tryTable hbt hm => exact MatchStore.of_same fun t hst => ⟨t, .tryTable hbt hm, hst⟩
  | handlerVals => exact MatchStore.of_same fun t hst => ⟨t, .handlerVals, hst⟩
  | trapInstrs hne => exact MatchStore.of_same fun t hst => ⟨t, .trapInstrs hne, hst⟩
  | trapLabel => exact MatchStore.of_same fun t hst => ⟨t, .trapLabel, hst⟩
  | trapHandler => exact MatchStore.of_same fun t hst => ⟨t, .trapHandler, hst⟩
  | trapFrame => exact MatchStore.of_same fun t hst => ⟨t, .trapFrame, hst⟩

end Silmaril.Wasm.Execution.Core.Sim
