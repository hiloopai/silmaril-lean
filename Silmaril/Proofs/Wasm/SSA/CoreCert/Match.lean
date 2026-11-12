module

public import Silmaril.Proofs.Wasm.SSA.CoreCert.Ctx
public import Silmaril.Wasm.Execution.Core.Sim.TypedProgress
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-!
# Stores with equivalent strict leaf functions: one step (proofs)

`FRel P`: two function instances are equal, or form a `LeafPair`: the same type and module
instance, Wasm code of strict leaf functions (`strictFunc`) of a type without reference
parameters, whose callee frames have the same canonical Core behaviours (`LBeh`) on all
arguments typed at the parameter types. Stores are related by silmaril's `Sim.StoreRel (FRel P)`.

`step_match`: on a typed configuration (`Sim.ContextTyped`, closed host), a Core step from store
`s` is matched by one step of the same code from any related store `t`; the resulting codes are
equal, or equal up to one pair of strict callee frames in context (`CodeR`) whose behaviours are
included (`InFlight`). The second case is a call of a `LeafPair` function: its arguments are of
the parameter types, extracted from the typing of the call (`args_typed`, silmaril's
`PC.callRef_front`). New proofs; the step-by-step skeleton follows silmaril's
`Sim.Step.match_storeRel`.
-/

namespace Silmaril.Proofs.Wasm.SSA.CoreCert

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SSA
open Silmaril.Wasm.SSA.CoreCert
open Silmaril.Wasm.Binaryen (closedHost)

variable {H : Type} {P : Numerics.Profile}

/-! ## Definitions -/

/-- A pair of strict frames whose behaviours are included. -/
def InFlight (P : Numerics.Profile) (X Y : Admin) : Prop :=
  LFrame X ∧ LFrame Y ∧ LBeh P X ⊆ LBeh P Y

/-- Equal codes, or equal codes up to one `InFlight` pair in context. -/
def CodeR (P : Numerics.Profile) (l l' : List Admin) : Prop :=
  l = l' ∨ ∃ (E : Ctx) (X Y : Admin), l = E.plug [X] ∧ l' = E.plug [Y] ∧ InFlight P X Y

/-! ## Basic facts -/

theorem InFlight.trans_left {X X' Y : Admin} (h : InFlight P X Y) (hX' : LFrame X')
    (hsub : LBeh P X' ⊆ LBeh P X) : InFlight P X' Y :=
  ⟨hX', h.2.1, hsub.trans h.2.2⟩

theorem CodeR.seq {l l' : List Admin} (h : CodeR P l l') (vs : List Val) (rest : List Admin) :
    CodeR P (vals vs ++ l ++ rest) (vals vs ++ l' ++ rest) := by
  rcases h with rfl | ⟨E, X, Y, rfl, rfl, hf⟩
  · exact .inl rfl
  · exact .inr ⟨E.seq vs rest, X, Y, (E.plug_seq _ _ _).symm, (E.plug_seq _ _ _).symm, hf⟩

theorem CodeR.label {l l' : List Admin} (h : CodeR P l l') (n : Nat) (cont : List Instr) :
    CodeR P [.label n cont l] [.label n cont l'] := by
  rcases h with rfl | ⟨E, X, Y, rfl, rfl, hf⟩
  · exact .inl rfl
  · exact .inr ⟨.label [] n cont E [], X, Y, by simp [Ctx.plug, vals], by simp [Ctx.plug, vals],
      hf⟩

theorem CodeR.frame {l l' : List Admin} (h : CodeR P l l') (n : Nat) (fr : Frame) :
    CodeR P [.frame n fr l] [.frame n fr l'] := by
  rcases h with rfl | ⟨E, X, Y, rfl, rfl, hf⟩
  · exact .inl rfl
  · exact .inr ⟨.frame [] n fr E [], X, Y, by simp [Ctx.plug, vals], by simp [Ctx.plug, vals],
      hf⟩

theorem CodeR.handler {l l' : List Admin} (h : CodeR P l l') (n : Nat) (cs : List Catch) :
    CodeR P [.handler n cs l] [.handler n cs l'] := by
  rcases h with rfl | ⟨E, X, Y, rfl, rfl, hf⟩
  · exact .inl rfl
  · exact .inr ⟨.handler [] n cs E [], X, Y, by simp [Ctx.plug, vals], by simp [Ctx.plug, vals],
      hf⟩

/-! ## Callee frames of strict leaf functions -/

theorem intLocals_cons {t : ValType} {ts : List ValType} (h : intLocals (t :: ts) = true) :
    (∃ it, t = .num (.int it)) ∧ intLocals ts = true := by
  simp only [intLocals, List.all_cons, Bool.and_eq_true] at h
  refine ⟨?_, h.2⟩
  rcases t with ⟨it | ft⟩ | vt | rt
  · exact ⟨it, rfl⟩
  all_goals simp at h

theorem forCall_withMod {mi mi' : ModuleInst} {vs : List Val} {ls : List ValType}
    (h : intLocals ls = true) : withMod (Frame.forCall mi vs ls) mi' = Frame.forCall mi' vs ls := by
  simp only [withMod, Frame.forCall, Frame.mk.injEq, List.append_cancel_left_eq, and_true]
  induction ls with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨⟨it, rfl⟩, hts⟩ := intLocals_cons h
    simp only [List.map_cons, ih hts]
    rfl

theorem frameS_forCall {mi : ModuleInst} {vs : List Val} {ls : List ValType}
    (hvs : ∀ v ∈ vs, ValS v) (hls : intLocals ls = true) : FrameS (Frame.forCall mi vs ls) := by
  intro v hv
  simp only [Frame.forCall, List.mem_append, List.mem_map] at hv
  rcases hv with ⟨w, hw, he⟩ | ⟨t, ht, he⟩
  · exact Option.some.inj he ▸ hvs w hw
  · have hint := List.all_eq_true.mp hls t ht
    rcases t with ⟨t | t⟩ | t | t
    · cases t
      · exact (Option.some.inj he) ▸ trivial
      · exact (Option.some.inj he) ▸ trivial
    all_goals simp at hint

theorem strictFunc_inv {fn : Func} (h : strictFunc fn = true) :
    strictInstrs fn.body = true ∧ intLocals fn.locals = true := by
  simpa only [strictFunc, Bool.and_eq_true] using h

theorem entry_lFrame {n : Nat} {mi : ModuleInst} {vs : List Val} {fn : Func}
    (hs : strictFunc fn = true) (hvs : ∀ v ∈ vs, ValS v) : LFrame (entry n mi vs fn) :=
  ⟨_, _, _, rfl, ⟨⟨rfl, by simpa using (strictFunc_inv hs).1⟩, trivial⟩,
    frameS_forCall hvs (strictFunc_inv hs).2⟩

theorem lBeh_entry {n : Nat} {mi : ModuleInst} {vs : List Val} {fn : Func}
    (hs : strictFunc fn = true) : LBeh P (entry n mi vs fn) = LBeh P (entry n {} vs fn) := by
  have h₁ : swapA {} (entry n mi vs fn) = swapA {} (entry n {} vs fn) := by
    simp only [entry, swapA, forCall_withMod (strictFunc_inv hs).2]
  simp only [LBeh, canon, h₁]

/-! ## The arguments of a typed call -/

/-- **The arguments of a typed `call_ref`** have the callee's parameter types. -/
theorem args_typed {s : Store H} {f : Frame} {pre vs : List Val} {a : Nat} {c : Admin}
    {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)}
    (ht : Sim.ContextTyped (⟨s, f, vals pre ++ (vals vs ++ [.ref (.func a), c])⟩ : Config H))
    (hcr : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) : List.Forall₂ (ValOk s) vs ps.toList := by
  obtain ⟨C, ts, xs, hs, hC, hc, hcode⟩ := ht.fragment_ctx
  obtain ⟨_, xs₁, _, hp, htl, _⟩ :=
    AdminsOk.split hcode hC (vals pre) (vals vs ++ [.ref (.func a), c]) rfl (by simp)
  have hC' := hC.initLocals xs₁
  have hc' := hc.initLocals hp.vals_inits
  obtain ⟨-, -, -, -, -, -, -, -, hargs, -⟩ :=
    PC.callRef_front hs ⟨hs.structsClosed, hs.arraysClosed⟩ hc' hC' hcr
      (wireCallRef_hcd hC' hcr htl) hf he hn htl
  exact hargs

/-! ## One step -/

/-- The conclusion of `step_match` for a step `c ~> c'`. -/
def Matched (P : Numerics.Profile) (c c' : Config H) : Prop :=
  ∀ pre : List Val, Sim.ContextTyped (⟨c.store, c.frame, vals pre ++ c.code⟩ : Config H) →
    ∀ t, SRel P c.store t → ∃ (t' : Store H) (es : List Admin),
      Step P closedHost ⟨t, c.frame, c.code⟩ ⟨t', c'.frame, es⟩ ∧ SRel P c'.store t' ∧
        CodeR P c'.code es

theorem Matched.of_same {c c' : Config H}
    (h : ∀ t, SRel P c.store t → ∃ t', Step P closedHost ⟨t, c.frame, c.code⟩ ⟨t', c'.frame, c'.code⟩ ∧
      SRel P c'.store t') : Matched P c c' := by
  intro _ _ t hst
  obtain ⟨t', h1, h2⟩ := h t hst
  exact ⟨t', _, h1, h2, .inl rfl⟩

/-- The callee of a `LeafPair` call, matched. -/
theorem callRefFunc_match {s t : Store H} {f : Frame} {pre : List Val} {c : Admin} {vs : List Val}
    {a : Nat} {fi : FuncInst H} {ps rs : Validation.Ty (.list .val)} {code : Func}
    (ht : Sim.ContextTyped (⟨s, f, vals pre ++ (vals vs ++ [.ref (.func a), c])⟩ : Config H))
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Validation.Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) (hst : SRel P s t) :
    ∃ (t' : Store H) (es : List Admin),
      Step P closedHost ⟨t, f, vals vs ++ [.ref (.func a), c]⟩ ⟨t', f, es⟩ ∧ SRel P s t' ∧
        CodeR P [entry rs.length fi.module vs code] es := by
  obtain ⟨gi, hg, hfg⟩ := Sim.forall₂_getElem? hst.funcs hf
  rcases hfg with rfl | ⟨hty, hmod, hnr, fn, fn', h₁, h₂, hs₁, hs₂, heq⟩
  · exact ⟨t, _, .callRefFunc hc hg he hn hcode, hst, .inl rfl⟩
  · rw [hcode] at h₁
    cases h₁
    have hargs := args_typed ht hc hf he hn
    have hvs := hnr ps rs he s vs hargs
    refine ⟨t, [entry rs.length gi.module vs fn'], .callRefFunc hc hg (hty ▸ he) hn h₂, hst,
      .inr ⟨.hole [] [], entry rs.length fi.module vs code, entry rs.length gi.module vs fn',
        by simp [Ctx.plug, vals], by simp [Ctx.plug, vals], entry_lFrame hs₁ hvs, entry_lFrame hs₂ hvs, ?_⟩⟩
    rw [lBeh_entry hs₁, lBeh_entry hs₂, heq ps rs vs he ⟨H, s, hargs⟩]

set_option linter.unusedSimpArgs false in
theorem matched_variable {c c' : Config H} (h : VariableStep c c') : Matched P c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', es'⟩ := c'
  refine Matched.of_same fun t hst => Sim.transport_redex hst (.variable h) (Sim.VariableStep.lastRedex_eq h) ?_
  intro a ha
  cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])

set_option linter.unusedSimpArgs false in
theorem matched_table {c c' : Config H} (h : TableStep P c c') : Matched P c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', es'⟩ := c'
  refine Matched.of_same fun t hst => Sim.transport_redex hst (.table h) (Sim.TableStep.lastRedex_eq h) ?_
  intro a ha
  cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])

set_option linter.unusedSimpArgs false in
theorem matched_memory {c c' : Config H} (h : MemoryStep P c c') : Matched P c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', es'⟩ := c'
  refine Matched.of_same fun t hst => Sim.transport_redex hst (.memory h) (Sim.MemoryStep.lastRedex_eq h) ?_
  intro a ha
  cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])

set_option linter.unusedSimpArgs false in
theorem matched_reference {c c' : Config H} (h : RefStep c c') : Matched P c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', es'⟩ := c'
  refine Matched.of_same fun t hst => Sim.transport_redex hst (.reference h) (Sim.RefStep.lastRedex_eq h) ?_
  intro a ha
  cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])

set_option linter.unusedSimpArgs false in
theorem matched_aggregate {c c' : Config H} (h : AggregateStep c c') : Matched P c c' := by
  obtain ⟨s, f, code⟩ := c
  obtain ⟨s', f', es'⟩ := c'
  refine Matched.of_same fun t hst => Sim.transport_redex hst (.aggregate h) (Sim.AggregateStep.lastRedex_eq h) ?_
  intro a ha
  cases h <;> simp [constI32] at ha <;> (subst ha; simp [Admin.IsCtx, Admin.IsCallRef])

theorem matched_ctxtInstrs {s s' : Store H} {f f' : Frame} {vs : List Val}
    {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (ih : Matched P ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Matched P ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  intro pre ht t hst
  have e : vals pre ++ (vals vs ++ is ++ rest) = vals (pre ++ vs) ++ is ++ rest := by
    simp [vals]
  have ht₀ : Sim.ContextTyped (⟨s, f, vals (pre ++ vs) ++ is ++ rest⟩ : Config H) := by
    rw [← e]; exact ht
  have ht' : Sim.ContextTyped (⟨s, f, vals (pre ++ vs) ++ is⟩ : Config H) := ht₀.suffix
  obtain ⟨t', es, h1, h2, h3⟩ := ih (pre ++ vs) ht' t hst
  exact ⟨t', _, .ctxtInstrs h1 hne, h2, h3.seq vs rest⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- **One step, matched** on any related store: the same code, or a call of a `LeafPair`
function leading to an `InFlight` pair of callee frames. -/
theorem step_match {c c' : Config H} (h : Step P closedHost c c') : Matched P c c' := by
  induction h with
  | parametric h => exact Matched.of_same fun t hst => ⟨t, .parametric h, hst⟩
  | numeric h => exact Matched.of_same fun t hst => ⟨t, .numeric h, hst⟩
  | vector h => exact Matched.of_same fun t hst => ⟨t, .vector h, hst⟩
  | «variable» h => exact matched_variable h
  | table h => exact matched_table h
  | memory h => exact matched_memory h
  | reference h => exact matched_reference h
  | aggregate h => exact matched_aggregate h
  | ctxtInstrs _ hne ih => exact matched_ctxtInstrs hne ih
  | @ctxtLabel s s' f f' n cont is is' _ ih =>
    intro pre ht t hst
    have ht₀ : Sim.ContextTyped (⟨s, f, vals pre ++ [.label n cont is] ++ []⟩ : Config H) := by
      simpa using ht
    have ht' : Sim.ContextTyped (⟨s, f, vals [] ++ is⟩ : Config H) := by
      simpa [vals] using ht₀.label
    obtain ⟨t', es, h1, h2, h3⟩ := ih [] ht' t hst
    exact ⟨t', _, .ctxtLabel h1, h2, h3.label n cont⟩
  | @ctxtHandler s s' f f' n cs is is' _ ih =>
    intro pre ht t hst
    have ht₀ : Sim.ContextTyped (⟨s, f, vals pre ++ [.handler n cs is] ++ []⟩ : Config H) := by
      simpa using ht
    have ht' : Sim.ContextTyped (⟨s, f, vals [] ++ is⟩ : Config H) := by
      simpa [vals] using ht₀.handler
    obtain ⟨t', es, h1, h2, h3⟩ := ih [] ht' t hst
    exact ⟨t', _, .ctxtHandler h1, h2, h3.handler n cs⟩
  | @ctxtFrame s s' f fi fi' n is is' _ ih =>
    intro pre ht t hst
    have ht₀ : Sim.ContextTyped (⟨s, f, vals pre ++ [.frame n fi is] ++ []⟩ : Config H) := by
      simpa using ht
    have ht' : Sim.ContextTyped (⟨s, fi, vals [] ++ is⟩ : Config H) := by
      simpa [vals] using ht₀.frame
    obtain ⟨t', es, h1, h2, h3⟩ := ih [] ht' t hst
    exact ⟨t', _, .ctxtFrame h1, h2, h3.frame n fi'⟩
  | block hbt hm => exact Matched.of_same fun t hst => ⟨t, .block hbt hm, hst⟩
  | loop hbt hm => exact Matched.of_same fun t hst => ⟨t, .loop hbt hm, hst⟩
  | ifTrue hc => exact Matched.of_same fun t hst => ⟨t, .ifTrue hc, hst⟩
  | ifFalse => exact Matched.of_same fun t hst => ⟨t, .ifFalse, hst⟩
  | labelVals => exact Matched.of_same fun t hst => ⟨t, .labelVals, hst⟩
  | brLabelZero hl hn => exact Matched.of_same fun t hst => ⟨t, .brLabelZero hl hn, hst⟩
  | brLabelSucc hl => exact Matched.of_same fun t hst => ⟨t, .brLabelSucc hl, hst⟩
  | brHandler => exact Matched.of_same fun t hst => ⟨t, .brHandler, hst⟩
  | brIfTrue hc => exact Matched.of_same fun t hst => ⟨t, .brIfTrue hc, hst⟩
  | brIfFalse => exact Matched.of_same fun t hst => ⟨t, .brIfFalse, hst⟩
  | brTableLt hi => exact Matched.of_same fun t hst => ⟨t, .brTableLt hi, hst⟩
  | brTableGe hi => exact Matched.of_same fun t hst => ⟨t, .brTableGe hi, hst⟩
  | brOnNullNull => exact Matched.of_same fun t hst => ⟨t, .brOnNullNull, hst⟩
  | brOnNullAddr hv => exact Matched.of_same fun t hst => ⟨t, .brOnNullAddr hv, hst⟩
  | brOnNonNullNull => exact Matched.of_same fun t hst => ⟨t, .brOnNonNullNull, hst⟩
  | brOnNonNullAddr hv => exact Matched.of_same fun t hst => ⟨t, .brOnNonNullAddr hv, hst⟩
  | brOnCastSucceed h =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.brOnCastSucceed h)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFail h =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.brOnCastFail h)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFailSucceed h =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.brOnCastFailSucceed h)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | brOnCastFailFail h =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.brOnCastFailFail h)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | call hx hf =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.call hx hf)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | callRefNull hc => exact Matched.of_same fun t hst => ⟨t, .callRefNull hc, hst⟩
  | callRefFunc hc hf he hn hcode =>
    intro pre ht t hst
    exact callRefFunc_match ht hc hf he hn hcode hst
  | callRefHost _ _ _ _ _ hh => exact (show False from hh).elim
  | callRefHostDiv _ _ _ _ _ hh => exact (show False from hh).elim
  | returnCall hx hf =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.returnCall hx hf)
      (by simp [Sim.lastRedex]; simp [Admin.val?]) (by simp [Admin.IsCtx, Admin.IsCallRef])
  | returnCallRefLabel hc => exact Matched.of_same fun t hst => ⟨t, .returnCallRefLabel hc, hst⟩
  | returnCallRefHandler hc =>
    exact Matched.of_same fun t hst => ⟨t, .returnCallRefHandler hc, hst⟩
  | returnCallRefFrameNull hc =>
    exact Matched.of_same fun t hst => ⟨t, .returnCallRefFrameNull hc, hst⟩
  | returnCallRefFrameAddr hc hf he hn =>
    refine Matched.of_same fun t hst => ?_
    obtain ⟨gi, hg, hfg⟩ := Sim.forall₂_getElem? hst.funcs hf
    exact ⟨t, .returnCallRefFrameAddr hc hg (by rw [← hfg.type_eq]; exact he) hn, hst⟩
  | callIndirect => exact Matched.of_same fun t hst => ⟨t, .callIndirect, hst⟩
  | returnCallIndirect => exact Matched.of_same fun t hst => ⟨t, .returnCallIndirect, hst⟩
  | frameVals hn => exact Matched.of_same fun t hst => ⟨t, .frameVals hn, hst⟩
  | returnFrame hn => exact Matched.of_same fun t hst => ⟨t, .returnFrame hn, hst⟩
  | returnLabel => exact Matched.of_same fun t hst => ⟨t, .returnLabel, hst⟩
  | returnHandler => exact Matched.of_same fun t hst => ⟨t, .returnHandler, hst⟩
  | throw ht he hn =>
    exact Matched.of_same fun t hst => Sim.transport_redex hst (.throw ht he hn)
      (by rw [Sim.lastRedex_vals_append _ (List.cons_ne_nil _ _)]; simp [Sim.lastRedex, Admin.val?])
      (by simp [Admin.IsCtx, Admin.IsCallRef])
  | throwRefNull => exact Matched.of_same fun t hst => ⟨t, .throwRefNull, hst⟩
  | throwRefInstrs hne => exact Matched.of_same fun t hst => ⟨t, .throwRefInstrs hne, hst⟩
  | throwRefLabel => exact Matched.of_same fun t hst => ⟨t, .throwRefLabel, hst⟩
  | throwRefFrame => exact Matched.of_same fun t hst => ⟨t, .throwRefFrame, hst⟩
  | throwRefHandlerEmpty => exact Matched.of_same fun t hst => ⟨t, .throwRefHandlerEmpty, hst⟩
  | throwRefHandlerCatch he ht =>
    exact Matched.of_same fun t hst =>
      ⟨t, .throwRefHandlerCatch (by rw [← hst.exns_eq]; exact he) ht, hst⟩
  | throwRefHandlerCatchRef he ht =>
    exact Matched.of_same fun t hst =>
      ⟨t, .throwRefHandlerCatchRef (by rw [← hst.exns_eq]; exact he) ht, hst⟩
  | throwRefHandlerCatchAll =>
    exact Matched.of_same fun t hst => ⟨t, .throwRefHandlerCatchAll, hst⟩
  | throwRefHandlerCatchAllRef =>
    exact Matched.of_same fun t hst => ⟨t, .throwRefHandlerCatchAllRef, hst⟩
  | throwRefHandlerNext h =>
    exact Matched.of_same fun t hst =>
      ⟨t, .throwRefHandlerNext ((Sim.catchMatches_congr hst.exns_eq _ _ _).not.mp h), hst⟩
  | tryTable hbt hm => exact Matched.of_same fun t hst => ⟨t, .tryTable hbt hm, hst⟩
  | handlerVals => exact Matched.of_same fun t hst => ⟨t, .handlerVals, hst⟩
  | trapInstrs hne => exact Matched.of_same fun t hst => ⟨t, .trapInstrs hne, hst⟩
  | trapLabel => exact Matched.of_same fun t hst => ⟨t, .trapLabel, hst⟩
  | trapHandler => exact Matched.of_same fun t hst => ⟨t, .trapHandler, hst⟩
  | trapFrame => exact Matched.of_same fun t hst => ⟨t, .trapFrame, hst⟩

end Silmaril.Proofs.Wasm.SSA.CoreCert
