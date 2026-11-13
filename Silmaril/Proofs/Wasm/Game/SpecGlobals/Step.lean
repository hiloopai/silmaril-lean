module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Leaf

/-!
# Host-free Core steps under global-address embeddings

`step`: every host-free Core 3.0 step (any profile `P`) of a configuration whose frames name
only globals in `D` is matched, one for one, by the step of the renamed configuration over an
embedded store (`Emb ρ D`); the result again names only globals in `D`. No typing is used.
`steps`, `diverges`: the same for runs and infinite runs.

With `D` everything this transports runs of the once-store into the spec store; with `D` the
range of an embedding `ι` and `ρ` a left inverse of `ι`, it transports runs of the spec store
(whose frames name only the images of `ι`) back.

Source: the case analysis is adapted from silmaril-lean's
`Silmaril/Wasm/Link/GlobalRenameSimulation.lean` (`step`, pinned revision
35a6f60ab146faef38970ec99e7399a0764dee82), with the permutation replaced by an embedding on a
domain; the domain invariant is new.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- The host relation with no host calls. -/
abbrev noHost : HostSemantics H := fun _ _ _ _ => False

/-- The conclusion of the step simulation: the renamed configuration steps to the renamed
result over an embedded store, and the result names only globals in `D`. -/
def Sim (P : Profile) (ρ : Nat → Nat) (D : Nat → Prop) (t : Store H) (c c' : Config H) : Prop :=
  ∃ t', Step P noHost (config ρ t c) (config ρ t' c') ∧ Emb ρ D c'.store t' ∧ CfgDom D c'

theorem call_ref_fixed {ρ : Nat → Nat} {a : Admin} (call : a.IsCallRef) : admin ρ a = a := by
  cases a <;> first | rfl | cases call

theorem return_call_ref_fixed {ρ : Nat → Nat} {a : Admin} (call : a.IsReturnCallRef) :
    admin ρ a = a := by
  cases a <;> first | rfl | cases call

theorem return_call_ref_dom {D : Nat → Prop} {a : Admin} (call : a.IsReturnCallRef) :
    AdminDom D a := by
  cases a with
  | label => exact call.elim
  | handler => exact call.elim
  | frame => exact call.elim
  | _ => trivial

theorem ret_to_call_in_fixed (ρ : Nat → Nat) (m : ModuleInst) {a : Admin}
    (call : a.IsReturnCallRef) :
    admin ρ (a.retToCallIn m) = a.retToCallIn (moduleView ρ m) := by
  cases a with
  | plain i =>
    cases i <;> try rfl
    simp only [Admin.retToCallIn, moduleView]
    split <;> rfl
  | returnCallRefType d => rfl
  | _ => cases call

theorem ret_to_call_in_dom (D : Nat → Prop) (m : ModuleInst) {a : Admin}
    (call : a.IsReturnCallRef) : AdminDom D (a.retToCallIn m) := by
  cases a with
  | plain i =>
    cases i <;> try trivial
    simp only [Admin.retToCallIn]
    split <;> trivial
  | returnCallRefType d => trivial
  | _ => cases call

theorem frame_forCall (ρ : Nat → Nat) (m : ModuleInst) (vs : List Val) (ls : List ValType) :
    frame ρ (Frame.forCall m vs ls) = Frame.forCall (moduleView ρ m) vs ls := rfl

theorem parametric {ρ : Nat → Nat} {code out : List Admin}
    (step : ParametricStep code out) : ParametricStep (admins ρ code) (admins ρ out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem numeric {ρ : Nat → Nat} {code out : List Admin}
    (step : NumericStep P code out) : NumericStep P (admins ρ code) (admins ρ out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem vector {ρ : Nat → Nat} {code out : List Admin}
    (step : VectorStep P code out) : VectorStep P (admins ρ code) (admins ρ out) := by
  have original := step
  cases step <;> simpa only [admins, admin, admin_value, constI32] using original

theorem parametric_dom {D : Nat → Prop} {code out : List Admin} (hd : AdminsDom D code)
    (step : ParametricStep code out) : AdminsDom D out := by
  cases step <;> simp_all

theorem numeric_dom (D : Nat → Prop) {code out : List Admin}
    (step : NumericStep P code out) : AdminsDom D out := by
  cases step <;> simp_all [constI32]

theorem vector_dom (D : Nat → Prop) {code out : List Admin}
    (step : VectorStep P code out) : AdminsDom D out := by
  cases step <;> simp_all [constI32]

/-! ## Leaf families -/

theorem sim_variable {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {code out : List Admin} (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, code⟩)
    (h : VariableStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    Sim P ρ D t ⟨s, f, code⟩ ⟨s', f', out⟩ := by
  obtain ⟨t', reduced, emb⟩ := variable_step stores dom.1 h
  obtain ⟨hc, ho, hd⟩ := variable_code (ρ := ρ) (D := D) h
  have hm : ModDom D f'.module := (variable_frame h) ▸ dom.1
  exact ⟨t', by simpa only [config, hc, ho] using Step.variable reduced, emb, hm, hd⟩

theorem sim_reference {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {code out : List Admin} (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, code⟩)
    (h : RefStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    Sim P ρ D t ⟨s, f, code⟩ ⟨s', f', out⟩ := by
  obtain ⟨hs, reduced⟩ := reference_step stores h
  obtain ⟨hc, ho, hd⟩ := reference_code (ρ := ρ) (D := D) h
  have hf : f' = f := reference_frame h
  have emb : Emb ρ D s' t := hs ▸ stores
  exact ⟨t, by simpa only [config, hc, ho] using Step.reference reduced, emb, hf ▸ dom.1, hd⟩

theorem sim_aggregate {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {code out : List Admin} (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, code⟩)
    (h : AggregateStep ⟨s, f, code⟩ ⟨s', f', out⟩) :
    Sim P ρ D t ⟨s, f, code⟩ ⟨s', f', out⟩ := by
  obtain ⟨t', reduced, emb⟩ := aggregate_step stores h
  obtain ⟨hc, ho, hd⟩ := aggregate_code (ρ := ρ) (D := D) h
  have hf : f' = f := aggregate_frame h
  exact ⟨t', by simpa only [config, hc, ho] using Step.aggregate reduced, emb, hf ▸ dom.1, hd⟩

theorem sim_table {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {code out : List Admin} (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, code⟩)
    (h : TableStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    Sim P ρ D t ⟨s, f, code⟩ ⟨s', f', out⟩ := by
  obtain ⟨t', reduced, emb⟩ := table_step stores h
  obtain ⟨hc, ho, hd⟩ := table_code (ρ := ρ) (D := D) h
  have hf : f' = f := table_frame h
  exact ⟨t', by simpa only [config, hc, ho] using Step.table reduced, emb, hf ▸ dom.1, hd⟩

theorem sim_memory {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {code out : List Admin} (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, code⟩)
    (h : MemoryStep P ⟨s, f, code⟩ ⟨s', f', out⟩) :
    Sim P ρ D t ⟨s, f, code⟩ ⟨s', f', out⟩ := by
  obtain ⟨t', reduced, emb⟩ := memory_step stores h
  obtain ⟨hc, ho, hd⟩ := memory_code (ρ := ρ) (D := D) h
  have hf : f' = f := memory_frame h
  exact ⟨t', by simpa only [config, hc, ho] using Step.memory reduced, emb, hf ▸ dom.1, hd⟩

/-! ## Contexts -/

theorem sim_ctxtInstrs {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {vs : List Val} {is is' rest : List Admin} (hne : vs ≠ [] ∨ rest ≠ [])
    (dom : CfgDom D ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → Sim P ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Sim P ρ D t ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have hd : AdminsDom D is ∧ AdminsDom D rest := by
    have h := dom.2
    simp only [adminsDom_append, adminsDom_vals, true_and] at h
    exact h
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih ⟨dom.1, hd.1⟩
  refine ⟨t', ?_, emb, hm, ?_⟩
  · simpa only [config, admins_append, admins_vals] using
      Step.ctxtInstrs reduced (hne.imp_right admins_ne_nil)
  · simp only [adminsDom_append, adminsDom_vals, true_and]
    exact ⟨hd', hd.2⟩

theorem sim_ctxtLabel {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {n : Nat} {cont : List Instr} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.label n cont is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → Sim P ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Sim P ρ D t ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtLabel reduced, emb, hm,
    hd', trivial⟩

theorem sim_ctxtHandler {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f f' : Frame}
    {n : Nat} {cs : List Catch} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.handler n cs is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → Sim P ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Sim P ρ D t ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtHandler reduced, emb, hm,
    hd', trivial⟩

theorem sim_ctxtFrame {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H} {f fi fi' : Frame}
    {n : Nat} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.frame n fi is]⟩)
    (ih : CfgDom D ⟨s, fi, is⟩ → Sim P ρ D t ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    Sim P ρ D t ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih dom.2.1
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtFrame reduced, emb, dom.1,
    ⟨hm, hd'⟩, trivial⟩

/-! ## Calls -/

theorem sim_callRefFunc {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} {f : Frame} {c : Admin}
    {vs : List Val} {a : Nat} {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
    (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
    Sim P ρ D t ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  have hm : ModDom D fi.module := stores.fdom fi (List.mem_of_getElem? hf)
  have reduced : Step P noHost ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩
      ⟨t, frame ρ f, [.frame rs.length (Frame.forCall (function ρ fi).module vs code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
    Step.callRefFunc hc (stores.func_lookup hf) he hn hcode
  refine ⟨t, ?_, stores, dom.1, ?_⟩
  · simpa only [config, admins_append, admins_vals, admins, admin, call_ref_fixed hc,
      admins_expression, frame_forCall, function] using reduced
  · simp only [adminsDom_cons, adminDom_frame, adminDom_label, adminsDom_expression,
      adminsDom_nil, and_true]
    exact hm

theorem sim_returnCallRefFrameAddr {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H}
    {f fi : Frame} {k : Nat} {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin}
    {fn : FuncInst H} {ps rs : Ty (.list .val)} (stores : Emb ρ D s t)
    (dom : CfgDom D ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩)
    (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
    (hn : vs.length = ps.length) :
    Sim P ρ D t ⟨s, f, [.frame k fi (vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩ := by
  have reduced := Step.returnCallRefFrameAddr (P := P) (host := noHost) (s := t)
    (f := frame ρ f) (fi := frame ρ fi) (k := k) (vs' := vs') (rest := admins ρ rest) hc
    (stores.func_lookup hf) he hn
  refine ⟨t, ?_, stores, dom.1, ?_⟩
  · simpa only [config, admins_append, admins_vals, admins, admin, return_call_ref_fixed hc,
      ret_to_call_in_fixed ρ _ hc, frame] using reduced
  · simp only [adminsDom_append, adminsDom_vals, adminsDom_cons, adminDom_ref, adminsDom_nil,
      true_and, and_true]
    exact ret_to_call_in_dom D fi.module hc

/-! ## The step simulation -/

/-- **Host-free steps commute with global-address embeddings**, for every profile. -/
theorem step {c c' : Config H} (h : Step P noHost c c') :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      Sim P ρ D t c c' := by
  induction h
  all_goals intro ρ D t stores dom
  case parametric hp =>
    exact ⟨t, by simpa only [config] using Step.parametric (parametric (ρ := ρ) hp), stores,
      dom.1, parametric_dom dom.2 hp⟩
  case numeric hp =>
    exact ⟨t, by simpa only [config] using Step.numeric (numeric (ρ := ρ) hp), stores,
      dom.1, numeric_dom D hp⟩
  case vector hp =>
    exact ⟨t, by simpa only [config] using Step.vector (vector (ρ := ρ) hp), stores,
      dom.1, vector_dom D hp⟩
  case «variable» c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact sim_variable stores dom hv
  case reference c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact sim_reference stores dom hv
  case aggregate c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact sim_aggregate stores dom hv
  case table c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact sim_table stores dom hv
  case memory c c' hv =>
    obtain ⟨s, f, code⟩ := c
    obtain ⟨s', f', out⟩ := c'
    exact sim_memory stores dom hv
  case ctxtInstrs hne ih => exact sim_ctxtInstrs hne dom (fun hd => ih stores hd)
  case ctxtLabel ih => exact sim_ctxtLabel dom (fun hd => ih stores hd)
  case ctxtHandler ih => exact sim_ctxtHandler dom (fun hd => ih stores hd)
  case ctxtFrame ih => exact sim_ctxtFrame dom (fun hd => ih stores hd)
  case callRefHost impossible => exact impossible.elim
  case callRefHostDiv impossible => exact impossible.elim
  case callRefFunc hc hf he hn hcode => exact sim_callRefFunc stores dom hc hf he hn hcode
  case returnCallRefFrameAddr hc hf he hn => exact sim_returnCallRefFrameAddr stores dom hc hf he hn
  case throw s f x vs ta ti ts ht he hn =>
    have exns : s.exns = t.exns := stores.exns
    refine ⟨_, ?_, stores.addExn _, dom.1, by simp⟩
    simpa only [config, throwing, exns, admins_append, admins_vals, admins, admin] using
      Step.throw (P := P) (host := noHost) (s := t) (f := frame ρ f)
        (by simpa only [Store.tag?, frame, moduleView, ← stores.tags] using ht) he hn
  all_goals unfold Sim
  all_goals simp only [config, admins_append, admins_vals, admins_expression, admins, admin,
    admin_value, constI32]
  case block hbt hm => exact ⟨t, .block hbt hm, stores, dom.1, by simp⟩
  case loop hbt hm => exact ⟨t, .loop hbt hm, stores, dom.1, by simp⟩
  case ifTrue hc => exact ⟨t, .ifTrue hc, stores, dom.1, by simp⟩
  case ifFalse => exact ⟨t, .ifFalse, stores, dom.1, by simp⟩
  case labelVals => exact ⟨t, .labelVals, stores, dom.1, by simp⟩
  case brLabelZero hl hn => exact ⟨t, .brLabelZero hl hn, stores, dom.1, by simp⟩
  case brLabelSucc hl => exact ⟨t, .brLabelSucc hl, stores, dom.1, by simp⟩
  case brHandler => exact ⟨t, .brHandler, stores, dom.1, by simp⟩
  case brIfTrue hc => exact ⟨t, .brIfTrue hc, stores, dom.1, by simp⟩
  case brIfFalse => exact ⟨t, .brIfFalse, stores, dom.1, by simp⟩
  case brTableLt hi => exact ⟨t, .brTableLt hi, stores, dom.1, by simp⟩
  case brTableGe hi => exact ⟨t, .brTableGe hi, stores, dom.1, by simp⟩
  case brOnNullNull => exact ⟨t, .brOnNullNull, stores, dom.1, by simp⟩
  case brOnNullAddr hv => exact ⟨t, .brOnNullAddr hv, stores, dom.1, by simp⟩
  case brOnNonNullNull => exact ⟨t, .brOnNonNullNull, stores, dom.1, by simp⟩
  case brOnNonNullAddr hv => exact ⟨t, .brOnNonNullAddr hv, stores, dom.1, by simp⟩
  case brOnCastSucceed hr =>
    exact ⟨t, .brOnCastSucceed (stores.refOk hr), stores, dom.1, by simp⟩
  case brOnCastFail hr =>
    exact ⟨t, .brOnCastFail (fun h' => hr (stores.refOk_back h')), stores, dom.1, by simp⟩
  case brOnCastFailSucceed hr =>
    exact ⟨t, .brOnCastFailSucceed (stores.refOk hr), stores, dom.1, by simp⟩
  case brOnCastFailFail hr =>
    exact ⟨t, .brOnCastFailFail (fun h' => hr (stores.refOk_back h')), stores, dom.1, by simp⟩
  case call s f x a fi hx hf =>
    refine ⟨t, ?_, stores, dom.1, by simp⟩
    simpa only [function] using (Step.call (P := P) (host := noHost) (s := t) (f := frame ρ f)
      (fi := function ρ fi) hx (stores.func_lookup hf))
  case callRefNull c hc =>
    refine ⟨t, ?_, stores, dom.1, by simp⟩
    simpa only [call_ref_fixed hc] using
      (Step.callRefNull (P := P) (host := noHost) (s := t) (f := frame ρ _) hc)
  case returnCall s f x a fi hx hf =>
    refine ⟨t, ?_, stores, dom.1, by simp⟩
    simpa only [function] using (Step.returnCall (P := P) (host := noHost) (s := t)
      (f := frame ρ f) (fi := function ρ fi) hx (stores.func_lookup hf))
  case returnCallRefLabel hc =>
    exact ⟨t, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefLabel hc, stores,
      dom.1, by simp [return_call_ref_dom hc]⟩
  case returnCallRefHandler hc =>
    exact ⟨t, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefHandler hc,
      stores, dom.1, by simp [return_call_ref_dom hc]⟩
  case returnCallRefFrameNull hc =>
    exact ⟨t, by simpa only [return_call_ref_fixed hc] using Step.returnCallRefFrameNull hc,
      stores, dom.1, by simp⟩
  case callIndirect => exact ⟨t, .callIndirect, stores, dom.1, by simp⟩
  case returnCallIndirect => exact ⟨t, .returnCallIndirect, stores, dom.1, by simp⟩
  case frameVals hn => exact ⟨t, .frameVals hn, stores, dom.1, by simp⟩
  case returnFrame hn => exact ⟨t, .returnFrame hn, stores, dom.1, by simp⟩
  case returnLabel => exact ⟨t, .returnLabel, stores, dom.1, by simp⟩
  case returnHandler => exact ⟨t, .returnHandler, stores, dom.1, by simp⟩
  case throwRefNull => exact ⟨t, .throwRefNull, stores, dom.1, by simp⟩
  case throwRefInstrs hne =>
    exact ⟨t, .throwRefInstrs (hne.imp_right admins_ne_nil), stores, dom.1, by simp⟩
  case throwRefLabel => exact ⟨t, .throwRefLabel, stores, dom.1, by simp⟩
  case throwRefFrame => exact ⟨t, .throwRefFrame, stores, dom.1, by simp⟩
  case throwRefHandlerEmpty => exact ⟨t, .throwRefHandlerEmpty, stores, dom.1, by simp⟩
  case throwRefHandlerCatch he ht =>
    exact ⟨t, .throwRefHandlerCatch (stores.exns ▸ he) ht, stores, dom.1, by simp⟩
  case throwRefHandlerCatchRef he ht =>
    exact ⟨t, .throwRefHandlerCatchRef (stores.exns ▸ he) ht, stores, dom.1, by simp⟩
  case throwRefHandlerCatchAll => exact ⟨t, .throwRefHandlerCatchAll, stores, dom.1, by simp⟩
  case throwRefHandlerCatchAllRef =>
    exact ⟨t, .throwRefHandlerCatchAllRef, stores, dom.1, by simp⟩
  case throwRefHandlerNext hm =>
    exact ⟨t, .throwRefHandlerNext (by simpa only [CatchMatches, frame, moduleView,
      ← stores.exns] using hm), stores, dom.1, by simp⟩
  case tryTable hbt hm => exact ⟨t, .tryTable hbt hm, stores, dom.1, by simp⟩
  case handlerVals => exact ⟨t, .handlerVals, stores, dom.1, by simp⟩
  case trapInstrs hne =>
    exact ⟨t, .trapInstrs (hne.imp_right admins_ne_nil), stores, dom.1, by simp⟩
  case trapLabel => exact ⟨t, .trapLabel, stores, dom.1, by simp⟩
  case trapHandler => exact ⟨t, .trapHandler, stores, dom.1, by simp⟩
  case trapFrame => exact ⟨t, .trapFrame, stores, dom.1, by simp⟩

end Silmaril.Proofs.Wasm.Game.SpecGlobals
