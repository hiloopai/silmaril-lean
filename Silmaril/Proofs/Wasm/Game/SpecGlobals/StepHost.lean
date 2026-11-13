module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Step
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Machine

/-!
# Core steps with a host under global-address embeddings

`Silmaril.Proofs.Wasm.Game.SpecGlobals.step` matches every **host-free** Core step across a
global-address embedding `Emb ρ D`. This module extends it to `Step P host` for a host that
commutes with the embeddings:

* `HostEmb host`: whenever `Emb ρ D s t`, a host call returning `s'` on `s` returns the same
  result on `t`, at a store `t'` with `Emb ρ D s' t'`, and a host call diverging on `s` diverges
  on `t`;
* `SimH`: `Sim` (the conclusion of `step`) with the host;
* **`stepH`**: with `HostEmb host`, every `Step P host` step (every profile) is matched one for
  one, and the result again names only globals in `D`. Non-host leaves come from the host-free
  `step` and `Step.of_noHost`; the contexts are re-proved; the two host rules use `HostEmb`.
* `hostEmb_noHost`, `HostEmb.blind`: the empty host commutes with the embeddings, and so does
  every host that keeps globals and functions and does not read them (`Blind`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- A host commutes with the global-address embeddings. -/
structure HostEmb (host : HostSemantics H) : Prop where
  ret : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t s' : Store H} {h : H} {vs : List Val}
    {r : Result}, Emb ρ D s t → host h s vs (.returned s' r) →
      ∃ t', host h t vs (.returned t' r) ∧ Emb ρ D s' t'
  div : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} {h : H} {vs : List Val},
    Emb ρ D s t → host h s vs .diverged → host h t vs .diverged

/-- The conclusion of the step simulation with a host. -/
def SimH (P : Profile) (host : HostSemantics H) (ρ : Nat → Nat) (D : Nat → Prop) (t : Store H)
    (c c' : Config H) : Prop :=
  ∃ t', Step P host (config ρ t c) (config ρ t' c') ∧ Emb ρ D c'.store t' ∧ CfgDom D c'

theorem Sim.lift {host : HostSemantics H} {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}
    {c c' : Config H} (h : Sim P ρ D t c c') : SimH P host ρ D t c c' :=
  let ⟨t', hs, e, d⟩ := h
  ⟨t', Step.of_noHost host hs, e, d⟩

/-- The empty host commutes with the embeddings. -/
theorem hostEmb_noHost : HostEmb (noHost : HostSemantics H) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

/-- A host that keeps the globals and functions of the store and does not read them. -/
structure Blind (host : HostSemantics H) : Prop where
  keeps : ∀ h s vs s' r, host h s vs (.returned s' r) → s'.globals = s.globals ∧ s'.funcs = s.funcs
  ret : ∀ h s vs s' r gs fs, host h s vs (.returned s' r) →
    host h { s with globals := gs, funcs := fs } vs (.returned { s' with globals := gs, funcs := fs } r)
  div : ∀ h s vs gs fs, host h s vs .diverged →
    host h { s with globals := gs, funcs := fs } vs .diverged

theorem Emb.swap_eq {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} (e : Emb ρ D s t) :
    t = { s with globals := t.globals, funcs := t.funcs } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := s
  obtain ⟨_, _, _, _, _, _, _, _, _, _⟩ := t
  simp only [Store.mk.injEq]
  exact ⟨e.tags.symm, trivial, e.mems.symm, e.tables.symm, trivial, e.datas.symm, e.elems.symm,
    e.structs.symm, e.arrays.symm, e.exns.symm⟩

/-- The embedding is kept when both stores change outside their globals and functions in
the same way. -/
theorem Emb.swap {ρ : Nat → Nat} {D : Nat → Prop} {s t s' : Store H} (e : Emb ρ D s t)
    (hk : s'.globals = s.globals ∧ s'.funcs = s.funcs) :
    Emb ρ D s' { s' with globals := t.globals, funcs := t.funcs } where
  globals a ha := by rw [hk.1]; exact e.globals a ha
  inj := e.inj
  funcs := by rw [hk.2]; exact e.funcs
  fdom fi hfi := e.fdom fi (hk.2 ▸ hfi)
  tags := rfl
  mems := rfl
  tables := rfl
  datas := rfl
  elems := rfl
  structs := rfl
  arrays := rfl
  exns := rfl

/-- **A host blind to globals and functions commutes with the embeddings.** -/
theorem HostEmb.blind {host : HostSemantics H} (hb : Blind host) : HostEmb host where
  ret {_ _ s t s' _ _ _} e hh := by
    refine ⟨{ s' with globals := t.globals, funcs := t.funcs }, ?_, e.swap (hb.keeps _ _ _ _ _ hh)⟩
    rw [e.swap_eq]
    exact hb.ret _ _ _ _ _ _ _ hh
  div {_ _ s t _ _} e hh := by
    rw [e.swap_eq]
    exact hb.div _ _ _ _ _ hh

/-! ## Contexts -/

section Contexts

variable {host : HostSemantics H} {ρ : Nat → Nat} {D : Nat → Prop} {s s' t : Store H}

theorem simH_ctxtInstrs {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (dom : CfgDom D ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimH P host ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimH P host ρ D t ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
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

theorem simH_ctxtLabel {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.label n cont is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimH P host ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimH P host ρ D t ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtLabel reduced, emb, hm,
    hd', trivial⟩

theorem simH_ctxtHandler {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.handler n cs is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimH P host ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimH P host ρ D t ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtHandler reduced, emb, hm,
    hd', trivial⟩

theorem simH_ctxtFrame {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.frame n fi is]⟩)
    (ih : CfgDom D ⟨s, fi, is⟩ → SimH P host ρ D t ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    SimH P host ρ D t ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨t', reduced, emb, hm, hd'⟩ := ih dom.2.1
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtFrame reduced, emb, dom.1,
    ⟨hm, hd'⟩, trivial⟩

end Contexts

/-! ## Host calls -/

theorem simH_callRefHost {host : HostSemantics H} (hh : HostEmb host) {ρ : Nat → Nat}
    {D : Nat → Prop} {s s' t : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) :
    SimH P host ρ D t ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ := by
  obtain ⟨t', ht, emb⟩ := hh.ret stores hhost
  have reduced : Step P host ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩
      ⟨t', frame ρ f, r.toAdmin⟩ :=
    Step.callRefHost hc (stores.func_lookup hf) he hn hcode ht
  refine ⟨t', ?_, emb, dom.1, adminsDom_result D r⟩
  simpa only [config, admins_append, admins_vals, admins, admin, call_ref_fixed hc,
    admins_result] using reduced

theorem simH_callRefHostDiv {host : HostSemantics H} (hh : HostEmb host) {ρ : Nat → Nat}
    {D : Nat → Prop} {s t : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (stores : Emb ρ D s t) (dom : CfgDom D ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged) :
    SimH P host ρ D t ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ := by
  have reduced : Step P host ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩
      ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩ :=
    Step.callRefHostDiv hc (stores.func_lookup hf) he hn hcode (hh.div stores hhost)
  refine ⟨t, ?_, stores, dom⟩
  simpa only [config, admins_append, admins_vals, admins, admin, call_ref_fixed hc] using reduced

/-! ## The step simulation with a host -/

/-- **Steps with a host commuting with the embeddings commute with global-address
embeddings**, for every profile. -/
theorem stepH {host : HostSemantics H} (hh : HostEmb host) {c c' : Config H}
    (h : Step P host c c') :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      SimH P host ρ D t c c' := by
  induction h
  all_goals intro ρ D t stores dom
  case parametric hp => exact (step (.parametric hp) stores dom).lift
  case numeric hp => exact (step (.numeric hp) stores dom).lift
  case vector hp => exact (step (.vector hp) stores dom).lift
  case «variable» hv => exact (step (.variable hv) stores dom).lift
  case reference hv => exact (step (.reference hv) stores dom).lift
  case aggregate hv => exact (step (.aggregate hv) stores dom).lift
  case table hv => exact (step (.table hv) stores dom).lift
  case memory hv => exact (step (.memory hv) stores dom).lift
  case ctxtInstrs hne ih => exact simH_ctxtInstrs hne dom (fun hd => ih stores hd)
  case ctxtLabel ih => exact simH_ctxtLabel dom (fun hd => ih stores hd)
  case ctxtHandler ih => exact simH_ctxtHandler dom (fun hd => ih stores hd)
  case ctxtFrame ih => exact simH_ctxtFrame dom (fun hd => ih stores hd)
  case callRefHost hc hf he hn hcode hhost =>
    exact simH_callRefHost hh stores dom hc hf he hn hcode hhost
  case callRefHostDiv hc hf he hn hcode hhost =>
    exact simH_callRefHostDiv hh stores dom hc hf he hn hcode hhost
  case callRefFunc hc hf he hn hcode => exact (step (.callRefFunc hc hf he hn hcode) stores dom).lift
  case returnCallRefFrameAddr hc hf he hn =>
    exact (step (.returnCallRefFrameAddr hc hf he hn) stores dom).lift
  case throw ht he hn => exact (step (.throw ht he hn) stores dom).lift
  case block hbt hm => exact (step (.block hbt hm) stores dom).lift
  case loop hbt hm => exact (step (.loop hbt hm) stores dom).lift
  case ifTrue hc => exact (step (.ifTrue hc) stores dom).lift
  case ifFalse => exact (step .ifFalse stores dom).lift
  case labelVals => exact (step .labelVals stores dom).lift
  case brLabelZero hl hn => exact (step (.brLabelZero hl hn) stores dom).lift
  case brLabelSucc hl => exact (step (.brLabelSucc hl) stores dom).lift
  case brHandler => exact (step .brHandler stores dom).lift
  case brIfTrue hc => exact (step (.brIfTrue hc) stores dom).lift
  case brIfFalse => exact (step .brIfFalse stores dom).lift
  case brTableLt hi => exact (step (.brTableLt hi) stores dom).lift
  case brTableGe hi => exact (step (.brTableGe hi) stores dom).lift
  case brOnNullNull => exact (step .brOnNullNull stores dom).lift
  case brOnNullAddr hv => exact (step (.brOnNullAddr hv) stores dom).lift
  case brOnNonNullNull => exact (step .brOnNonNullNull stores dom).lift
  case brOnNonNullAddr hv => exact (step (.brOnNonNullAddr hv) stores dom).lift
  case brOnCastSucceed hr => exact (step (.brOnCastSucceed hr) stores dom).lift
  case brOnCastFail hr => exact (step (.brOnCastFail hr) stores dom).lift
  case brOnCastFailSucceed hr => exact (step (.brOnCastFailSucceed hr) stores dom).lift
  case brOnCastFailFail hr => exact (step (.brOnCastFailFail hr) stores dom).lift
  case call hx hf => exact (step (.call hx hf) stores dom).lift
  case callRefNull hc => exact (step (.callRefNull hc) stores dom).lift
  case returnCall hx hf => exact (step (.returnCall hx hf) stores dom).lift
  case returnCallRefLabel hc => exact (step (.returnCallRefLabel hc) stores dom).lift
  case returnCallRefHandler hc => exact (step (.returnCallRefHandler hc) stores dom).lift
  case returnCallRefFrameNull hc => exact (step (.returnCallRefFrameNull hc) stores dom).lift
  case callIndirect => exact (step .callIndirect stores dom).lift
  case returnCallIndirect => exact (step .returnCallIndirect stores dom).lift
  case frameVals hn => exact (step (.frameVals hn) stores dom).lift
  case returnFrame hn => exact (step (.returnFrame hn) stores dom).lift
  case returnLabel => exact (step .returnLabel stores dom).lift
  case returnHandler => exact (step .returnHandler stores dom).lift
  case throwRefNull => exact (step .throwRefNull stores dom).lift
  case throwRefInstrs hne => exact (step (.throwRefInstrs hne) stores dom).lift
  case throwRefLabel => exact (step .throwRefLabel stores dom).lift
  case throwRefFrame => exact (step .throwRefFrame stores dom).lift
  case throwRefHandlerEmpty => exact (step .throwRefHandlerEmpty stores dom).lift
  case throwRefHandlerCatch he ht => exact (step (.throwRefHandlerCatch he ht) stores dom).lift
  case throwRefHandlerCatchRef he ht =>
    exact (step (.throwRefHandlerCatchRef he ht) stores dom).lift
  case throwRefHandlerCatchAll => exact (step .throwRefHandlerCatchAll stores dom).lift
  case throwRefHandlerCatchAllRef => exact (step .throwRefHandlerCatchAllRef stores dom).lift
  case throwRefHandlerNext hm => exact (step (.throwRefHandlerNext hm) stores dom).lift
  case tryTable hbt hm => exact (step (.tryTable hbt hm) stores dom).lift
  case handlerVals => exact (step .handlerVals stores dom).lift
  case trapInstrs hne => exact (step (.trapInstrs hne) stores dom).lift
  case trapLabel => exact (step .trapLabel stores dom).lift
  case trapHandler => exact (step .trapHandler stores dom).lift
  case trapFrame => exact (step .trapFrame stores dom).lift

end Silmaril.Proofs.Wasm.Game.SpecGlobals
