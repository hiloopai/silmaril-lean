module

public import Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHost
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Frame
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.Behaviours

/-!
# Hosts that commute with the embeddings on well-behaved targets

`HostEmb` (`StepHost`) asks a host to commute with **every** global-address embedding. A host
induced from another Wasm version (`liftHost` of a 2.0 host) answers only on stores in the image
of that version, and an embedding's target may hold arbitrary globals outside the image of the
source, so such a host cannot satisfy `HostEmb`. This module relativises it:

* `OutG Good ρ D t`: every global of `t` outside the image `ImgD ρ D` satisfies `Good`;
* `HostEmbR Good host`: `HostEmb` for embeddings whose target satisfies `OutG Good`, and the
  host's answer again satisfies it;
* **`stepHR`**: with `HostEmbR Good host`, every `Step P host` step is matched one for one, and
  `OutG Good` is kept. The non-host leaves come from the host-free `step`; their target steps
  keep the globals outside `ImgD ρ D` (`step_globals_out`), so `OutG` is kept;
* `steps_embHR`, `diverges_embHR`, **`behavioursOf_embHR_sub`**: runs, divergence and behaviours
  of `c` are matched by the renamed configuration over an embedded store satisfying `OutG Good`;
* `HostEmb.toR`: a host commuting with every embedding commutes with these (`Good` anything).

New proofs (the structure of `stepH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.SpecGlobals

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Every global of `t` outside the image of `D` under `ρ` satisfies `Good`. -/
def OutG (Good : GlobalInst → Prop) (ρ : Nat → Nat) (D : Nat → Prop) (t : Store H) : Prop :=
  ∀ b g, ¬ ImgD ρ D b → t.globals[b]? = some g → Good g

/-- A host commutes with the global-address embeddings whose targets satisfy `OutG Good`. -/
structure HostEmbR (Good : GlobalInst → Prop) (host : HostSemantics H) : Prop where
  ret : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t s' : Store H} {h : H} {vs : List Val}
    {r : Result}, Emb ρ D s t → OutG Good ρ D t → host h s vs (.returned s' r) →
      ∃ t', host h t vs (.returned t' r) ∧ Emb ρ D s' t' ∧ OutG Good ρ D t'
  div : ∀ {ρ : Nat → Nat} {D : Nat → Prop} {s t : Store H} {h : H} {vs : List Val},
    Emb ρ D s t → OutG Good ρ D t → host h s vs .diverged → host h t vs .diverged

/-- `OutG` is kept when the globals outside the image do not change. -/
theorem OutG.of_eq {Good : GlobalInst → Prop} {ρ : Nat → Nat} {D : Nat → Prop} {t t' : Store H}
    (ho : OutG Good ρ D t) (he : ∀ {b}, ¬ ImgD ρ D b → t'.globals[b]? = t.globals[b]?) :
    OutG Good ρ D t' := fun b g hb hg => ho b g hb ((he hb).symm.trans hg)

/-- A host commuting with every embedding commutes with those whose target satisfies `OutG`,
provided every target store satisfies it after the call: here `Good` is everything. -/
theorem HostEmb.toR {host : HostSemantics H} (hh : HostEmb host) :
    HostEmbR (fun _ => True) host where
  ret e _ hs := let ⟨t', ht, e'⟩ := hh.ret e hs; ⟨t', ht, e', fun _ _ _ _ => trivial⟩
  div e _ hs := hh.div e hs

/-- The conclusion of the relativised step simulation. -/
def SimHR (P : Profile) (host : HostSemantics H) (Good : GlobalInst → Prop) (ρ : Nat → Nat)
    (D : Nat → Prop) (t : Store H) (c c' : Config H) : Prop :=
  ∃ t', Step P host (config ρ t c) (config ρ t' c') ∧ Emb ρ D c'.store t' ∧ CfgDom D c' ∧
    OutG Good ρ D t'

/-- A host-free step, lifted: the target step keeps the globals outside the image. -/
theorem simHR_leaf {host : HostSemantics H} {Good : GlobalInst → Prop} {ρ : Nat → Nat}
    {D : Nat → Prop} {t : Store H} {c c' : Config H} (hs : Step P noHost c c')
    (stores : Emb ρ D c.store t) (dom : CfgDom D c) (out : OutG Good ρ D t) :
    SimHR P host Good ρ D t c c' := by
  obtain ⟨t', hst, e, d⟩ := step hs stores dom
  have hdom : CfgDom (ImgD ρ D) (config ρ t c) := cfgDom_config dom
  have hkeep : ∀ {b}, ¬ ImgD ρ D b → t'.globals[b]? = t.globals[b]? := fun hb =>
    step_globals_out hst hdom hb
  exact ⟨t', Step.of_noHost host hst, e, d, out.of_eq hkeep⟩

section Contexts

variable {host : HostSemantics H} {Good : GlobalInst → Prop} {ρ : Nat → Nat} {D : Nat → Prop}
  {s s' t : Store H}

theorem simHR_ctxtInstrs {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
    (hne : vs ≠ [] ∨ rest ≠ []) (dom : CfgDom D ⟨s, f, vals vs ++ is ++ rest⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimHR P host Good ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimHR P host Good ρ D t ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩ := by
  have hd : AdminsDom D is ∧ AdminsDom D rest := by
    have h := dom.2
    simp only [adminsDom_append, adminsDom_vals, true_and] at h
    exact h
  obtain ⟨t', reduced, emb, ⟨hm, hd'⟩, out⟩ := ih ⟨dom.1, hd.1⟩
  refine ⟨t', ?_, emb, ⟨hm, ?_⟩, out⟩
  · simpa only [config, admins_append, admins_vals] using
      Step.ctxtInstrs reduced (hne.imp_right admins_ne_nil)
  · simp only [adminsDom_append, adminsDom_vals, true_and]
    exact ⟨hd', hd.2⟩

theorem simHR_ctxtLabel {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.label n cont is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimHR P host Good ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimHR P host Good ρ D t ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩ := by
  obtain ⟨t', reduced, emb, ⟨hm, hd'⟩, out⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtLabel reduced, emb,
    ⟨hm, hd', trivial⟩, out⟩

theorem simHR_ctxtHandler {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.handler n cs is]⟩)
    (ih : CfgDom D ⟨s, f, is⟩ → SimHR P host Good ρ D t ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    SimHR P host Good ρ D t ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩ := by
  obtain ⟨t', reduced, emb, ⟨hm, hd'⟩, out⟩ := ih ⟨dom.1, dom.2.1⟩
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtHandler reduced, emb,
    ⟨hm, hd', trivial⟩, out⟩

theorem simHR_ctxtFrame {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
    (dom : CfgDom D ⟨s, f, [.frame n fi is]⟩)
    (ih : CfgDom D ⟨s, fi, is⟩ → SimHR P host Good ρ D t ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
    SimHR P host Good ρ D t ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩ := by
  obtain ⟨t', reduced, emb, ⟨hm, hd'⟩, out⟩ := ih dom.2.1
  exact ⟨t', by simpa only [config, admins, admin] using Step.ctxtFrame reduced, emb,
    ⟨dom.1, ⟨hm, hd'⟩, trivial⟩, out⟩

end Contexts

/-- The host-call rule under a relativised host embedding. -/
theorem simHR_callRefHost {host : HostSemantics H} {Good : GlobalInst → Prop}
    (hh : HostEmbR Good host) {ρ : Nat → Nat}
    {D : Nat → Prop} {s s' t : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H} {r : Result}
    (stores : Emb ρ D s t) (out : OutG Good ρ D t)
    (dom : CfgDom D ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h)
    (hhost : host h s vs (.returned s' r)) :
    SimHR P host Good ρ D t ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ ⟨s', f, r.toAdmin⟩ := by
  obtain ⟨t', ht, emb, out'⟩ := hh.ret stores out hhost
  have reduced : Step P host ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩
      ⟨t', frame ρ f, r.toAdmin⟩ :=
    Step.callRefHost hc (stores.func_lookup hf) he hn hcode ht
  refine ⟨t', ?_, emb, ⟨dom.1, adminsDom_result D r⟩, out'⟩
  simpa only [config, admins_append, admins_vals, admins, admin, call_ref_fixed hc,
    admins_result] using reduced

/-- The diverging host-call rule under a relativised host embedding. -/
theorem simHR_callRefHostDiv {host : HostSemantics H} {Good : GlobalInst → Prop}
    (hh : HostEmbR Good host) {ρ : Nat → Nat}
    {D : Nat → Prop} {s t : Store H} {f : Frame} {c : Admin} {vs : List Val} {a : Nat}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} {h : H}
    (stores : Emb ρ D s t) (out : OutG Good ρ D t)
    (dom : CfgDom D ⟨s, f, vals vs ++ [.ref (.func a), c]⟩)
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (hcode : fi.code = .host h) (hhost : host h s vs .diverged) :
    SimHR P host Good ρ D t ⟨s, f, vals vs ++ [.ref (.func a), c]⟩
      ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ := by
  have reduced : Step P host ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩
      ⟨t, frame ρ f, vals vs ++ [.ref (.func a), c]⟩ :=
    Step.callRefHostDiv hc (stores.func_lookup hf) he hn hcode (hh.div stores out hhost)
  refine ⟨t, ?_, stores, dom, out⟩
  simpa only [config, admins_append, admins_vals, admins, admin, call_ref_fixed hc] using reduced

/-- **Steps with a host commuting with the embeddings on well-behaved targets commute with
those embeddings**, for every profile, and keep the targets well behaved. -/
theorem stepHR {host : HostSemantics H} {Good : GlobalInst → Prop} (hh : HostEmbR Good host)
    {c c' : Config H} (h : Step P host c c') :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      OutG Good ρ D t → SimHR P host Good ρ D t c c' := by
  induction h
  all_goals intro ρ D t stores dom out
  case ctxtInstrs hne ih => exact simHR_ctxtInstrs hne dom (fun hd => ih stores hd out)
  case ctxtLabel ih => exact simHR_ctxtLabel dom (fun hd => ih stores hd out)
  case ctxtHandler ih => exact simHR_ctxtHandler dom (fun hd => ih stores hd out)
  case ctxtFrame ih => exact simHR_ctxtFrame dom (fun hd => ih stores hd out)
  case callRefHost hc hf he hn hcode hhost =>
    exact simHR_callRefHost hh stores out dom hc hf he hn hcode hhost
  case callRefHostDiv hc hf he hn hcode hhost =>
    exact simHR_callRefHostDiv hh stores out dom hc hf he hn hcode hhost
  case parametric hp => exact simHR_leaf (.parametric hp) stores dom out
  case numeric hp => exact simHR_leaf (.numeric hp) stores dom out
  case vector hp => exact simHR_leaf (.vector hp) stores dom out
  case «variable» hv => exact simHR_leaf (.variable hv) stores dom out
  case reference hv => exact simHR_leaf (.reference hv) stores dom out
  case aggregate hv => exact simHR_leaf (.aggregate hv) stores dom out
  case table hv => exact simHR_leaf (.table hv) stores dom out
  case memory hv => exact simHR_leaf (.memory hv) stores dom out
  case callRefFunc hc hf he hn hcode =>
    exact simHR_leaf (.callRefFunc hc hf he hn hcode) stores dom out
  case returnCallRefFrameAddr hc hf he hn =>
    exact simHR_leaf (.returnCallRefFrameAddr hc hf he hn) stores dom out
  case throw ht he hn => exact simHR_leaf (.throw ht he hn) stores dom out
  case block hbt hm => exact simHR_leaf (.block hbt hm) stores dom out
  case loop hbt hm => exact simHR_leaf (.loop hbt hm) stores dom out
  case ifTrue hc => exact simHR_leaf (.ifTrue hc) stores dom out
  case ifFalse => exact simHR_leaf .ifFalse stores dom out
  case labelVals => exact simHR_leaf .labelVals stores dom out
  case brLabelZero hl hn => exact simHR_leaf (.brLabelZero hl hn) stores dom out
  case brLabelSucc hl => exact simHR_leaf (.brLabelSucc hl) stores dom out
  case brHandler => exact simHR_leaf .brHandler stores dom out
  case brIfTrue hc => exact simHR_leaf (.brIfTrue hc) stores dom out
  case brIfFalse => exact simHR_leaf .brIfFalse stores dom out
  case brTableLt hi => exact simHR_leaf (.brTableLt hi) stores dom out
  case brTableGe hi => exact simHR_leaf (.brTableGe hi) stores dom out
  case brOnNullNull => exact simHR_leaf .brOnNullNull stores dom out
  case brOnNullAddr hv => exact simHR_leaf (.brOnNullAddr hv) stores dom out
  case brOnNonNullNull => exact simHR_leaf .brOnNonNullNull stores dom out
  case brOnNonNullAddr hv => exact simHR_leaf (.brOnNonNullAddr hv) stores dom out
  case brOnCastSucceed hr => exact simHR_leaf (.brOnCastSucceed hr) stores dom out
  case brOnCastFail hr => exact simHR_leaf (.brOnCastFail hr) stores dom out
  case brOnCastFailSucceed hr => exact simHR_leaf (.brOnCastFailSucceed hr) stores dom out
  case brOnCastFailFail hr => exact simHR_leaf (.brOnCastFailFail hr) stores dom out
  case call hx hf => exact simHR_leaf (.call hx hf) stores dom out
  case callRefNull hc => exact simHR_leaf (.callRefNull hc) stores dom out
  case returnCall hx hf => exact simHR_leaf (.returnCall hx hf) stores dom out
  case returnCallRefLabel hc => exact simHR_leaf (.returnCallRefLabel hc) stores dom out
  case returnCallRefHandler hc => exact simHR_leaf (.returnCallRefHandler hc) stores dom out
  case returnCallRefFrameNull hc => exact simHR_leaf (.returnCallRefFrameNull hc) stores dom out
  case callIndirect => exact simHR_leaf .callIndirect stores dom out
  case returnCallIndirect => exact simHR_leaf .returnCallIndirect stores dom out
  case frameVals hn => exact simHR_leaf (.frameVals hn) stores dom out
  case returnFrame hn => exact simHR_leaf (.returnFrame hn) stores dom out
  case returnLabel => exact simHR_leaf .returnLabel stores dom out
  case returnHandler => exact simHR_leaf .returnHandler stores dom out
  case throwRefNull => exact simHR_leaf .throwRefNull stores dom out
  case throwRefInstrs hne => exact simHR_leaf (.throwRefInstrs hne) stores dom out
  case throwRefLabel => exact simHR_leaf .throwRefLabel stores dom out
  case throwRefFrame => exact simHR_leaf .throwRefFrame stores dom out
  case throwRefHandlerEmpty => exact simHR_leaf .throwRefHandlerEmpty stores dom out
  case throwRefHandlerCatch he ht => exact simHR_leaf (.throwRefHandlerCatch he ht) stores dom out
  case throwRefHandlerCatchRef he ht =>
    exact simHR_leaf (.throwRefHandlerCatchRef he ht) stores dom out
  case throwRefHandlerCatchAll => exact simHR_leaf .throwRefHandlerCatchAll stores dom out
  case throwRefHandlerCatchAllRef => exact simHR_leaf .throwRefHandlerCatchAllRef stores dom out
  case throwRefHandlerNext hm => exact simHR_leaf (.throwRefHandlerNext hm) stores dom out
  case tryTable hbt hm => exact simHR_leaf (.tryTable hbt hm) stores dom out
  case handlerVals => exact simHR_leaf .handlerVals stores dom out
  case trapInstrs hne => exact simHR_leaf (.trapInstrs hne) stores dom out
  case trapLabel => exact simHR_leaf .trapLabel stores dom out
  case trapHandler => exact simHR_leaf .trapHandler stores dom out
  case trapFrame => exact simHR_leaf .trapFrame stores dom out

variable {host : HostSemantics H} {Good : GlobalInst → Prop}

/-- **Runs commute with a global embedding whose target is well behaved.** -/
theorem steps_embHR (hh : HostEmbR Good host) {c d : Config H} (h : Steps P host c d) :
    ∀ {ρ : Nat → Nat} {D : Nat → Prop} {t : Store H}, Emb ρ D c.store t → CfgDom D c →
      OutG Good ρ D t →
      ∃ t', Steps P host (config ρ t c) (config ρ t' d) ∧ Emb ρ D d.store t' ∧ CfgDom D d ∧
        OutG Good ρ D t' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun stores dom out => ⟨_, .refl, stores, dom, out⟩
  | head hstep _ ih =>
    intro ρ D t stores dom out
    obtain ⟨t₁, hs₁, e₁, d₁, o₁⟩ := stepHR hh hstep stores dom out
    obtain ⟨t', hr, e', d', o'⟩ := ih e₁ d₁ o₁
    exact ⟨t', .head hs₁ hr, e', d', o'⟩

/-- **Divergence commutes with a global embedding whose target is well behaved.** -/
theorem diverges_embHR (hh : HostEmbR Good host) {ρ : Nat → Nat} {D : Nat → Prop}
    {c : Config H} {t : Store H}
    (h : Diverges P host c) (stores : Emb ρ D c.store t) (dom : CfgDom D c)
    (out : OutG Good ρ D t) : Diverges P host (config ρ t c) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun y => ∃ c t, y = config ρ t c ∧ Emb ρ D c.store t ∧ CfgDom D c ∧ OutG Good ρ D t ∧
      Diverges P host c) ?_ ⟨c, t, rfl, stores, dom, out, h⟩
  rintro _ ⟨c, t, rfl, stores, dom, out, hdiv⟩
  obtain ⟨c', hs, hdiv'⟩ := Silmaril.InfiniteTrace.unfold hdiv
  obtain ⟨t', hs', e', d', o'⟩ := stepHR hh hs stores dom out
  exact ⟨config ρ t' c', hs', c', t', rfl, e', d', o', hdiv'⟩

/-- **Behaviours are behaviours of the renamed configuration** over a well-behaved target. -/
theorem behavioursOf_embHR_sub (hh : HostEmbR Good host) {ρ : Nat → Nat} {D : Nat → Prop}
    {c : Config H} {t : Store H} (stores : Emb ρ D c.store t) (dom : CfgDom D c)
    (out : OutG Good ρ D t) :
    behavioursOf P host c ⊆ behavioursOf P host (config ρ t c) := by
  rintro b (⟨d, r, hrun, hcode, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨t', hrun', -, -, -⟩ := steps_embHR hh hrun stores dom out
    have hcode' : (config ρ t' d).code = r.toAdmin := by
      show admins ρ d.code = r.toAdmin
      rw [hcode, admins_result]
    exact Or.inl ⟨config ρ t' d, r, hrun', hcode', rfl⟩
  · exact Or.inr ⟨rfl, diverges_embHR hh hdiv stores dom out⟩

/-- **Single-allocation residue behaviours are spec behaviours** for a host commuting with the
embeddings whose targets keep `Good` globals, every profile, provided the spec preparation's
store holds only `Good` globals. -/
theorem spec_behaviours_sub_residueHR {Good : GlobalInst → Prop} {host : HostSemantics Nat}
    (hh : HostEmbR Good host) {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, ModDom (· < s.globals.length) fi.module)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c₁.withStart st) ⊆
        behavioursOf P host (c.withStart st) := by
  obtain ⟨c, ι, hc, hcode, hframe, -, he, -, -⟩ :=
    prepare_residue_emb (Emb.refl s) Function.injective_id hb (imports_globals_lt hxas) hg hp
  have hcode₁ : c₁.code = segCode m := residue_code hp
  have hc' : prepare? evalConst? s m xas = some (c, st) := by
    rw [← map_external_id xas]
    exact hc
  have hcfg : c.withStart st = config ι c.store (c₁.withStart st) :=
    withStart_config (hcode.trans hcode₁) hcode₁ hframe st
  have he' : Emb ι Univ (c₁.withStart st).store c.store := by
    rw [withStart_store]
    exact he
  have hout : OutG Good ι Univ c.store := fun _ g _ hgb =>
    hgood c st hc' g (List.mem_of_getElem? hgb)
  have hdom : CfgDom Univ (c₁.withStart st) := ⟨modDom_univ _, adminsDom_univ _⟩
  refine ⟨c, hc', fun P => ?_⟩
  rw [hcfg]
  exact behavioursOf_embHR_sub hh he' hdom hout

end Silmaril.Proofs.Wasm.Game.SpecGlobals
