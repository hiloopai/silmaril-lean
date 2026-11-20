module

public import Silmaril.Proofs.Wasm.Component.Reference.HostWrite.Dispatch

/-!
# Host-state writes along machine runs: every machine rule

`step_cfgSafe` goes through the rules of `Machine.Step` (as the table frame argument
`Silmaril.Proofs.Wasm.Resource.MachineTab.Step`): the rules that replace the running program by a
continuation keep `CfgSafe` (the continuations of a host-safe program are host-safe, those of a
read with the read pending), `call`/`coreCallout` push a dispatched program (`DispatchSafe`),
`newThread` saves a dispatched thread body, `block`/`blockSwitch`/`resumeThread` move activations
between the control chain and the saved continuations (which have no pending read), and the host
events start the host-frame programs, none of which writes the host state. `hostSet s'` is the
only rule that changes the host state; by `CfgSafe` it is the next operation after a read of the
current host state `s`, so `Ext s s'` (`step_host`).

* `step_host`: along a step from a host-safe configuration the host state is unchanged or
  related by `Ext`; `steps_host`: along a run, unchanged or related by the transitive closure;
* `steps_cfgSafe`: runs keep `CfgSafe` (host-frame programs host-safe, `RunSafe`);
* `cfgSafe_init`: the initial configurations are host-safe.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HostWrite

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {Ext : σ → σ → Prop}
variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

/-! ## Activations -/

theorem ActSafe.mono {a : Activation E σ} (h : ActSafe Ext none a) (c : Option σ) :
    ActSafe Ext c a := by
  obtain ⟨th, f, segs⟩ := a
  refine ⟨?_, h.2⟩
  cases f with
  | prog p => exact HostSafe.mono h.1 c
  | core t k => exact h.1

theorem ctlSafe_cons {c : Option σ} {a : Activation E σ} {rest : List (Activation E σ)}
    (ha : ActSafe Ext c a) (hr : ∀ b ∈ rest, ActSafe Ext none b) : CtlSafe Ext c (a :: rest) :=
  ⟨ha, hr⟩

theorem ctlSafe_of_none {c : Option σ} :
    ∀ {l : List (Activation E σ)}, (∀ b ∈ l, ActSafe Ext none b) → CtlSafe Ext c l
  | [], _ => trivial
  | a :: _, h =>
    ⟨ActSafe.mono (h a List.mem_cons_self) c, fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem cfgSafe_head {m : Config E σ} {a : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgSafe Ext m) (hc : m.ctl = a :: rest) :
    ActSafe Ext (some m.host) a ∧ ∀ b ∈ rest, ActSafe Ext none b := by
  have h := hm.1
  rw [hc] at h
  exact h

theorem actSafe_op {c c' : Option σ} {th : Option ThreadId} {o : (Eff E σ).Op}
    {k : (Eff E σ).Resp o → P E σ (Ret E)} {segs : List (Seg E σ)} (ho : Op.Plain o)
    (h : ActSafe Ext c ⟨th, .prog (.op (S := Eff E σ) o k), segs⟩) (r : (Eff E σ).Resp o) :
    ActSafe Ext c' ⟨th, .prog (k r), segs⟩ :=
  ⟨(HostSafe.of_op ho h.1 r).mono c', h.2⟩

theorem actSafe_none_op {c : Option σ} {th : Option ThreadId} {o : (Eff E σ).Op}
    {k : (Eff E σ).Resp o → P E σ (Ret E)} {segs : List (Seg E σ)} (ho : Op.Plain o)
    (h : ActSafe Ext c ⟨th, .prog (.op (S := Eff E σ) o k), segs⟩) (r : (Eff E σ).Resp o) :
    ActSafe Ext none ⟨th, .prog (k r), segs⟩ :=
  actSafe_op ho h r

/-! ## Configurations -/

/-- Replace the running activation (and the store), the host state unchanged. -/
theorem cfgSafe_set {m : Config E σ} {a a' : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgSafe Ext m) (hc : m.ctl = a :: rest)
    (ha : ActSafe Ext (some m.host) a → ActSafe Ext (some m.host) a') (s' : CStore E) :
    CfgSafe Ext { m with store := s', ctl := a' :: rest } :=
  ⟨⟨ha (cfgSafe_head hm hc).1, (cfgSafe_head hm hc).2⟩, hm.2⟩

/-- Pop the running activation. -/
theorem cfgSafe_pop {m : Config E σ} {a : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgSafe Ext m) (hc : m.ctl = a :: rest) (s' : CStore E) :
    CfgSafe Ext { m with store := s', ctl := rest } :=
  ⟨ctlSafe_of_none (cfgSafe_head hm hc).2, hm.2⟩

/-- A host frame running `p`. -/
theorem cfgSafe_host {m : Config E σ} (hm : CfgSafe Ext m) {p : P E σ (Ret E)}
    (hp : HostSafe Ext none p) : CfgSafe Ext { m with ctl := [.ofProg none p] } :=
  ⟨⟨⟨hp.mono _, fun _ h => nomatch h⟩, fun _ h => nomatch h⟩, hm.2⟩

theorem cont?_setCont (m : Config E σ) (t u : ThreadId) (v : Option (Activation E σ)) :
    (m.setCont t v).cont? u = if u = t then v else m.cont? u := by
  by_cases h : u = t
  · subst h
    simp
  · simp [h, Config.cont?_setCont_ne _ _ _ _ h]

theorem conts_setCont {m : Config E σ} (hm : ∀ t a, m.cont? t = some a → ActSafe Ext none a)
    {t : ThreadId} {v : Option (Activation E σ)} (hv : ∀ b, v = some b → ActSafe Ext none b) :
    ∀ u b, (m.setCont t v).cont? u = some b → ActSafe Ext none b := by
  intro u b hb
  rw [cont?_setCont] at hb
  split at hb
  · exact hv b hb
  · exact hm u b hb

theorem hostFinish_eq (r : Ret E) (rest : List (Activation E σ)) (m : Config E σ) :
    (hostFinish r rest m).host = m.host ∧ (hostFinish r rest m).conts = m.conts ∧
      (hostFinish r rest m).ctl = rest := by
  unfold hostFinish
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem observe_eq (m : Config E σ) (o : HostObs) :
    (observe m o).host = m.host ∧ (observe m o).conts = m.conts := by
  cases o <;> exact ⟨rfl, rfl⟩

theorem cfgSafe_trapCfg {m : Config E σ} (hm : CfgSafe Ext m) : CfgSafe Ext (trapCfg m) :=
  ⟨trivial, hm.2⟩

/-! ## The host-frame programs -/

theorem hostSafe_invokeProg (c : CallId) (f : FuncId)
    (args : List Silmaril.Wasm.Component.Value.Val) :
    HostSafe Ext none (StepDefs.invokeProg (E := E) (σ := σ) c f args) :=
  HostSafe.of_invW (I := TT)
    (P.Inv.bind (P.Inv.allocObj _ _ tf_insts') fun _ =>
      P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ =>
        P.Inv.bind (P.Inv.callRet _) fun _ =>
          P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ => P.Inv.pure _) none

theorem hostSafe_tickProg (hr : HostReady σ) :
    HostSafe Ext none (StepDefs.tickProg (E := E) hr) := by
  refine HostSafe.of_invW (I := TT) ?_ none
  unfold StepDefs.tickProg
  refine P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ => ?_
  refine P.Inv.bind P.Inv.getStore fun s => P.Inv.bind P.Inv.hostGet fun h => ?_
  have hl : P.InvW (TT : CStore E → Prop) (fun _ : σ => False)
      (modifyStore StepDefs.leaveHostSt >>= fun _ => (pure Ret.unit : P E σ (Ret E))) :=
    P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ => P.Inv.pure _
  dsimp only
  split
  · exact hl
  · exact P.Inv.bind (P.Inv.pickTick _ _) fun t =>
      P.Inv.bind (Thread.resume_inv t tf_insts') fun _ => hl

theorem hostSafe_cancelProg (r : CancelRef) :
    HostSafe Ext none (StepDefs.cancelProg (E := E) (σ := σ) r) :=
  HostSafe.of_invW (I := TT)
    (P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ =>
      P.Inv.bind (P.Inv.callRet _) fun _ =>
        P.Inv.bind (P.Inv.modifyStore tf_insts') fun _ => P.Inv.pure _) none

theorem hostSafe_runProg {p : P E σ (Ret E)} (hp : HostSafe Ext none p) :
    HostSafe Ext none (StepDefs.runProg p) :=
  hp.bind fun _ => .pure _ _

/-! ## The rules -/

/-- **Every machine step keeps every program host-safe.** -/
theorem step_cfgSafe (hd : DispatchSafe Ext dispatch) {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') (hm : CfgSafe Ext m)
    (hl : ∀ p, l = .host (.run p) → HostSafe Ext none p) : CfgSafe Ext m' := by
  cases h with
  | @popProg th r k segs rest hc =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k r), segs⟩) (fun _ =>
      ⟨HostSafe.mono (h.2 _ List.mem_cons_self r) _,
        fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩) m.store
  | @popCore th vs ct k segs rest hc =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc
      (a' := ⟨th, .core (E.resume m.core ct (.values vs)) k, segs⟩) (fun _ =>
      ⟨h.2 _ List.mem_cons_self, fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩) m.store
  | threadExit hc => exact cfgSafe_pop hm hc _
  | @hostDone r rest hc =>
    obtain ⟨-, hconts, hctl⟩ := hostFinish_eq r rest m
    refine ⟨?_, fun t b hb => hm.2 t b ?_⟩
    · rw [hctl]
      exact ctlSafe_of_none (cfgSafe_head hm hc).2
    · have e : (hostFinish r rest m).cont? t = m.cont? t := by simp [Config.cont?, hconts]
      rwa [e] at hb
  | @call th c k segs rest hc =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (dispatch c), .prog k :: segs⟩) (fun _ =>
      ⟨HostSafe.mono (hd c) _, List.forall_mem_cons.2
        ⟨fun r => HostSafe.of_op (by trivial) h.1 r, h.2⟩⟩) m.store
  | @callCore th f args k segs rest hc =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc (a' := ⟨th, .core (E.invoke f args) k, segs⟩) (fun _ =>
      ⟨fun vs => HostSafe.of_op (by trivial) h.1 vs, h.2⟩) m.store
  | @coreInternal th ct k segs rest c' ct' hc _ _ =>
    exact cfgSafe_set (m := { m with core := c' }) hm hc (a' := ⟨th, .core ct' k, segs⟩)
      (fun h => h) m.store
  | @coreReturned th ct k segs rest vs hc _ =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k vs), segs⟩) (fun _ =>
      ⟨HostSafe.mono (h.1 vs) _, h.2⟩) m.store
  | coreTrap hc _ => exact cfgSafe_trapCfg hm
  | @coreCallout th ct k segs rest h' args hc _ =>
    have h := (cfgSafe_head hm hc).1
    exact cfgSafe_set hm hc
      (a' := ⟨th, .prog (dispatch (.hostCallout h' args)), .core ct k :: segs⟩) (fun _ =>
      ⟨HostSafe.mono (hd _) _, List.forall_mem_cons.2 ⟨h.1, h.2⟩⟩) m.store
  | @get th k segs rest hc =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k m.store), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | @modify th f k segs rest hc =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k ()), segs⟩)
      (fun h => actSafe_op (by trivial) h _) _
  | trap hc => exact cfgSafe_trapCfg hm
  | @choose th ck k segs rest r hc _ =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k r), segs⟩)
      (fun h => actSafe_op (by trivial) h r) m.store
  | @currentThread th k segs rest hc =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k th), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | @newThread th b k segs rest s' t hc _ =>
    exact ⟨⟨actSafe_op (by trivial) (cfgSafe_head hm hc).1 t, (cfgSafe_head hm hc).2⟩,
      conts_setCont hm.2 fun _ e => Option.some.inj e ▸
        (⟨hd _, fun _ h => nomatch h⟩ : ActSafe Ext none (threadAct dispatch t b))⟩
  | @block t k segs rest hc =>
    exact ⟨ctlSafe_of_none (cfgSafe_head hm hc).2,
      conts_setCont hm.2 fun _ e => Option.some.inj e ▸
        (actSafe_none_op (by trivial) (cfgSafe_head hm hc).1 () :
          ActSafe Ext none (blockedAct t k segs))⟩
  | @blockSwitch t o k segs rest b hc hb =>
    have h₁ := conts_setCont hm.2 (t := t) (v := some (blockedAct t k segs)) fun _ e =>
      Option.some.inj e ▸ (actSafe_none_op (by trivial) (cfgSafe_head hm hc).1 () :
        ActSafe Ext none (blockedAct t k segs))
    exact ⟨⟨ActSafe.mono (h₁ _ _ hb) _, (cfgSafe_head hm hc).2⟩,
      conts_setCont h₁ fun _ e => nomatch e⟩
  | @resumeThread th t k segs rest b hc hb =>
    exact ⟨⟨ActSafe.mono (hm.2 _ _ hb) _, List.forall_mem_cons.2
        ⟨actSafe_none_op (by trivial) (cfgSafe_head hm hc).1 (), (cfgSafe_head hm hc).2⟩⟩,
      conts_setCont hm.2 fun _ e => nomatch e⟩
  | @hostGet th k segs rest hc =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k m.host), segs⟩)
      (fun h => ⟨HostSafe.of_get h.1 _, h.2⟩) m.store
  | @hostSet th s k segs rest hc =>
    have h := (cfgSafe_head hm hc).1
    obtain ⟨s₀, -, -, hk⟩ := HostSafe.of_set h.1
    exact ⟨⟨⟨HostSafe.mono hk _, h.2⟩, (cfgSafe_head hm hc).2⟩, hm.2⟩
  | @emit th o k segs rest hc =>
    obtain ⟨hh, hconts⟩ := observe_eq m o
    refine ⟨?_, fun t b hb => hm.2 t b ?_⟩
    · show CtlSafe Ext (some (observe m o).host) _
      rw [hh]
      exact ⟨actSafe_op (by trivial) (cfgSafe_head hm hc).1 (), (cfgSafe_head hm hc).2⟩
    · cases o <;> exact hb
  | @readCore th k segs rest hc =>
    exact cfgSafe_set hm hc (a' := ⟨th, .prog (k (E.view m.core)), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | @memWrite th a ptr bytes k segs rest hc =>
    exact cfgSafe_set (m := { m with core := _ }) hm hc (a' := ⟨th, .prog (k ()), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | @allocHost th ty h k segs rest hc =>
    exact cfgSafe_set (m := { m with core := _ }) hm hc (a' := ⟨th, .prog (k ()), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | @prepare th md imports k segs rest hc =>
    exact cfgSafe_set (m := { m with core := _ }) hm hc (a' := ⟨th, .prog (k ()), segs⟩)
      (fun h => actSafe_op (by trivial) h _) m.store
  | fault _ => exact cfgSafe_trapCfg hm
  | hostInvoke _ _ => exact cfgSafe_host hm (hostSafe_invokeProg _ _ _)
  | hostTick _ => exact cfgSafe_host hm (hostSafe_tickProg hr)
  | hostCancel _ _ _ => exact cfgSafe_host (m := m.dropCancel _) hm (hostSafe_cancelProg _)
  | hostRun _ => exact cfgSafe_host hm (hostSafe_runProg (hl _ rfl))

/-- **Along a step from a host-safe configuration the host state is unchanged, or the step is a
write allowed by `Ext`.** -/
theorem step_host {m m' : Config E σ} {l : Label E σ} (h : Step prof hr dispatch m l m')
    (hm : CfgSafe Ext m) : m'.host = m.host ∨ Ext m.host m'.host := by
  cases h with
  | @hostSet th s k segs rest hc =>
    obtain ⟨s₀, e, hx, -⟩ := HostSafe.of_set (cfgSafe_head hm hc).1.1
    obtain rfl := Option.some.inj e
    exact .inr hx
  | @hostDone r rest _ => exact .inl (hostFinish_eq r rest m).1
  | @emit _ o _ _ _ _ => exact .inl (observe_eq m o).1
  | _ => exact .inl rfl

/-- The reflexive closure of `Ext` along runs. -/
inductive HostChain (Ext : σ → σ → Prop) : σ → σ → Prop where
  | refl (s : σ) : HostChain Ext s s
  | tail {s s₁ s₂ : σ} : HostChain Ext s s₁ → Ext s₁ s₂ → HostChain Ext s s₂

theorem HostChain.trans {s₁ s₂ s₃ : σ} (h₁ : HostChain Ext s₁ s₂) (h₂ : HostChain Ext s₂ s₃) :
    HostChain Ext s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hx ih => exact .tail ih hx

theorem HostChain.head {s₁ s₂ s₃ : σ} (hx : Ext s₁ s₂) (h : HostChain Ext s₂ s₃) :
    HostChain Ext s₁ s₃ := HostChain.trans (.tail (.refl _) hx) h

/-- **Runs keep every program host-safe, and the host state moves along `Ext`.** -/
theorem steps_cfgSafe (hd : DispatchSafe Ext dispatch) {m m' : Config E σ}
    {tr : List (Label E σ)} (h : Steps prof hr dispatch m tr m') (hm : CfgSafe Ext m)
    (hl : RunSafe Ext tr) : CfgSafe Ext m' ∧ HostChain Ext m.host m'.host := by
  induction h with
  | refl => exact ⟨hm, .refl _⟩
  | @cons m₁ m₂ m₃ l tr s _ ih =>
    have hm₂ : CfgSafe Ext m₂ := step_cfgSafe hd s hm fun p e => hl p (e ▸ List.mem_cons_self)
    obtain ⟨hm', hc⟩ := ih hm₂ fun p hp => hl p (List.mem_cons_of_mem _ hp)
    refine ⟨hm', ?_⟩
    rcases step_host s hm with e | hx
    · rw [← e]
      exact hc
    · exact HostChain.head hx hc

theorem cfgSafe_init (s : CStore E) (σ0 : σ) : CfgSafe Ext (Config.init s σ0) := by
  refine ⟨trivial, fun t a e => ?_⟩
  rw [Config.init_cont?] at e
  cases e

end Silmaril.Proofs.Wasm.Component.Reference.HostWrite
