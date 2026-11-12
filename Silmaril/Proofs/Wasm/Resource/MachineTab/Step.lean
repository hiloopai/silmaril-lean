module

public import Silmaril.Proofs.Wasm.Resource.MachineTab.Frame
public import Silmaril.Wasm.Component.Reference.Laws.Thms

/-!
# Handle tables along whole machine runs: every machine rule

`step_cfgTab` and `step_tabMove` go through the 31 rules of `Machine.Step`: the rules that
replace the running program by a continuation keep `CfgTab` (the continuations of a
table-moving program are table-moving), `call`/`coreCallout` push a dispatched program
(`TabDispatch`), `newThread` saves a dispatched thread body, `block`/`blockSwitch`/
`resumeThread` move activations between the control chain and the saved continuations, and
the host events start the host-frame programs. Only `modify` changes an instance table, by a
table move (`TabProg.modify`); the other store updates (thread statuses, the core store, the
lockdown flag, thread allocation) leave the instance arena unchanged. `steps_tab`: the same for
runs; `steps_init_tab`: a run from the initial configuration keeps every handle table on a
successful history from `Table.empty`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Resource

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {j : InstId}
variable {prof : ProfileKind} {hr : HostReady σ} {dispatch : Call E → P E σ (Ret E)}

/-! ## Configurations -/

theorem cfgTab_head {m : Config E σ} {a : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgTab j m) (hc : m.ctl = a :: rest) : ActTab j a ∧ ∀ b ∈ rest, ActTab j b :=
  List.forall_mem_cons.1 (hc ▸ hm.1)

/-- Replace the running activation and the store. -/
theorem cfgTab_set {m : Config E σ} {a a' : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgTab j m) (hc : m.ctl = a :: rest) (ha : ActTab j a → ActTab j a') (s' : CStore E) :
    CfgTab j { m with store := s', ctl := a' :: rest } :=
  ⟨List.forall_mem_cons.2 ⟨ha (cfgTab_head hm hc).1, (cfgTab_head hm hc).2⟩, hm.2⟩

/-- Pop the running activation. -/
theorem cfgTab_pop {m : Config E σ} {a : Activation E σ} {rest : List (Activation E σ)}
    (hm : CfgTab j m) (hc : m.ctl = a :: rest) (s' : CStore E) :
    CfgTab j { m with store := s', ctl := rest } :=
  ⟨(cfgTab_head hm hc).2, hm.2⟩

/-- A host frame running `p`. -/
theorem cfgTab_host {m : Config E σ} (hm : CfgTab j m) {p : P E σ (Ret E)} (hp : TabProg j p) :
    CfgTab j { m with ctl := [.ofProg none p] } :=
  ⟨List.forall_mem_cons.2 ⟨⟨hp, fun _ h => nomatch h⟩, fun _ h => nomatch h⟩, hm.2⟩

theorem cont?_setCont (m : Config E σ) (t u : ThreadId) (v : Option (Activation E σ)) :
    (m.setCont t v).cont? u = if u = t then v else m.cont? u := by
  by_cases h : u = t
  · subst h
    simp
  · simp [h, Config.cont?_setCont_ne _ _ _ _ h]

theorem conts_setCont {m : Config E σ} (hm : ∀ t a, m.cont? t = some a → ActTab j a)
    {t : ThreadId} {v : Option (Activation E σ)} (hv : ∀ b, v = some b → ActTab j b) :
    ∀ u b, (m.setCont t v).cont? u = some b → ActTab j b := by
  intro u b hb
  rw [cont?_setCont] at hb
  split at hb
  · exact hv b hb
  · exact hm u b hb

/-! ## Activations -/

theorem actTab_op {th : Option ThreadId} {o : (Eff E σ).Op} {k : (Eff E σ).Resp o → P E σ (Ret E)}
    {segs : List (Seg E σ)} (h : ActTab j ⟨th, .prog (.op (S := Eff E σ) o k), segs⟩)
    (r : (Eff E σ).Resp o) : ActTab j ⟨th, .prog (k r), segs⟩ :=
  ⟨TabProg.cont h.1 r, h.2⟩

theorem actTab_popProg {th : Option ThreadId} {r : Ret E} {k : Ret E → P E σ (Ret E)}
    {segs : List (Seg E σ)} (h : ActTab j ⟨th, .prog (.pure r), .prog k :: segs⟩) :
    ActTab j ⟨th, .prog (k r), segs⟩ :=
  ⟨h.2 _ List.mem_cons_self r, fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩

theorem actTab_popCore {th : Option ThreadId} {r : Ret E} {ct ct' : E.Thread (CanonHost E)}
    {k : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    (h : ActTab j ⟨th, .prog (.pure r), .core ct k :: segs⟩) :
    ActTab j ⟨th, .core ct' k, segs⟩ :=
  ⟨h.2 _ List.mem_cons_self, fun g hg => h.2 g (List.mem_cons_of_mem _ hg)⟩

theorem actTab_call (hd : TabDispatch j dispatch) {th : Option ThreadId} {c : Call E}
    {k : Ret E → P E σ (Ret E)} {segs : List (Seg E σ)}
    (h : ActTab j ⟨th, .prog (.op (S := Eff E σ) (.call c) k), segs⟩) :
    ActTab j ⟨th, .prog (dispatch c), .prog k :: segs⟩ :=
  ⟨hd c, List.forall_mem_cons.2 ⟨fun r => TabProg.cont h.1 r, h.2⟩⟩

theorem actTab_callCore {th : Option ThreadId} {f : E.FuncAddr} {args : List FlatValue}
    {k : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)} {ct : E.Thread (CanonHost E)}
    (h : ActTab j ⟨th, .prog (.op (S := Eff E σ) (.callCore f args) k), segs⟩) :
    ActTab j ⟨th, .core ct k, segs⟩ :=
  ⟨fun vs => TabProg.cont h.1 vs, h.2⟩

theorem actTab_core {th : Option ThreadId} {ct ct' : E.Thread (CanonHost E)}
    {k : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    (h : ActTab j ⟨th, .core ct k, segs⟩) : ActTab j ⟨th, .core ct' k, segs⟩ := h

theorem actTab_coreReturned {th : Option ThreadId} {ct : E.Thread (CanonHost E)}
    {k : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    (h : ActTab j ⟨th, .core ct k, segs⟩) (vs : List FlatValue) :
    ActTab j ⟨th, .prog (k vs), segs⟩ := ⟨h.1 vs, h.2⟩

theorem actTab_coreCallout (hd : TabDispatch j dispatch) {th : Option ThreadId}
    {ct : E.Thread (CanonHost E)} {k : List FlatValue → P E σ (Ret E)} {segs : List (Seg E σ)}
    (h : ActTab j ⟨th, .core ct k, segs⟩) (c : Call E) :
    ActTab j ⟨th, .prog (dispatch c), .core ct k :: segs⟩ :=
  ⟨hd c, List.forall_mem_cons.2 ⟨h.1, h.2⟩⟩

theorem actTab_threadAct (hd : TabDispatch j dispatch) (t : ThreadId) (b : ThreadBody E) :
    ActTab j (threadAct dispatch t b) := ⟨hd _, fun _ h => nomatch h⟩

/-! ## The rules -/

theorem hostFinish_eq (r : Ret E) (rest : List (Activation E σ)) (m : Config E σ) :
    (hostFinish r rest m).store = m.store ∧ (hostFinish r rest m).conts = m.conts ∧
      (hostFinish r rest m).ctl = rest := by
  unfold hostFinish
  split <;> exact ⟨rfl, rfl, rfl⟩

theorem cfgTab_hostFinish {m : Config E σ} {r : Ret E} {rest : List (Activation E σ)}
    {a : Activation E σ} (hm : CfgTab j m) (hc : m.ctl = a :: rest) :
    CfgTab j (hostFinish r rest m) := by
  obtain ⟨-, hconts, hctl⟩ := hostFinish_eq r rest m
  refine ⟨fun b hb => (cfgTab_head hm hc).2 b (hctl ▸ hb), fun t b hb => hm.2 t b ?_⟩
  simpa [Config.cont?, hconts] using hb

theorem observe_eq (m : Config E σ) (o : HostObs) :
    (observe m o).store = m.store ∧ (observe m o).conts = m.conts := by
  cases o <;> exact ⟨rfl, rfl⟩

theorem cfgTab_emit {m : Config E σ} {o : HostObs} {th : Option ThreadId}
    {k : Unit → P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hm : CfgTab j m) (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.emit o) k), segs⟩ :: rest) :
    CfgTab j { observe m o with ctl := ⟨th, .prog (k ()), segs⟩ :: rest } := by
  obtain ⟨-, hconts⟩ := observe_eq m o
  refine ⟨List.forall_mem_cons.2 ⟨actTab_op (cfgTab_head hm hc).1 (), (cfgTab_head hm hc).2⟩,
    fun t b hb => hm.2 t b ?_⟩
  simpa [Config.cont?, hconts] using hb

theorem cfgTab_newThread (hd : TabDispatch j dispatch) {m : Config E σ} {th : Option ThreadId}
    {b : ThreadBody E} {k : ThreadId → P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {t : ThreadId} {s' : CStore E}
    (hm : CfgTab j m)
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.newThread b) k), segs⟩ :: rest) :
    CfgTab j { (m.setCont t (some (threadAct dispatch t b))) with
      store := s', ctl := ⟨th, .prog (k t), segs⟩ :: rest } :=
  ⟨List.forall_mem_cons.2 ⟨actTab_op (cfgTab_head hm hc).1 t, (cfgTab_head hm hc).2⟩,
    conts_setCont hm.2 fun _ e => Option.some.inj e ▸ actTab_threadAct hd t b⟩

theorem cfgTab_block {m : Config E σ} {t : ThreadId} {k : Unit → P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)} (hm : CfgTab j m)
    (hc : m.ctl = ⟨some t, .prog (.op (S := Eff E σ) (.block none) k), segs⟩ :: rest) :
    CfgTab j { (m.setCont t (some (blockedAct t k segs))) with
      store := threadStatusSt t .blocked m.store, ctl := rest } :=
  ⟨(cfgTab_head hm hc).2,
    conts_setCont hm.2 fun _ e => Option.some.inj e ▸ actTab_op (cfgTab_head hm hc).1 ()⟩

theorem cfgTab_blockSwitch {m : Config E σ} {t o : ThreadId} {k : Unit → P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)} {b : Activation E σ}
    (hm : CfgTab j m)
    (hc : m.ctl = ⟨some t, .prog (.op (S := Eff E σ) (.block (some o)) k), segs⟩ :: rest)
    (hb : (m.setCont t (some (blockedAct t k segs))).cont? o = some b) :
    CfgTab j { ((m.setCont t (some (blockedAct t k segs))).setCont o none) with
      store := threadStatusSt o .running (threadStatusSt t .blocked m.store)
      ctl := b :: rest } := by
  have h₁ : ∀ u a, (m.setCont t (some (blockedAct t k segs))).cont? u = some a → ActTab j a :=
    conts_setCont hm.2 fun _ e => Option.some.inj e ▸ actTab_op (cfgTab_head hm hc).1 ()
  exact ⟨List.forall_mem_cons.2 ⟨h₁ o b hb, (cfgTab_head hm hc).2⟩,
    conts_setCont h₁ fun _ e => nomatch e⟩

theorem cfgTab_resumeThread {m : Config E σ} {th : Option ThreadId} {t : ThreadId}
    {k : Unit → P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    {b : Activation E σ} (hm : CfgTab j m)
    (hc : m.ctl = ⟨th, .prog (.op (S := Eff E σ) (.resumeThread t) k), segs⟩ :: rest)
    (hb : m.cont? t = some b) :
    CfgTab j { (m.setCont t none) with
      store := threadStatusSt t .running m.store
      ctl := b :: ⟨th, .prog (k ()), segs⟩ :: rest } :=
  ⟨List.forall_mem_cons.2 ⟨hm.2 t b hb,
      List.forall_mem_cons.2 ⟨actTab_op (cfgTab_head hm hc).1 (), (cfgTab_head hm hc).2⟩⟩,
    conts_setCont hm.2 fun _ e => nomatch e⟩

theorem cfgTab_trapCfg {m : Config E σ} (hm : CfgTab j m) : CfgTab j (trapCfg m) :=
  ⟨fun _ h => (nomatch h), hm.2⟩

/-- **Every machine step keeps every program table-moving.** -/
theorem step_cfgTab (hd : TabDispatch j dispatch) {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') (hm : CfgTab j m)
    (hl : ∀ p, l = .host (.run p) → TabProg j p) : CfgTab j m' := by
  cases h with
  | popProg hc => exact cfgTab_set hm hc actTab_popProg m.store
  | popCore hc => exact cfgTab_set hm hc actTab_popCore m.store
  | threadExit hc => exact cfgTab_pop hm hc _
  | hostDone hc => exact cfgTab_hostFinish hm hc
  | call hc => exact cfgTab_set hm hc (actTab_call hd) m.store
  | callCore hc => exact cfgTab_set hm hc actTab_callCore m.store
  | coreInternal hc _ _ => exact cfgTab_set hm hc actTab_core _
  | coreReturned hc _ => exact cfgTab_set hm hc (fun h => actTab_coreReturned h _) m.store
  | coreTrap hc _ => exact cfgTab_trapCfg hm
  | coreCallout hc _ => exact cfgTab_set hm hc (fun h => actTab_coreCallout hd h _) m.store
  | get hc => exact cfgTab_set hm hc (fun h => actTab_op h _) m.store
  | modify hc => exact cfgTab_set hm hc (fun h => actTab_op h _) _
  | trap hc => exact cfgTab_trapCfg hm
  | choose r hc _ => exact cfgTab_set hm hc (fun h => actTab_op h r) m.store
  | currentThread hc => exact cfgTab_set hm hc (fun h => actTab_op h _) m.store
  | newThread hc _ => exact cfgTab_newThread hd hm hc
  | block hc => exact cfgTab_block hm hc
  | blockSwitch hc hb => exact cfgTab_blockSwitch hm hc hb
  | resumeThread hc hb => exact cfgTab_resumeThread hm hc hb
  | hostGet hc => exact cfgTab_set hm hc (fun h => actTab_op h _) m.store
  | hostSet hc => exact cfgTab_set hm hc (fun h => actTab_op h _) m.store
  | emit hc => exact cfgTab_emit hm hc
  | fault _ => exact cfgTab_trapCfg hm
  | hostInvoke _ _ => exact cfgTab_host hm (tabProg_invokeProg _ _ _)
  | hostTick _ => exact cfgTab_host hm (tabProg_tickProg hr)
  | hostCancel _ _ _ => exact cfgTab_host (m := m.dropCancel _) hm (tabProg_cancelProg _)
  | hostRun _ => exact cfgTab_host hm (tabProg_runProg (hl _ rfl))

theorem tabMove_alloc_threads (s s' : CStore E) (x : Thread) (t : ThreadId)
    (h : ArenaField.threads.alloc s x = (s', t)) : TabMove j s s' :=
  TabMove.of_insts <| by
    have e : (ArenaField.threads.alloc s x).1.insts = s'.insts := congrArg (fun p => p.1.insts) h
    exact e.symm.trans rfl

/-- **Every machine step moves every handle table by a successful history.** -/
theorem step_tabMove {m m' : Config E σ} {l : Label E σ} (h : Step prof hr dispatch m l m')
    (hm : CfgTab j m) : TabMove j m.store m'.store := by
  cases h with
  | hostDone => exact (hostFinish_eq _ _ m).1 ▸ TabMove.refl _
  | modify hc => exact TabProg.modify (cfgTab_head hm hc).1.1 m.store
  | newThread _ ht => exact tabMove_alloc_threads _ _ _ _ ht
  | emit => exact (observe_eq m _).1 ▸ TabMove.refl _
  | _ => exact TabMove.of_insts rfl

/-- **Runs.** -/
theorem steps_tab (hd : TabDispatch j dispatch) {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') (hm : CfgTab j m) (hl : RunTab j tr) :
    CfgTab j m' ∧ TabMove j m.store m'.store := by
  induction h with
  | refl => exact ⟨hm, TabMove.refl _⟩
  | cons s _ ih =>
    have hm₂ : CfgTab j _ := step_cfgTab hd s hm fun p e => hl p (e ▸ List.mem_cons_self)
    obtain ⟨hm', hmv⟩ := ih hm₂ fun p hp => hl p (List.mem_cons_of_mem _ hp)
    exact ⟨hm', (step_tabMove s hm).trans hmv⟩

theorem cfgTab_init (s : CStore E) (σ0 : σ) : CfgTab j (Config.init s σ0) := by
  refine ⟨fun _ h => (nomatch h), fun t a e => ?_⟩
  rw [Config.init_cont?] at e
  cases e

theorem vtab_empty : vtab (CStore.empty (E := E)) j = Silmaril.Wasm.Component.Runtime.Table.empty := rfl

/-- **From the initial configuration**: every machine run with a table-moving dispatcher
keeps the handle table of every instance on a successful history from `Table.empty`. -/
theorem steps_init_tab (hd : TabDispatch j dispatch) {σ0 : σ} {m' : Config E σ}
    {tr : List (Label E σ)} (h : Steps prof hr dispatch (Config.init CStore.empty σ0) tr m')
    (hl : RunTab j tr) : ∃ evs, Silmaril.Wasm.Component.Runtime.Table.Steps Silmaril.Wasm.Component.Runtime.Table.empty evs (vtab m'.store j) :=
  vtab_empty (j := j) ▸ (steps_tab hd h (cfgTab_init _ _) hl).2

end Silmaril.Wasm.Resource
