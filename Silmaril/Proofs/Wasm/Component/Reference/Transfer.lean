module

public import Silmaril.Wasm.Component.Reference.Machine.Transfer.Defs
public meta import Lean

/-!
# Proofs: the component machine over `E.withStore I` is simulated by the machine over `E`

* Programs: `ProgRel.bind` and the primitive operations (`rel_getStore_bind`, `rel_modifyStore`,
  `rel_callRet`, …); the host-frame programs `invokeProg`, `cancelProg`, `runProg` and
  `tickProg` are related to themselves.
* Configurations: inversion of the running activation (`ctl_prog`, `ctl_core`), saved
  continuations (`setSlot`, `cont?`).
* `step_sim`: every step of `E.withStore I` from a configuration related to `m` is matched by a
  step of `E` from `m` with a related label, given related dispatchers. `steps_sim`: runs.
-/

open Lean Elab Tactic Meta in
/-- Close `a = b` by `Eq.refl a`, leaving the definitional check to the kernel. The elaborator
does not unfold two instances of one matcher at different engines (`E` and `E.withStore I`)
when the discriminant is stuck, although the kernel does. -/
elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let some (_, a, _) := (← whnfR (← g.getType)).eq? | throwError "kernel_rfl: not an equation"
  g.assign (← mkEqRefl a)
  replaceMainGoal []

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Transfer

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Value Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
  Silmaril.Wasm.Component.Machine.Transfer Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {I : E.StoreImpl} (S : E.StoreSim I) {σ : Type}

local notation "E'" => CoreEngine.withStore E I

/-! ## Programs -/

theorem ProgRel.bind {α β : Type} {p' : P E' σ α} {p : P E σ α} (h : ProgRel S p' p)
    {f' : α → P E' σ β} {f : α → P E σ β} (hf : ∀ a, ProgRel S (f' a) (f a)) :
    ProgRel S (p' >>= f') (p >>= f) := by
  induction h with
  | pure a => exact hf a
  | get _ ih => exact .get fun s => ih s
  | modify hc _ ih => exact .modify hc ih
  | trap r k k' => exact .trap r _ _
  | choose ck _ ih => exact .choose ck fun r => ih r
  | callCore f args _ ih => exact .callCore f args fun r => ih r
  | call c _ ih => exact .call c fun r => ih r
  | currentThread _ ih => exact .currentThread fun r => ih r
  | newThread b _ ih => exact .newThread b fun r => ih r
  | block sw _ ih => exact .block sw ih
  | resumeThread t _ ih => exact .resumeThread t ih
  | hostGet _ ih => exact .hostGet fun r => ih r
  | hostSet h _ ih => exact .hostSet h ih
  | emit o _ ih => exact .emit o ih

theorem ProgRel.pure' {α : Type} (a : α) : ProgRel S (Pure.pure a : P E' σ α) (Pure.pure a) :=
  .pure a

theorem rel_getStore_bind {α : Type} {k' : CStore E' → P E' σ α} {k : CStore E → P E σ α}
    (h : ∀ s, ProgRel S (k' s) (k (mapStore S s))) :
    ProgRel S (getStore >>= k') (getStore >>= k) :=
  .get h

theorem rel_modifyStore {f' : CStore E' → CStore E'} {f : CStore E → CStore E}
    (h : ∀ s, mapStore S (f' s) = f (mapStore S s)) :
    ProgRel S (modifyStore f' : P E' σ Unit) (modifyStore f) :=
  .modify h (.pure ())

theorem rel_callRet (c : Call E) :
    ProgRel S (callRet c : P E' σ (Ret E')) (callRet c : P E σ (Ret E)) :=
  .call c fun r => .pure r

theorem rel_choose (ck : ChoiceKind) :
    ProgRel S (Canon.choose ck : P E' σ ck.Resp) (Canon.choose ck) :=
  .choose ck fun r => .pure r

theorem rel_hostGet : ProgRel S (hostGet : P E' σ σ) hostGet := .hostGet fun r => .pure r

theorem rel_resumeThread (t : ThreadId) :
    ProgRel S (resumeThread t : P E' σ Unit) (resumeThread t) := .resumeThread t (.pure ())

/-! ## Store updates that do not touch the core store -/

theorem mapStore_threadStatusSt (t : ThreadId) (st : ThreadStatus) (s : CStore E') :
    mapStore S (threadStatusSt t st s) = threadStatusSt t st (mapStore S s) := rfl

theorem mapStore_lockdownSt (s : CStore E') : mapStore S (lockdownSt s) = lockdownSt (mapStore S s) :=
  rfl

theorem mapStore_enterHostSt (s : CStore E') :
    mapStore S (enterHostSt s) = enterHostSt (mapStore S s) := rfl

theorem mapStore_leaveHostSt (s : CStore E') :
    mapStore S (leaveHostSt s) = leaveHostSt (mapStore S s) := rfl

theorem mapStore_stopWaitingSt (t : ThreadId) (s : CStore E') :
    mapStore S (s.stopWaitingSt t) = (mapStore S s).stopWaitingSt t := rfl

theorem mapStore_allocCaller (x : Caller E) (s : CStore E') :
    mapStore S (ArenaOps.allocSt ArenaField.callers x s) =
      ArenaOps.allocSt ArenaField.callers x (mapStore S s) := rfl

theorem candidates_mapStore (hr : Nat → Bool) (s : CStore E') :
    (mapStore S s).candidates hr = s.candidates hr := by
  kernel_rfl

theorem threadIs_mapStore (p : Thread → Bool) (t : ThreadId) (s : CStore E') :
    (mapStore S s).threadIs p t = s.threadIs p t := by
  kernel_rfl

/-! ## The host-frame programs -/

theorem rel_invokeProg (c : CallId) (f : FuncId) (args : List Val) :
    ProgRel S (invokeProg c f args : P E' σ (Ret E')) (invokeProg c f args) := by
  refine rel_getStore_bind S fun s => ?_
  refine .modify (fun s => mapStore_allocCaller S _ s) ?_
  refine .modify (fun s => mapStore_enterHostSt S s) ?_
  refine .call _ fun r => ?_
  exact .modify (fun s => mapStore_leaveHostSt S s) (.pure r)

theorem rel_cancelProg (r : CancelRef) :
    ProgRel S (cancelProg r : P E' σ (Ret E')) (cancelProg r) := by
  refine .modify (fun s => mapStore_enterHostSt S s) ?_
  refine .call _ fun _ => ?_
  exact .modify (fun s => mapStore_leaveHostSt S s) (.pure _)

theorem rel_runProg {p' : P E' σ (Ret E')} {p : P E σ (Ret E)} (h : ProgRel S p' p) :
    ProgRel S (runProg p') (runProg p) :=
  ProgRel.bind S h fun _ => .pure _

theorem rel_resume (t : ThreadId) :
    ProgRel S (Thread.resume t : P E' σ Unit) (Thread.resume t) := by
  refine rel_getStore_bind S fun s => ?_
  rw [threadIs_mapStore]
  split
  · exact .modify (fun s => mapStore_stopWaitingSt S t s) (rel_resumeThread S t)
  · exact rel_resumeThread S t

theorem rel_tickProg (hr : HostReady σ) :
    ProgRel S (tickProg hr : P E' σ (Ret E')) (tickProg hr) := by
  refine .modify (fun s => mapStore_enterHostSt S s) ?_
  refine rel_getStore_bind S fun s => ?_
  refine ProgRel.bind S (rel_hostGet S) fun h => ?_
  rw [candidates_mapStore]
  split
  · exact .modify (fun s => mapStore_leaveHostSt S s) (.pure _)
  · refine ProgRel.bind S (ProgRel.bind S (rel_choose S _) fun _ => .pure _) fun t => ?_
    refine ProgRel.bind S (rel_resume S t) fun _ => ?_
    exact .modify (fun s => mapStore_leaveHostSt S s) (.pure _)

/-! ## Inversion of related programs -/

section Inv

variable {S} {α : Type}

theorem inv_pure {a : α} {p : P E σ α} (h : ProgRel S (.pure a : P E' σ α) p) : p = .pure a := by
  cases h; rfl

theorem inv_get {k' : CStore E' → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) .get k') p) :
    ∃ k, p = .op (S := Eff E σ) .get k ∧ ∀ s, ProgRel S (k' s) (k (mapStore S s)) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_modify {f' : CStore E' → CStore E'} {k' : Unit → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.modify f') k') p) :
    ∃ f k, p = .op (S := Eff E σ) (.modify f) k ∧ (∀ s, mapStore S (f' s) = f (mapStore S s)) ∧
      ProgRel S (k' ()) (k ()) := by
  cases h; exact ⟨_, _, rfl, ‹_›, ‹_›⟩

theorem inv_trap {r : TrapReason} {k' : Empty → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.trap r) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.trap r) k := by
  cases h; exact ⟨_, rfl⟩

theorem inv_choose {ck : ChoiceKind} {k' : ck.Resp → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.choose ck) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.choose ck) k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_callCore {f : E.FuncAddr} {args : List FlatValue} {k' : List FlatValue → P E' σ α}
    {p : P E σ α} (h : ProgRel S (.op (S := Eff E' σ) (.callCore f args) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.callCore f args) k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_call {c : Call E} {k' : Ret E → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.call c) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.call c) k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_currentThread {k' : Option ThreadId → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) .currentThread k') p) :
    ∃ k, p = .op (S := Eff E σ) .currentThread k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_newThread {b : ThreadBody E} {k' : ThreadId → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.newThread b) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.newThread b) k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_block {sw : Option ThreadId} {k' : Unit → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.block sw) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.block sw) k ∧ ProgRel S (k' ()) (k ()) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_resumeThread {t : ThreadId} {k' : Unit → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.resumeThread t) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.resumeThread t) k ∧ ProgRel S (k' ()) (k ()) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_hostGet {k' : σ → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) .hostGet k') p) :
    ∃ k, p = .op (S := Eff E σ) .hostGet k ∧ ∀ r, ProgRel S (k' r) (k r) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_hostSet {x : σ} {k' : Unit → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.hostSet x) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.hostSet x) k ∧ ProgRel S (k' ()) (k ()) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

theorem inv_emit {o : HostObs} {k' : Unit → P E' σ α} {p : P E σ α}
    (h : ProgRel S (.op (S := Eff E' σ) (.emit o) k') p) :
    ∃ k, p = .op (S := Eff E σ) (.emit o) k ∧ ProgRel S (k' ()) (k ()) := by
  cases h; exact ⟨_, rfl, ‹_›⟩

end Inv

/-! ## Configurations -/

section Cfg

variable {S}

theorem forall₂_setSlot {α β : Type} {R : α → β → Prop} {xs : List (Option α)}
    {ys : List (Option β)} (h : List.Forall₂ (Option.Rel R) xs ys) (i : Nat) {a : Option α}
    {b : Option β} (hab : Option.Rel R a b) :
    List.Forall₂ (Option.Rel R) (Config.setSlot xs i a) (Config.setSlot ys i b) := by
  induction h generalizing i with
  | nil =>
    induction i with
    | zero => exact .cons hab .nil
    | succ i ih => exact .cons .none ih
  | cons hxy _ ih =>
    cases i with
    | zero => exact .cons hab ‹_›
    | succ i => exact .cons hxy (ih i)

theorem rel_getElem?_join {α β : Type} {R : α → β → Prop} {xs : List (Option α)}
    {ys : List (Option β)} (h : List.Forall₂ (Option.Rel R) xs ys) (i : Nat) :
    Option.Rel R (xs[i]?).join (ys[i]?).join := by
  induction h generalizing i with
  | nil => exact .none
  | cons hxy _ ih =>
    cases i with
    | zero => simpa using hxy
    | succ i => simpa using ih i

theorem cfgRel_setCont {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) (t : ThreadId)
    {a' : Option (Activation E' σ)} {a : Option (Activation E σ)} (ha : Option.Rel (ActRel S) a' a) :
    CfgRel S (m'.setCont t a') (m.setCont t a) :=
  { hm with conts := forall₂_setSlot hm.conts t.idx ha }

theorem cfgRel_cont? {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) (t : ThreadId) :
    Option.Rel (ActRel S) (m'.cont? t) (m.cont? t) :=
  rel_getElem?_join hm.conts t.idx

theorem cont?_some {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) {t : ThreadId}
    {b' : Activation E' σ} (h : m'.cont? t = some b') : ∃ b, m.cont? t = some b ∧ ActRel S b' b := by
  have := cfgRel_cont? hm t
  rw [h] at this
  generalize m.cont? t = x at this ⊢
  cases this with
  | some hb => exact ⟨_, rfl, hb⟩

theorem cont?_none {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) {t : ThreadId}
    (h : m'.cont? t = none) : m.cont? t = none := by
  have := cfgRel_cont? hm t
  rw [h] at this
  generalize m.cont? t = x at this ⊢
  cases this
  rfl

theorem ctl_prog {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) {th p' segs' rest'}
    (hc : m'.ctl = ⟨th, .prog p', segs'⟩ :: rest') :
    ∃ p segs rest, m.ctl = ⟨th, .prog p, segs⟩ :: rest ∧ ProgRel S p' p ∧
      List.Forall₂ (SegRel S) segs' segs ∧ List.Forall₂ (ActRel S) rest' rest := by
  have h := hm.ctl
  rw [hc] at h
  obtain ⟨⟨th₀, f, segs⟩, rest, ⟨ht, hf, hs⟩, hr, he⟩ :
      ∃ a rest, ActRel S ⟨th, .prog p', segs'⟩ a ∧ List.Forall₂ (ActRel S) rest' rest ∧
        m.ctl = a :: rest := by
    generalize hl : m.ctl = l at h
    cases h with
    | cons ha hr => exact ⟨_, _, ha, hr, rfl⟩
  cases f with
  | prog p => exact ⟨p, segs, rest, by rw [he]; cases ht; rfl, hf, hs, hr⟩
  | core => exact hf.elim

theorem ctl_core {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) {th ct k' segs' rest'}
    (hc : m'.ctl = ⟨th, .core ct k', segs'⟩ :: rest') :
    ∃ k segs rest, m.ctl = ⟨th, .core ct k, segs⟩ :: rest ∧ (∀ vs, ProgRel S (k' vs) (k vs)) ∧
      List.Forall₂ (SegRel S) segs' segs ∧ List.Forall₂ (ActRel S) rest' rest := by
  have h := hm.ctl
  rw [hc] at h
  obtain ⟨⟨th₀, f, segs⟩, rest, ⟨ht, hf, hs⟩, hr, he⟩ :
      ∃ a rest, ActRel S ⟨th, .core ct k', segs'⟩ a ∧ List.Forall₂ (ActRel S) rest' rest ∧
        m.ctl = a :: rest := by
    generalize hl : m.ctl = l at h
    cases h with
    | cons ha hr => exact ⟨_, _, ha, hr, rfl⟩
  cases f with
  | prog p => exact hf.elim
  | core t k =>
    obtain ⟨rfl, hk⟩ := hf
    exact ⟨k, segs, rest, by rw [he]; cases ht; rfl, hk, hs, hr⟩

theorem segs_prog {k' : Ret E' → P E' σ (Ret E')} {segs' : List (Seg E' σ)} {segs : List (Seg E σ)}
    (h : List.Forall₂ (SegRel S) (.prog k' :: segs') segs) :
    ∃ k segs₀, segs = .prog k :: segs₀ ∧ (∀ r : Ret E, ProgRel S (k' r) (k r)) ∧
      List.Forall₂ (SegRel S) segs' segs₀ := by
  cases h with
  | cons hs hr =>
    rename_i s _
    cases s with
    | prog k => exact ⟨k, _, rfl, hs, hr⟩
    | core => exact hs.elim

theorem segs_core {ct} {k' : List FlatValue → P E' σ (Ret E')} {segs' : List (Seg E' σ)}
    {segs : List (Seg E σ)} (h : List.Forall₂ (SegRel S) (.core ct k' :: segs') segs) :
    ∃ k segs₀, segs = .core ct k :: segs₀ ∧ (∀ vs, ProgRel S (k' vs) (k vs)) ∧
      List.Forall₂ (SegRel S) segs' segs₀ := by
  cases h with
  | cons hs hr =>
    rename_i s _
    cases s with
    | prog k => exact hs.elim
    | core t k =>
      obtain ⟨rfl, hk⟩ := hs
      exact ⟨k, _, rfl, hk, hr⟩

theorem segs_nil {segs : List (Seg E σ)} (h : List.Forall₂ (SegRel S) ([] : List (Seg E' σ)) segs) :
    segs = [] := by
  cases h; rfl

theorem cfgRel_hostReady {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m)
    (h : HostReadyCfg m') : HostReadyCfg m := by
  obtain ⟨hc, hl, hn⟩ := h
  have hctl := hm.ctl
  rw [hc] at hctl
  generalize hc' : m.ctl = l at hctl
  cases hctl
  refine ⟨hc', ?_, ?_⟩ <;> rw [hm.store]
  · exact hl
  · exact hn

theorem cfgRel_trapCfg {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) :
    CfgRel S (trapCfg m') (trapCfg m) :=
  { hm with
    store := by rw [StepDefs.trapCfg, StepDefs.trapCfg, hm.store]; rfl
    ctl := .nil }

theorem cfgRel_hostFinish {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) (r : Ret E)
    {rest' rest} (hr : List.Forall₂ (ActRel S) rest' rest) :
    CfgRel S (StepDefs.hostFinish r rest' m') (StepDefs.hostFinish r rest m) := by
  have hl : lastCall? m' = lastCall? m := by unfold lastCall?; rw [hm.pending]
  have base : CfgRel S { m' with ctl := rest' } { m with ctl := rest } := { hm with ctl := hr }
  unfold StepDefs.hostFinish
  rw [hl]
  cases hr with
  | nil =>
    cases r <;> (try exact base)
    cases lastCall? m with
    | none => exact base
    | some c =>
      exact { base with cancels := by show _ :: _ = _ :: _; rw [hm.cancels] }
  | cons => exact base

theorem cfgRel_observe {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) (o : HostObs) :
    CfgRel S (StepDefs.observe m' o) (StepDefs.observe m o) := by
  cases o <;> first
    | exact hm
    | exact { hm with results := by show _ ++ _ = _ ++ _; rw [hm.results] }

end Cfg

theorem threadBody_task (b : ThreadBody E) :
    ThreadBody.task (E := E') b = ThreadBody.task (E := E) b := by
  cases b <;> rfl

theorem alloc_threads_mapStore (s : CStore E') (x : Runtime.Thread) :
    ArenaField.threads.alloc (mapStore S s) x =
      (mapStore S (ArenaField.threads.alloc s x).1, (ArenaField.threads.alloc s x).2) := rfl

/-! ## Labels -/

section Labels

variable {S}

theorem labelRel_tau {l : Label E σ} (h : LabelRel S .tau l) : l = .tau := by
  cases l <;> first | rfl | exact h.elim

theorem labelRel_core {l : Label E σ} (h : LabelRel S .core l) : l = .core := by
  cases l <;> first | rfl | exact h.elim

theorem labelRel_trap {r : TrapReason} {l : Label E σ} (h : LabelRel S (.trap r) l) :
    l = .trap r := by
  cases l <;> first | exact h.elim | (cases h; rfl)

theorem labelRel_obs {o : HostObs} {l : Label E σ} (h : LabelRel S (.obs o) l) : l = .obs o := by
  cases l <;> first | exact h.elim | (cases h; rfl)

theorem labelRel_choice {ck : ChoiceKind} {r : ck.Resp} {l : Label E σ}
    (h : LabelRel S (.choice ck r) l) : l = .choice ck r := by
  cases l <;> first | exact h.elim | (cases h; rfl)

theorem labelRel_host {ev' : HostEvent E' σ} {l : Label E σ} (h : LabelRel S (.host ev') l) :
    ∃ ev, l = .host ev ∧ EventRel S ev' ev := by
  cases l <;> first | exact h.elim | exact ⟨_, rfl, h⟩

theorem eventRel_invoke {c f args} {ev : HostEvent E σ}
    (h : EventRel S (.invoke c f args : HostEvent E' σ) ev) : ev = .invoke c f args := by
  cases ev <;> first | exact h.elim | (obtain ⟨rfl, rfl, rfl⟩ := h; rfl)

theorem eventRel_tick {ev : HostEvent E σ} (h : EventRel S (.tick : HostEvent E' σ) ev) :
    ev = .tick := by
  cases ev <;> first | rfl | exact h.elim

theorem eventRel_cancel {c} {ev : HostEvent E σ} (h : EventRel S (.cancel c : HostEvent E' σ) ev) :
    ev = .cancel c := by
  cases ev <;> first | exact h.elim | (cases h; rfl)

theorem eventRel_run {p'} {ev : HostEvent E σ} (h : EventRel S (.run p' : HostEvent E' σ) ev) :
    ∃ p, ev = .run p ∧ ProgRel S p' p := by
  cases ev <;> first | exact h.elim | exact ⟨_, rfl, h⟩

end Labels

/-! ## Traces without `run` events -/

section Traces

theorem labelRel_labelOf {l : Label E' σ} (h : ∀ p, l ≠ .host (.run p)) :
    LabelRel S l (labelOf l) := by
  rcases l with _ | _ | ev | _ | _ | _
  · trivial
  · rfl
  · rcases ev with _ | _ | _ | p
    · exact ⟨rfl, rfl, rfl⟩
    · trivial
    · rfl
    · exact (h p rfl).elim
  · rfl
  · rfl
  · trivial

theorem forall₂_labelOf {tr : List (Label E' σ)} (h : ∀ p, Label.host (.run p) ∉ tr) :
    List.Forall₂ (LabelRel S) tr (tr.map labelOf) := by
  induction tr with
  | nil => exact .nil
  | cons l tr ih =>
    refine .cons (labelRel_labelOf S fun p hp => h p (hp ▸ List.mem_cons_self)) (ih fun p hp => ?_)
    exact h p (List.mem_cons_of_mem _ hp)

theorem obs?_labelOf (l : Label E' σ) : (labelOf l : Label E σ).obs? = l.obs? := by
  rcases l with _ | _ | ev | _ | _ | _
  · rfl
  · rfl
  · rcases ev <;> rfl
  · rfl
  · rfl
  · rfl

theorem traceObs_map_labelOf (tr : List (Label E' σ)) :
    traceObs (tr.map labelOf : List (Label E σ)) = traceObs tr := by
  induction tr with
  | nil => rfl
  | cons l tr ih =>
    simp only [List.map_cons, traceObs, List.filterMap_cons] at ih ⊢
    rw [obs?_labelOf, ih]

theorem labelOf_host {l : Label E' σ} {ev : HostEvent E σ} (h : labelOf l = .host ev) :
    ∃ ev', l = .host ev' := by
  rcases l with _ | _ | ev' | _ | _ | _ <;> first | exact ⟨_, rfl⟩ | cases h

end Traces

/-! ## The step simulation -/

section Sim

variable {S} {prof : ProfileKind} {hr : HostReady σ}
  {d' : Call (E.withStore I) → P (E.withStore I) σ (Ret (E.withStore I))}
  {d : Call E → P E σ (Ret E)}

theorem fault_sim {m' : Config E' σ} {m : Config E σ} (hm : CfgRel S m' m) {msg : String}
    (h : Fault m' msg) : Fault m msg := by
  cases h with
  | blockNoThread hc =>
    obtain ⟨p, segs, rest, hc', hp, -, -⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, -⟩ := inv_block hp
    exact .blockNoThread hc'
  | switchMissing hc hn =>
    obtain ⟨p, segs, rest, hc', hp, hs, -⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_block hp
    exact .switchMissing hc' (cont?_none (cfgRel_setCont hm _ (.some (⟨rfl, hk, hs⟩ :
      ActRel S (blockedAct _ _ _) (blockedAct _ _ _)))) hn)
  | resumeMissing hc hn =>
    obtain ⟨p, segs, rest, hc', hp, -, -⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, -⟩ := inv_resumeThread hp
    exact .resumeMissing hc' (cont?_none hm hn)
  | calloutBadRet hc hne =>
    obtain ⟨p, segs, rest, hc', hp, hs, -⟩ := ctl_prog hm hc
    cases inv_pure hp
    obtain ⟨k, segs₀, rfl, -, -⟩ := segs_core hs
    exact .calloutBadRet hc' hne

/-- **One step of `E.withStore I` is matched by a step of `E`** from a related configuration,
with any related label, given related dispatchers. -/
theorem step_sim (hd : DispatchRel S d' d) {m' n' : Config E' σ} {l' : Label E' σ}
    (h : Step prof hr d' m' l' n') {m : Config E σ} (hm : CfgRel S m' m) {l : Label E σ}
    (hl : LabelRel S l' l) : ∃ n, Step prof hr d m l n ∧ CfgRel S n' n := by
  cases h with
  | popProg hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    cases inv_pure hp
    obtain ⟨k, segs₀, rfl, hk, hs⟩ := segs_prog hs
    exact ⟨_, .popProg hc', { hm with ctl := .cons ⟨rfl, hk _, hs⟩ hr }⟩
  | popCore hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    cases inv_pure hp
    obtain ⟨k, segs₀, rfl, hk, hs⟩ := segs_core hs
    refine ⟨_, .popCore hc', { hm with ctl := .cons ⟨rfl, ⟨?_, hk⟩, hs⟩ hr }⟩
    rw [hm.store]
    exact (S.resume _ _ _).symm
  | threadExit hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    cases inv_pure hp
    cases segs_nil hs
    exact ⟨_, .threadExit hc', { hm with
      store := by rw [hm.store]; exact (mapStore_threadStatusSt S _ _ _).symm
      ctl := hr }⟩
  | hostDone hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    cases inv_pure hp
    cases segs_nil hs
    exact ⟨_, .hostDone hc', cfgRel_hostFinish hm _ hr⟩
  | call hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_call hp
    exact ⟨_, .call hc', { hm with ctl := .cons ⟨rfl, hd _, .cons hk hs⟩ hr }⟩
  | callCore hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_callCore hp
    exact ⟨_, .callCore hc', { hm with ctl := .cons ⟨rfl, ⟨rfl, hk⟩, hs⟩ hr }⟩
  | @coreInternal _ ct₀ _ _ _ c₁ ct₁ hc hst hint =>
    cases labelRel_core hl
    obtain ⟨k, segs, rest, hc', hk, hs, hr⟩ := ctl_core hm hc
    have hst' : E.status m.store.core ct₀ = .running ∨ E.status m.store.core ct₀ = .stuck := by
      rw [hm.store]
      exact (S.status _ _).symm ▸ hst
    have hint' := S.internal hint
    refine ⟨_, .coreInternal (c' := S.φ c₁) (ct' := ct₁) hc' hst'
      (by rw [hm.store]; exact hint'), { hm with
      store := by rw [hm.store]; rfl
      ctl := .cons ⟨rfl, ⟨rfl, hk⟩, hs⟩ hr }⟩
  | @coreReturned _ ct₀ _ _ _ vs hc hst =>
    cases labelRel_tau hl
    obtain ⟨k, segs, rest, hc', hk, hs, hr⟩ := ctl_core hm hc
    have hst' : E.status m.store.core ct₀ = .returned (.values vs) := by
      rw [hm.store]
      exact (S.status _ _).trans hst
    exact ⟨_, .coreReturned hc' hst', { hm with ctl := .cons ⟨rfl, hk _, hs⟩ hr }⟩
  | @coreTrap _ ct₀ _ _ _ hc hst =>
    cases labelRel_trap hl
    obtain ⟨k, segs, rest, hc', hk, hs, hr⟩ := ctl_core hm hc
    have hst' : E.status m.store.core ct₀ = .returned .trap := by
      rw [hm.store]
      exact (S.status _ _).trans hst
    exact ⟨_, .coreTrap hc' hst', cfgRel_trapCfg hm⟩
  | @coreCallout _ ct₀ _ _ _ h₀ args₀ hc hst =>
    cases labelRel_tau hl
    obtain ⟨k, segs, rest, hc', hk, hs, hr⟩ := ctl_core hm hc
    have hst' : E.status m.store.core ct₀ = .callout h₀ args₀ := by
      rw [hm.store]
      exact (S.status _ _).trans hst
    exact ⟨_, .coreCallout hc' hst', { hm with
      ctl := .cons ⟨rfl, hd _, .cons ⟨rfl, hk⟩ hs⟩ hr }⟩
  | get hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_get hp
    refine ⟨_, .get hc', { hm with ctl := .cons ⟨rfl, ?_, hs⟩ hr }⟩
    rw [hm.store]
    exact hk _
  | modify hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨f, k, rfl, hf, hk⟩ := inv_modify hp
    exact ⟨_, .modify hc', { hm with
      store := by rw [hm.store]; exact (hf _).symm
      ctl := .cons ⟨rfl, hk, hs⟩ hr }⟩
  | trap hc =>
    cases labelRel_trap hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl⟩ := inv_trap hp
    exact ⟨_, .trap hc', cfgRel_trapCfg hm⟩
  | choose r hc hal =>
    cases labelRel_choice hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_choose hp
    exact ⟨_, .choose r hc' hal, { hm with ctl := .cons ⟨rfl, hk _, hs⟩ hr }⟩
  | currentThread hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_currentThread hp
    exact ⟨_, .currentThread hc', { hm with ctl := .cons ⟨rfl, hk _, hs⟩ hr }⟩
  | @newThread _ b₀ _ _ _ s₀ t₀ hc halloc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_newThread hp
    have halloc' : ArenaField.threads.alloc m.store { task := ThreadBody.task (E := E) b₀ } =
        (mapStore S s₀, t₀) := by
      rw [hm.store, alloc_threads_mapStore, ← threadBody_task, halloc]
    have hc2 := cfgRel_setCont hm t₀ (.some (⟨rfl, hd _, .nil⟩ :
      ActRel S (threadAct d' t₀ b₀) (threadAct d t₀ b₀)))
    exact ⟨_, .newThread hc' halloc', { hc2 with
      store := rfl
      ctl := .cons ⟨rfl, hk _, hs⟩ hr }⟩
  | @block t₀ _ _ _ hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_block hp
    have hc2 := cfgRel_setCont hm t₀ (.some (⟨rfl, hk, hs⟩ :
      ActRel S (blockedAct t₀ _ _) (blockedAct t₀ _ _)))
    exact ⟨_, .block hc', { hc2 with
      store := by rw [hm.store]; exact (mapStore_threadStatusSt S _ _ _).symm
      ctl := hr }⟩
  | @blockSwitch t₀ o₀ _ _ _ _ hc hb =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_block hp
    have hc2 := cfgRel_setCont hm t₀ (.some (⟨rfl, hk, hs⟩ :
      ActRel S (blockedAct t₀ _ _) (blockedAct t₀ _ _)))
    obtain ⟨b, hb', hbr⟩ := cont?_some hc2 hb
    have hc3 := cfgRel_setCont hc2 o₀ (.none : Option.Rel (ActRel S) none none)
    exact ⟨_, .blockSwitch hc' hb', { hc3 with
      store := by
        rw [hm.store]
        exact ((mapStore_threadStatusSt S _ _ _).trans
          (congrArg _ (mapStore_threadStatusSt S _ _ _))).symm
      ctl := .cons hbr hr }⟩
  | @resumeThread _ t₀ _ _ _ _ hc hb =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_resumeThread hp
    obtain ⟨b, hb', hbr⟩ := cont?_some hm hb
    have hc2 := cfgRel_setCont hm t₀ (.none : Option.Rel (ActRel S) none none)
    exact ⟨_, .resumeThread hc' hb', { hc2 with
      store := by rw [hm.store]; exact (mapStore_threadStatusSt S _ _ _).symm
      ctl := .cons hbr (.cons ⟨rfl, hk, hs⟩ hr) }⟩
  | hostGet hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_hostGet hp
    refine ⟨_, .hostGet hc', { hm with ctl := .cons ⟨rfl, ?_, hs⟩ hr }⟩
    rw [← hm.host]
    exact hk _
  | hostSet hc =>
    cases labelRel_tau hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_hostSet hp
    exact ⟨_, .hostSet hc', { hm with host := rfl, ctl := .cons ⟨rfl, hk, hs⟩ hr }⟩
  | emit hc =>
    cases labelRel_obs hl
    obtain ⟨p, segs, rest, hc', hp, hs, hr⟩ := ctl_prog hm hc
    obtain ⟨k, rfl, hk⟩ := inv_emit hp
    exact ⟨_, .emit hc', { cfgRel_observe hm _ with ctl := .cons ⟨rfl, hk, hs⟩ hr }⟩
  | fault hf =>
    cases labelRel_trap hl
    exact ⟨_, .fault (fault_sim hm hf), cfgRel_trapCfg hm⟩
  | hostInvoke hready hfresh =>
    obtain ⟨ev, rfl, hev⟩ := labelRel_host hl
    cases eventRel_invoke hev
    refine ⟨_, .hostInvoke (cfgRel_hostReady hm hready) (hm.pending ▸ hfresh), { hm with
      pending := by rw [hm.pending]
      ctl := .cons ⟨rfl, rel_invokeProg S _ _ _, .nil⟩ .nil }⟩
  | hostTick hready =>
    obtain ⟨ev, rfl, hev⟩ := labelRel_host hl
    cases eventRel_tick hev
    exact ⟨_, .hostTick (cfgRel_hostReady hm hready), { hm with
      ctl := .cons ⟨rfl, rel_tickProg S hr, .nil⟩ .nil }⟩
  | @hostCancel c₀ r₀ hready hc hres =>
    obtain ⟨ev, rfl, hev⟩ := labelRel_host hl
    cases eventRel_cancel hev
    have hc' : m.cancel? c₀ = some r₀ := by unfold Config.cancel?; rw [← hm.cancels]; exact hc
    have hres' : m.result? c₀ = none := by unfold Config.result?; rw [← hm.results]; exact hres
    exact ⟨_, .hostCancel (cfgRel_hostReady hm hready) hc' hres', { hm with
      cancels := by show List.filter _ _ = List.filter _ _; rw [hm.cancels]
      ctl := .cons ⟨rfl, rel_cancelProg S _, .nil⟩ .nil }⟩
  | hostRun hready =>
    obtain ⟨ev, rfl, hev⟩ := labelRel_host hl
    obtain ⟨p, rfl, hp⟩ := eventRel_run hev
    exact ⟨_, .hostRun (cfgRel_hostReady hm hready), { hm with
      ctl := .cons ⟨rfl, rel_runProg S hp, .nil⟩ .nil }⟩

/-- **Runs of `E.withStore I` are matched by runs of `E`** with related traces. -/
theorem steps_sim (hd : DispatchRel S d' d) {m' n' : Config E' σ} {tr' : List (Label E' σ)}
    (h : Steps prof hr d' m' tr' n') {m : Config E σ} (hm : CfgRel S m' m)
    {tr : List (Label E σ)} (htr : List.Forall₂ (LabelRel S) tr' tr) :
    ∃ n, Steps prof hr d m tr n ∧ CfgRel S n' n := by
  induction h generalizing m tr with
  | refl => cases htr; exact ⟨_, .refl _, hm⟩
  | cons hs _ ih =>
    cases htr with
    | cons hl htr =>
      obtain ⟨n₁, hs₁, hm₁⟩ := step_sim hd hs hm hl
      obtain ⟨n, hs₂, hm₂⟩ := ih hm₁ htr
      exact ⟨n, .cons hs₁ hs₂, hm₂⟩

end Sim

end Silmaril.Proofs.Wasm.Component.Reference.Transfer
