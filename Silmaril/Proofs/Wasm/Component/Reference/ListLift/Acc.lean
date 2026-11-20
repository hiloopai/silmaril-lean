module

public import Silmaril.Proofs.Wasm.Component.Reference.CallRun

/-!
# Accepting runs of the copied component machine, program by program

Only *accepting* runs of a call matter for `CallPhaseL`: those that end with the host in
control, no lockdown, and top-level call `0` resolved with `[true]` (`Accepting`). This file
gives a small program logic for them, generic in the engine and the dispatcher:

* `Acc m Q`: every accepting run from `m` yields `Q`. It is closed under unique steps
  backwards from live configurations (`acc_step`, `acc_prog`), holds trivially after a machine
  trap (`acc_trapCfg`), and is inherited by a core activation from what follows its returns,
  given that it never calls out (`acc_core`);
* `Spec th p m R`: running the program `p` on thread `th` from `m`, in any context, only
  continues (towards acceptance) at results `a` and configurations `m'` with `R a m'`, the
  lockdown flag still clear and the resolutions unchanged. Traps impose nothing
  (`Spec.trap`), so a check on an accepting path may be assumed to pass. `Spec` composes
  (`Spec.bind`, `Spec.mono`) and has rules for the effects: store access, the current thread,
  observations that are not resolutions, late-bound calls (`Spec.call`), thread creation and
  resumption of a thread whose body has a `Spec` (`Spec.newThread`, `Spec.resumeThread`), and
  core calls (`Spec.callCore`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.ListLift

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs
open Silmaril.Proofs.Wasm.Component.Reference

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- An accepting final configuration: the host in control, no lockdown, top-level call `0`
resolved with `[true]`. -/
def Accepting (m : Config E σ) : Prop :=
  m.ctl = [] ∧ m.store.lockdown = false ∧ m.result? ⟨0⟩ = some (some [.bool true])

variable (prof hr dispatch) in
/-- Every accepting run from `m` yields `Q`. -/
def Acc (m : Config E σ) (Q : Prop) : Prop :=
  ∀ tr m', Steps prof hr dispatch m tr m' → Accepting m' → Q

variable (prof hr dispatch) in
/-- Running `p` on thread `th` from `m` (in any context) continues only at results `a` and
configurations `m'` with `R a m'`, with the lockdown flag clear and the resolutions of `m`. -/
def Spec {α : Type} (th : Option ThreadId) (p : P E σ α) (m : Config E σ)
    (R : α → Config E σ → Prop) : Prop :=
  m.store.lockdown = false → ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ))
    (rest : List (Activation E σ)) (Q : Prop),
    (∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results →
      Acc prof hr dispatch { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } Q) →
    Acc prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } Q

/-! ## Accepting runs -/

theorem acc_step {m m₁ : Config E σ} {l : Label E σ} {Q : Prop} (hl : Live m)
    (s : UniqueStep prof hr dispatch m l m₁) (h : Acc prof hr dispatch m₁ Q) :
    Acc prof hr dispatch m Q := by
  intro tr m' r ha
  cases r with
  | refl => exact absurd ha.1 hl.1
  | cons s' r' =>
    obtain ⟨rfl, rfl⟩ := s.2 _ _ s'
    exact h _ _ r' ha

theorem acc_prog {m m₁ : Config E σ} {l : Label E σ} {Q : Prop} {th : Option ThreadId}
    {p : P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog p, segs⟩ :: rest) (hp : NotChoose p)
    (hl : m.store.lockdown = false) (s : Step prof hr dispatch m l m₁)
    (h : Acc prof hr dispatch m₁ Q) : Acc prof hr dispatch m Q :=
  acc_step ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩ (.of_prog hc hp s) h

theorem acc_prog' {m m₁ : Config E σ} {l : Label E σ} {Q : Prop} {th : Option ThreadId}
    {p : P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hp : NotChoose p) (hl : m.store.lockdown = false)
    (s : Step prof hr dispatch { m with ctl := ⟨th, .prog p, segs⟩ :: rest } l m₁)
    (h : Acc prof hr dispatch m₁ Q) :
    Acc prof hr dispatch { m with ctl := ⟨th, .prog p, segs⟩ :: rest } Q :=
  acc_step ⟨List.cons_ne_nil _ _, hl⟩ (.of_prog rfl hp s) h

theorem acc_trapCfg (m : Config E σ) (Q : Prop) : Acc prof hr dispatch (trapCfg m) Q := by
  intro tr m' r ha
  have e := steps_of_locked (m := trapCfg m) rfl rfl r
  subst e
  exact absurd ha.2.1 (by simp [trapCfg, lockdownSt])

theorem Acc.mono {m : Config E σ} {Q Q' : Prop} (h : Acc prof hr dispatch m Q) (hq : Q → Q') :
    Acc prof hr dispatch m Q' :=
  fun tr m' r ha => hq (h tr m' r ha)

/-- **A core activation** that never calls out passes acceptance on to what follows its
returns. -/
theorem acc_core {B : Config E σ} {th : Option ThreadId} {K : List FlatValue → P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)} {x : CoreSt E} {Q : Prop}
    (hno : ∀ y, Relation.ReflTransGen (CoreStep E) x y → ∀ h args,
      E.status y.1 y.2 ≠ .callout h args)
    (hret : ∀ y vs, Relation.ReflTransGen (CoreStep E) x y →
      E.status y.1 y.2 = .returned (.values vs) →
      Acc prof hr dispatch (retCfg B th K segs rest y vs) Q) :
    Acc prof hr dispatch (coreCfg B th K segs rest x) Q := by
  intro tr m' r ha
  rcases coreCfg_steps_inv r with ⟨y, -, rfl, -⟩ | ⟨y, pre, l, m₁, tr₂, hy, -, -, hx, r'⟩
  · exact absurd ha.1 (List.cons_ne_nil _ _)
  · rcases hx with ⟨vs, hs, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨h, args, hs⟩
    · exact hret y vs hy hs _ _ r' ha
    · exact acc_trapCfg _ _ _ _ r' ha
    · exact absurd hs (hno y hy h args)

/-! ## Programs -/

namespace Spec

variable {α β : Type} {th : Option ThreadId} {m : Config E σ}

theorem mono {p : P E σ α} {R R' : α → Config E σ → Prop} (h : Spec prof hr dispatch th p m R)
    (hR : ∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results → R' a m') :
    Spec prof hr dispatch th p m R' := by
  intro hl f segs rest Q k
  exact h hl f segs rest Q fun a m' hr hl' hres => k a m' (hR a m' hr hl' hres) hl' hres

theorem pure (a : α) : Spec prof hr dispatch th (Prog.pure a : P E σ α) m
    (fun b m' => b = a ∧ m' = m) := by
  intro hl f segs rest Q k
  exact k a m ⟨rfl, rfl⟩ hl rfl

theorem bind {p : P E σ α} {g : α → P E σ β} {R : α → Config E σ → Prop}
    {S : β → Config E σ → Prop} (h₁ : Spec prof hr dispatch th p m R)
    (h₂ : ∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results →
      Spec prof hr dispatch th (g a) m' S) :
    Spec prof hr dispatch th (p >>= g) m S := by
  intro hl f segs rest Q k
  have e : (p >>= g) >>= f = p >>= (fun a => g a >>= f) := by
    simp only [Prog.bind_eq, Prog.bind_assoc]
  rw [e]
  exact h₁ hl (fun a => g a >>= f) segs rest Q fun a m' hR hl' hres =>
    h₂ a m' hR hl' hres hl' f segs rest Q fun b m'' hS hl'' hres' =>
      k b m'' hS hl'' (hres'.trans hres)

/-- A program whose every continuation is excluded (for instance a trap). -/
theorem trap (r : TrapReason) (R : α → Config E σ → Prop) :
    Spec prof hr dispatch th (Canon.trap r : P E σ α) m R := by
  intro hl f segs rest Q _
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.trap rfl) (acc_trapCfg _ _)

theorem internal (msg : String) (R : α → Config E σ → Prop) :
    Spec prof hr dispatch th (Canon.internal msg : P E σ α) m R :=
  trap _ R

theorem get : Spec prof hr dispatch th (Canon.getStore : P E σ (CStore E)) m
    (fun s m' => s = m.store ∧ m' = m) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.get rfl) (k _ m ⟨rfl, rfl⟩ hl rfl)

theorem modify (g : CStore E → CStore E) (hg : (g m.store).lockdown = m.store.lockdown) :
    Spec prof hr dispatch th (Canon.modifyStore g : P E σ Unit) m
      (fun _ m' => m' = { m with store := g m.store }) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.modify rfl)
    (k _ _ rfl (hg.trans hl) rfl)

theorem readCore : Spec prof hr dispatch th (Canon.readCore : P E σ _) m
    (fun v m' => v = E.view m.core ∧ m' = m) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.readCore rfl) (k _ m ⟨rfl, rfl⟩ hl rfl)

theorem memWriteOp (a : E.MemAddr) (ptr : Nat) (bytes : ByteArray) :
    Spec prof hr dispatch th (Canon.memWriteOp a ptr bytes : P E σ Unit) m
      (fun _ m' => m' = { m with core := (E.memWrite? m.core a ptr bytes).getD m.core }) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.memWrite rfl) (k _ _ rfl hl rfl)

theorem currentThread : Spec prof hr dispatch th (Canon.currentThread : P E σ _) m
    (fun t m' => t = th ∧ m' = m) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.currentThread rfl)
    (k _ m ⟨rfl, rfl⟩ hl rfl)

theorem hostGet : Spec prof hr dispatch th (Canon.hostGet : P E σ σ) m
    (fun h m' => h = m.host ∧ m' = m) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.hostGet rfl) (k _ m ⟨rfl, rfl⟩ hl rfl)

/-- An observation that does not change the configuration (not a resolution). -/
theorem emit (o : HostObs) (ho : ∀ m : Config E σ, observe m o = m) :
    Spec prof hr dispatch th (Canon.emit o : P E σ Unit) m (fun _ m' => m' = m) := by
  intro hl f segs rest Q k
  have s := Step.emit (prof := prof) (hr := hr) (dispatch := dispatch)
    (m := { m with ctl := ⟨th, .prog (Canon.emit o >>= f), segs⟩ :: rest })
    (k := fun r => (Prog.pure r).bind f) rfl
  rw [ho] at s
  exact acc_prog' (fun _ _ e => by cases e) hl s (k _ m rfl hl rfl)

/-- **A late-bound call** runs the dispatched program. -/
theorem call {c : Call E} {R : Ret E → Config E σ → Prop}
    (h : Spec prof hr dispatch th (dispatch c) m R) :
    Spec prof hr dispatch th (Canon.callRet c) m R := by
  intro hl f segs rest Q k
  have h' := h hl Prog.pure (.prog (fun r => (Prog.pure r).bind f) :: segs) rest Q
    fun a m' hR hl' hres => acc_prog' (fun _ _ e => by cases e) hl' (Step.popProg rfl)
      (k a m' hR hl' hres)
  rw [Prog.bind_eq, Prog.bind_pure] at h'
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.call rfl) h'

theorem newThread (b : ThreadBody E) :
    Spec prof hr dispatch th (Canon.newThread b : P E σ ThreadId) m
      (fun t m' => t = (ArenaField.threads.alloc m.store { task := b.task }).2 ∧
        m' = { m.setCont t (some (threadAct dispatch t b)) with
          store := (ArenaField.threads.alloc m.store { task := b.task }).1 }) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.newThread rfl rfl)
    (k _ _ ⟨rfl, rfl⟩ hl rfl)

/-- **Resuming a thread** whose saved activation runs `body` from its start: the body runs on
the thread above the resumer, and when it returns the thread exits. -/
theorem resumeThread {t : ThreadId} {body : P E σ (Ret E)} {R : Ret E → Config E σ → Prop}
    (hb : m.cont? t = some ⟨some t, .prog body, []⟩)
    (h : Spec prof hr dispatch (some t) body
      { m.setCont t none with store := threadStatusSt t .running m.store } R) :
    Spec prof hr dispatch th (Canon.resumeThread t : P E σ Unit) m
      (fun _ m' => ∃ r m₂, R r m₂ ∧ m₂.store.lockdown = false ∧
        m' = { m₂ with store := threadStatusSt t .exited m₂.store }) := by
  intro hl f segs rest Q k
  have h' := h hl Prog.pure [] (⟨th, .prog ((Prog.pure ()).bind f), segs⟩ :: rest) Q
    fun a m' hR hl' hres => acc_prog' (fun _ _ e => by cases e) hl' (Step.threadExit rfl)
      (k () _ ⟨a, m', hR, hl', rfl⟩ hl' hres)
  rw [Prog.bind_eq, Prog.bind_pure] at h'
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.resumeThread rfl hb) h'

/-- **A core call** that never calls out continues at its returned values, in the core store
it left. -/
theorem callCore {a : E.FuncAddr} {args : List FlatValue}
    (hno : ∀ y, Relation.ReflTransGen (CoreStep E) (m.core, E.invoke a args) y →
      ∀ h xs, E.status y.1 y.2 ≠ .callout h xs) :
    Spec prof hr dispatch th (Canon.callCore a args : P E σ (List FlatValue)) m
      (fun vs m' => ∃ y, Relation.ReflTransGen (CoreStep E) (m.core, E.invoke a args) y ∧
        E.status y.1 y.2 = .returned (.values vs) ∧
        m' = { m with core := y.1 }) := by
  intro hl f segs rest Q k
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.callCore rfl)
    (acc_core (B := m) (x := (m.core, E.invoke a args)) hno
      fun y vs hy hs => k vs { m with core := y.1 } ⟨y, hy, hs, rfl⟩
        hl rfl)

/-! ### Derived programs -/

theorem getObj {Id : Type} (F : ArenaField E Id α) (i : Id) :
    Spec prof hr dispatch th (Canon.getObj F i : P E σ α) m
      (fun x m' => F.get? m.store i = some x ∧ m' = m) := by
  unfold Canon.getObj
  refine bind get fun s m' ⟨hs, hm⟩ _ _ => ?_
  subst hs hm
  cases e : F.get? m'.store i with
  | none => exact internal _ _
  | some x => exact mono (pure x) fun b m'' ⟨hb, hm⟩ _ _ => ⟨hb ▸ rfl, hm⟩

theorem allocObj {Id : Type} (F : ArenaField E Id α) (x : α)
    (hl : (ArenaOps.allocSt F x m.store).lockdown = m.store.lockdown) :
    Spec prof hr dispatch th (Canon.allocObj F x : P E σ Id) m
      (fun i m' => i = F.mkId (F.size m.store) ∧
        m' = { m with store := ArenaOps.allocSt F x m.store }) := by
  unfold Canon.allocObj
  refine bind get fun s m' ⟨hs, hm⟩ _ _ => ?_
  subst hs hm
  refine bind (modify _ hl) fun _ m'' hm _ _ => ?_
  subst hm
  exact mono (pure _) fun b m₃ ⟨hb, hm⟩ _ _ => ⟨hb, hm⟩

theorem trapIf (c : Bool) (r : TrapReason) :
    Spec prof hr dispatch th (Canon.trapIf c r : P E σ Unit) m
      (fun _ m' => c = false ∧ m' = m) := by
  unfold Canon.trapIf
  cases c with
  | true => exact trap _ _
  | false => exact mono (pure ()) fun _ m' ⟨_, hm⟩ _ _ => ⟨rfl, hm⟩

theorem orTrap (r : TrapReason) (o : Option α) :
    Spec prof hr dispatch th (Canon.orTrap r o : P E σ α) m
      (fun a m' => o = some a ∧ m' = m) := by
  cases o with
  | none => exact trap _ _
  | some a => exact mono (pure a) fun b m' ⟨hb, hm⟩ _ _ => ⟨hb ▸ rfl, hm⟩

theorem getsCore (g : CoreEngine.CoreView E (CanonHost E) → α) :
    Spec prof hr dispatch th (Canon.getsCore g : P E σ α) m
      (fun a m' => a = g (E.view m.core) ∧ m' = m) := by
  unfold Canon.getsCore
  refine bind readCore fun v m' ⟨hv, hm⟩ _ _ => ?_
  subst hv hm
  exact pure _

theorem gets (g : CStore E → α) :
    Spec prof hr dispatch th (Canon.gets g : P E σ α) m (fun a m' => a = g m.store ∧ m' = m) := by
  unfold Canon.gets
  refine bind get fun s m' ⟨hs, hm⟩ _ _ => ?_
  subst hs hm
  exact pure _

end Spec

/-! ## Resolutions are final -/

theorem observe_results (m : Config E σ) (o : HostObs) :
    ∃ xs, (observe m o).results = m.results ++ xs := by
  cases o <;> first
    | exact ⟨[], (List.append_nil _).symm⟩
    | exact ⟨_, rfl⟩

theorem result?_resolve {m : Config E σ} {c : CallId} {r : Option (List Value.Val)}
    (h : m.result? c = none) : (m.resolve c r).result? c = some r := by
  unfold Config.result? Config.resolve at *
  rw [List.find?_append]
  cases e : m.results.find? (·.1 == c) with
  | none => simp
  | some p => rw [e] at h; cases h

/-- A step only appends resolutions. -/
theorem step_results {m m' : Config E σ} {l : Label E σ}
    (h : Step prof hr dispatch m l m') : ∃ xs, m'.results = m.results ++ xs := by
  cases h with
  | emit => exact observe_results _ _
  | hostDone =>
    unfold hostFinish
    split <;> exact ⟨[], (List.append_nil _).symm⟩
  | _ => exact ⟨[], (List.append_nil _).symm⟩

theorem steps_results {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') : ∃ xs, m'.results = m.results ++ xs := by
  induction h with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | cons s _ ih =>
    obtain ⟨xs, hx⟩ := step_results s
    obtain ⟨ys, hy⟩ := ih
    exact ⟨xs ++ ys, by rw [hy, hx, List.append_assoc]⟩

/-- A resolution, once recorded, stays. -/
theorem steps_result? {m m' : Config E σ} {tr : List (Label E σ)}
    (h : Steps prof hr dispatch m tr m') {c : CallId} {r : Option (List Value.Val)}
    (hc : m.result? c = some r) : m'.result? c = some r := by
  obtain ⟨xs, hx⟩ := steps_results h
  unfold Config.result? at *
  rw [hx, List.find?_append]
  cases e : m.results.find? (·.1 == c) with
  | none => rw [e] at hc; cases hc
  | some p => rw [e] at hc; simpa using hc

/-- After a resolution of call `0` by `r`, every accepting run needs `r = some [true]`. -/
theorem acc_of_result {m : Config E σ} {r : Option (List Value.Val)} {Q : Prop}
    (hc : m.result? ⟨0⟩ = some r) (hq : r = some [.bool true] → Q) :
    Acc prof hr dispatch m Q := by
  intro tr m' run ha
  have h := steps_result? run hc
  rw [ha.2.2] at h
  exact hq (Option.some.inj h).symm

/-! ## Programs towards a fixed goal -/

variable (prof hr dispatch) in
/-- `Spec` for one goal `Q`: the continuation may be cut by a resolution that settles `Q`. -/
def SpecQ (Q : Prop) {α : Type} (th : Option ThreadId) (p : P E σ α) (m : Config E σ)
    (R : α → Config E σ → Prop) : Prop :=
  m.store.lockdown = false → ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ))
    (rest : List (Activation E σ)),
    (∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results →
      Acc prof hr dispatch { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } Q) →
    Acc prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } Q

namespace SpecQ

variable {α β : Type} {th : Option ThreadId} {m : Config E σ} {Q : Prop}

theorem ofSpec {p : P E σ α} {R : α → Config E σ → Prop} (h : Spec prof hr dispatch th p m R) :
    SpecQ prof hr dispatch Q th p m R :=
  fun hl f segs rest k => h hl f segs rest Q k

theorem mono {p : P E σ α} {R R' : α → Config E σ → Prop}
    (h : SpecQ prof hr dispatch Q th p m R)
    (hR : ∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results → R' a m') :
    SpecQ prof hr dispatch Q th p m R' := by
  intro hl f segs rest k
  exact h hl f segs rest fun a m' hr hl' hres => k a m' (hR a m' hr hl' hres) hl' hres

theorem bind {p : P E σ α} {g : α → P E σ β} {R : α → Config E σ → Prop}
    {S : β → Config E σ → Prop} (h₁ : SpecQ prof hr dispatch Q th p m R)
    (h₂ : ∀ a m', R a m' → m'.store.lockdown = false → m'.results = m.results →
      SpecQ prof hr dispatch Q th (g a) m' S) :
    SpecQ prof hr dispatch Q th (p >>= g) m S := by
  intro hl f segs rest k
  have e : (p >>= g) >>= f = p >>= (fun a => g a >>= f) := by
    simp only [Prog.bind_eq, Prog.bind_assoc]
  rw [e]
  exact h₁ hl (fun a => g a >>= f) segs rest fun a m' hR hl' hres =>
    h₂ a m' hR hl' hres hl' f segs rest fun b m'' hS hl'' hres' =>
      k b m'' hS hl'' (hres'.trans hres)

theorem call {c : Call E} {R : Ret E → Config E σ → Prop}
    (h : SpecQ prof hr dispatch Q th (dispatch c) m R) :
    SpecQ prof hr dispatch Q th (Canon.callRet c) m R := by
  intro hl f segs rest k
  have h' := h hl Prog.pure (.prog (fun r => (Prog.pure r).bind f) :: segs) rest
    fun a m' hR hl' hres => acc_prog' (fun _ _ e => by cases e) hl' (Step.popProg rfl)
      (k a m' hR hl' hres)
  rw [Prog.bind_eq, Prog.bind_pure] at h'
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.call rfl) h'

theorem resumeThread {t : ThreadId} {body : P E σ (Ret E)} {R : Ret E → Config E σ → Prop}
    (hb : m.cont? t = some ⟨some t, .prog body, []⟩)
    (h : SpecQ prof hr dispatch Q (some t) body
      { m.setCont t none with store := threadStatusSt t .running m.store } R) :
    SpecQ prof hr dispatch Q th (Canon.resumeThread t : P E σ Unit) m
      (fun _ m' => ∃ r m₂, R r m₂ ∧ m₂.store.lockdown = false ∧
        m' = { m₂ with store := threadStatusSt t .exited m₂.store }) := by
  intro hl f segs rest k
  have h' := h hl Prog.pure [] (⟨th, .prog ((Prog.pure ()).bind f), segs⟩ :: rest)
    fun a m' hR hl' hres => acc_prog' (fun _ _ e => by cases e) hl' (Step.threadExit rfl)
      (k () _ ⟨a, m', hR, hl', rfl⟩ hl' hres)
  rw [Prog.bind_eq, Prog.bind_pure] at h'
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.resumeThread rfl hb) h'

/-- **The resolution of call `0`** by `r` settles the goal: no continuation is needed. -/
theorem emitResolved {r : Option (List Value.Val)} {R : Unit → Config E σ → Prop}
    (hres : m.result? ⟨0⟩ = none) (hq : r = some [.bool true] → Q) :
    SpecQ prof hr dispatch Q th (Canon.emit (.resolved ⟨0⟩ r) : P E σ Unit) m R := by
  intro hl f segs rest _
  exact acc_prog' (fun _ _ e => by cases e) hl (Step.emit rfl)
    (acc_of_result (result?_resolve (m := m) hres) hq)

end SpecQ

end Silmaril.Proofs.Wasm.Component.Reference.ListLift
