module

public import Silmaril.Proofs.Wasm.Component.Reference.MachineDet

/-!
# Deterministic runs of the copied component machine

Tools for the symbolic execution of the copied machine (`Silmaril.Raw.Wasm.Component.Machine`):

* `UniqueStep m l m₁`: `m` has exactly one step, labelled `l`, to `m₁`. A step whose
  configuration runs a program that is not a choice is unique (`UniqueStep.of_prog`), and so is
  a step of a core activation that has returned or called out (`UniqueStep.of_core`);
* `DetRun m tr m₂`: a run of unique steps. Every machine run from `m` is a prefix of it or
  extends it (`DetRun.inv`), and a divergent `m` makes `m₂` divergent (`DetRun.diverges`);
* `Runs th p m tr a m'`: a big-step run of a program `p` on the thread `th` that uses only
  store and host-state access, the current thread, observations, thread creation and complete
  late-bound calls. A program `p >>= f` in focus runs deterministically to `f a`
  (`Runs.detRun`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-! ## Unique steps -/

variable (prof hr dispatch) in
/-- `m` has exactly one step, labelled `l`, to `m₁`. -/
def UniqueStep (m : Config E σ) (l : Label E σ) (m₁ : Config E σ) : Prop :=
  Step prof hr dispatch m l m₁ ∧ ∀ l' m', Step prof hr dispatch m l' m' → l' = l ∧ m' = m₁

/-- The focus program is not a choice. -/
def NotChoose {α : Type} (p : P E σ α) : Prop :=
  ∀ (ck : ChoiceKind) (k : ck.Resp → P E σ α), p ≠ .op (S := Eff E σ) (.choose ck) k

/-- A step of a configuration running a non-choice program has a deterministic label. -/
theorem det_of_prog {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {p : P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog p, segs⟩ :: rest) (hp : NotChoose p)
    (h : Step prof hr dispatch m l m') : Label.Det l := by
  refine ⟨fun k r e => ?_, fun e => ?_, fun ev e => ?_⟩
  · subst e
    cases h with
    | choose r' hc' _ =>
      rw [hc] at hc'
      obtain ⟨-, hf, -⟩ := Activation.mk.inj (List.cons.inj hc').1
      exact hp _ _ (Focus.prog.inj hf)
  · subst e
    cases h with
    | coreInternal hc' _ _ =>
      rw [hc] at hc'
      cases (Activation.mk.inj (List.cons.inj hc').1).2.1
  · subst e
    have hr' := Step.host_ready h
    rw [hr'.1] at hc
    cases hc

/-- **A step of a non-choice program is the unique step.** -/
theorem UniqueStep.of_prog {m m₁ : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {p : P E σ (Ret E)} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .prog p, segs⟩ :: rest) (hp : NotChoose p)
    (h : Step prof hr dispatch m l m₁) : UniqueStep prof hr dispatch m l m₁ :=
  ⟨h, fun _ _ h' => Step.det h' (det_of_prog hc hp h') h (det_of_prog hc hp h)⟩

/-- A step of a core activation that is neither running nor stuck has a deterministic label. -/
theorem det_of_core {m m' : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {ct : E.Thread (CanonHost E)} {k : List FlatValue → P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.store.core ct ≠ .running ∧ E.status m.store.core ct ≠ .stuck)
    (h : Step prof hr dispatch m l m') : Label.Det l := by
  refine ⟨fun k r e => ?_, fun e => ?_, fun ev e => ?_⟩
  · subst e
    cases h with
    | choose r' hc' _ =>
      rw [hc] at hc'
      cases (Activation.mk.inj (List.cons.inj hc').1).2.1
  · subst e
    cases h with
    | coreInternal hc' hst _ =>
      rw [hc] at hc'
      obtain ⟨-, hf, -⟩ := Activation.mk.inj (List.cons.inj hc').1
      cases hf
      rcases hst with e | e
      · exact hs.1 e
      · exact hs.2 e
  · subst e
    have hr' := Step.host_ready h
    rw [hr'.1] at hc
    cases hc

/-- **A step of a returned or calling-out core activation is the unique step.** -/
theorem UniqueStep.of_core {m m₁ : Config E σ} {l : Label E σ} {th : Option ThreadId}
    {ct : E.Thread (CanonHost E)} {k : List FlatValue → P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    (hc : m.ctl = ⟨th, .core ct k, segs⟩ :: rest)
    (hs : E.status m.store.core ct ≠ .running ∧ E.status m.store.core ct ≠ .stuck)
    (h : Step prof hr dispatch m l m₁) : UniqueStep prof hr dispatch m l m₁ :=
  ⟨h, fun _ _ h' => Step.det h' (det_of_core hc hs h') h (det_of_core hc hs h)⟩

/-! ## Deterministic runs -/

variable (prof hr dispatch) in
/-- A run of unique steps. -/
inductive DetRun : Config E σ → List (Label E σ) → Config E σ → Prop where
  | refl (m : Config E σ) : DetRun m [] m
  | cons {m m₁ m₂ : Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
      UniqueStep prof hr dispatch m l m₁ → DetRun m₁ tr m₂ → DetRun m (l :: tr) m₂

namespace DetRun

theorem trans {m₁ m₂ m₃ : Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : DetRun prof hr dispatch m₁ tr₁ m₂) (h₂ : DetRun prof hr dispatch m₂ tr₂ m₃) :
    DetRun prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons s _ ih => exact .cons s (ih h₂)

theorem single {m m₁ : Config E σ} {l : Label E σ} (h : UniqueStep prof hr dispatch m l m₁) :
    DetRun prof hr dispatch m [l] m₁ :=
  .cons h (.refl _)

theorem steps {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : DetRun prof hr dispatch m tr m₂) : Steps prof hr dispatch m tr m₂ := by
  induction h with
  | refl => exact .refl _
  | cons s _ ih => exact .cons s.1 ih

/-- **Inversion**: a run from the start of a deterministic run is a prefix of it, or extends
it. -/
theorem inv {m m₂ m' : Config E σ} {tr tr' : List (Label E σ)}
    (h : DetRun prof hr dispatch m tr m₂) (h' : Steps prof hr dispatch m tr' m') :
    (∃ tr₂, tr = tr' ++ tr₂ ∧ DetRun prof hr dispatch m' tr₂ m₂) ∨
      (∃ tr'', tr' = tr ++ tr'' ∧ Steps prof hr dispatch m₂ tr'' m') := by
  induction h generalizing tr' with
  | refl m => exact .inr ⟨tr', rfl, h'⟩
  | @cons m m₁ m₂ l tr s _ ih =>
    cases h' with
    | refl => exact .inl ⟨_, rfl, .cons s ‹_›⟩
    | cons s' r' =>
      obtain ⟨rfl, rfl⟩ := s.2 _ _ s'
      rcases ih r' with ⟨tr₂, e, d⟩ | ⟨tr'', e, r⟩
      · exact .inl ⟨tr₂, by rw [e]; rfl, d⟩
      · exact .inr ⟨tr'', by rw [e]; rfl, r⟩

/-- A divergent start of a deterministic run makes its end divergent. -/
theorem diverges {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : DetRun prof hr dispatch m tr m₂) (d : Diverges prof hr dispatch m) :
    Diverges prof hr dispatch m₂ := by
  induction h with
  | refl => exact d
  | cons s _ ih =>
    obtain ⟨m', ⟨l', _, s'⟩, d'⟩ := d.unfold
    obtain ⟨-, rfl⟩ := s.2 _ _ s'
    exact ih d'

end DetRun

/-! ## Big-step runs of deterministic programs -/

variable (dispatch) in
/-- **Big-step runs of deterministic programs.** `Runs th p m tr a m'`: on the thread `th`,
the program `p` runs from `m` (whose control chain is ignored) to the result `a` and the
configuration `m'`, with trace `tr`, using only store and host-state access, the current
thread, observations, thread creation and late-bound calls that themselves run to completion. -/
inductive Runs : {α : Type} → Option ThreadId → P E σ α → Config E σ → List (Label E σ) → α →
    Config E σ → Prop where
  | pure {α : Type} {th : Option ThreadId} (a : α) (m : Config E σ) :
      Runs th (.pure a) m [] a m
  | get {α : Type} {th : Option ThreadId} {k : CStore E → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      Runs th (k m.store) m tr a m' → Runs th (.op (S := Eff E σ) .get k) m (.tau :: tr) a m'
  | modify {α : Type} {th : Option ThreadId} {f : CStore E → CStore E} {k : Unit → P E σ α}
      {m : Config E σ} {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      Runs th (k ()) { m with store := f m.store } tr a m' →
      Runs th (.op (S := Eff E σ) (.modify f) k) m (.tau :: tr) a m'
  | hostGet {α : Type} {th : Option ThreadId} {k : σ → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      Runs th (k m.host) m tr a m' → Runs th (.op (S := Eff E σ) .hostGet k) m (.tau :: tr) a m'
  | currentThread {α : Type} {th : Option ThreadId} {k : Option ThreadId → P E σ α}
      {m : Config E σ} {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      Runs th (k th) m tr a m' →
      Runs th (.op (S := Eff E σ) .currentThread k) m (.tau :: tr) a m'
  | emit {α : Type} {th : Option ThreadId} {o : HostObs} {k : Unit → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      Runs th (k ()) (observe m o) tr a m' →
      Runs th (.op (S := Eff E σ) (.emit o) k) m (.obs o :: tr) a m'
  | newThread {α : Type} {th : Option ThreadId} {b : ThreadBody E} {k : ThreadId → P E σ α}
      {m : Config E σ} {s' : CStore E} {t : ThreadId} {tr : List (Label E σ)} {a : α}
      {m' : Config E σ} :
      ArenaField.threads.alloc m.store { task := b.task } = (s', t) →
      Runs th (k t) { m.setCont t (some (threadAct dispatch t b)) with store := s' } tr a m' →
      Runs th (.op (S := Eff E σ) (.newThread b) k) m (.tau :: tr) a m'
  | call {α : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → P E σ α} {m : Config E σ}
      {tr₁ : List (Label E σ)} {r : Ret E} {m₁ : Config E σ} {tr₂ : List (Label E σ)} {a : α}
      {m' : Config E σ} :
      Runs th (dispatch c) m tr₁ r m₁ → Runs th (k r) m₁ tr₂ a m' →
      Runs th (.op (S := Eff E σ) (.call c) k) m (.tau :: (tr₁ ++ .tau :: tr₂)) a m'

namespace Runs

/-- Sequencing. -/
theorem bind {α β : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ β}
    {m m₁ m₂ : Config E σ} {tr₁ tr₂ : List (Label E σ)} {a : α} {b : β}
    (h₁ : Runs dispatch th p m tr₁ a m₁) (h₂ : Runs dispatch th (f a) m₁ tr₂ b m₂) :
    Runs dispatch th (p >>= f) m (tr₁ ++ tr₂) b m₂ := by
  induction h₁ with
  | pure => exact h₂
  | get _ ih => exact .get (ih h₂)
  | modify _ ih => exact .modify (ih h₂)
  | hostGet _ ih => exact .hostGet (ih h₂)
  | currentThread _ ih => exact .currentThread (ih h₂)
  | emit _ ih => exact .emit (ih h₂)
  | newThread ha _ ih => exact .newThread ha (ih h₂)
  | call hc _ _ ih =>
    rw [List.cons_append, List.append_assoc, List.cons_append]
    exact Runs.call hc (ih h₂)

/-- `Runs` of a `pure` program. -/
theorem pure_inv {α : Type} {th : Option ThreadId} {a b : α} {m m' : Config E σ}
    {tr : List (Label E σ)} (h : Runs dispatch th (.pure a) m tr b m') :
    tr = [] ∧ b = a ∧ m' = m := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- `Runs` of a `pure` program (as `Pure.pure`). -/
theorem pure' {α : Type} {th : Option ThreadId} (a : α) (m : Config E σ) :
    Runs dispatch th (Pure.pure a : P E σ α) m [] a m :=
  .pure a m

theorem getStore {th : Option ThreadId} (m : Config E σ) :
    Runs dispatch th (Canon.getStore : P E σ (CStore E)) m [.tau] m.store m :=
  .get (.pure _ _)

theorem modifyStore {th : Option ThreadId} (f : CStore E → CStore E) (m : Config E σ) :
    Runs dispatch th (Canon.modifyStore f : P E σ Unit) m [.tau] () { m with store := f m.store } :=
  .modify (.pure _ _)

/-- **Deterministic big-step runs are deterministic machine runs**, in any context. -/
theorem detRun {α : Type} {th : Option ThreadId} {p : P E σ α} {m m' : Config E σ}
    {tr : List (Label E σ)} {a : α} (h : Runs dispatch th p m tr a m') :
    ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      DetRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  induction h with
  | pure => intro f segs rest; exact .refl _
  | get _ ih =>
    intro f segs rest
    exact .cons (.of_prog rfl (fun _ _ e => by cases e) (.get rfl)) (ih f segs rest)
  | modify _ ih =>
    intro f segs rest
    exact .cons (.of_prog rfl (fun _ _ e => by cases e) (.modify rfl)) (ih f segs rest)
  | hostGet _ ih =>
    intro f segs rest
    exact .cons (.of_prog rfl (fun _ _ e => by cases e) (.hostGet rfl)) (ih f segs rest)
  | currentThread _ ih =>
    intro f segs rest
    exact .cons (.of_prog rfl (fun _ _ e => by cases e) (.currentThread rfl)) (ih f segs rest)
  | @emit _ th o k m tr a m' _ ih =>
    intro f segs rest
    have e : ∀ X Y : List (Activation E σ),
        ({ observe { m with ctl := X } o with ctl := Y } : Config E σ) =
          { observe m o with ctl := Y } := by
      intro X Y
      cases o <;> rfl
    have s : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog ((Prog.op (S := Eff E σ) (.emit o) k) >>= f), segs⟩ :: rest }
        (.obs o) { observe m o with ctl := ⟨th, .prog (k () >>= f), segs⟩ :: rest } := by
      have s₀ : UniqueStep prof hr dispatch
          { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ ::
            rest }
          (.obs o) { observe { m with ctl :=
            ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ :: rest } o with
              ctl := ⟨th, .prog (k () >>= f), segs⟩ :: rest } :=
        .of_prog rfl (fun _ _ e => by cases e) (.emit (k := fun r => k r >>= f) rfl)
      rw [e] at s₀
      exact s₀
    exact .cons s (ih f segs rest)
  | newThread ha _ ih =>
    intro f segs rest
    exact .cons (.of_prog rfl (fun _ _ e => by cases e) (.newThread rfl ha)) (ih f segs rest)
  | @call _ th c k m tr₁ r m₁ tr₂ a m' _ _ ih₁ ih₂ =>
    intro f segs rest
    have s₁ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => k r >>= f), segs⟩ ::
          rest }
        .tau { m with ctl := ⟨th, .prog (dispatch c), .prog (fun r => k r >>= f) :: segs⟩ ::
          rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => k r >>= f) rfl)
    have d₁ := ih₁ Prog.pure (.prog (fun r => k r >>= f) :: segs) rest
    rw [Prog.bind_eq, Prog.bind_pure] at d₁
    have s₂ : UniqueStep prof hr dispatch
        { m₁ with ctl := ⟨th, .prog (Prog.pure r), .prog (fun r => k r >>= f) :: segs⟩ :: rest }
        .tau { m₁ with ctl := ⟨th, .prog (k r >>= f), segs⟩ :: rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.popProg (k := fun r => k r >>= f) (r := r) rfl)
    exact .cons s₁ (d₁.trans (.cons s₂ (ih₂ f segs rest)))

end Runs

end Silmaril.Proofs.Wasm.Component.Reference
