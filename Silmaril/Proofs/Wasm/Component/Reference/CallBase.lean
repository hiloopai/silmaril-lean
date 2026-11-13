module

public import Silmaril.Proofs.Wasm.Component.Reference.DetRun

/-!
# Live deterministic runs of the copied component machine

Refinements of `DetRun` and `Runs` (`Silmaril.Proofs.Wasm.Component.Reference.DetRun`) that also
record that every configuration the run passes through is *live*: some activation runs
(`ctl ≠ []`) and the store is not locked down. A live configuration satisfies none of the
terminal predicates of a top-level call (`CallOutcome.Holds`), so a machine run that stops
inside a live run has no outcome.

* `Live m`, `LRun m tr m₂`: a run of unique steps from live configurations;
* `LRun.inv`: a machine run from the start of an `LRun` stops at a live configuration inside
  it, or extends it; `LRun.diverges`;
* `RunsQ`: `Runs` whose store updates keep the lockdown flag; `RunsQ.lrun`: in focus, it is a
  live run.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-- Some activation runs and the store is not locked down. -/
def Live (m : Config E σ) : Prop := m.ctl ≠ [] ∧ m.store.lockdown = false

variable (prof hr dispatch) in
/-- A run of unique steps from live configurations. -/
inductive LRun : Config E σ → List (Label E σ) → Config E σ → Prop where
  | refl (m : Config E σ) : LRun m [] m
  | cons {m m₁ m₂ : Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
      Live m → UniqueStep prof hr dispatch m l m₁ → LRun m₁ tr m₂ → LRun m (l :: tr) m₂

namespace LRun

theorem trans {m₁ m₂ m₃ : Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : LRun prof hr dispatch m₁ tr₁ m₂) (h₂ : LRun prof hr dispatch m₂ tr₂ m₃) :
    LRun prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons hl s _ ih => exact .cons hl s (ih h₂)

theorem steps {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m₂) : Steps prof hr dispatch m tr m₂ := by
  induction h with
  | refl => exact .refl _
  | cons _ s _ ih => exact .cons s.1 ih

/-- **Inversion**: a run from the start of a live run stops at a live configuration inside
it, or extends it. -/
theorem inv {m m₂ m' : Config E σ} {tr tr' : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m₂) (h' : Steps prof hr dispatch m tr' m') :
    Live m' ∨ (∃ tr'', tr' = tr ++ tr'' ∧ Steps prof hr dispatch m₂ tr'' m') := by
  induction h generalizing tr' with
  | refl m => exact .inr ⟨tr', rfl, h'⟩
  | @cons m m₁ m₂ l tr hl s _ ih =>
    cases h' with
    | refl => exact .inl hl
    | cons s' r' =>
      obtain ⟨rfl, rfl⟩ := s.2 _ _ s'
      rcases ih r' with hl' | ⟨tr'', e, r⟩
      · exact .inl hl'
      · exact .inr ⟨tr'', by rw [e]; rfl, r⟩

/-- A divergent start of a live run makes its end divergent. -/
theorem diverges {m m₂ : Config E σ} {tr : List (Label E σ)}
    (h : LRun prof hr dispatch m tr m₂) (d : Diverges prof hr dispatch m) :
    Diverges prof hr dispatch m₂ := by
  induction h with
  | refl => exact d
  | cons _ s _ ih =>
    obtain ⟨m', ⟨l', _, s'⟩, d'⟩ := d.unfold
    obtain ⟨-, rfl⟩ := s.2 _ _ s'
    exact ih d'

/-- One step of a non-choice program. -/
theorem prog {m m₁ m₂ : Config E σ} {l : Label E σ} {tr : List (Label E σ)}
    {th : Option ThreadId} {p : P E σ (Ret E)} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (hc : m.ctl = ⟨th, .prog p, segs⟩ :: rest)
    (hp : NotChoose p) (hl : m.store.lockdown = false) (s : Step prof hr dispatch m l m₁)
    (r : LRun prof hr dispatch m₁ tr m₂) : LRun prof hr dispatch m (l :: tr) m₂ :=
  .cons ⟨by rw [hc]; exact List.cons_ne_nil _ _, hl⟩ (.of_prog hc hp s) r

end LRun

/-! ## Big-step runs keeping the lockdown flag -/

variable (dispatch) in
/-- `Runs` whose store updates keep the lockdown flag. -/
inductive RunsQ : {α : Type} → Option ThreadId → P E σ α → Config E σ → List (Label E σ) →
    α → Config E σ → Prop where
  | pure {α : Type} {th : Option ThreadId} (a : α) (m : Config E σ) :
      RunsQ th (.pure a) m [] a m
  | get {α : Type} {th : Option ThreadId} {k : CStore E → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      RunsQ th (k m.store) m tr a m' → RunsQ th (.op (S := Eff E σ) .get k) m (.tau :: tr) a m'
  | modify {α : Type} {th : Option ThreadId} {f : CStore E → CStore E} {k : Unit → P E σ α}
      {m : Config E σ} {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      (f m.store).lockdown = m.store.lockdown →
      RunsQ th (k ()) { m with store := f m.store } tr a m' →
      RunsQ th (.op (S := Eff E σ) (.modify f) k) m (.tau :: tr) a m'
  | hostGet {α : Type} {th : Option ThreadId} {k : σ → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      RunsQ th (k m.host) m tr a m' →
      RunsQ th (.op (S := Eff E σ) .hostGet k) m (.tau :: tr) a m'
  | hostSet {α : Type} {th : Option ThreadId} {s : σ} {k : Unit → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      RunsQ th (k ()) { m with host := s } tr a m' →
      RunsQ th (.op (S := Eff E σ) (.hostSet s) k) m (.tau :: tr) a m'
  | currentThread {α : Type} {th : Option ThreadId} {k : Option ThreadId → P E σ α}
      {m : Config E σ} {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      RunsQ th (k th) m tr a m' →
      RunsQ th (.op (S := Eff E σ) .currentThread k) m (.tau :: tr) a m'
  | emit {α : Type} {th : Option ThreadId} {o : HostObs} {k : Unit → P E σ α} {m : Config E σ}
      {tr : List (Label E σ)} {a : α} {m' : Config E σ} :
      RunsQ th (k ()) (observe m o) tr a m' →
      RunsQ th (.op (S := Eff E σ) (.emit o) k) m (.obs o :: tr) a m'
  | newThread {α : Type} {th : Option ThreadId} {b : ThreadBody E} {k : ThreadId → P E σ α}
      {m : Config E σ} {s' : CStore E} {t : ThreadId} {tr : List (Label E σ)} {a : α}
      {m' : Config E σ} :
      ArenaField.threads.alloc m.store { task := b.task } = (s', t) →
      s'.lockdown = m.store.lockdown →
      RunsQ th (k t) { m.setCont t (some (threadAct dispatch t b)) with store := s' } tr a m' →
      RunsQ th (.op (S := Eff E σ) (.newThread b) k) m (.tau :: tr) a m'
  | call {α : Type} {th : Option ThreadId} {c : Call E} {k : Ret E → P E σ α} {m : Config E σ}
      {tr₁ : List (Label E σ)} {r : Ret E} {m₁ : Config E σ} {tr₂ : List (Label E σ)} {a : α}
      {m' : Config E σ} :
      RunsQ th (dispatch c) m tr₁ r m₁ → RunsQ th (k r) m₁ tr₂ a m' →
      RunsQ th (.op (S := Eff E σ) (.call c) k) m (.tau :: (tr₁ ++ .tau :: tr₂)) a m'

/-- `observe` keeps the store. -/
@[simp] theorem observe_store (m : Config E σ) (o : HostObs) : (observe m o).store = m.store := by
  cases o <;> rfl

/-- `observe` commutes with replacing the control chain. -/
theorem observe_ctl (m : Config E σ) (o : HostObs) (X Y : List (Activation E σ)) :
    ({ observe { m with ctl := X } o with ctl := Y } : Config E σ) =
      { observe m o with ctl := Y } := by
  cases o <;> rfl

namespace RunsQ

/-- Sequencing. -/
theorem bind {α β : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ β}
    {m m₁ m₂ : Config E σ} {tr₁ tr₂ : List (Label E σ)} {a : α} {b : β}
    (h₁ : RunsQ dispatch th p m tr₁ a m₁) (h₂ : RunsQ dispatch th (f a) m₁ tr₂ b m₂) :
    RunsQ dispatch th (p >>= f) m (tr₁ ++ tr₂) b m₂ := by
  induction h₁ with
  | pure => exact h₂
  | get _ ih => exact .get (ih h₂)
  | modify hf _ ih => exact .modify hf (ih h₂)
  | hostGet _ ih => exact .hostGet (ih h₂)
  | hostSet _ ih => exact .hostSet (ih h₂)
  | currentThread _ ih => exact .currentThread (ih h₂)
  | emit _ ih => exact .emit (ih h₂)
  | newThread ha hs _ ih => exact .newThread ha hs (ih h₂)
  | call hc _ _ ih =>
    rw [List.cons_append, List.append_assoc, List.cons_append]
    exact RunsQ.call hc (ih h₂)

/-- The lockdown flag is kept. -/
theorem lock {α : Type} {th : Option ThreadId} {p : P E σ α} {m m' : Config E σ}
    {tr : List (Label E σ)} {a : α} (h : RunsQ dispatch th p m tr a m') :
    m'.store.lockdown = m.store.lockdown := by
  induction h with
  | pure => rfl
  | get _ ih => exact ih
  | modify hf _ ih => exact ih.trans hf
  | hostGet _ ih => exact ih
  | hostSet _ ih => exact ih
  | currentThread _ ih => exact ih
  | emit _ ih => exact ih.trans (congrArg CStore.lockdown (observe_store _ _))
  | newThread _ hs _ ih => exact ih.trans hs
  | call _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- One live step of the program in focus. -/
theorem live_op {m : Config E σ} {th : Option ThreadId} {p : P E σ (Ret E)}
    {segs : List (Seg E σ)} {rest : List (Activation E σ)} (hl : m.store.lockdown = false) :
    Live ({ m with ctl := ⟨th, .prog p, segs⟩ :: rest } : Config E σ) :=
  ⟨List.cons_ne_nil _ _, hl⟩

/-- **Big-step runs are live runs**, in any context. -/
theorem lrun {α : Type} {th : Option ThreadId} {p : P E σ α} {m m' : Config E σ}
    {tr : List (Label E σ)} {a : α} (h : RunsQ dispatch th p m tr a m') :
    m.store.lockdown = false →
    ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      LRun prof hr dispatch { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  induction h with
  | pure => intro _ f segs rest; exact .refl _
  | get _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.get rfl))
      (ih hl f segs rest)
  | modify hf _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.modify rfl))
      (ih (hf.trans hl) f segs rest)
  | hostGet _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.hostGet rfl))
      (ih hl f segs rest)
  | hostSet _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.hostSet rfl))
      (ih hl f segs rest)
  | currentThread _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.currentThread rfl))
      (ih hl f segs rest)
  | @emit _ th o k m tr a m' _ ih =>
    intro hl f segs rest
    have s₀ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ ::
          rest }
        (.obs o) { observe { m with ctl :=
          ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ :: rest } o with
            ctl := ⟨th, .prog (k () >>= f), segs⟩ :: rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.emit (k := fun r => k r >>= f) rfl)
    rw [observe_ctl] at s₀
    have hl' : (observe m o).store.lockdown = false := by rw [observe_store]; exact hl
    exact .cons (live_op hl) s₀ (ih hl' f segs rest)
  | newThread ha hs _ ih =>
    intro hl f segs rest
    exact .cons (live_op hl) (.of_prog rfl (fun _ _ e => by cases e) (.newThread rfl ha))
      (ih (hs.trans hl) f segs rest)
  | @call _ th c k m tr₁ r m₁ tr₂ a m' h₁ _ ih₁ ih₂ =>
    intro hl f segs rest
    have s₁ : UniqueStep prof hr dispatch
        { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.call c) fun r => k r >>= f), segs⟩ ::
          rest }
        .tau { m with ctl := ⟨th, .prog (dispatch c), .prog (fun r => k r >>= f) :: segs⟩ ::
          rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.call (k := fun r => k r >>= f) rfl)
    have d₁ := ih₁ hl Prog.pure (.prog (fun r => k r >>= f) :: segs) rest
    rw [Prog.bind_eq, Prog.bind_pure] at d₁
    have hl₁ : m₁.store.lockdown = false := h₁.lock.trans hl
    have s₂ : UniqueStep prof hr dispatch
        { m₁ with ctl := ⟨th, .prog (Prog.pure r), .prog (fun r => k r >>= f) :: segs⟩ :: rest }
        .tau { m₁ with ctl := ⟨th, .prog (k r >>= f), segs⟩ :: rest } :=
      .of_prog rfl (fun _ _ e => by cases e) (.popProg (k := fun r => k r >>= f) (r := r) rfl)
    exact .cons (live_op hl) s₁ (d₁.trans (.cons (live_op hl₁) s₂ (ih₂ hl₁ f segs rest)))

/-- `lrun` at a configuration whose focus is `p >>= f`. -/
theorem lrun_at {α : Type} {th : Option ThreadId} {p : P E σ α} {M m' : Config E σ}
    {tr : List (Label E σ)} {a : α} (h : RunsQ dispatch th p M tr a m')
    (hl : M.store.lockdown = false) (f : α → P E σ (Ret E)) {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) :
    LRun prof hr dispatch M tr { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  have e : M = { M with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } := by
    cases M
    cases hc
    rfl
  have d := h.lrun (prof := prof) (hr := hr) hl f segs rest
  rw [← e] at d
  exact d

/-- A big-step chunk followed by a live run. -/
theorem chunk {α : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ (Ret E)}
    {M m' M₂ : Config E σ} {segs : List (Seg E σ)} {rest : List (Activation E σ)}
    {tr tr' : List (Label E σ)} {a : α}
    (hc : M.ctl = ⟨th, .prog (p >>= f), segs⟩ :: rest) (h : RunsQ dispatch th p M tr a m')
    (hl : M.store.lockdown = false)
    (r : LRun prof hr dispatch { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } tr' M₂) :
    LRun prof hr dispatch M (tr ++ tr') M₂ :=
  (h.lrun_at hl f hc).trans r

/-- A big-step chunk under one more continuation. -/
theorem chunk2 {α β : Type} {th : Option ThreadId} {p : P E σ α} {f : α → P E σ β}
    {g : β → P E σ (Ret E)} {M m' M₂ : Config E σ} {segs : List (Seg E σ)}
    {rest : List (Activation E σ)} {tr tr' : List (Label E σ)} {a : α}
    (hc : M.ctl = ⟨th, .prog ((p >>= f) >>= g), segs⟩ :: rest)
    (h : RunsQ dispatch th p M tr a m') (hl : M.store.lockdown = false)
    (r : LRun prof hr dispatch { m' with ctl := ⟨th, .prog (f a >>= g), segs⟩ :: rest } tr'
      M₂) :
    LRun prof hr dispatch M (tr ++ tr') M₂ := by
  have hc' : M.ctl = ⟨th, .prog (p >>= fun a => f a >>= g), segs⟩ :: rest := by
    rw [hc, Prog.bind_eq, Prog.bind_eq, Prog.bind_assoc]
    rfl
  exact chunk hc' h hl r

end RunsQ

end Silmaril.Proofs.Wasm.Component.Reference
