module

public import Silmaril.Proofs.Wasm.Component.Reference.DetRun

/-!
# Silent runs that keep the store unlocked

Instantiation of `Simple.toRef` uses only store reads, store updates that leave the lockdown
flag alone, and one observation. For such programs:

* `SRuns p m a m'`: the program `p` runs from `m` to the result `a` and `m'` (big-step), every
  store update keeping the lockdown flag;
* `DetRunL m tr m₂`: a deterministic run (`DetRun`) whose configurations are all unlocked;
* `SRuns.detRunL`: in any context, an `SRuns` run from an unlocked configuration is a `DetRunL`
  run whose labels are `tau` or observations;
* `DetRunL.inv`: a machine run from the start of a `DetRunL` run either stops at an unlocked
  configuration of it, or extends it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Component.Machine.StepDefs

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → P E σ (Ret E)}

/-! ## Unlocked deterministic runs -/

variable (prof hr dispatch) in
/-- A deterministic run through unlocked configurations. -/
inductive DetRunL : Machine.Config E σ → List (Label E σ) → Machine.Config E σ → Prop where
  | refl {m : Machine.Config E σ} : m.store.lockdown = false → DetRunL m [] m
  | cons {m m₁ m₂ : Machine.Config E σ} {l : Label E σ} {tr : List (Label E σ)} :
      m.store.lockdown = false → UniqueStep prof hr dispatch m l m₁ → DetRunL m₁ tr m₂ →
      DetRunL m (l :: tr) m₂

namespace DetRunL

theorem toDetRun {m m₂ : Machine.Config E σ} {tr : List (Label E σ)}
    (h : DetRunL prof hr dispatch m tr m₂) : DetRun prof hr dispatch m tr m₂ := by
  induction h with
  | refl => exact .refl _
  | cons _ s _ ih => exact .cons s ih

theorem trans {m₁ m₂ m₃ : Machine.Config E σ} {tr₁ tr₂ : List (Label E σ)}
    (h₁ : DetRunL prof hr dispatch m₁ tr₁ m₂) (h₂ : DetRunL prof hr dispatch m₂ tr₂ m₃) :
    DetRunL prof hr dispatch m₁ (tr₁ ++ tr₂) m₃ := by
  induction h₁ with
  | refl => exact h₂
  | cons hl s _ ih => exact .cons hl s (ih h₂)

theorem start {m m₂ : Machine.Config E σ} {tr : List (Label E σ)}
    (h : DetRunL prof hr dispatch m tr m₂) : m.store.lockdown = false := by
  cases h with
  | refl hl => exact hl
  | cons hl _ _ => exact hl

/-- **Inversion**: a run from the start either stops at an unlocked configuration of the
deterministic run, or extends it. -/
theorem inv {m m₂ m' : Machine.Config E σ} {tr tr' : List (Label E σ)}
    (h : DetRunL prof hr dispatch m tr m₂) (h' : Steps prof hr dispatch m tr' m') :
    (∃ tr₂, tr = tr' ++ tr₂ ∧ DetRunL prof hr dispatch m' tr₂ m₂) ∨
      (∃ tr'', tr' = tr ++ tr'' ∧ Steps prof hr dispatch m₂ tr'' m') := by
  induction h generalizing tr' with
  | refl _ => exact .inr ⟨tr', rfl, h'⟩
  | @cons m m₁ m₂ l tr hl s d ih =>
    cases h' with
    | refl => exact .inl ⟨_, rfl, .cons hl s d⟩
    | cons s' r' =>
      obtain ⟨rfl, rfl⟩ := s.2 _ _ s'
      rcases ih r' with ⟨tr₂, e, d'⟩ | ⟨tr'', e, r⟩
      · exact .inl ⟨tr₂, by rw [e]; rfl, d'⟩
      · exact .inr ⟨tr'', by rw [e]; rfl, r⟩

end DetRunL

/-! ## Silent big-step runs -/

/-- Big-step runs of programs that only read the store, update it without touching the
lockdown flag, and make the observations `os`. -/
inductive SRuns : {α : Type} → P E σ α → Machine.Config E σ → List HostObs → α →
    Machine.Config E σ → Prop where
  | pure {α : Type} (a : α) (m : Machine.Config E σ) : SRuns (.pure a) m [] a m
  | get {α : Type} {k : CStore E → P E σ α} {m : Machine.Config E σ} {os : List HostObs} {a : α}
      {m' : Machine.Config E σ} :
      SRuns (k m.store) m os a m' → SRuns (.op (S := Eff E σ) .get k) m os a m'
  | modify {α : Type} {f : CStore E → CStore E} {k : Unit → P E σ α} {m : Machine.Config E σ}
      {os : List HostObs} {a : α} {m' : Machine.Config E σ} :
      (∀ s, (f s).lockdown = s.lockdown) →
      SRuns (k ()) { m with store := f m.store } os a m' →
      SRuns (.op (S := Eff E σ) (.modify f) k) m os a m'
  | emit {α : Type} {o : HostObs} {k : Unit → P E σ α} {m : Machine.Config E σ}
      {os : List HostObs} {a : α} {m' : Machine.Config E σ} :
      SRuns (k ()) (observe m o) os a m' → SRuns (.op (S := Eff E σ) (.emit o) k) m (o :: os) a m'

theorem observe_store (m : Machine.Config E σ) (o : HostObs) : (observe m o).store = m.store := by
  cases o <;> rfl

namespace SRuns

theorem bind {α β : Type} {p : P E σ α} {f : α → P E σ β} {m m₁ m₂ : Machine.Config E σ}
    {os₁ os₂ : List HostObs} {a : α} {b : β} (h₁ : SRuns p m os₁ a m₁)
    (h₂ : SRuns (f a) m₁ os₂ b m₂) : SRuns (p >>= f) m (os₁ ++ os₂) b m₂ := by
  induction h₁ with
  | pure => exact h₂
  | get _ ih => exact .get (ih h₂)
  | modify hf _ ih => exact .modify hf (ih h₂)
  | emit _ ih => exact .emit (ih h₂)

/-- The labels of a silent run: `tau` and observations. -/
def Quiet (tr : List (Label E σ)) : Prop := ∀ l ∈ tr, l = .tau ∨ ∃ o, l = .obs o

theorem Quiet.cons {l : Label E σ} {tr : List (Label E σ)} (hl : l = .tau ∨ ∃ o, l = .obs o)
    (h : Quiet tr) : Quiet (l :: tr) := by
  intro l' hl'
  rcases List.mem_cons.1 hl' with rfl | hl'
  · exact hl
  · exact h l' hl'

/-- The emit step in context. -/
theorem emit_step {α : Type} (th : Option ThreadId) (o : HostObs) (k : Unit → P E σ α)
    (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ))
    (m : Machine.Config E σ) :
    UniqueStep prof hr dispatch
      { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ :: rest }
      (.obs o) { observe m o with ctl := ⟨th, .prog (k () >>= f), segs⟩ :: rest } := by
  have e : ∀ X Y : List (Activation E σ),
      ({ observe { m with ctl := X } o with ctl := Y } : Machine.Config E σ) =
        { observe m o with ctl := Y } := by
    intro X Y
    cases o <;> rfl
  have s₀ : UniqueStep prof hr dispatch
      { m with ctl := ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ :: rest }
      (.obs o) { observe { m with ctl :=
        ⟨th, .prog (.op (S := Eff E σ) (.emit o) fun r => k r >>= f), segs⟩ :: rest } o with
          ctl := ⟨th, .prog (k () >>= f), segs⟩ :: rest } :=
    .of_prog rfl (fun _ _ e => by cases e) (.emit (k := fun r => k r >>= f) rfl)
  rw [e] at s₀
  exact s₀

/-- **Silent runs are unlocked deterministic machine runs**, in any context, whose
observations are those of the run. -/
theorem detRunL {α : Type} {p : P E σ α} {m m' : Machine.Config E σ} {os : List HostObs}
    {a : α} (h : SRuns p m os a m') (hl : m.store.lockdown = false) (th : Option ThreadId) :
    ∀ (f : α → P E σ (Ret E)) (segs : List (Seg E σ)) (rest : List (Activation E σ)),
      ∃ tr, Quiet tr ∧ traceObs tr = os ∧ DetRunL prof hr dispatch
        { m with ctl := ⟨th, .prog (p >>= f), segs⟩ :: rest } tr
        { m' with ctl := ⟨th, .prog (f a), segs⟩ :: rest } := by
  induction h with
  | pure => intro f segs rest; exact ⟨[], (fun _ h' => nomatch h'), rfl, DetRunL.refl hl⟩
  | get _ ih =>
    intro f segs rest
    obtain ⟨tr, hq, ho, d⟩ := ih hl f segs rest
    exact ⟨_, hq.cons (.inl rfl), ho,
      .cons hl (.of_prog rfl (fun _ _ e => by cases e) (.get rfl)) d⟩
  | modify hf _ ih =>
    intro f segs rest
    obtain ⟨tr, hq, ho, d⟩ := ih ((hf _).trans hl) f segs rest
    exact ⟨_, hq.cons (.inl rfl), ho,
      .cons hl (.of_prog rfl (fun _ _ e => by cases e) (.modify rfl)) d⟩
  | @emit o k m _ _ _ _ ih =>
    intro f segs rest
    obtain ⟨tr, hq, ho, d⟩ :=
      ih ((congrArg CStore.lockdown (observe_store m o)).trans hl) f segs rest
    refine ⟨_, hq.cons (.inr ⟨o, rfl⟩), ?_, .cons hl (emit_step th o k f segs rest m) d⟩
    rw [← ho]
    rfl

end SRuns

end Silmaril.Proofs.Wasm.Component.Reference
