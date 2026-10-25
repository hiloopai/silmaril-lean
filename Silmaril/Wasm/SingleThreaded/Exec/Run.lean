module

public import Silmaril.Wasm.SingleThreaded.Exec.Driver
public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Fuel-bounded run loop (single-threaded profile)

`run? head n c` iterates the generic driver `step? head` at most `n` times. It
returns the last configuration together with `true` when the driver stopped
(`step?` returned `none`) and `false` when the fuel ran out.

* `run?_steps`: the result is reachable (soundness).
* `run?_stopped`, `run?_stopped_no_step`: a stopped result has no step.
* `run?_complete`: if `c` reaches a normal form `c'`, some fuel makes the loop
  stop exactly at `c'`. Core reduction is only deterministic up to bubbling
  (`Det.DStep.join'`), so this needs the driver to be *maximal*: any other step
  from `c` reaches the driver's successor in at most one step
  (`step?_maximal`). That in turn needs the head function to return exactly
  every non-context head step (`HeadExact`), which is the shape of the family
  completeness lemmas (`…Step?_complete : … = some (args.length, c)`).
* `Config.outcome?`: classify a final configuration as a `Result`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det

variable {H : Type}

/-- The type of head-step functions the driver is generic over. -/
abbrev HeadFn (H : Type) := Store H → Frame → List Val → Admin → Option (Nat × Config H)

/-! ## The run loop -/

/-- Iterate `step? head` at most `n` times: `(c', true)` if the driver stopped at
`c'`, `(c', false)` if the fuel ran out at `c'`. -/
def run? (head : HeadFn H) : Nat → Config H → Config H × Bool
  | 0, c => (c, false)
  | n + 1, c =>
    match step? head c with
    | none => (c, true)
    | some c' => run? head n c'

section basic
variable {head : HeadFn H}

@[simp] theorem run?_zero (c : Config H) : run? head 0 c = (c, false) := rfl

theorem run?_succ_none {n : Nat} {c : Config H} (h : step? head c = none) :
    run? head (n + 1) c = (c, true) := by
  simp [run?, h]

theorem run?_succ_some {n : Nat} {c c' : Config H} (h : step? head c = some c') :
    run? head (n + 1) c = run? head n c' := by
  simp [run?, h]

/-- More fuel does not change a stopped result. -/
theorem run?_mono : ∀ {n m : Nat} {c c' : Config H}, run? head n c = (c', true) → n ≤ m →
    run? head m c = (c', true)
  | 0, _, _, _, h, _ => by simp at h
  | n + 1, m + 1, c, c', h, hle => by
    cases hs : step? head c with
    | none => rw [run?_succ_none hs] at h ⊢; exact h
    | some d =>
      rw [run?_succ_some hs] at h ⊢
      exact run?_mono h (by omega)
  | _ + 1, 0, _, _, _, hle => by omega

/-- **Stopped** results are driver-stuck. -/
theorem run?_stopped : ∀ (n : Nat) (c : Config H), (run? head n c).2 = true →
    step? head (run? head n c).1 = none
  | 0, c, h => by simp at h
  | n + 1, c, h => by
    cases hs : step? head c with
    | none => rw [run?_succ_none hs]; exact hs
    | some d =>
      rw [run?_succ_some hs] at h ⊢
      exact run?_stopped n d h

end basic

/-! ## Hypotheses on the head function -/

/-- Soundness of `head` at every store (the form `step?_sound` needs, for each
store met along the run). -/
def HeadSound (o : GrowOracle) (Inv : Frame → Admin → Prop) (head : HeadFn H) : Prop :=
  ∀ s f vs e k c, Inv f e → head s f vs e = some (k, c) →
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c

/-- Completeness of `head` at every store (the form `step?_complete` needs). -/
def HeadComplete (o : GrowOracle) (Inv : Frame → Admin → Prop) (head : HeadFn H) : Prop :=
  ∀ s f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
    head s f vs e = none → IsCtxtHead (profile o) s f e c

/-- Exact completeness: `head` returns every head step exactly, except context
steps into label/handler/frame bodies, on which it returns `none`. -/
def HeadExact (o : GrowOracle) (Inv : Frame → Admin → Prop) (head : HeadFn H) : Prop :=
  ∀ s f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
    head s f vs e = some (args.length, c) ∨
      (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c)

/-- `Inv` (deeply) is preserved by core reduction. -/
def InvPres (o : GrowOracle) (Inv : Frame → Admin → Prop) : Prop :=
  ∀ c c' : Config H, DeepAll Inv c.frame c.code → Step (profile o) noHost c c' →
    DeepAll Inv c'.frame c'.code

theorem HeadExact.complete {o : GrowOracle} {Inv : Frame → Admin → Prop} {head : HeadFn H}
    (hx : HeadExact o Inv head) : HeadComplete o Inv head := by
  intro s f vs args e c hi hH hq hnone
  rcases hx s f vs args e c hi hH hq with h | ⟨-, h⟩
  · rw [h] at hnone; cases hnone
  · exact h

mutual
theorem deepAll_true (f : Frame) : (l : List Admin) → DeepAll (fun _ _ => True) f l
  | [] => by simp only [DeepAll]
  | e :: es => by simp only [DeepAll]; exact ⟨deepAt_true f e, deepAll_true f es⟩

theorem deepAt_true (f : Frame) : (e : Admin) → Drv.DeepAt (fun _ _ => True) f e
  | .label _ _ is => by simp only [Drv.DeepAt]; exact ⟨trivial, deepAll_true f is⟩
  | .handler _ _ is => by simp only [Drv.DeepAt]; exact ⟨trivial, deepAll_true f is⟩
  | .frame _ fi is => by simp only [Drv.DeepAt]; exact ⟨trivial, deepAll_true fi is⟩
  | .plain _ => by simp only [Drv.DeepAt]
  | .ref _ => by simp only [Drv.DeepAt]
  | .trap => by simp only [Drv.DeepAt]
  | .callRefType _ => by simp only [Drv.DeepAt]
  | .returnCallRefType _ => by simp only [Drv.DeepAt]
end

theorem invPres_true {o : GrowOracle} : InvPres (H := H) o (fun _ _ => True) :=
  fun _ _ _ _ => deepAll_true _ _

/-! ## Soundness -/

section sound
variable {o : GrowOracle} {head : HeadFn H} {Inv : Frame → Admin → Prop}

theorem deepAll_of_steps (hpres : InvPres (H := H) o Inv) {c c' : Config H}
    (h : Steps (profile o) noHost c c') (hi : DeepAll Inv c.frame c.code) :
    DeepAll Inv c'.frame c'.code := by
  induction h with
  | refl => exact hi
  | tail _ hst ih => exact hpres _ _ ih hst

/-- **Soundness** of the run loop. -/
theorem run?_steps (hhead : HeadSound o Inv head) (hpres : InvPres (H := H) o Inv) :
    ∀ (n : Nat) (c : Config H), DeepAll Inv c.frame c.code →
      Steps (profile o) noHost c (run? head n c).1
  | 0, c, _ => .refl
  | n + 1, c, hi => by
    cases hs : step? head c with
    | none => rw [run?_succ_none hs]
    | some d =>
      have h1 : Step (profile o) noHost c d := step?_sound (hhead c.store) rfl hi hs
      rw [run?_succ_some hs]
      exact Relation.ReflTransGen.head h1 (run?_steps hhead hpres n d (hpres _ _ hi h1))

/-- Soundness of the run loop without an invariant. -/
theorem run?_steps_true
    (hhead : ∀ s f vs e k c, head s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c)
    (n : Nat) (c : Config H) : Steps (profile o) noHost c (run? head n c).1 :=
  run?_steps (Inv := fun _ _ => True) (fun s f vs e k c _ h => hhead s f vs e k c h)
    invPres_true n c (deepAll_true _ _)

/-- A stopped result has no core step. -/
theorem run?_stopped_no_step (hhead : HeadSound o Inv head) (hcomp : HeadComplete o Inv head)
    (hpres : InvPres (H := H) o Inv) {n : Nat} {c : Config H} (hi : DeepAll Inv c.frame c.code)
    (h : (run? head n c).2 = true) (c' : Config H) :
    ¬ Step (profile o) noHost (run? head n c).1 c' := by
  intro hst
  have hi' := deepAll_of_steps hpres (run?_steps hhead hpres n c hi) hi
  have := step?_complete (hcomp (run? head n c).1.store) rfl hi' hst
  rw [run?_stopped n c h] at this
  cases this

end sound

/-! ## Completeness via determinism -/

namespace Run

/-- Reduction in at most `n` steps. -/
inductive StepsN {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop where
  | refl (n : Nat) (a : α) : StepsN R n a a
  | step {n : Nat} {a b c : α} : R a b → StepsN R n b c → StepsN R (n + 1) a c

theorem StepsN.mono {α : Type _} {R : α → α → Prop} {n : Nat} {a b : α} (h : StepsN R n a b) :
    ∀ {m : Nat}, n ≤ m → StepsN R m a b := by
  induction h with
  | refl n a => intro m _; exact .refl m a
  | @step n a b c hab _ ih =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .step hab (ih (by omega))

theorem StepsN.of_rtg {α : Type _} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) : ∃ n, StepsN R n a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl 0 _⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hab hn⟩

/-- In a relation with the one-step diamond property, a step out of a
configuration that normalises in at most `n` steps leads to one that also
normalises in at most `n` steps. -/
theorem StepsN.diamond {α : Type _} {R : α → α → Prop}
    (hjoin : ∀ a b c, R a b → R a c → Join R b c) {c' : α} (hnf : ∀ x, ¬ R c' x)
    {n : Nat} {c : α} (h : StepsN R n c c') : ∀ {d : α}, R c d → StepsN R n d c' := by
  induction h with
  | refl n a => intro d hd; exact absurd hd (hnf d)
  | @step n a b _ hab hbc ih =>
    intro d hd
    obtain ⟨z, hdz, hbz⟩ := hjoin a d b hd hab
    cases hbz with
    | refl =>
      cases hdz with
      | refl => exact hbc.mono (by omega)
      | single h => exact .step h hbc
    | single hbz' =>
      have hz := ih hnf hbz'
      cases hdz with
      | refl => exact hz.mono (by omega)
      | single h => exact .step h hz

end Run

section complete
variable {o : GrowOracle} {head : HeadFn H} {Inv : Frame → Admin → Prop}

theorem Head.args_nil_label {P : Profile} {s : Store H} {f : Frame} {args : List Val}
    {n : Nat} {cont : List Instr} {is : List Admin} {c : Config H}
    (h : Head P s f args (.label n cont is) c) : args = [] := by
  generalize he : Admin.label n cont is = e at h
  cases h <;> first
    | rfl
    | (cases he; done)
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (ParametricStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (NumericStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VectorStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VariableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (TableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (MemoryStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (RefStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (AggregateStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; simp_all [Admin.IsCallRef])

theorem Head.args_nil_handler {P : Profile} {s : Store H} {f : Frame} {args : List Val}
    {n : Nat} {cs : List Catch} {is : List Admin} {c : Config H}
    (h : Head P s f args (.handler n cs is) c) : args = [] := by
  generalize he : Admin.handler n cs is = e at h
  cases h <;> first
    | rfl
    | (cases he; done)
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (ParametricStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (NumericStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VectorStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VariableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (TableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (MemoryStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (RefStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (AggregateStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; simp_all [Admin.IsCallRef])

theorem Head.args_nil_frame {P : Profile} {s : Store H} {f : Frame} {args : List Val}
    {n : Nat} {fi : Frame} {is : List Admin} {c : Config H}
    (h : Head P s f args (.frame n fi is) c) : args = [] := by
  generalize he : Admin.frame n fi is = e at h
  cases h <;> first
    | rfl
    | (cases he; done)
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (ParametricStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (NumericStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VectorStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (VariableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (TableStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (MemoryStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (RefStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; rename_i hst; exact absurd (famOf_of_shape (AggregateStep.shape hst)).2 (by simp only [famOf]; decide))
    | (subst he; simp_all [Admin.IsCallRef])

/-- **Maximality** of the driver: every step out of `c` reaches the driver's
successor in at most one step. -/
theorem step?_maximal_aux (hx : HeadExact o Inv head) :
    ∀ (n : Nat) (c c₁ d : Config H), sizeOf c.code = n → DeepAll Inv c.frame c.code →
      Step (profile o) noHost c c₁ → step? head c = some d →
      Relation.ReflGen (Step (profile o) noHost) c₁ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c₁ d hn hinv hstep hd
  simp only at hinv hn
  rcases Step.decomp hstep with hdec | hb
  · obtain ⟨vs₀, args, e, rest, c₀, hcode, hH, rfl⟩ := hdec
    simp only at hcode hH
    have hg := hH.good
    have hs : splitVals code = (vs₀ ++ args, e :: rest) := by
      rw [hcode, ← List.append_assoc, ← vals_append]; exact splitVals_vals_cons hg.val_none rest
    rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
    have hat : Drv.DeepAt Inv f e := by
      rw [hcode, ← List.append_assoc, ← vals_append] at hinv; exact Drv.deepAll_split hinv
    have htrap : Drv.isTrap e = false := by
      cases e <;> simp [Drv.isTrap]; exact hg.ne_trap rfl
    have hthrow : Drv.throwAddr? (vs₀ ++ args) e = none := by
      unfold Drv.throwAddr?
      split
      · rw [hg.throwRef rfl]; simp
      · rfl
    simp only [Drv.layer, htrap, hthrow] at hd
    rcases hx s₀ f (vs₀ ++ args) args e c₀ hat.inv hH ⟨vs₀, rfl⟩ with hsome | ⟨hnone, hctx⟩
    · rw [hsome] at hd
      simp only [Option.some.injEq] at hd
      subst hd
      have : (vs₀ ++ args).take ((vs₀ ++ args).length - args.length) = vs₀ := by
        simp
      simp only [this]
      exact .refl
    · rw [hnone] at hd
      simp only at hd
      rcases hctx with ⟨n', cont, is, s', f', is', rfl, rfl, hin⟩ |
        ⟨n', cs, is, s', f', is', rfl, rfl, hin⟩ | ⟨n', fi, is, s', fi', is', rfl, rfl, hin⟩
      · obtain rfl := Head.args_nil_label hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_label_body (n := n') (cont := cont) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .label n' cont is) (rest := rest)
              omega)
          ⟨s₀, f, is⟩ _ d' rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest _ _ (lift_label n' cont _ _ h)
          exact .single (by simpa using this)
      · obtain rfl := Head.args_nil_handler hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_handler_body (n := n') (cs := cs) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .handler n' cs is) (rest := rest)
              omega)
          ⟨s₀, f, is⟩ _ d' rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest _ _ (lift_handler n' cs _ _ h)
          exact .single (by simpa using this)
      · obtain rfl := Head.args_nil_frame hH
        obtain ⟨d', hd', rfl⟩ := Option.map_eq_some_iff.mp hd
        have hr := ih (sizeOf is)
          (by rw [← hn, hcode]; have := Drv.sizeOf_frame_body (n := n') (fi := fi) (is := is)
              have := sizeOf_lt_code (vs := vs₀) (args := []) (e := .frame n' fi is) (rest := rest)
              omega)
          ⟨s₀, fi, is⟩ _ d' rfl hat.2 hin hd'
        cases hr with
        | refl => simpa using (Relation.ReflGen.refl : Relation.ReflGen (Step (profile o) noHost) _ _)
        | single h =>
          have := lift_instrs vs₀ rest ⟨s', f, _⟩ ⟨d'.store, f, _⟩ (lift_frame n' f _ _ h)
          exact .single (by simpa using this)
  · obtain ⟨p, q, u, r, hqu, ⟨-, hcode, rfl⟩ | ⟨a, -, hcode, rfl⟩⟩ := fnv_bubble hb <;>
      simp only at hcode
    · have hs : splitVals code = (p ++ q, .trap :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
      simp only [Drv.layer, Drv.isTrap] at hd
      split at hd
      · cases hd
      · cases hd
        exact bubble_to (o := o) (.inl rfl)
    · have hs : splitVals code = (p ++ q ++ [.ref (.exn a)], .plain .throwRef :: (u ++ r)) := by
        rw [hcode]; exact splitVals_vals_cons rfl _
      rw [step?_cons (c := ⟨s₀, f, code⟩) hs] at hd
      simp only [Drv.layer, Drv.isTrap, Drv.throwAddr?, List.getLast?_append,
        List.getLast?_singleton, Option.some_or, List.dropLast_concat] at hd
      split at hd
      · cases hd
      · cases hd
        exact bubble_to (o := o) (.inr ⟨a, rfl⟩)

theorem step?_maximal (hx : HeadExact o Inv head) {c c₁ d : Config H}
    (hi : DeepAll Inv c.frame c.code) (h : Step (profile o) noHost c c₁)
    (hd : step? head c = some d) : Relation.ReflGen (Step (profile o) noHost) c₁ d :=
  step?_maximal_aux hx _ c c₁ d rfl hi h hd

theorem step_join {c c₁ c₂ : Config H} (h₁ : Step (profile o) noHost c c₁)
    (h₂ : Step (profile o) noHost c c₂) : Join (Step (profile o) noHost) c₁ c₂ :=
  DStep.join' (o := o) h₁ h₂

theorem run?_complete_aux (hhead : HeadSound o Inv head) (hx : HeadExact o Inv head)
    (hpres : InvPres (H := H) o Inv) {c' : Config H} (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∀ (n : Nat) (c : Config H), DeepAll Inv c.frame c.code →
      Run.StepsN (Step (profile o) noHost) n c c' → run? head (n + 1) c = (c', true) := by
  intro n
  induction n with
  | zero =>
    intro c hi hN
    obtain rfl : c = c' := by cases hN; rfl
    cases hs : step? head c with
    | none => exact run?_succ_none hs
    | some d => exact absurd (step?_sound (hhead c.store) rfl hi hs) (hnf d)
  | succ m ih =>
    intro c hi hN
    cases hs : step? head c with
    | none =>
      rw [run?_succ_none hs]
      cases hN with
      | refl => rfl
      | step h _ =>
        have := step?_complete (hx.complete c.store) rfl hi h
        rw [hs] at this; cases this
    | some d =>
      have hcd : Step (profile o) noHost c d := step?_sound (hhead c.store) rfl hi hs
      rw [run?_succ_some hs]
      have hid := hpres _ _ hi hcd
      cases hN with
      | refl => exact absurd hcd (hnf _)
      | step h₁ hrest =>
        rcases step?_maximal hx hi h₁ hs with _ | h₁d
        · exact ih d hid hrest
        · exact ih d hid (Run.StepsN.diamond (fun _ _ _ => step_join) hnf hrest h₁d)

/-- **Completeness** of the run loop: if `c` reaches a configuration `c'` with no
core step, some fuel makes the loop stop exactly at `c'`. -/
theorem run?_complete (hhead : HeadSound o Inv head) (hx : HeadExact o Inv head)
    (hpres : InvPres (H := H) o Inv) {c c' : Config H} (hi : DeepAll Inv c.frame c.code)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, run? head n c = (c', true) := by
  obtain ⟨n, hn⟩ := Run.StepsN.of_rtg h
  exact ⟨n + 1, run?_complete_aux hhead hx hpres hnf n c hi hn⟩

/-- Completeness of the run loop without an invariant. -/
theorem run?_complete_true
    (hhead : ∀ s f vs e k c, head s f vs e = some (k, c) →
      k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c)
    (hx : ∀ s f vs args e c, Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = some (args.length, c) ∨
        (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c))
    {c c' : Config H} (h : Steps (profile o) noHost c c')
    (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, run? head n c = (c', true) :=
  run?_complete (Inv := fun _ _ => True) (fun s f vs e k c _ h => hhead s f vs e k c h)
    (fun s f vs args e c _ h hq => hx s f vs args e c h hq) invPres_true (deepAll_true _ _) h hnf

end complete

/-! ## Results -/

/-- Classify a final instruction sequence: values, a trap, or an uncaught
exception (`(REF.EXN_ADDR a) THROW_REF`). -/
def codeOutcome? : List Admin → Option Result
  | [.trap] => some .trap
  | [.ref (.exn a), .plain .throwRef] => some (.throw a)
  | code => (code.mapM Admin.val?).map .values

/-- Classify a final configuration. -/
def _root_.Silmaril.Wasm.Execution.Core.Config.outcome? (c : Config H) : Option Result := codeOutcome? c.code

theorem mapM_val?_eq_some : ∀ {l : List Admin} {vs : List Val},
    l.mapM Admin.val? = some vs → l = vals vs
  | [], vs, h => by simp at h; subst h; rfl
  | a :: l, vs, h => by
    rw [List.mapM_cons] at h
    cases hv : a.val? with
    | none => simp [hv] at h
    | some v =>
      cases hws : l.mapM Admin.val? with
      | none => simp [hv, hws] at h
      | some ws =>
        simp [hv, hws] at h
        subst h
        rw [mapM_val?_eq_some hws, val?_eq_some.mp hv]
        rfl

theorem codeOutcome?_sound {code : List Admin} {r : Result} (h : codeOutcome? code = some r) :
    code = r.toAdmin := by
  unfold codeOutcome? at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
    exact mapM_val?_eq_some hvs

/-- **Soundness** of the classifier: the code is the lifted result. -/
theorem _root_.Silmaril.Wasm.Execution.Core.Config.outcome?_sound {c : Config H} {r : Result} (h : c.outcome? = some r) :
    c.code = r.toAdmin :=
  codeOutcome?_sound h

end Silmaril.Wasm.SingleThreaded.Exec
