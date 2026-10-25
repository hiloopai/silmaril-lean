module

public import Silmaril.Wasm.SingleThreaded.Exec.Run
public import Silmaril.Wasm.SingleThreaded.Soundness

@[expose] public section

/-! # Run loop under a configuration-level invariant

`Exec/Run.lean` states its run-loop theorems for head functions that are sound
and exact at *every* store. The concrete head (a separate execution-head development (not included in this package)) is only
complete at `StoreOk` stores, so here the head hypotheses are only required at
stores satisfying a predicate `SI`, and a configuration invariant `I`
(preserved by `Step`) supplies `SI c.store` and the deep head invariant.

* generic: `run?_steps_inv`, `run?_stopped_no_step_inv`, `run?_complete_inv`;
* typed instance (`I c := ∃ ts, ConfigOk c ts`, `SI := StoreOk`):
  `run?_steps_typed`, `run?_stopped_no_step_typed`, `run?_complete_typed`.

Head functions are written with their explicit type rather than `HeadFn`.
-/

namespace Silmaril.Wasm.SingleThreaded.Exec.RunInv

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.SingleThreaded.Exec

variable {H : Type}

/-- Head soundness at the stores satisfying `SI`. -/
def HeadSoundAt (o : GrowOracle) (SI : Store H → Prop) (Inv : Frame → Admin → Prop)
    (head : Store H → Frame → List Val → Admin → Option (Nat × Config H)) : Prop :=
  ∀ s, SI s → ∀ f vs e k c, Inv f e → head s f vs e = some (k, c) →
    k ≤ vs.length ∧ Head (profile o) s f (vs.drop (vs.length - k)) e c

/-- Head exactness at the stores satisfying `SI`. -/
def HeadExactAt (o : GrowOracle) (SI : Store H → Prop) (Inv : Frame → Admin → Prop)
    (head : Store H → Frame → List Val → Admin → Option (Nat × Config H)) : Prop :=
  ∀ s, SI s → ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
    head s f vs e = some (args.length, c) ∨
      (head s f vs e = none ∧ IsCtxtHead (profile o) s f e c)

section generic
variable {o : GrowOracle} {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
  {I : Config H → Prop} {SI : Store H → Prop} {Inv : Frame → Admin → Prop}

theorem HeadExactAt.complete (hx : HeadExactAt o SI Inv head) {s : Store H} (hs : SI s) :
    ∀ f vs args e c, Inv f e → Head (profile o) s f args e c → (∃ q, vs = q ++ args) →
      head s f vs e = none → IsCtxtHead (profile o) s f e c := by
  intro f vs args e c hi hH hq hnone
  rcases hx s hs f vs args e c hi hH hq with h | ⟨-, h⟩
  · rw [h] at hnone; cases hnone
  · exact h

theorem step_of_step?
    (hIs : ∀ c, I c → SI c.store ∧ DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o SI Inv head) {c d : Config H} (hc : I c)
    (hs : step? head c = some d) : Step (profile o) noHost c d :=
  step?_sound (hhead c.store (hIs c hc).1) rfl (hIs c hc).2 hs

theorem inv_of_steps (hI : ∀ c c', I c → Step (profile o) noHost c c' → I c')
    {c c' : Config H} (h : Steps (profile o) noHost c c') (hc : I c) : I c' := by
  induction h with
  | refl => exact hc
  | tail _ hst ih => exact hI _ _ ih hst

/-- **Soundness** of the run loop under an invariant. -/
theorem run?_steps_inv (hI : ∀ c c', I c → Step (profile o) noHost c c' → I c')
    (hIs : ∀ c, I c → SI c.store ∧ DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o SI Inv head) :
    ∀ (n : Nat) (c : Config H) {c' : Config H} {b : Bool}, I c → run? head n c = (c', b) →
      Steps (profile o) noHost c c' ∧ I c'
  | 0, c, c', b, hc, h => by
    simp only [run?_zero, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨.refl, hc⟩
  | n + 1, c, c', b, hc, h => by
    cases hs : step? head c with
    | none =>
      rw [run?_succ_none hs] at h
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨.refl, hc⟩
    | some d =>
      have h1 := step_of_step? hIs hhead hc hs
      rw [run?_succ_some hs] at h
      obtain ⟨h2, h3⟩ := run?_steps_inv hI hIs hhead n d (hI _ _ hc h1) h
      exact ⟨Relation.ReflTransGen.head h1 h2, h3⟩

/-- A stopped result has no core step. -/
theorem run?_stopped_no_step_inv (hI : ∀ c c', I c → Step (profile o) noHost c c' → I c')
    (hIs : ∀ c, I c → SI c.store ∧ DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o SI Inv head) (hx : HeadExactAt o SI Inv head)
    {n : Nat} {c : Config H} (hc : I c) (h : (run? head n c).2 = true) (c' : Config H) :
    ¬ Step (profile o) noHost (run? head n c).1 c' := by
  intro hst
  have hi' := (run?_steps_inv hI hIs hhead n c hc (b := (run? head n c).2) rfl).2
  have := step?_complete (hx.complete (hIs _ hi').1) rfl (hIs _ hi').2 hst
  rw [run?_stopped n c h] at this
  cases this

theorem step?_maximal_aux (hx : HeadExactAt o SI Inv head) :
    ∀ (n : Nat) (c c₁ d : Config H), sizeOf c.code = n → SI c.store → DeepAll Inv c.frame c.code →
      Step (profile o) noHost c c₁ → step? head c = some d →
      Relation.ReflGen (Step (profile o) noHost) c₁ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro ⟨s₀, f, code⟩ c₁ d hn hSI hinv hstep hd
  simp only at hinv hn hSI
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
    rcases hx s₀ hSI f (vs₀ ++ args) args e c₀ hat.inv hH ⟨vs₀, rfl⟩ with hsome | ⟨hnone, hctx⟩
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
          ⟨s₀, f, is⟩ _ d' rfl hSI hat.2 hin hd'
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
          ⟨s₀, f, is⟩ _ d' rfl hSI hat.2 hin hd'
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
          ⟨s₀, fi, is⟩ _ d' rfl hSI hat.2 hin hd'
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

theorem step?_maximal (hx : HeadExactAt o SI Inv head) {c c₁ d : Config H}
    (hs : SI c.store) (hi : DeepAll Inv c.frame c.code) (h : Step (profile o) noHost c c₁)
    (hd : step? head c = some d) : Relation.ReflGen (Step (profile o) noHost) c₁ d :=
  step?_maximal_aux hx _ c c₁ d rfl hs hi h hd

theorem run?_complete_aux (hI : ∀ c c', I c → Step (profile o) noHost c c' → I c')
    (hIs : ∀ c, I c → SI c.store ∧ DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o SI Inv head) (hx : HeadExactAt o SI Inv head)
    {c' : Config H} (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∀ (n : Nat) (c : Config H), I c →
      Run.StepsN (Step (profile o) noHost) n c c' → run? head (n + 1) c = (c', true) := by
  intro n
  induction n with
  | zero =>
    intro c hi hN
    obtain rfl : c = c' := by cases hN; rfl
    cases hs : step? head c with
    | none => exact run?_succ_none hs
    | some d => exact absurd (step_of_step? hIs hhead hi hs) (hnf d)
  | succ m ih =>
    intro c hi hN
    cases hs : step? head c with
    | none =>
      rw [run?_succ_none hs]
      cases hN with
      | refl => rfl
      | step h _ =>
        have := step?_complete (hx.complete (hIs c hi).1) rfl (hIs c hi).2 h
        rw [hs] at this; cases this
    | some d =>
      have hcd : Step (profile o) noHost c d := step_of_step? hIs hhead hi hs
      rw [run?_succ_some hs]
      have hid := hI _ _ hi hcd
      cases hN with
      | refl => exact absurd hcd (hnf _)
      | step h₁ hrest =>
        rcases step?_maximal hx (hIs c hi).1 (hIs c hi).2 h₁ hs with _ | h₁d
        · exact ih d hid hrest
        · exact ih d hid (Run.StepsN.diamond (fun _ _ _ => step_join) hnf hrest h₁d)

/-- **Completeness** of the run loop under an invariant. -/
theorem run?_complete_inv (hI : ∀ c c', I c → Step (profile o) noHost c c' → I c')
    (hIs : ∀ c, I c → SI c.store ∧ DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o SI Inv head) (hx : HeadExactAt o SI Inv head)
    {c c' : Config H} (hc : I c)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, run? head n c = (c', true) := by
  obtain ⟨n, hn⟩ := Run.StepsN.of_rtg h
  exact ⟨n + 1, run?_complete_aux hI hIs hhead hx hnf n c hc hn⟩

end generic

/-! ## Typed instance: `I c := ∃ ts, ConfigOk c ts`, `SI := StoreOk` -/

section typed
variable {o : GrowOracle} {head : Store H → Frame → List Val → Admin → Option (Nat × Config H)}
  {Inv : Frame → Admin → Prop}

/-- Typing is preserved by host-free steps. -/
theorem typed_pres (c c' : Config H) (hc : ∃ ts, ConfigOk c ts)
    (h : Step (profile o) noHost c c') : ∃ ts, ConfigOk c' ts := by
  obtain ⟨ts, hts⟩ := hc
  exact ⟨ts, (Step.preservation (P := profile o) divHost_ok hts (Step.of_noHost divHost h)).1⟩

theorem typed_inv (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (c : Config H) (hc : ∃ ts, ConfigOk c ts) : StoreOk c.store ∧ DeepAll Inv c.frame c.code := by
  obtain ⟨ts, hts⟩ := hc
  exact ⟨ConfigOk.storeOk hts, hInv c ts hts⟩

/-- Typed soundness: the result is reachable and keeps the result type. -/
theorem run?_steps_typed
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head)
    (n : Nat) {c c' : Config H} {b : Bool} {ts : List CValType} (hc : ConfigOk c ts)
    (h : run? head n c = (c', b)) : Steps (profile o) noHost c c' ∧ ConfigOk c' ts :=
  run?_steps_inv (I := fun c => ConfigOk c ts) (fun _ _ hc hst =>
    (Step.preservation (P := profile o) divHost_ok hc (Step.of_noHost divHost hst)).1)
    (fun c hc => ⟨ConfigOk.storeOk hc, hInv c ts hc⟩) hhead n c hc h

theorem run?_stopped_no_step_typed
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head) (hx : HeadExactAt o StoreOk Inv head)
    {n : Nat} {c : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (h : (run? head n c).2 = true) (c' : Config H) :
    ¬ Step (profile o) noHost (run? head n c).1 c' :=
  run?_stopped_no_step_inv (I := fun c => ∃ ts, ConfigOk c ts) typed_pres (typed_inv hInv)
    hhead hx ⟨ts, hc⟩ h c'

theorem run?_complete_typed
    (hInv : ∀ (c : Config H) ts, ConfigOk c ts → DeepAll Inv c.frame c.code)
    (hhead : HeadSoundAt o StoreOk Inv head) (hx : HeadExactAt o StoreOk Inv head)
    {c c' : Config H} {ts : List CValType} (hc : ConfigOk c ts)
    (h : Steps (profile o) noHost c c') (hnf : ∀ x, ¬ Step (profile o) noHost c' x) :
    ∃ n, run? head n c = (c', true) :=
  run?_complete_inv (I := fun c => ∃ ts, ConfigOk c ts) typed_pres (typed_inv hInv)
    hhead hx ⟨ts, hc⟩ h hnf

end typed

end Silmaril.Wasm.SingleThreaded.Exec.RunInv
