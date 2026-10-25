module

public import Silmaril.Wasm.SingleThreaded.Exec.Status
public import Silmaril.Wasm.SingleThreaded.Determinism

@[expose] public section

/-! # Completeness of the fuelled runner `runC`

* Abstract rewriting: a relation whose peaks are joinable in at most one step
  on each side (`Det.Join`) has unique normal forms (`nf_unique_of_join`), and
  stepping off a counted path to a normal form never lengthens it.
* `Det.DStep.shrink`: when two host-free steps from the same configuration
  differ, both keep the frame and strictly shrink the code (the only source of
  non-determinism is bubbling of `TRAP` / `THROW_REF`). This gives a
  well-founded measure making every internal path to a normal form terminate.
* `status_ne_running_no_internal`, `status_running_iff`.
* `runC_complete`: if `(s, t)` reaches `(s', t')` by internal steps and
  `(s', t')` is not `running`, some fuel makes `runC` return exactly
  `(s', t', status o s' t')`.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Abstract rewriting -/

/-- Paths of a given length. -/
inductive NSteps {α : Type _} (R : α → α → Prop) : Nat → α → α → Prop
  | refl (x : α) : NSteps R 0 x x
  | head {x y z : α} {k : Nat} : R x y → NSteps R k y z → NSteps R (k + 1) x z

theorem NSteps.of_rtg {α : Type _} {R : α → α → Prop} {x y : α}
    (h : Relation.ReflTransGen R x y) : ∃ k, NSteps R k x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hxy _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .head hxy hk⟩

/-- Under the `Join` diamond, stepping off a counted path to a normal form does
not lengthen the remaining distance. -/
theorem NSteps.of_step_join {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b) {y : α} (hy : ∀ z, ¬ R y z) :
    ∀ {k : Nat} {x x' : α}, NSteps R k x y → R x x' → ∃ m ≤ k, NSteps R m x' y := by
  intro k
  induction k with
  | zero =>
    intro x x' h hs
    cases h
    exact absurd hs (hy _)
  | succ k ih =>
    intro x x' h hs
    cases h with
    | head hx1 hrest =>
      obtain ⟨w, h1, h2⟩ := hj hx1 hs
      cases h1 with
      | refl =>
        cases h2 with
        | refl => exact ⟨k, by omega, hrest⟩
        | single h2 => exact ⟨k + 1, le_rfl, .head h2 hrest⟩
      | single h1 =>
        obtain ⟨m, hm, hw⟩ := ih hrest h1
        cases h2 with
        | refl => exact ⟨m, by omega, hw⟩
        | single h2 => exact ⟨m + 1, by omega, .head h2 hw⟩

theorem NSteps.nf_eq {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b) {y z : α} (hy : ∀ w, ¬ R y w)
    (hz : ∀ w, ¬ R z w) {x : α} (hxz : Relation.ReflTransGen R x z) :
    ∀ {k : Nat}, NSteps R k x y → y = z := by
  induction hxz using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro k h
    cases h with
    | refl => rfl
    | head h _ => exact absurd h (hz _)
  | head hxx' _ ih =>
    intro k h
    obtain ⟨m, -, hm⟩ := NSteps.of_step_join hj hy h hxx'
    exact ih hm

/-- **Confluence from the `Join` diamond**: normal forms are unique. -/
theorem nf_unique_of_join {α : Type _} {R : α → α → Prop}
    (hj : ∀ {x a b : α}, R x a → R x b → Det.Join R a b) {x y z : α}
    (hxy : Relation.ReflTransGen R x y) (hxz : Relation.ReflTransGen R x z)
    (hy : ∀ w, ¬ R y w) (hz : ∀ w, ¬ R z w) : y = z := by
  obtain ⟨k, hk⟩ := NSteps.of_rtg hxy
  exact NSteps.nf_eq hj hy hz hxz hk

/-- Normal forms of `Internal o` are unique. -/
theorem Internal.nf_unique {o : GrowOracle} {x y z : Store H × Thread}
    (hxy : Relation.ReflTransGen (Internal o) x y) (hxz : Relation.ReflTransGen (Internal o) x z)
    (hy : ∀ w, ¬ Internal o y w) (hz : ∀ w, ¬ Internal o z w) : y = z :=
  nf_unique_of_join (fun ha hb => Internal.deterministic ha hb) hxy hxz hy hz

/-! ## Status versus internal steps -/

theorem status_ne_running_no_internal {o : GrowOracle} {s : Store H} {t : Thread}
    (hs : status o s t ≠ .running) : ∀ y, ¬ Internal o (s, t) y := by
  cases h : status o s t with
  | running => exact absurd h hs
  | returned r => exact returned_no_internal h
  | callout hc args => exact callout_no_internal h
  | stuck => exact stuck_no_internal h

theorem status_running_iff {o : GrowOracle} {s : Store H} {t : Thread} :
    status o s t = .running ↔ ∃ y, Internal o (s, t) y := by
  constructor
  · intro h
    obtain ⟨y, hy, -⟩ := running_unique h
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    by_contra hne
    exact status_ne_running_no_internal hne y hy

/-! ## Diverging steps shrink the code -/

namespace Det

/-- Frame kept and code strictly smaller than a head instruction `[e]`. -/
def ShrP (f : Frame) (e : Admin) (c : Config H) : Prop :=
  c.frame = f ∧ sizeOf c.code < sizeOf [e]

/-- Two successors of `⟨_, f, body⟩` are equal, or both keep the frame and
shrink the code. -/
def Shrink (f : Frame) (body : List Admin) (c₁ c₂ : Config H) : Prop :=
  c₁ = c₂ ∨ (c₁.frame = f ∧ c₂.frame = f ∧ sizeOf c₁.code < sizeOf body ∧
    sizeOf c₂.code < sizeOf body)

theorem Shrink.symm {f : Frame} {body : List Admin} {c₁ c₂ : Config H}
    (h : Shrink f body c₁ c₂) : Shrink f body c₂ c₁ := by
  rcases h with rfl | ⟨a, b, c, d⟩
  · exact .inl rfl
  · exact .inr ⟨b, a, d, c⟩

theorem join_and_of {α : Type _} {P : α → Prop} {x y : α} (hx : P x) (hy : P y) :
    Join (fun a b => P a ∧ P b) x y :=
  ⟨y, .single ⟨hx, hy⟩, .refl⟩

theorem join_and_cases {α : Type _} {P : α → Prop} {x y : α}
    (h : Join (fun a b => P a ∧ P b) x y) : x = y ∨ (P x ∧ P y) := by
  obtain ⟨z, h1, h2⟩ := h
  cases h1 with
  | refl =>
    cases h2 with
    | refl => exact .inl rfl
    | single h2 => exact .inr ⟨h2.2, h2.1⟩
  | single h1 =>
    cases h2 with
    | refl => exact .inr ⟨h1.1, h1.2⟩
    | single h2 => exact .inr ⟨h1.1, h2.1⟩

theorem sizeOf_append' {α : Type _} [SizeOf α] (A B : List α) :
    sizeOf (A ++ B) + 1 = sizeOf A + sizeOf B := by
  induction A with
  | nil => simp only [List.nil_append, List.nil.sizeOf_spec]; omega
  | cons a A ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

theorem sizeOf_list_pos {α : Type _} [SizeOf α] (l : List α) : 1 ≤ sizeOf l := by
  cases l <;> simp only [List.nil.sizeOf_spec, List.cons.sizeOf_spec] <;> omega

theorem sizeOf_list_two {α : Type _} [SizeOf α] {l : List α} (h : l ≠ []) : 2 ≤ sizeOf l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => have := sizeOf_list_pos l; simp only [List.cons.sizeOf_spec]; omega

theorem label_shrink {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f f₁ f₂ : Frame} {n : Nat} {cont : List Instr} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.label n cont is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Shrink f body c₁ c₂)
    (h₁ : DStep o ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : DStep o ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (fun a b : Config H =>
        ShrP f (.label n cont is) a ∧ ShrP f (.label n cont is) b)
      ⟨s₁, f₁, [.label n cont is₁]⟩ ⟨s₂, f₂, [.label n cont is₂]⟩ := by
  refine ⟨by simpa using hp, ?_⟩
  rcases ih s f is _ _ (by simp) h₁ h₂ with h | ⟨hf₁, hf₂, hl₁, hl₂⟩
  · simp only [Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Join.rfl'
  · simp only at hf₁ hf₂ hl₁ hl₂
    subst hf₁ hf₂
    exact join_and_of ⟨rfl, by simp; omega⟩ ⟨rfl, by simp; omega⟩

theorem handler_shrink {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f f₁ f₂ : Frame} {n : Nat} {cs : List Catch} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.handler n cs is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Shrink f body c₁ c₂)
    (h₁ : DStep o ⟨s, f, is⟩ ⟨s₁, f₁, is₁⟩) (h₂ : DStep o ⟨s, f, is⟩ ⟨s₂, f₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (fun a b : Config H =>
        ShrP f (.handler n cs is) a ∧ ShrP f (.handler n cs is) b)
      ⟨s₁, f₁, [.handler n cs is₁]⟩ ⟨s₂, f₂, [.handler n cs is₂]⟩ := by
  refine ⟨by simpa using hp, ?_⟩
  rcases ih s f is _ _ (by simp) h₁ h₂ with h | ⟨hf₁, hf₂, hl₁, hl₂⟩
  · simp only [Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Join.rfl'
  · simp only at hf₁ hf₂ hl₁ hl₂
    subst hf₁ hf₂
    exact join_and_of ⟨rfl, by simp; omega⟩ ⟨rfl, by simp; omega⟩

theorem frame_shrink {o : GrowKind → Nat → Nat → Nat → Bool} {s s₁ s₂ : Store H}
    {f fi fi₁ fi₂ : Frame} {n : Nat} {is is₁ is₂ : List Admin} {p : List Val}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf (Admin.frame n fi is) → DStep o ⟨s, f, body⟩ c₁ →
      DStep o ⟨s, f, body⟩ c₂ → Shrink f body c₁ c₂)
    (h₁ : DStep o ⟨s, fi, is⟩ ⟨s₁, fi₁, is₁⟩) (h₂ : DStep o ⟨s, fi, is⟩ ⟨s₂, fi₂, is₂⟩)
    (hp : ([] : List Val) = p ++ []) :
    p = [] ∧ Join (fun a b : Config H =>
        ShrP f (.frame n fi is) a ∧ ShrP f (.frame n fi is) b)
      ⟨s₁, f, [.frame n fi₁ is₁]⟩ ⟨s₂, f, [.frame n fi₂ is₂]⟩ := by
  refine ⟨by simpa using hp, ?_⟩
  rcases ih s fi is _ _ (by simp) h₁ h₂ with h | ⟨hf₁, hf₂, hl₁, hl₂⟩
  · simp only [Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Join.rfl'
  · simp only at hf₁ hf₂ hl₁ hl₂
    subst hf₁ hf₂
    exact join_and_of ⟨rfl, by simp; omega⟩ ⟨rfl, by simp; omega⟩

set_option maxHeartbeats 0 in
theorem Head.det_ctl_size {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {args₁ args₂ p : List Val} {e : Admin} {c₁ c₂ : Config H} (hk : famOf e = .control)
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
      Shrink f body c₁ c₂)
    (h₁ : Head (Profile.deterministic o) s f args₁ e c₁)
    (h₂ : Head (Profile.deterministic o) s f args₂ e c₂) (hp : args₁ = p ++ args₂) :
    p = [] ∧ Join (fun a b : Config H => ShrP f e a ∧ ShrP f e b) c₁ c₂ := by
  have hc : ∀ {k : Fam}, famOf e = k → k ≠ .control → False := fun h hk' => hk' (h ▸ hk)
  cases h₁ <;> try fam_excl
  all_goals (cases h₂ <;> try fam_excl)
  all_goals (try hd_close)
  case ctxtLabel.ctxtLabel => exact label_shrink ih ‹_› ‹_› hp
  case ctxtHandler.ctxtHandler => exact handler_shrink ih ‹_› ‹_› hp
  case ctxtFrame.ctxtFrame => exact frame_shrink ih ‹_› ‹_› hp
  all_goals (clear ih hc hk; vn_all; subst_vars)
  all_goals (repeat' rcr_step)
  all_goals (try ctl_single)
  all_goals (try ctl_step)
  all_goals (try ctl_body)
  all_goals (try ctl_same)
  all_goals (try ctl_vals)
  all_goals (try ctl_catch)
  case block.block => ctl_block
  case loop.loop => ctl_block
  case tryTable.tryTable => ctl_block
  case throw.throw =>
    rename_i ta₁ ti₁ ts₁ he₁ ht₁ ta₂ ti₂ ts₂ he₂ hn₂ ht₂ hn₁
    rw [ht₁] at ht₂
    cases ht₂
    cases Expand.det he₁ he₂
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero (by simp at hn₁; omega)
    simp only [List.nil_append]
    exact ⟨trivial, Join.rfl'⟩
  case call.call | returnCall.returnCall =>
    rename_i a₁ fi₁ hf₁ hx₁ a₂ fi₂ hf₂ hx₂
    rw [hx₁] at hx₂
    cases hx₂
    rw [hf₁] at hf₂
    cases hf₂
    exact ⟨by simpa using hp, Join.rfl'⟩
  case throwRefHandlerCatch.throwRefHandlerCatch | throwRefHandlerCatchRef.throwRefHandlerCatchRef =>
    rename_i e₁ he₁ ht₁ e₂ ht₂ he₂
    rw [he₁] at he₂
    cases he₂
    exact ⟨by simpa using hp, Join.rfl'⟩
  case brTableLt.brTableLt =>
    rename_i i₁ ls l' l₁ hi₁ i₂ l₂ hi₂
    obtain ⟨rfl, hx⟩ := singleton_hp hp
    cases hx
    rw [hi₁] at hi₂
    cases hi₂
    exact ⟨rfl, Join.rfl'⟩
  case brLabelZero.brLabelZero =>
    rename_i vs'₁ vs₁ l₁ r₁ hl₁ vs'₂ vs₂ l₂ r₂ hl₂ hn hb
    have h := congrArg fnv hb
    simp at h
    obtain ⟨h1, rfl, rfl⟩ := h
    obtain ⟨-, rfl⟩ := List.append_inj' h1 hn.symm
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnFrame.returnFrame =>
    rename_i vs'₁ vs₁ r₁ vs'₂ vs₂ r₂ hn hb
    obtain rfl := br_body_inj rfl hb hn.symm
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnCallRefFrameAddr.returnCallRefFrameAddr.inl.inl |
      returnCallRefFrameAddr.returnCallRefFrameAddr.inr.inr =>
    rename_i vs'₁ vs₁ a₁ r₁ fn₁ ps₁ rs₁ hf₁ he₁ hn₁ vs'₂ vs₂ a₂ r₂ fn₂ ps₂ rs₂ hf₂ he₂ hn₂ w₁ hvn₁ w₂ hb
    simp only [← vals_append] at hb
    obtain ⟨h1, hx, hc, -⟩ :=
      frame_body_inj (x := .ref (.func a₁)) (y := .ref (.func a₂)) rfl rfl hb
    cases hx
    cases hc
    rw [hf₁] at hf₂
    cases hf₂
    cases Expand.det he₁ he₂
    obtain ⟨-, rfl⟩ := List.append_inj' h1 (hn₁.trans hn₂.symm)
    exact ⟨by simpa using hp, Join.rfl'⟩
  case returnCallRefFrameAddr.returnCallRefFrameNull.inl.inl |
      returnCallRefFrameAddr.returnCallRefFrameNull.inr.inr =>
    rename_i hb
    simp only [← vals_append] at hb
    obtain ⟨-, hx, -⟩ := frame_body_inj (x := .ref (.func _)) (y := .ref .null) rfl rfl hb
    cases hx
  case returnCallRefFrameNull.returnCallRefFrameAddr.inl.inl |
      returnCallRefFrameNull.returnCallRefFrameAddr.inr.inr =>
    rename_i hb
    simp only [← vals_append] at hb
    obtain ⟨-, hx, -⟩ := frame_body_inj (x := .ref .null) (y := .ref (.func _)) rfl rfl hb
    cases hx
  case callRefNull.callRefFunc.inl | callRefNull.callRefFunc.inr =>
    rw [← List.append_assoc] at hp
    obtain ⟨-, hx⟩ := singleton_hp hp
    cases hx
  case callRefFunc.callRefFunc.inl | callRefFunc.callRefFunc.inr =>
    rename_i vs₁ a₁ fi₁ ps₁ rs₁ code₁ hf₁ he₁ hn₁ hcode₁ vs₂ a₂ fi₂ ps₂ rs₂ code₂ hf₂ he₂ hn₂ hcode₂
      ha w hc hvn'
    rw [← List.append_assoc] at ha
    obtain ⟨h1, hx⟩ := append_singleton_inj.mp ha
    cases hx
    rw [hf₁] at hf₂
    cases hf₂
    cases Expand.det he₁ he₂
    rw [hcode₁] at hcode₂
    cases hcode₂
    subst h1
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero (by simp at hn₁; omega)
    simp only [List.nil_append]
    exact ⟨trivial, Join.rfl'⟩


theorem head_shrink {o : GrowKind → Nat → Nat → Nat → Bool} {s : Store H} {f : Frame}
    {vs₁ vs₂ args₁ args₂ : List Val} {e : Admin} {rest : List Admin} {c₀₁ c₀₂ : Config H}
    (ih : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
      sizeOf body < sizeOf e → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
      Shrink f body c₁ c₂)
    (hva : vs₁ ++ args₁ = vs₂ ++ args₂)
    (hh₁ : Head (Profile.deterministic o) s f args₁ e c₀₁)
    (hh₂ : Head (Profile.deterministic o) s f args₂ e c₀₂) (p : List Val)
    (hp : args₁ = p ++ args₂) :
    Shrink f (vals vs₁ ++ (vals args₁ ++ e :: rest))
      ⟨c₀₁.store, c₀₁.frame, vals vs₁ ++ c₀₁.code ++ rest⟩
      ⟨c₀₂.store, c₀₂.frame, vals vs₂ ++ c₀₂.code ++ rest⟩ := by
  have key : p = [] ∧ (c₀₁ = c₀₂ ∨ (ShrP f e c₀₁ ∧ ShrP f e c₀₂)) := by
    by_cases hk : famOf e = .control
    · obtain ⟨hp', hj⟩ := Head.det_ctl_size hk ih hh₁ hh₂ hp
      exact ⟨hp', join_and_cases hj⟩
    · obtain ⟨hp', rfl⟩ := Head.det_fam hk hh₁ hh₂ hp
      exact ⟨hp', .inl rfl⟩
  obtain ⟨rfl, hj⟩ := key
  simp only [List.nil_append] at hp
  subst hp
  have : vs₁ = vs₂ := List.append_cancel_right hva
  subst this
  rcases hj with rfl | ⟨⟨hf₁, hl₁⟩, ⟨hf₂, hl₂⟩⟩
  · exact .inl rfl
  · have size : ∀ c : Config H, sizeOf c.code < sizeOf [e] →
        sizeOf (vals vs₁ ++ c.code ++ rest) < sizeOf (vals vs₁ ++ (vals args₁ ++ e :: rest)) := by
      intro c hc
      have a1 := sizeOf_append' (vals vs₁ ++ c.code) rest
      have a2 := sizeOf_append' (vals vs₁) c.code
      have a3 := sizeOf_append' (vals vs₁) (vals args₁ ++ e :: rest)
      have a4 := sizeOf_append' (vals args₁) (e :: rest)
      have a5 : sizeOf (e :: rest) = 1 + sizeOf e + sizeOf rest := by simp
      have a6 : sizeOf [e] = 1 + sizeOf e + 1 := by simp
      have a7 := sizeOf_list_pos (vals args₁)
      omega
    exact .inr ⟨hf₁, hf₂, size _ hl₁, size _ hl₂⟩

theorem bubble_size {p q : List Val} {X u r : List Admin} (hqu : q ≠ [] ∨ u ≠ []) :
    sizeOf (vals p ++ X ++ r) < sizeOf (vals (p ++ q) ++ X ++ (u ++ r)) := by
  have a1 := sizeOf_append' (vals p ++ X) r
  have a2 := sizeOf_append' (vals p) X
  have a3 := sizeOf_append' (vals (p ++ q) ++ X) (u ++ r)
  have a4 := sizeOf_append' (vals (p ++ q)) X
  have a5 := sizeOf_append' u r
  have a6 := sizeOf_append' (vals p) (vals q)
  rw [vals_append] at a3 a4 ⊢
  have a9 := sizeOf_append' (vals p ++ vals q) X
  have a7 := sizeOf_list_pos (vals q)
  have a8 := sizeOf_list_pos u
  rcases hqu with h | h
  · have := sizeOf_list_two (l := vals q) (by simpa using h)
    omega
  · have := sizeOf_list_two h
    omega

/-- **Diverging host-free steps shrink the code.** -/
theorem DStep.shrink {o : GrowKind → Nat → Nat → Nat → Bool} :
    ∀ (n : Nat) (s : Store H) (f : Frame) (code : List Admin) (c₁ c₂ : Config H),
      sizeOf code = n → DStep o ⟨s, f, code⟩ c₁ → DStep o ⟨s, f, code⟩ c₂ →
      Shrink f code c₁ c₂ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s f code c₁ c₂ hn h₁ h₂
  rcases Step.decomp h₁ with hd₁ | hb₁ <;> rcases Step.decomp h₂ with hd₂ | hb₂
  · obtain ⟨vs₁, args₁, e₁, rest₁, c₀₁, hf₁, hc₁, hh₁, rfl⟩ := fnv_headDec hd₁
    obtain ⟨vs₂, args₂, e₂, rest₂, c₀₂, hf₂, -, hh₂, rfl⟩ := fnv_headDec hd₂
    simp only at hf₁ hf₂ hc₁ hh₁ hh₂
    rw [hf₁] at hf₂
    simp only [Prod.mk.injEq, List.cons.injEq] at hf₂
    obtain ⟨hva, rfl, rfl⟩ := hf₂
    have ih' : ∀ (s : Store H) (f : Frame) (body : List Admin) (c₁ c₂ : Config H),
        sizeOf body < sizeOf e₁ → DStep o ⟨s, f, body⟩ c₁ → DStep o ⟨s, f, body⟩ c₂ →
        Shrink f body c₁ c₂ := by
      intro s f body c₁ c₂ hlt
      refine ih _ ?_ s f body c₁ c₂ rfl
      subst hn hc₁
      exact lt_trans hlt sizeOf_lt_code
    subst hc₁
    rcases append_eq_append_suffix hva with ⟨p, hp⟩ | ⟨p, hp⟩
    · exact head_shrink ih' hva hh₁ hh₂ p hp
    · have hc : vals vs₁ ++ (vals args₁ ++ e₁ :: rest₁) =
          vals vs₂ ++ (vals args₂ ++ e₁ :: rest₁) := by
        simp only [← List.append_assoc, ← vals_append, hva]
      rw [hc]
      exact (head_shrink ih' hva.symm hh₂ hh₁ p hp).symm
  · exact (headDec_bubble_false hd₁ hb₂).elim
  · exact (headDec_bubble_false hd₂ hb₁).elim
  · obtain ⟨p₁, q₁, X₁, u₁, r₁, hc₁, -, hqu₁, rfl⟩ := hb₁
    obtain ⟨p₂, q₂, X₂, u₂, r₂, hc₂, -, hqu₂, rfl⟩ := hb₂
    refine .inr ⟨rfl, rfl, ?_, ?_⟩
    · simp only
      have hc₁' : code = _ := hc₁
      rw [hc₁']
      exact bubble_size hqu₁
    · simp only
      have hc₂' : code = _ := hc₂
      rw [hc₂']
      exact bubble_size hqu₂

end Det

/-! ## Internal steps -/

/-- The size of a thread's code. -/
noncomputable def tsize (x : Store H × Thread) : Nat := sizeOf (x.2.config x.1).code

theorem Internal.shrink {o : GrowOracle} {x a b : Store H × Thread}
    (ha : Internal o x a) (hb : Internal o x b) : a = b ∨ tsize a < tsize x := by
  rcases x with ⟨s, t⟩
  rcases a with ⟨s₁, t₁⟩
  rcases b with ⟨s₂, t₂⟩
  obtain ⟨f₁, c₁, rfl, h₁⟩ := ha
  obtain ⟨f₂, c₂, rfl, h₂⟩ := hb
  rcases Det.DStep.shrink (o := o) _ (t.config s).store (t.config s).frame (t.config s).code
      _ _ rfl h₁ h₂ with h | ⟨-, -, hl, -⟩
  · simp only [Config.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .inl rfl
  · exact .inr hl

/-! ## The runner -/

theorem runC_stop {stepC : Config H → Option (Config H)} {s : Store H} {t : Thread} {n : Nat}
    (h : statusC stepC s t ≠ .running) : runC stepC (n + 1) s t = (s, t, statusC stepC s t) := by
  unfold runC
  generalize statusC stepC s t = st at *
  cases st <;> simp_all

theorem runC_step {stepC : Config H → Option (Config H)} {s s₁ : Store H} {t t₁ : Thread}
    {n : Nat} (h : statusC stepC s t = .running) (hi : internalC stepC (s, t) = some (s₁, t₁)) :
    runC stepC (n + 1) s t = runC stepC n s₁ t₁ := by
  simp only [runC, h, hi]

/-- **Completeness of `runC`.** If `(s, t)` reaches `(s', t')` by internal steps
and `(s', t')` is not running, then for some fuel the runner returns exactly
`(s', t', status o s' t')`. -/
theorem runC_complete {stepC : Config H → Option (Config H)} (o : GrowOracle)
    (hsound : ∀ (s : Store H) (t : Thread) c', stepC (t.config s) = some c' →
      Step (profile o) (fun _ _ _ _ => False) (t.config s) c')
    (hcomplete : ∀ (s : Store H) (t : Thread) c',
      Step (profile o) (fun _ _ _ _ => False) (t.config s) c' → (stepC (t.config s)).isSome)
    {s s' : Store H} {t t' : Thread}
    (hr : Relation.ReflTransGen (Internal o) (s, t) (s', t'))
    (hst : status o s' t' ≠ .running) :
    ∃ n, runC stepC n s t = (s', t', status o s' t') := by
  have hy : ∀ z, ¬ Internal o (s', t') z := status_ne_running_no_internal hst
  have hj : ∀ {x a b : Store H × Thread}, Internal o x a → Internal o x b →
      Det.Join (Internal o) a b := fun ha hb => Internal.deterministic ha hb
  have hsc : ∀ (s : Store H) (t : Thread), statusC stepC s t = status o s t :=
    fun s t => statusC_eq o (hsound s t) (hcomplete s t)
  have aux : ∀ (k m : Nat) (x : Store H × Thread), tsize x = m →
      NSteps (Internal o) k x (s', t') →
      ∃ n, runC stepC n x.1 x.2 = (s', t', status o s' t') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ihk =>
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
    rintro ⟨s₀, t₀⟩ hm hk
    by_cases hs0 : status o s₀ t₀ = .running
    · obtain ⟨⟨s₁', t₁'⟩, hx1'⟩ := status_running_iff.mp hs0
      have hsome : (stepC (t₀.config s₀)).isSome := by
        obtain ⟨f', code', -, hst'⟩ := hx1'
        exact hcomplete s₀ t₀ _ hst'
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hsome
      have hi : internalC stepC (s₀, t₀) = some (c'.store, .active c'.frame c'.code) := by
        simp [internalC, hc']
      have hx' := internalC_sound o (hsound s₀ t₀) hi
      have hrun : ∀ n, runC stepC (n + 1) s₀ t₀ =
          runC stepC n c'.store (.active c'.frame c'.code) :=
        fun n => runC_step ((hsc s₀ t₀).trans hs0) hi
      cases hk with
      | refl => exact absurd hs0 hst
      | @head _ x1 _ j hx1 hrest =>
        rcases Internal.shrink hx' hx1 with heq | hlt
        · subst heq
          obtain ⟨n, hn⟩ := ihk j (by omega) _ _ rfl hrest
          exact ⟨n + 1, (hrun n).trans hn⟩
        · obtain ⟨m', hm', hpath⟩ := NSteps.of_step_join hj hy (.head hx1 hrest) hx'
          rcases Nat.lt_or_eq_of_le hm' with hlt' | rfl
          · obtain ⟨n, hn⟩ := ihk m' hlt' _ _ rfl hpath
            exact ⟨n + 1, (hrun n).trans hn⟩
          · obtain ⟨n, hn⟩ := ihm _ (hm ▸ hlt) _ rfl hpath
            exact ⟨n + 1, (hrun n).trans hn⟩
    · have hno := status_ne_running_no_internal hs0
      cases hk with
      | refl =>
        refine ⟨1, ?_⟩
        rw [runC_stop (by rw [hsc]; exact hs0), hsc]
      | head h _ => exact absurd h (hno _)
  obtain ⟨k, hk⟩ := NSteps.of_rtg hr
  exact aux k _ (s, t) rfl hk

end Silmaril.Wasm.SingleThreaded
