module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdCatch

/-!
# The backward simulation of the tail-call rewrite: steps inside the target's wrappers

* `return_stuck`: `val* RETURN` does not step on its own;
* `fill_inv'`: a step of a nest of labels around code whose first non-value is a `CALL_REF` or a
  frame is a step of that code;
* `pw_step`: a step of a wrapper body whose innermost label holds values before `RETURN` brings
  `RETURN` out of one label (`return-label`), keeping the shape, the store and the frame.

New proofs (`return_stuck` follows silmaril's `Closure.Step.returnCallRef_stuck_aux`).
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- `val* RETURN` does not step on its own. -/
theorem return_stuck_aux {c c' : Config H} (h : Step P host c c') :
    ∀ us : List Val, c.code = vals us ++ [.plain .return_] → False := by
  induction h with
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro us hc
    dsimp only at hc
    obtain ⟨u₁, e', is₁, he', rfl⟩ := exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ u₁) ++ e' :: (is₁ ++ rest) = vals us ++ Admin.plain .return_ :: [] := by
      rw [← hc]; simp
    obtain ⟨-, rfl, h3⟩ := vals_append_cons_inj he' rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h3
    exact ih u₁ (by simp)
  | @trapInstrs s f vs₀ rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals us ++ Admin.plain .return_ :: [] := by
      rw [← hc]; simp
    exact absurd (vals_append_cons_inj val?_trap rfl hc').2.1 (by simp)
  | @throwRefInstrs s f vs₀ a rest hne =>
    intro us hc
    dsimp only at hc
    have hc' : vals (vs₀ ++ [.ref (.exn a)]) ++ Admin.plain .throwRef :: rest =
        vals us ++ Admin.plain .return_ :: [] := by
      rw [← hc]; simp [vals, throwing, Val.toAdmin]
    exact absurd (vals_append_cons_inj val?_throwRef rfl hc').2.1 (by simp)
  | _ =>
    intro us hc
    first
      | (have := congrArg List.getLast? hc; simp at this; done)
      | (have := congrArg List.getLast? hc; simp at this; subst this;
          simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)
      | (rename_i hf; cases hf <;>
          (have := congrArg List.getLast? hc; simp [constI32, Val.i32, Val.toAdmin] at this) <;>
          done)

theorem return_stuck {s s' : Store H} {f f' : Frame} {us : List Val} {es' : List Admin}
    (h : Step P host ⟨s, f, vals us ++ [.plain .return_]⟩ ⟨s', f', es'⟩) : False :=
  return_stuck_aux h us rfl

/-- The heads at which a nest of labels steps only inside: a `CALL_REF` or a frame. -/
def InnerHead (b : Admin) : Prop := b.IsCallRef ∨ ∃ n fi bb, b = .frame n fi bb

theorem InnerHead.val?_eq {b : Admin} (h : InnerHead b) : b.val? = none := by
  rcases h with h | ⟨_, _, _, rfl⟩
  · exact Admin.val?_of_isCallRef h
  · rfl

/-- The first non-value of a nest around an inner head is that head or a label. -/
theorem fill_head' (N : NCtx) {V : List Val} {b : Admin} {Y : List Admin} :
    ∃ V' b' r, N.fill (vals V ++ b :: Y) = vals V' ++ b' :: r ∧
      (b' = b ∨ ∃ n cont bb, b' = .label n cont bb) := by
  cases N with
  | hole => exact ⟨V, b, Y, rfl, .inl rfl⟩
  | label V₀ n cont N L => exact ⟨V₀, _, L, rfl, .inr ⟨_, _, _, rfl⟩⟩

/-- **A step of a nest of labels around an inner head** is a step of the innermost code. -/
theorem fill_inv' {V : List Val} {b : Admin} {Y : List Admin} (hb : InnerHead b) :
    ∀ (N : NCtx) {t t' : Store H} {g g' : Frame} {Z : List Admin},
      Step P host ⟨t, g, N.fill (vals V ++ b :: Y)⟩ ⟨t', g', Z⟩ →
      ∃ X', Step P host ⟨t, g, vals V ++ b :: Y⟩ ⟨t', g', X'⟩ ∧ Z = N.fill X'
  | .hole, t, t', g, g', Z, h => ⟨Z, h, rfl⟩
  | .label V₀ n cont N L, t, t', g, g', Z, h => by
    rcases Step.split_head rfl h with ⟨ws, us, is', hV, hs, rfl⟩ | ⟨hc', -⟩ | ⟨hc', -⟩
    rotate_left
    · cases hc'
    · cases hc'
    obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
    have hbad : ∀ (vs : List Val) (k : Admin) (r : List Admin), k.val? = none →
        N.fill (vals V ++ b :: Y) = vals vs ++ k :: r → InnerHead k ∨ ∃ n cont bb, k = .label n cont bb := by
      intro vs k r hk hx
      obtain ⟨V', b', r', he, hb'⟩ := fill_head' N (V := V) (b := b) (Y := Y)
      rw [he] at hx
      have hbv : b'.val? = none := by
        rcases hb' with rfl | ⟨_, _, _, rfl⟩
        · exact hb.val?_eq
        · rfl
      obtain ⟨-, rfl, -⟩ := vals_append_cons_inj hbv hk hx
      rcases hb' with rfl | h
      · exact .inl hb
      · exact .inr h
    have hnot : ∀ k : Admin, (InnerHead k ∨ ∃ n cont bb, k = .label n cont bb) →
        k ≠ .trap ∧ k ≠ .plain .return_ ∧ (∀ l, k ≠ .plain (.br l)) ∧ ¬ k.IsReturnCallRef ∧
          k ≠ .plain .throwRef := by
      intro k hk
      rcases hk with (hk | ⟨_, _, _, rfl⟩) | ⟨_, _, _, rfl⟩
      · exact ⟨fun h => by subst h; exact hk, fun h => by subst h; exact hk,
          fun l h => by subst h; exact hk, fun h => Admin.IsCallRef.not_isReturnCallRef hk h,
          fun h => by subst h; exact hk⟩
      all_goals exact ⟨by simp, by simp, by simp, by simp [Admin.IsReturnCallRef], by simp⟩
    generalize hB : N.fill (vals V ++ b :: Y) = B at hred
    cases hred with
    | ctxt hs₁ =>
      subst hB
      obtain ⟨X', hX, rfl⟩ := fill_inv' hb N hs₁
      refine ⟨X', hX, ?_⟩
      simp [NCtx.fill, hV]
    | values vs =>
      exfalso
      obtain ⟨V', b', r', he, hb'⟩ := fill_head' N (V := V) (b := b) (Y := Y)
      have hm : b' ∈ vals vs := by rw [← hB, he]; simp
      obtain ⟨w, rfl⟩ := PC.mem_vals hm
      rcases hb' with hb' | ⟨_, _, _, hb'⟩
      · have := hb.val?_eq; rw [← hb'] at this; simp at this
      · rcases w with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hb'
    | @brZero vs' vs l rest hl hn =>
      exact ((hnot _ (hbad (vs' ++ vs) (.plain (.br l)) rest rfl (by rw [hB]; simp))).2.2.1 l
        rfl).elim
    | @brSucc vs l rest hl =>
      exact ((hnot _ (hbad vs (.plain (.br l)) rest rfl (by rw [hB]; simp))).2.2.1 l rfl).elim
    | @returnCallRef vs c₀ rest hc₀ =>
      exact ((hnot _ (hbad vs c₀ rest (Admin.val?_of_isReturnCallRef hc₀) (by rw [hB]; simp))).2.2.2.1
        hc₀).elim
    | @return_ vs rest =>
      exact ((hnot _ (hbad vs (.plain .return_) rest rfl (by rw [hB]; simp))).2.1 rfl).elim
    | throwRef a =>
      exact ((hnot _ (hbad [.ref (.exn a)] (.plain .throwRef) [] rfl (by
        rw [hB]; simp [throwing, vals, Val.toAdmin]))).2.2.2.2 rfl).elim
    | trap =>
      exact ((hnot _ (hbad [] .trap [] rfl (by rw [hB]; simp))).1 rfl).elim

/-- The label rules other than `ctxt-label` and `return-label` do not apply to a body whose
first non-value is `RETURN` or a label. -/
theorem labelRed_ret_or_label {t t' : Store H} {g g' : Frame} {n : Nat} {cont : List Instr}
    {B is₂ : List Admin} (hred : Closure.LabelRed P host t g n cont B t' g' is₂) {V : List Val}
    {e : Admin} {r : List Admin} (hB : B = vals V ++ e :: r)
    (he : e = .plain .return_ ∨ ∃ n' cont' bb, e = .label n' cont' bb) :
    (∃ B', Step P host ⟨t, g, B⟩ ⟨t', g', B'⟩ ∧ is₂ = [.label n cont B']) ∨
      (e = .plain .return_ ∧ t' = t ∧ g' = g ∧ ∃ vs rest, B = vals vs ++ [.plain .return_] ++ rest ∧
        is₂ = vals vs ++ [.plain .return_]) := by
  have hev : e.val? = none := by rcases he with rfl | ⟨_, _, _, rfl⟩ <;> rfl
  cases hred with
  | ctxt hs => exact .inl ⟨_, hs, rfl⟩
  | values vs =>
    exfalso
    have hm : e ∈ vals vs := by rw [hB]; simp
    obtain ⟨w, rfl⟩ := PC.mem_vals hm
    simp at hev
  | @brZero vs' vs l rest hl hn =>
    exfalso
    have h2 : vals V ++ e :: r = vals (vs' ++ vs) ++ Admin.plain (.br l) :: rest := by
      rw [← hB]; simp
    have := (vals_append_cons_inj hev rfl h2).2.1
    rcases he with rfl | ⟨_, _, _, rfl⟩ <;> cases this
  | @brSucc vs l rest hl =>
    exfalso
    have h2 : vals V ++ e :: r = vals vs ++ Admin.plain (.br l) :: rest := by rw [← hB]; simp
    have := (vals_append_cons_inj hev rfl h2).2.1
    rcases he with rfl | ⟨_, _, _, rfl⟩ <;> cases this
  | @returnCallRef vs c₀ rest hc₀ =>
    exfalso
    have h2 : vals V ++ e :: r = vals vs ++ c₀ :: rest := by rw [← hB]; simp
    have := (vals_append_cons_inj hev (Admin.val?_of_isReturnCallRef hc₀) h2).2.1
    subst this
    rcases he with rfl | ⟨_, _, _, rfl⟩ <;> exact hc₀
  | @return_ vs rest =>
    have h2 : vals V ++ e :: r = vals vs ++ Admin.plain .return_ :: rest := by rw [← hB]; simp
    have := (vals_append_cons_inj hev rfl h2).2.1
    subst this
    exact .inr ⟨rfl, rfl, rfl, vs, rest, rfl, rfl⟩
  | throwRef a =>
    exfalso
    have h2 : vals V ++ e :: r = vals [.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      rw [← hB]; simp [throwing, vals, Val.toAdmin]
    have := (vals_append_cons_inj hev rfl h2).2.1
    rcases he with rfl | ⟨_, _, _, rfl⟩ <;> cases this
  | trap =>
    exfalso
    have h2 : vals V ++ e :: r = vals [] ++ Admin.trap :: [] := by
      rw [← hB]; simp
    have := (vals_append_cons_inj hev rfl h2).2.1
    rcases he with rfl | ⟨_, _, _, rfl⟩ <;> cases this

/-- **A step of a wrapper body that is returning values.** -/
theorem pw_step {ws : List Val} :
    ∀ (N : NCtx) {pre : List Val} {Y : List Admin} {t t' : Store H} {g g' : Frame}
      {Z : List Admin},
      Step P host ⟨t, g, N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y)⟩ ⟨t', g', Z⟩ →
      t' = t ∧ g' = g ∧ ∃ (N' : NCtx) (pre' : List Val) (Y' : List Admin),
        Z = N'.fill (vals pre' ++ vals ws ++ .plain .return_ :: Y') ∧
        codeSize Z < codeSize (N.fill (vals pre ++ vals ws ++ .plain .return_ :: Y))
  | .hole, pre, Y, t, t', g, g', Z, h => by
    exfalso
    have h' : Step P host ⟨t, g, vals (pre ++ ws) ++ .plain .return_ :: Y⟩ ⟨t', g', Z⟩ := by
      simpa [NCtx.fill] using h
    rcases Step.split_head rfl h' with ⟨ws', us, is', -, hs, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    · exact return_stuck hs
    · cases hc
    · cases hc
  | .label V₀ n cont N L, pre, Y, t, t', g, g', Z, h => by
    rcases Step.split_head rfl h with ⟨ws', us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
    cases N with
    | hole =>
      rcases labelRed_ret_or_label hred (V := pre ++ ws) (e := .plain .return_) (r := Y)
        (by simp [NCtx.fill]) (.inl rfl) with ⟨B', hs₁, -⟩ | ⟨-, rfl, rfl, vs, rest, hB, rfl⟩
      · exfalso
        have h' : Step P host ⟨t, g, vals (pre ++ ws) ++ .plain .return_ :: Y⟩ ⟨t', g', B'⟩ := by
          simpa [NCtx.fill] using hs₁
        rcases Step.split_head rfl h' with ⟨ws'', us', is'', -, hs₂, -⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
        · exact return_stuck hs₂
        · cases hc
        · cases hc
      · have hB' : vals (pre ++ ws) ++ Admin.plain .return_ :: Y =
            vals vs ++ Admin.plain .return_ :: rest := by simpa [NCtx.fill] using hB
        obtain ⟨rfl, -, rfl⟩ := vals_append_cons_inj rfl rfl hB'
        subst hV
        refine ⟨rfl, rfl, .hole, ws' ++ us ++ pre, L, ?_, ?_⟩
        · simp [NCtx.fill]
        · have := codeSize_unlabel (ws' ++ us) (pre ++ ws) n cont (.plain .return_) Y L
          simpa [NCtx.fill] using this
    | label V₁ n₁ cont₁ N₁ L₁ =>
      rcases labelRed_ret_or_label hred (V := V₁) (r := L₁)
          (e := .label n₁ cont₁ (N₁.fill (vals pre ++ vals ws ++ .plain .return_ :: Y)))
          (by simp [NCtx.fill]) (.inr ⟨_, _, _, rfl⟩) with ⟨B', hs₁, rfl⟩ | ⟨h1, -⟩
      · obtain ⟨rfl, rfl, N', pre', Y', rfl, hlt⟩ := pw_step (.label V₁ n₁ cont₁ N₁ L₁) hs₁
        refine ⟨rfl, rfl, .label V₀ n cont N' L, pre', Y', ?_, ?_⟩
        · simp [NCtx.fill, hV]
        · have := LawfulCodeRank.label_lt (vals V₀) L n cont hlt
          simpa [NCtx.fill, hV] using this
      · cases h1

end Silmaril.Raw.Wasm.LimeCompile.TailSim
