module

public import Silmaril.Raw.Wasm.LimeCompile.TailSim.BwdInv

/-!
# The backward simulation of the tail-call rewrite: steps of active traps and throws, calls

* `TA.step`, `TT.step`: trap- and throw-active code steps only to trap- and throw-active code,
  in the same store and frame, with smaller code (so the source may stutter);
* `CallHead.match_back`: a target call is matched by the same call on the source, with related
  stores and results.

New proofs.
-/

@[expose] public section

namespace Silmaril.Raw.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)
open Silmaril.Wasm.LimeCompile.TailSim

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem codeSize_label_trap (W : List Val) (n : Nat) (cont : List Instr) (y : List Admin) :
    codeSize (vals W ++ [.trap] ++ y) < codeSize (vals W ++ [.label n cont [.trap]] ++ y) :=
  LawfulCodeRank.context_lt (vals W) y (by
    simpa using LawfulCodeRank.label_body_lt (rank := codeSize) [] [] n cont [.trap])

theorem codeSize_frame_trap (W : List Val) (n : Nat) (fi : Frame) (y : List Admin) :
    codeSize (vals W ++ [.trap] ++ y) < codeSize (vals W ++ [.frame n fi [.trap]] ++ y) :=
  LawfulCodeRank.context_lt (vals W) y (by
    simpa using LawfulCodeRank.frame_body_lt (rank := codeSize) [] [] n fi [.trap])

theorem codeSize_label_throw (W : List Val) (n : Nat) (cont : List Instr) (a : Nat)
    (y : List Admin) :
    codeSize (vals W ++ throwing a ++ y) < codeSize (vals W ++ [.label n cont (throwing a)] ++ y) :=
  LawfulCodeRank.context_lt (vals W) y (by
    simpa using LawfulCodeRank.label_body_lt (rank := codeSize) [] [] n cont (throwing a))

theorem codeSize_frame_throw (W : List Val) (n : Nat) (fi : Frame) (a : Nat) (y : List Admin) :
    codeSize (vals W ++ throwing a ++ y) < codeSize (vals W ++ [.frame n fi (throwing a)] ++ y) :=
  LawfulCodeRank.context_lt (vals W) y (by
    simpa using LawfulCodeRank.frame_body_lt (rank := codeSize) [] [] n fi (throwing a))

theorem rcr_not_ctx {c : Admin} (hc : c.IsReturnCallRef) : ¬ c.IsCtx := by
  rcases c with _ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Admin.IsCtx, Admin.IsReturnCallRef]

/-- A kernel of trap-active code is not a `br`, `return` or `return_call_ref` exit. -/
theorem TA.not_exit {b : List Admin} (hb : TA b) {vs : List Val} {k : Admin} {r : List Admin}
    (hk : k.val? = none) (hk' : k ≠ .trap) (hctx : ¬ k.IsCtx) (hx : b = vals vs ++ k :: r) :
    False := by
  rcases TA.head hb hk hx with h | ⟨_, _, _, h, -⟩ | ⟨_, _, _, h, -⟩
  · exact hk' h
  · subst h; exact hctx trivial
  · subst h; exact hctx trivial

theorem TT.not_exit {a : Nat} {b : List Admin} (hb : TT a b) {vs : List Val} {k : Admin}
    {r : List Admin} (hk : k.val? = none) (hk' : k ≠ .plain .throwRef) (hctx : ¬ k.IsCtx)
    (hx : b = vals vs ++ k :: r) : False := by
  rcases TT.head hb hk hx with ⟨h, -⟩ | ⟨_, _, _, h, -⟩ | ⟨_, _, _, h, -⟩
  · exact hk' h
  · subst h; exact hctx trivial
  · subst h; exact hctx trivial

/-- **Steps of trap-active code.** -/
theorem TA.step {y : List Admin} (hy : TA y) :
    ∀ {t t' : Store H} {g g' : Frame} {y' : List Admin}, Step P host ⟨t, g, y⟩ ⟨t', g', y'⟩ →
      t' = t ∧ g' = g ∧ TA y' ∧ codeSize y' < codeSize y := by
  induction hy with
  | base ws y =>
    intro t t' g g' y' h
    rcases Step.split_head rfl h with ⟨ws', us, is', rfl, hs, rfl⟩ |
        ⟨-, rfl, rfl, ws', us, r, r', rfl, rfl, hne, rfl⟩ | ⟨hc, -⟩
    · obtain ⟨hs', hf', p, w, q, rfl, hw, he⟩ := Step.trap_redex_aux hs us rfl
      dsimp only at hs' hf' he
      subst hs' hf' he
      refine ⟨rfl, rfl, by simpa using TA.base (ws' ++ (p ++ q)) y, ?_⟩
      have := codeSize_drop_vals_lt (ws' ++ p) w q (.trap :: y) hw
      simpa using this
    · refine ⟨rfl, rfl, by simpa using TA.base ws' r', ?_⟩
      have := codeSize_discard_lt ws' us [.trap] r r' hne
      simpa using this
    · cases hc
  | @label ws n cont b y hb ih =>
    intro t t' g g' y' h
    rcases Step.split_head rfl h with ⟨ws', us, is', hws, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
    have e1 : vals ws' ++ (vals us ++ is₂) ++ y = vals ws ++ is₂ ++ y := by rw [hws]; simp
    rw [e1]
    have e2 : vals ws ++ Admin.label n cont b :: y = vals ws ++ [.label n cont b] ++ y := by simp
    clear hs
    cases hred with
    | ctxt hs₁ =>
      obtain ⟨rfl, rfl, hb', hlt⟩ := ih hs₁
      refine ⟨rfl, rfl, by simpa using TA.label ws n cont y hb', ?_⟩
      rw [e2]
      exact LawfulCodeRank.label_lt (vals ws) y n cont hlt
    | values vs => exact (TA.not_vals hb vs rfl).elim
    | brZero hl hn =>
      rename_i vs' vs l rest
      exact (TA.not_exit hb (vs := vs' ++ vs) (k := .plain (.br l)) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | brSucc hl =>
      rename_i vs l rest
      exact (TA.not_exit hb (vs := vs) (k := .plain (.br l)) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | returnCallRef hc =>
      rename_i vs c rest
      exact (TA.not_exit hb (vs := vs) (k := c) (r := rest) (Admin.val?_of_isReturnCallRef hc)
        (fun h => by subst h; exact hc) (rcr_not_ctx hc) (by simp)).elim
    | return_ =>
      rename_i vs rest
      exact (TA.not_exit hb (vs := vs) (k := .plain .return_) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | throwRef a =>
      exact (TA.not_exit hb (vs := [.ref (.exn a)]) (k := .plain .throwRef) (r := []) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp [throwing, vals, Val.toAdmin])).elim
    | trap =>
      refine ⟨rfl, rfl, by simpa using TA.base ws y, ?_⟩
      rw [e2]
      exact codeSize_label_trap ws n cont y
  | @frame ws n fi b y hb ih =>
    intro t t' g g' y' h
    rcases Step.split_head rfl h with ⟨ws', us, is', hws, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₀, hcode, hfr⟩ := Closure.Step.frame_redex_aux hs us n fi b rfl
    dsimp only at hcode hfr
    subst hcode
    have e1 : vals ws' ++ (vals us ++ is₀) ++ y = vals ws ++ is₀ ++ y := by rw [hws]; simp
    rw [e1]
    have e2 : vals ws ++ Admin.frame n fi b :: y = vals ws ++ [.frame n fi b] ++ y := by simp
    clear hs
    cases hfr with
    | ctxt hs₁ =>
      obtain ⟨rfl, rfl, hb', hlt⟩ := ih hs₁
      refine ⟨rfl, rfl, by simpa using TA.frame ws n _ y hb', ?_⟩
      rw [e2]
      exact LawfulCodeRank.frame_lt (vals ws) y n _ hlt
    | values hn => exact (TA.not_vals hb _ rfl).elim
    | ret hn =>
      rename_i vs' vs rest
      exact (TA.not_exit hb (vs := vs' ++ vs) (k := .plain .return_) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | callNull hc =>
      rename_i vs c rest
      exact (TA.not_exit hb (vs := vs ++ [.ref .null]) (k := c) (r := rest)
        (Admin.val?_of_isReturnCallRef hc) (fun h => by subst h; exact hc) (rcr_not_ctx hc)
        (by simp [vals, Val.toAdmin])).elim
    | callAddr hc hf he hn =>
      rename_i vs' vs a c rest fn ps rs
      exact (TA.not_exit hb (vs := vs' ++ vs ++ [.ref (.func a)]) (k := c) (r := rest)
        (Admin.val?_of_isReturnCallRef hc) (fun h => by subst h; exact hc) (rcr_not_ctx hc)
        (by simp [vals, Val.toAdmin])).elim
    | throw =>
      rename_i a
      exact (TA.not_exit hb (vs := [.ref (.exn a)]) (k := .plain .throwRef) (r := []) rfl
        (by simp) (by simp [Admin.IsCtx]) (by simp [throwing, vals, Val.toAdmin])).elim
    | trap =>
      refine ⟨rfl, rfl, by simpa using TA.base ws y, ?_⟩
      rw [e2]
      exact codeSize_frame_trap ws n fi y

/-- **Steps of throw-active code.** -/
theorem TT.step {a : Nat} {y : List Admin} (hy : TT a y) :
    ∀ {t t' : Store H} {g g' : Frame} {y' : List Admin}, Step P host ⟨t, g, y⟩ ⟨t', g', y'⟩ →
      t' = t ∧ g' = g ∧ TT a y' ∧ codeSize y' < codeSize y := by
  induction hy with
  | base ws y =>
    intro t t' g g' y' h
    rw [throw_eq] at h
    rcases Step.split_head rfl h with ⟨ws', us, is', hV, hs, rfl⟩ | ⟨hc, -⟩ |
        ⟨-, rfl, rfl, ws', us, x, r, r', hV, rfl, hne, rfl⟩
    · obtain ⟨hs', hf', hcase⟩ := Step.throwRef_redex_aux hs us rfl
      dsimp only at hs' hf' hcase
      subst hs' hf'
      rcases hcase with ⟨p, w, q, a', rfl, hw, he⟩ | ⟨u, u', rfl, -⟩
      · have hea : a' = a := by
          have := congrArg List.getLast? hV
          simp at this; exact this.symm
        subst hea
        rw [he]
        have hV' : ws = ws' ++ p ++ w ++ q := by
          have := hV
          rw [show ws' ++ (p ++ w ++ q ++ [Val.ref (.exn a')]) = (ws' ++ p ++ w ++ q) ++
            [.ref (.exn a')] by simp] at this
          exact List.append_inj_left' this rfl
        subst hV'
        refine ⟨rfl, rfl, by simpa using TT.base (a := a') (ws' ++ (p ++ q)) y, ?_⟩
        have := codeSize_drop_vals_lt (ws' ++ p) w (q ++ [.ref (.exn a')]) (.plain .throwRef :: y) hw
        simpa [throwing, Val.toAdmin] using this
      · have := congrArg List.getLast? hV
        simp at this
    · cases hc
    · have hxa : x = a := by
        have := congrArg List.getLast? hV
        simp at this; exact this.symm
      subst hxa
      have hV' : ws = ws' ++ us := by
        have := hV
        rw [show ws' ++ us ++ [Val.ref (.exn x)] = (ws' ++ us) ++ [.ref (.exn x)] by simp] at this
        exact List.append_inj_left' this rfl
      subst hV'
      refine ⟨rfl, rfl, TT.base ws' r', ?_⟩
      have := codeSize_discard_lt ws' us (throwing x) r r' hne
      simpa [throwing, Val.toAdmin] using this
  | @label ws n cont b y hb ih =>
    intro t t' g g' y' h
    rcases Step.split_head rfl h with ⟨ws', us, is', hws, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₂, hred, rfl⟩ := Closure.Step.label_inv hs
    have e1 : vals ws' ++ (vals us ++ is₂) ++ y = vals ws ++ is₂ ++ y := by rw [hws]; simp
    rw [e1]
    have e2 : vals ws ++ Admin.label n cont b :: y = vals ws ++ [.label n cont b] ++ y := by simp
    clear hs
    cases hred with
    | ctxt hs₁ =>
      obtain ⟨rfl, rfl, hb', hlt⟩ := ih hs₁
      refine ⟨rfl, rfl, by simpa using TT.label ws n cont y hb', ?_⟩
      rw [e2]
      exact LawfulCodeRank.label_lt (vals ws) y n cont hlt
    | values vs => exact (TT.not_vals hb vs rfl).elim
    | brZero hl hn =>
      rename_i vs' vs l rest
      exact (TT.not_exit hb (vs := vs' ++ vs) (k := .plain (.br l)) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | brSucc hl =>
      rename_i vs l rest
      exact (TT.not_exit hb (vs := vs) (k := .plain (.br l)) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | returnCallRef hc =>
      rename_i vs c rest
      exact (TT.not_exit hb (vs := vs) (k := c) (r := rest) (Admin.val?_of_isReturnCallRef hc)
        (fun h => by subst h; exact hc) (rcr_not_ctx hc) (by simp)).elim
    | return_ =>
      rename_i vs rest
      exact (TT.not_exit hb (vs := vs) (k := .plain .return_) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | throwRef a' =>
      have hea : a' = a := by
        rcases TT.head hb (ws := [.ref (.exn a')]) (b := .plain .throwRef) (r := []) rfl
          (by simp [throwing, vals, Val.toAdmin]) with ⟨-, ws', hws'⟩ | ⟨_, _, _, h1, -⟩ |
          ⟨_, _, _, h1, -⟩
        · have := congrArg List.getLast? hws'
          simp at this; exact this
        · cases h1
        · cases h1
      subst hea
      refine ⟨rfl, rfl, TT.base ws y, ?_⟩
      rw [e2]
      exact codeSize_label_throw ws n cont a' y
    | trap =>
      exact (TT.not_exit hb (vs := []) (k := .trap) (r := []) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
  | @frame ws n fi b y hb ih =>
    intro t t' g g' y' h
    rcases Step.split_head rfl h with ⟨ws', us, is', hws, hs, rfl⟩ | ⟨hc, -⟩ | ⟨hc, -⟩
    rotate_left
    · cases hc
    · cases hc
    obtain ⟨is₀, hcode, hfr⟩ := Closure.Step.frame_redex_aux hs us n fi b rfl
    dsimp only at hcode hfr
    subst hcode
    have e1 : vals ws' ++ (vals us ++ is₀) ++ y = vals ws ++ is₀ ++ y := by rw [hws]; simp
    rw [e1]
    have e2 : vals ws ++ Admin.frame n fi b :: y = vals ws ++ [.frame n fi b] ++ y := by simp
    clear hs
    cases hfr with
    | ctxt hs₁ =>
      obtain ⟨rfl, rfl, hb', hlt⟩ := ih hs₁
      refine ⟨rfl, rfl, by simpa using TT.frame ws n _ y hb', ?_⟩
      rw [e2]
      exact LawfulCodeRank.frame_lt (vals ws) y n _ hlt
    | values hn => exact (TT.not_vals hb _ rfl).elim
    | ret hn =>
      rename_i vs' vs rest
      exact (TT.not_exit hb (vs := vs' ++ vs) (k := .plain .return_) (r := rest) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim
    | callNull hc =>
      rename_i vs c rest
      exact (TT.not_exit hb (vs := vs ++ [.ref .null]) (k := c) (r := rest)
        (Admin.val?_of_isReturnCallRef hc) (fun h => by subst h; exact hc) (rcr_not_ctx hc)
        (by simp [vals, Val.toAdmin])).elim
    | callAddr hc hf he hn =>
      rename_i vs' vs a c rest fn ps rs
      exact (TT.not_exit hb (vs := vs' ++ vs ++ [.ref (.func a)]) (k := c) (r := rest)
        (Admin.val?_of_isReturnCallRef hc) (fun h => by subst h; exact hc) (rcr_not_ctx hc)
        (by simp [vals, Val.toAdmin])).elim
    | throw =>
      rename_i a'
      have hea : a' = a := by
        rcases TT.head hb (ws := [.ref (.exn a')]) (b := .plain .throwRef) (r := []) rfl
          (by simp [throwing, vals, Val.toAdmin]) with ⟨-, ws', hws'⟩ | ⟨_, _, _, h1, -⟩ |
          ⟨_, _, _, h1, -⟩
        · have := congrArg List.getLast? hws'
          simp at this; exact this
        · cases h1
        · cases h1
      subst hea
      refine ⟨rfl, rfl, TT.base ws y, ?_⟩
      rw [e2]
      exact codeSize_frame_throw ws n _ a' y
    | trap =>
      exact (TT.not_exit hb (vs := []) (k := .trap) (r := []) rfl (by simp)
        (by simp [Admin.IsCtx]) (by simp)).elim

/-- **Calls, backwards**: a target call is matched by the same call on the source. -/
theorem CallHead.match_back {s t t' : Store H} {us : List Val} {c : Admin} {is' : List Admin}
    (hhost : HostRespects (fun g f => FRel f g) host) (hst : StoreRel FRel s t)
    (h : CallHead host t us c t' is') :
    ∃ s' is'', CallHead host s us c s' is'' ∧ StoreRel FRel s' t' ∧
      (is'' = is' ∨ ∃ (n : Nat) (fc : Frame) (b b' : List Admin), is'' = [.frame n fc b] ∧
        is' = [.frame n fc b'] ∧ ∀ fw, R fw true b b') := by
  have hst' := hst.symm
  cases h with
  | null => exact ⟨s, _, .null, hst, Or.inl rfl⟩
  | @func _ vs a gn ps rs code' hg he hn hcode =>
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst'.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hcr := hfg'.2.2
    cases hfc : fn.code with
    | host h' =>
      rw [hfc, hcode] at hcr; exact hcr.elim
    | wasm code =>
      obtain ⟨code₂, hc₂, hl, hb⟩ := FRel.wasm hfg' hfc
      rw [hcode] at hc₂
      cases hc₂
      refine ⟨s, _, .func hf he' hn hfc, hst, Or.inr ⟨_, _, _, _, rfl, ?_, fun fw => hb fw _⟩⟩
      rw [← hl, ← hfg'.2.1]
  | @host _ vs a gn ps rs h t'' r hg he hn hcode hh =>
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst'.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hfc : fn.code = .host h := by
      obtain ⟨-, -, hcr⟩ := hfg'
      rw [hcode] at hcr
      cases hfc : fn.code with
      | wasm g => rw [hfc] at hcr; exact hcr.elim
      | host h' => rw [hfc] at hcr; exact congrArg _ hcr
    obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst' hh
    cases out' with
    | diverged => simp [OutcomeRel] at hrel
    | returned s' r' =>
      simp only [OutcomeRel, Execution.Host.Outcome.Sim_returned_returned, id] at hrel
      obtain ⟨hs', rfl⟩ := hrel
      exact ⟨s', _, .host hf he' hn hfc hout', hs'.symm, Or.inl rfl⟩
  | @div _ vs a gn ps rs h hg he hn hcode hh =>
    obtain ⟨fn, hf, hfg⟩ := forall₂_getElem? hst'.funcs hg
    have hfg' : FRel fn gn := hfg
    have he' : Expand fn.type (.func ps rs) := by rw [hfg'.1]; exact he
    have hfc : fn.code = .host h := by
      obtain ⟨-, -, hcr⟩ := hfg'
      rw [hcode] at hcr
      cases hfc : fn.code with
      | wasm g => rw [hfc] at hcr; exact hcr.elim
      | host h' => rw [hfc] at hcr; exact congrArg _ hcr
    obtain ⟨out', hout', hrel⟩ := hhost _ _ _ _ _ hst' hh
    cases out' with
    | returned s' r' => simp [OutcomeRel] at hrel
    | diverged => exact ⟨s, _, .div hf he' hn hfc hout', hst, Or.inl rfl⟩

end Silmaril.Raw.Wasm.LimeCompile.TailSim
