module

public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Auto.Equiv.Defs

/-!
# Inversion of the sequencing and label rules (unrefined)

The every-run logic (`Silmaril.Wasm.Logic.Hoare`, `Silmaril.Wasm.Logic.Total`) has the forward rules
`HWP.seq`/`TSafe.seq` (a sequence from its first part and the postcondition `seqPost`) and
`HWP.label`/`TSafe.label` (a label from its body and `labelPost`). This file proves their
converses, so that both rules become equivalences:

* `exits_unique`, `Exits.of_append`: the outcome of an exit is unique, and an exit of `c₁ ++ c₂`
  whose first part is not all values is an exit of `c₁`;
* `hwp_exit_post`, `tsafe_exit_post`: a weakest precondition at an exit gives the postcondition
  of that exit;
* `hwp_seq_inv`, `tsafe_seq_inv`: the weakest precondition of `c₁ ++ c₂` is that of `c₁` with
  `seqPost c₂`/`seqPostT c₂`;
* `hwp_label_inv`, `tsafe_label_inv`: the weakest precondition of `val* LABEL_m{cont} b` is that
  of the body `b` with `labelPost`/`labelPostT`.

The proofs are case analyses on the first non-value of the code and on silmaril-lean's step
inversions (`Sim.Step.split_head`, `Sim.Closure.Step.label_inv`), kept here unrefined. They are
used by `Silmaril.Proofs.Wasm.Auto.Equiv.Ctl.Congr` and `Loop`.

New proofs (a Silmaril addition).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Equiv

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-! ## Exits -/

theorem exits_unique {o o' : Outcome} {c : List Admin} (h : Exits o c) (h' : Exits o' c) :
    o = o' := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · exact (exits_vals_inv ((show c = vals vs from h) ▸ h')).symm
  · obtain ⟨x, rest, hx, rfl⟩ := h
    rw [exits_br_inv h', hx]
  · obtain ⟨rest, rfl⟩ := h
    exact (exits_ret_inv h').symm
  · obtain ⟨vs, rest, rfl⟩ := h
    exact (exits_trap_inv h').symm
  · obtain ⟨vs, rest, rfl⟩ := h
    exact (exits_throw_inv h').symm
  · obtain ⟨hr, rest, rfl⟩ := h
    exact (exits_tail_inv hr h').symm

/-- An exit of `c₁ ++ c₂` whose first part is not all values is an exit of `c₁`. -/
theorem Exits.of_append {o : Outcome} {c₁ c₂ : List Admin} (hna : c₁.all Admin.isVal = false)
    (h : Exits o (c₁ ++ c₂)) : Exits o c₁ := by
  obtain ⟨vs, a, es, ha, rfl⟩ := Sim.exists_head_of_not_all hna
  have hf : FnvOk o (vs, a :: (es ++ c₂)) := by
    rw [← fnv_vals_cons ha]; simpa using h.fnv
  rcases o with vs' | ⟨l, vs'⟩ | vs' | _ | a' | ⟨vs', a', r⟩
  · simp [FnvOk] at hf
  · obtain ⟨x, rest, hx, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, -⟩ := hp
    exact ⟨x, es, hx, by simp⟩
  · obtain ⟨rest, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, -⟩ := hp
    exact ⟨es, by simp⟩
  · obtain ⟨ws, rest, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, -⟩ := hp
    exact ⟨vs, es, by simp⟩
  · obtain ⟨ws, rest, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨rfl, rfl, -⟩ := hp
    exact ⟨ws, es, (throwing_code ws a' es).symm ▸ by simp⟩
  · obtain ⟨hr, rest, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨hv, ha', -⟩ := hp
    have hr' : Admin.IsReturnCallRef r := by
      rcases hr with ⟨y, hy⟩ | ⟨d, hd⟩
      · rw [hy]; trivial
      · rw [hd]; trivial
    refine ⟨hr', es, ?_⟩
    rw [tail_code, hv, ha']

/-- A weakest precondition at an exit gives the postcondition of the exit. -/
theorem hwp_exit_post {s : Store H} {f : Frame} {c : List Admin} {Q : Post H} {o : Outcome}
    (h : HWP P host s f c Q) (he : Exits o c) : Q s f o := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · obtain ⟨o', he', hq⟩ := (h 1).exit_of_stuck fun _ hst =>
      not_step_vals ((show c = vals vs from he) ▸ hst)
    exact exits_unique he' he ▸ hq
  · obtain ⟨x, rest, hx, rfl⟩ := he
    obtain ⟨o', he', hq⟩ := (h 1).exit_of_stuck fun _ hst =>
      not_step_blocked (Or.inl ⟨x, rfl⟩) hst
    exact exits_unique he' (show Exits (.br l vs) _ from ⟨x, rest, hx, rfl⟩) ▸ hq
  · obtain ⟨rest, rfl⟩ := he
    obtain ⟨o', he', hq⟩ := (h 1).exit_of_stuck fun _ hst =>
      not_step_blocked (Or.inr (Or.inl rfl)) hst
    exact exits_unique he' (show Exits (.ret vs) _ from ⟨rest, rfl⟩) ▸ hq
  · obtain ⟨vs, rest, rfl⟩ := he
    exact Safe.trap_post (h 2)
  · obtain ⟨vs, rest, rfl⟩ := he
    exact Safe.throw_post (h 2)
  · obtain ⟨hr, rest, rfl⟩ := he
    obtain ⟨o', he', hq⟩ := (h 1).exit_of_stuck fun _ hst =>
      not_step_blocked (Or.inr (Or.inr hr)) (tail_code vs a r rest ▸ hst)
    exact exits_unique he' (show Exits (.tail vs a r) _ from ⟨hr, rest, rfl⟩) ▸ hq

theorem tsafe_exit_post {s : Store H} {f : Frame} {c : List Admin} {Q : Post H} {o : Outcome}
    (h : TSafe P host Q ⟨s, f, c⟩) (he : Exits o c) : Q s f o :=
  hwp_exit_post (fun n => h.safe n) he

/-- The first part of a sequence that is not all values and not an exit can step, if the
sequence can. -/
theorem step_of_append {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {c' : Config H}
    (hna : c₁.all Admin.isVal = false) (hex : ¬ ∃ o, Exits o c₁)
    (hst : Step P host ⟨s, f, c₁ ++ c₂⟩ c') : ∃ c'', Step P host ⟨s, f, c₁⟩ c'' := by
  obtain ⟨vs, a, es, ha, rfl⟩ := Sim.exists_head_of_not_all hna
  have hst' : Step P host ⟨s, f, vals vs ++ a :: (es ++ c₂)⟩ c' := by simpa using hst
  rcases c' with ⟨s', f', es'⟩
  rcases Sim.Step.split_head ha hst' with ⟨ws, us, is', rfl, hu, rfl⟩ |
      ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, ws, us, x, r, r', hvs, -⟩
  · exact ⟨_, by simpa using Sim.Step.vals_left (Sim.Step.append_right hu es) ws⟩
  · exact (hex ⟨.trap, vs, es, rfl⟩).elim
  · subst hvs
    exact (hex ⟨.throw x, ws ++ us, es, by simp [throwing, vals, Val.toAdmin]⟩).elim

/-! ## Sequencing -/

/-- **Inversion of sequencing** (partial correctness). -/
theorem safe_seq_inv {c₂ : List Admin} {Q : Post H} :
    ∀ (n : Nat) {s : Store H} {f : Frame} {c₁ : List Admin}, HWP P host s f (c₁ ++ c₂) Q →
      Safe P host (seqPost P host c₂ Q) n ⟨s, f, c₁⟩
  | 0, _, _, _, _ => trivial
  | n + 1, s, f, c₁, h => by
    by_cases hall : c₁.all Admin.isVal = true
    · obtain ⟨vs, rfl⟩ := Sim.exists_vals_of_all hall
      exact Or.inl ⟨.normal vs, rfl, h⟩
    · have hna : c₁.all Admin.isVal = false := by simpa using hall
      by_cases hex : ∃ o, Exits o c₁
      · obtain ⟨o, he⟩ := hex
        have hn : ∀ vs, o ≠ .normal vs := by
          rintro vs rfl
          have : c₁ = vals vs := he
          subst this
          simp at hna
        have hq := hwp_exit_post h (he.append hn c₂)
        refine Or.inl ⟨o, he, ?_⟩
        rcases o with vs | _ | _ | _ | _ | _
        · exact (hn vs rfl).elim
        all_goals exact hq
      · refine Or.inr ⟨?_, fun c' hst => ?_⟩
        · rcases h 1 with ⟨o, he, -⟩ | ⟨⟨c', hc'⟩, -⟩
          · exact (hex ⟨o, Exits.of_append hna he⟩).elim
          · exact step_of_append hna hex hc'
        · rcases c' with ⟨s', f', c₁'⟩
          exact safe_seq_inv n (h.step_inv (Sim.Step.append_right hst c₂))

theorem hwp_seq_inv {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : HWP P host s f (c₁ ++ c₂) Q) : HWP P host s f c₁ (seqPost P host c₂ Q) :=
  fun n => safe_seq_inv n h

/-- **Inversion of sequencing** (total correctness). -/
theorem tsafe_seq_inv {c₂ : List Admin} {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∀ c₁ : List Admin, c.code = c₁ ++ c₂ →
      TSafe P host (seqPostT P host c₂ Q) ⟨c.store, c.frame, c₁⟩ := by
  induction h with
  | @exit c o he hq =>
    intro c₁ hc
    rcases c with ⟨s, f, code⟩
    dsimp only at hc he hq ⊢
    subst hc
    by_cases hall : c₁.all Admin.isVal = true
    · obtain ⟨vs, rfl⟩ := Sim.exists_vals_of_all hall
      exact .exit (.normal vs) rfl (TSafe.exit o he hq)
    · have hna : c₁.all Admin.isVal = false := by simpa using hall
      have he₁ := Exits.of_append hna he
      refine .exit o he₁ ?_
      rcases o with vs | _ | _ | _ | _ | _
      · have : c₁ = vals vs := he₁
        subst this
        simp at hna
      all_goals exact hq
  | @step c hp hs ih =>
    intro c₁ hc
    rcases c with ⟨s, f, code⟩
    dsimp only at hc hp hs ih ⊢
    subst hc
    by_cases hall : c₁.all Admin.isVal = true
    · obtain ⟨vs, rfl⟩ := Sim.exists_vals_of_all hall
      exact .exit (.normal vs) rfl (TSafe.step hp hs)
    · have hna : c₁.all Admin.isVal = false := by simpa using hall
      by_cases hex : ∃ o, Exits o c₁
      · obtain ⟨o, he⟩ := hex
        have hn : ∀ vs, o ≠ .normal vs := by
          rintro vs rfl
          have : c₁ = vals vs := he
          subst this
          simp at hna
        have hq := tsafe_exit_post (TSafe.step hp hs) (he.append hn c₂)
        refine .exit o he ?_
        rcases o with vs | _ | _ | _ | _ | _
        · exact (hn vs rfl).elim
        all_goals exact hq
      · obtain ⟨c', hc'⟩ := hp
        refine .step (step_of_append hna hex hc') fun c'' hst => ?_
        rcases c'' with ⟨s', f', c₁'⟩
        exact ih _ (Sim.Step.append_right hst c₂) c₁' rfl

theorem twp_seq_inv {s : Store H} {f : Frame} {c₁ c₂ : List Admin} {Q : Post H}
    (h : TWP P host s f (c₁ ++ c₂) Q) : TWP P host s f c₁ (seqPostT P host c₂ Q) :=
  tsafe_seq_inv h c₁ rfl

/-! ## Labels -/

/-- A label is never an exit. -/
theorem not_exits_label {o : Outcome} {us : List Val} {m : Nat} {cont : List Instr}
    {b : List Admin} : ¬ Exits o (vals us ++ [.label m cont b]) := by
  intro he
  have hf : FnvOk o (us, [.label m cont b]) := by
    rw [← fnv_vals_cons (e := .label m cont b) rfl]; exact he.fnv
  rcases o with _ | _ | _ | _ | _ | ⟨vs, a, r⟩
  · simp [FnvOk] at hf
  · obtain ⟨x, rest, -, hp⟩ := hf; simp at hp
  · obtain ⟨rest, hp⟩ := hf; simp at hp
  · obtain ⟨_, rest, hp⟩ := hf; simp at hp
  · obtain ⟨_, rest, hp⟩ := hf; simp at hp
  · obtain ⟨hr, rest, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    obtain ⟨-, rfl, -⟩ := hp
    rcases hr with ⟨y, hy⟩ | ⟨d, hd⟩
    · cases hy
    · cases hd

/-! ## Both readings at once -/

theorem wp_step_inv {m : Corr} {s s' : Store H} {f f' : Frame} {c c' : List Admin} {Q : Post H}
    (h : Wp m P host s f c Q) (hst : Step P host ⟨s, f, c⟩ ⟨s', f', c'⟩) :
    Wp m P host s' f' c' Q := by
  cases m
  · exact HWP.step_inv h hst
  · exact TSafe.step_inv h hst

theorem wp_exit_post {m : Corr} {s : Store H} {f : Frame} {c : List Admin} {Q : Post H}
    {o : Outcome} (h : Wp m P host s f c Q) (he : Exits o c) : Q s f o := by
  cases m
  · exact hwp_exit_post h he
  · exact tsafe_exit_post h he

theorem wp_progress {m : Corr} {s : Store H} {f : Frame} {c : List Admin} {Q : Post H}
    (h : Wp m P host s f c Q) (hex : ∀ o, ¬ Exits o c) : ∃ c', Step P host ⟨s, f, c⟩ c' := by
  cases m
  · rcases (h 1) with ⟨o, he, -⟩ | ⟨hp, -⟩
    · exact (hex o he).elim
    · exact hp
  · cases h with
    | exit o he _ => exact (hex o he).elim
    | step hp _ => exact hp

theorem not_exits_of_val_none {o : Outcome} {vs : List Val} {a : Admin} {rest : List Admin}
    (ha : a.val? = none) (hnb : ∀ x, a ≠ .plain (.br x)) (hnr : a ≠ .plain .return_)
    (hnt : a ≠ .trap) (hnth : a ≠ .plain .throwRef) (hnc : ¬ a.IsReturnCallRef) :
    ¬ Exits o (vals vs ++ a :: rest) := by
  intro he
  have hf : FnvOk o (vs, a :: rest) := by rw [← fnv_vals_cons ha]; exact he.fnv
  rcases o with _ | _ | _ | _ | _ | _
  · simp [FnvOk] at hf
  · obtain ⟨x, r, -, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    exact hnb x hp.2.1
  · obtain ⟨r, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    exact hnr hp.2.1
  · obtain ⟨_, r, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    exact hnt hp.2.1
  · obtain ⟨_, r, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    exact hnth hp.2.1
  · obtain ⟨hr, r, hp⟩ := hf
    simp only [Prod.mk.injEq, List.cons.injEq] at hp
    rw [hp.2.1] at hnc
    rcases hr with ⟨y, rfl⟩ | ⟨d, rfl⟩ <;> exact hnc trivial

/-- A `br 0` with fewer values than the label's arity: the label cannot step. -/
theorem label_br0_stuck {s : Store H} {f : Frame} {us vs : List Val} {m : Nat}
    {cont : List Instr} {x : LabelIdx} {rest : List Admin} {c' : Config H} (hx : x.toNat = 0)
    (hlt : vs.length < m)
    (hst : Step P host ⟨s, f, vals us ++ [.label m cont (vals vs ++ .plain (.br x) :: rest)]⟩ c') :
    False := by
  rcases c' with ⟨s', f', es'⟩
  obtain ⟨is', hr, -⟩ := Sim.Closure.Step.label_inv hst
  have key : ∀ (ws : List Val) (e : Admin) (rest' : List Admin), e.val? = none →
      vals vs ++ .plain (.br x) :: rest = vals ws ++ e :: rest' →
      vs = ws ∧ Admin.plain (.br x) = e ∧ rest = rest' := fun ws e rest' he h =>
    Sim.vals_append_cons_inj rfl he h
  generalize hb : vals vs ++ Admin.plain (.br x) :: rest = b at hr
  cases hr with
  | ctxt hb' =>
    rw [← hb] at hb'
    exact not_step_blocked (Or.inl ⟨x, rfl⟩) hb'
  | values ws =>
    have h1 := congrArg (fun l => l.all Admin.isVal) hb
    simp [vals, List.all_map, Admin.isVal, Admin.val?] at h1
    obtain ⟨v, -, hv⟩ := h1
    rcases v with ⟨⟨_ | _, _⟩⟩ | _ | _ <;> simp [Val.toAdmin] at hv
  | @brZero vs' ws l rest' hl hn =>
    obtain ⟨e, -, -⟩ := key (vs' ++ ws) (.plain (.br l)) rest' rfl (by rw [hb]; simp)
    have := congrArg List.length e
    simp at this
    omega
  | @brSucc ws l rest' hl =>
    obtain ⟨-, e, -⟩ := key ws (.plain (.br l)) rest' rfl (by rw [hb]; simp)
    have hxl : x = l := by simpa using e
    subst hxl
    omega
  | @returnCallRef ws c rest' hc =>
    obtain ⟨-, e, -⟩ := key ws c rest' (SingleThreaded.val?_returnCallRef hc) (by rw [hb]; simp)
    rw [← e] at hc
    exact hc
  | @return_ ws rest' =>
    obtain ⟨-, e, -⟩ := key ws (.plain .return_) rest' rfl (by rw [hb]; simp)
    simp at e
  | throwRef a =>
    obtain ⟨-, e, -⟩ := key [.ref (.exn a)] (.plain .throwRef) [] rfl (by rw [hb]; simp [throwing, vals, Val.toAdmin])
    simp at e
  | trap =>
    obtain ⟨-, e, -⟩ := key [] .trap [] rfl (by rw [hb]; simp)
    simp at e

/-- **A label around an exited body**: the weakest precondition of the label gives the label
postcondition of the body's exit. -/
theorem wp_label_exit_post {m : Corr} {s : Store H} {f : Frame} {us : List Val} {k : Nat}
    {cont : List Instr} {b : List Admin} {Q : Post H} {o : Outcome}
    (h : Wp m P host s f (vals us ++ [.label k cont b]) Q) (he : Exits o b) :
    labelPostM m P host k cont us Q s f o := by
  have lift : ∀ {b' : List Admin}, Step P host ⟨s, f, [.label k cont b]⟩ ⟨s, f, b'⟩ →
      Wp m P host s f (vals us ++ b') Q := fun hb =>
    wp_step_inv h (Sim.Step.vals_left hb us)
  rcases o with vs | ⟨_ | l, vs⟩ | vs | _ | a | ⟨vs, a, r⟩
  · have hb : b = vals vs := he
    subst hb
    have h₁ := lift Step.labelVals
    have := wp_exit_post h₁ (o := .normal (us ++ vs)) (by simp [Exits])
    cases m <;> exact this
  · obtain ⟨x, rest, hx, rfl⟩ := he
    by_cases hlen : k ≤ vs.length
    · obtain ⟨vs₁, vs₂, rfl, hn⟩ : ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = k :=
        ⟨vs.take (vs.length - k), vs.drop (vs.length - k), by simp, by simp; omega⟩
      have hst : Step P host ⟨s, f, [.label k cont (vals (vs₁ ++ vs₂) ++ .plain (.br x) :: rest)]⟩
          ⟨s, f, vals vs₂ ++ expression cont⟩ := by
        simpa using Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (cont := cont)
          (vs' := vs₁) (rest := rest) hx hn
      have h₁ := lift hst
      cases m
      · exact ⟨vs₁, vs₂, rfl, hn, by simpa using h₁⟩
      · exact ⟨vs₁, vs₂, rfl, hn, by simpa [Wp, TWP] using h₁⟩
    · obtain ⟨c', hc'⟩ := wp_progress h fun o he => not_exits_label he
      exact (label_br0_stuck hx (by omega) hc').elim
  · obtain ⟨x, rest, hx, rfl⟩ := he
    have hst : Step P host ⟨s, f, [.label k cont (vals vs ++ .plain (.br x) :: rest)]⟩
        ⟨s, f, vals vs ++ [.plain (.br (labelPred x))]⟩ := by
      simpa using Step.brLabelSucc (P := P) (host := host) (s := s) (f := f) (n := k)
        (cont := cont) (vs := vs) (rest := rest) (by omega)
    have h₁ := lift hst
    have hx' : (labelPred x).toNat = l := by show x.toNat - 1 = l; omega
    have := wp_exit_post h₁ (o := .br l (us ++ vs)) ⟨labelPred x, [], hx', by simp⟩
    cases m <;> exact this
  · obtain ⟨rest, rfl⟩ := he
    have hst : Step P host ⟨s, f, [.label k cont (vals vs ++ .plain .return_ :: rest)]⟩
        ⟨s, f, vals vs ++ [.plain .return_]⟩ := by
      simpa using Step.returnLabel (P := P) (host := host) (s := s) (f := f) (n := k)
        (cont := cont) (vs := vs) (rest := rest)
    have := wp_exit_post (lift hst) (o := .ret (us ++ vs)) ⟨[], by simp⟩
    cases m <;> exact this
  · obtain ⟨vs, rest, rfl⟩ := he
    have hq : Q s f .trap := by
      by_cases hne : vs ≠ [] ∨ rest ≠ []
      · have h₁ : Step P host ⟨s, f, vals us ++ [.label k cont (vals vs ++ .trap :: rest)]⟩
            ⟨s, f, vals us ++ [.label k cont [.trap]]⟩ :=
          Sim.Step.vals_left (Step.ctxtLabel (by simpa using Step.trapInstrs hne)) us
        have h₂ := wp_step_inv (wp_step_inv h h₁) (Sim.Step.vals_left Step.trapLabel us)
        exact wp_exit_post h₂ ⟨us, [], by simp⟩
      · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by
          simpa only [ne_eq, not_or, not_not] using hne
        exact wp_exit_post (lift (by simpa using Step.trapLabel)) ⟨us, [], by simp⟩
    cases m <;> exact hq
  · obtain ⟨vs, rest, rfl⟩ := he
    have hq : Q s f (.throw a) := by
      by_cases hne : vs ≠ [] ∨ rest ≠ []
      · have h₁ : Step P host ⟨s, f, vals us ++ [.label k cont (vals vs ++ throwing a ++ rest)]⟩
            ⟨s, f, vals us ++ [.label k cont (throwing a)]⟩ :=
          Sim.Step.vals_left (Step.ctxtLabel (Step.throwRefInstrs hne)) us
        have h₂ := wp_step_inv (wp_step_inv h h₁) (Sim.Step.vals_left Step.throwRefLabel us)
        exact wp_exit_post h₂ ⟨us, [], by simp⟩
      · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by
          simpa only [ne_eq, not_or, not_not] using hne
        exact wp_exit_post (lift (by simpa using Step.throwRefLabel)) ⟨us, [], by simp⟩
    cases m <;> exact hq
  · obtain ⟨hr, rest, rfl⟩ := he
    have hst : Step P host ⟨s, f, [.label k cont (vals vs ++ .ref (.func a) :: r :: rest)]⟩
        ⟨s, f, vals (vs ++ [.ref (.func a)]) ++ [r]⟩ := by
      have := Step.returnCallRefLabel (P := P) (host := host) (s := s) (f := f) (k := k)
        (cont := cont) (vs := vs ++ [.ref (.func a)]) (rest := rest) hr
      have e : vals (vs ++ [.ref (.func a)]) ++ [r] ++ rest = vals vs ++ .ref (.func a) :: r :: rest := by
        simp [vals, Val.toAdmin]
      rw [e] at this
      exact this
    have := wp_exit_post (lift hst) (o := .tail (us ++ vs) a r) ⟨hr, [], by simp [vals, Val.toAdmin]⟩
    cases m <;> exact this

/-- A label body that is neither all values nor an exit steps, if the label does. -/
theorem body_step_of_label {m : Corr} {s : Store H} {f : Frame} {us : List Val} {k : Nat}
    {cont : List Instr} {b : List Admin} {Q : Post H} (hus : NoFuncTop us)
    (h : Wp m P host s f (vals us ++ [.label k cont b]) Q) (hex : ∀ o, ¬ Exits o b) :
    ∃ c'', Step P host ⟨s, f, b⟩ c'' := by
  obtain ⟨⟨s', f', es'⟩, hst⟩ := wp_progress h fun o he => not_exits_label he
  have h' := wp_step_inv h hst
  obtain ⟨is', hr, rfl⟩ := Sim.Closure.Step.label_inv hst
  cases hr with
  | ctxt hb => exact ⟨_, hb⟩
  | values vs => exact (hex (.normal vs) rfl).elim
  | @brZero vs' vs l rest _ _ => exact (hex (.br l.toNat (vs' ++ vs)) ⟨l, rest, rfl, by simp⟩).elim
  | @brSucc vs l rest _ => exact (hex (.br l.toNat vs) ⟨l, rest, rfl, by simp⟩).elim
  | @returnCallRef vs c rest hc =>
    have hstuck : ∀ c', ¬ Step P host ⟨s, f, vals us ++ (vals vs ++ [c])⟩ c' := fun c' hc' =>
      not_step_blocked (vs := us ++ vs) (rest := []) (Or.inr (Or.inr hc)) (by simpa using hc')
    obtain ⟨o, he⟩ : ∃ o, Exits o (vals us ++ (vals vs ++ [c])) := by
      by_contra hno
      push Not at hno
      obtain ⟨c', hc'⟩ := wp_progress h' hno
      exact hstuck c' hc'
    have he' : Exits o (vals (us ++ vs) ++ c :: []) := by simpa using he
    obtain ⟨vs₀, a, hvs, rfl⟩ := exits_rcr_inv hc he'
    rcases List.eq_nil_or_concat vs with rfl | ⟨vs₁, v, rfl⟩
    · rw [List.append_nil] at hvs
      exact (hus a (by rw [hvs]; simp)).elim
    · have hv : us ++ vs₁ = vs₀ ∧ [v] = [.ref (.func a)] :=
        List.append_inj' (by simpa using hvs) rfl
      obtain rfl : v = .ref (.func a) := by simpa using hv.2
      exact (hex (.tail vs₁ a c) ⟨hc, rest, by simp [vals, Val.toAdmin]⟩).elim
  | @return_ vs rest => exact (hex (.ret vs) ⟨rest, by simp⟩).elim
  | throwRef a => exact (hex (.throw a) ⟨[], [], by simp⟩).elim
  | trap => exact (hex .trap ⟨[], [], rfl⟩).elim

/-- **Inversion of labels** (partial correctness). -/
theorem safe_label_inv {us : List Val} {k : Nat} {cont : List Instr} {Q : Post H}
    (hus : NoFuncTop us) :
    ∀ (n : Nat) {s : Store H} {f : Frame} {b : List Admin},
      HWP P host s f (vals us ++ [.label k cont b]) Q →
      Safe P host (labelPost P host k cont us Q) n ⟨s, f, b⟩
  | 0, _, _, _, _ => trivial
  | n + 1, s, f, b, h => by
    by_cases hex : ∃ o, Exits o b
    · obtain ⟨o, he⟩ := hex
      exact Or.inl ⟨o, he, wp_label_exit_post (m := .part) h he⟩
    · push Not at hex
      refine Or.inr ⟨body_step_of_label (m := .part) hus h hex, fun c' hst => ?_⟩
      rcases c' with ⟨s', f', b'⟩
      exact safe_label_inv hus n (h.step_inv (label_ctxt hst))

theorem hwp_label_inv {s : Store H} {f : Frame} {us : List Val} {k : Nat} {cont : List Instr}
    {b : List Admin} {Q : Post H} (hus : NoFuncTop us)
    (h : HWP P host s f (vals us ++ [.label k cont b]) Q) :
    HWP P host s f b (labelPost P host k cont us Q) :=
  fun n => safe_label_inv hus n h

/-- **Inversion of labels** (total correctness). -/
theorem tsafe_label_inv {us : List Val} {k : Nat} {cont : List Instr} {Q : Post H}
    (hus : NoFuncTop us) {c : Config H} (h : TSafe P host Q c) :
    ∀ b : List Admin, c.code = vals us ++ [.label k cont b] →
      TSafe P host (labelPostT P host k cont us Q) ⟨c.store, c.frame, b⟩ := by
  induction h with
  | @exit c o he _ =>
    intro b hc
    rw [hc] at he
    exact (not_exits_label he).elim
  | @step c hp hs ih =>
    intro b hc
    rcases c with ⟨s, f, code⟩
    dsimp only at hc hp hs ih ⊢
    subst hc
    have h : TWP P host s f (vals us ++ [.label k cont b]) Q := TSafe.step hp hs
    by_cases hex : ∃ o, Exits o b
    · obtain ⟨o, he⟩ := hex
      exact .exit o he (wp_label_exit_post (m := .total) h he)
    · push Not at hex
      refine .step (body_step_of_label (m := .total) hus h hex) fun c' hst => ?_
      rcases c' with ⟨s', f', b'⟩
      exact ih _ (label_ctxt hst) b' rfl

theorem twp_label_inv {s : Store H} {f : Frame} {us : List Val} {k : Nat} {cont : List Instr}
    {b : List Admin} {Q : Post H} (hus : NoFuncTop us)
    (h : TWP P host s f (vals us ++ [.label k cont b]) Q) :
    TWP P host s f b (labelPostT P host k cont us Q) :=
  tsafe_label_inv hus h b rfl

end Silmaril.Proofs.Wasm.Auto.Equiv