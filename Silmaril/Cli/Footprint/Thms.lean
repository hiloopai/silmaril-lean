module

public import Silmaril.Cli.Footprint.Defs
public import Silmaril.Cli.Behaviour.Thms

/-!
# File footprints: when the pipe is the sequential pipe (theorems)

PROVED (standard axioms), namespace `Silmaril.Cli`.

* **Commuting events.** `FileEv.Indep.symm`, `Fs.set_comm`, `Fs.replay_swap` (two commuting
  events replay in either order), `Fs.replay_move` (an event that commutes with a log moves past
  it), **`Fs.replay_interleave`** (an interleaving of apart logs replays as their
  concatenation), `Interleave.perm`.
* **Separate footprints.** `Apart.symm`, `separate_of_within` (specs logging disjoint path sets
  are separate), `Separate.symm`.
* **Framing.** `framed_pure` (a pure program that does not look at the files).
* **Reordered logs.** `le_relog`, `relog_mono`, `relog_relog`, `logBlind_relog`, `logBlind_of`
  (a spec that ignores the log is log-blind).
* **The pipe is the sequential pipe** for framed specs with separate footprints:
  **`pipe_le_pipeSeq`** (`pipe S T ≤ relog (pipeSeq S T)`), **`relog_pipe_eq`** (with `Logged`,
  `relog (pipe S T) = relog (pipeSeq S T)`), and **`pipe_le_of_pipeSeq`** (a log-blind spec
  met by the sequential schedule is met by the pipe).

The plain `pipe S T ≤ pipeSeq S T` is false even for separate footprints, since `pipeSeq` fixes
the order of the log (`Silmaril.Cli.Footprint.Examples.not_pipe_le_pipeSeq`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli

/-! ## Commuting events -/

theorem FileEv.Indep.symm {e₁ e₂ : FileEv} (h : e₁.Indep e₂) : e₂.Indep e₁ :=
  h.imp Ne.symm And.symm

theorem Apart.symm {l₁ l₂ : List FileEv} (h : Apart l₁ l₂) : Apart l₂ l₁ :=
  fun e₂ h₂ e₁ h₁ => (h e₁ h₁ e₂ h₂).symm

theorem Apart.of_cons_left {e : FileEv} {l₁ l₂ : List FileEv} (h : Apart (e :: l₁) l₂) :
    Apart l₁ l₂ :=
  fun e₁ h₁ => h e₁ (List.mem_cons_of_mem _ h₁)

theorem Apart.of_cons_right {e : FileEv} {l₁ l₂ : List FileEv} (h : Apart l₁ (e :: l₂)) :
    Apart l₁ l₂ :=
  fun e₁ h₁ e₂ h₂ => h e₁ h₁ e₂ (List.mem_cons_of_mem _ h₂)

theorem Fs.set_ne {fs : Fs} {p q : FPath} (c : Option Bytes) (h : q ≠ p) :
    fs.set p c q = fs q := by
  simp [Fs.set, h]

/-- Writes to different paths commute. -/
theorem Fs.set_comm (fs : Fs) {p q : FPath} (h : p ≠ q) (c d : Option Bytes) :
    (fs.set p c).set q d = (fs.set q d).set p c := by
  funext r
  by_cases hq : r = q
  · have hp : q ≠ p := h.symm
    simp [Fs.set, hq, hp]
  · simp [Fs.set, hq]

/-- A read on `p` after a write on another path `q` sees what was there before. -/
theorem Fs.replay_read_set (fs : Fs) {p q : FPath} (h : p ≠ q) (c d : Option Bytes)
    (l : List FileEv) :
    (fs.set q d).replay (.read p c :: l) = if fs p = c then (fs.set q d).replay l else none := by
  rw [Fs.replay_read, Fs.set_ne d h]

/-- **Two commuting events replay in either order.** -/
theorem Fs.replay_swap {e₁ e₂ : FileEv} (h : e₁.Indep e₂) (fs : Fs) (l : List FileEv) :
    fs.replay (e₁ :: e₂ :: l) = fs.replay (e₂ :: e₁ :: l) := by
  cases e₁ with
  | read p c =>
    cases e₂ with
    | read q d =>
      simp only [Fs.replay_read]
      by_cases hp : fs p = c <;> by_cases hq : fs q = d <;> simp [hp, hq]
    | write q d =>
      have hpq : p ≠ q := h.resolve_right (by simp [FileEv.isWrite])
      rw [Fs.replay_write, Fs.replay_read_set fs hpq, Fs.replay_read, Fs.replay_write]
  | write p c =>
    cases e₂ with
    | read q d =>
      have hqp : q ≠ p := (h.resolve_right (by simp [FileEv.isWrite])).symm
      rw [Fs.replay_write, Fs.replay_read_set fs hqp, Fs.replay_read, Fs.replay_write]
    | write q d =>
      have hpq : p ≠ q := h.resolve_right (by simp [FileEv.isWrite])
      simp only [Fs.replay_write, Fs.set_comm fs hpq]

/-- Replaying is a congruence for a common first event. -/
theorem Fs.replay_cons_congr (e : FileEv) {l l' : List FileEv}
    (h : ∀ fs : Fs, fs.replay l = fs.replay l') (fs : Fs) :
    fs.replay (e :: l) = fs.replay (e :: l') := by
  cases e with
  | read p c => simp only [Fs.replay_read, h]
  | write p c => simp only [Fs.replay_write, h]

/-- **An event that commutes with a log moves past it.** -/
theorem Fs.replay_move {x : FileEv} {a : List FileEv} (h : ∀ y ∈ a, x.Indep y)
    (r : List FileEv) (fs : Fs) : fs.replay (x :: (a ++ r)) = fs.replay (a ++ x :: r) := by
  induction a generalizing fs with
  | nil => rfl
  | cons y a ih =>
    have hy : x.Indep y := h y List.mem_cons_self
    have ih' : ∀ fs : Fs, fs.replay (x :: (a ++ r)) = fs.replay (a ++ x :: r) :=
      ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    calc fs.replay (x :: y :: (a ++ r)) = fs.replay (y :: x :: (a ++ r)) := Fs.replay_swap hy _ _
      _ = fs.replay (y :: (a ++ x :: r)) := Fs.replay_cons_congr y ih' fs

/-- **An interleaving of apart logs replays as their concatenation.** -/
theorem Fs.replay_interleave {a b l : List FileEv} (hab : Apart a b) (h : Interleave a b l)
    (fs : Fs) : fs.replay l = fs.replay (a ++ b) := by
  induction h generalizing fs with
  | nil => rfl
  | @left x a b l _ ih =>
    exact Fs.replay_cons_congr x (ih hab.of_cons_left) fs
  | @right x a b l _ ih =>
    have hx : ∀ y ∈ a, x.Indep y := fun y hy => (hab y hy x List.mem_cons_self).symm
    calc fs.replay (x :: l) = fs.replay (x :: (a ++ b)) :=
          Fs.replay_cons_congr x (ih hab.of_cons_right) fs
      _ = fs.replay (a ++ x :: b) := Fs.replay_move hx b fs

/-- An interleaving is a permutation of the concatenation. -/
theorem Interleave.perm {α : Type} {a b l : List α} (h : Interleave a b l) : (a ++ b).Perm l := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact ih.cons _
  | @right x a b l _ ih => exact List.perm_middle.trans (ih.cons x)

/-! ## Separate footprints and framing -/

namespace Spec

theorem Separate.symm {S T : Spec} (h : S.Separate T) : T.Separate S :=
  fun _ _ _ _ h₁ h₂ => (h _ _ _ _ h₂ h₁).symm

/-- **Specs logging disjoint sets of paths are separate.** -/
theorem separate_of_within {P Q : FPath → Prop} {S T : Spec} (hS : S.Within P) (hT : T.Within Q)
    (hPQ : ∀ p, P p → Q p → False) : S.Separate T :=
  fun _ _ _ _ h₁ h₂ e₁ he₁ e₂ he₂ =>
    .inl fun heq => hPQ _ (hS _ _ h₁ e₁ he₁) (heq ▸ hT _ _ h₂ e₂ he₂)

/-- **A pure program that does not look at the files is framed**: it logs nothing and keeps
them. -/
theorem framed_pure {f : Input → Out} (hf : ∀ i fs, f { i with fs := fs } = f i) :
    (pure f).Framed := by
  rintro i o fs g ⟨hs, he, hx, -, hr, hc, hl⟩ hg
  have hfg : some fs = some g := by rw [← hg, hl, Fs.replay_nil]
  have hf' : f { i with fs := fs } = f i := hf i fs
  exact ⟨hf' ▸ hs, hf' ▸ he, hf' ▸ hx, (Option.some.inj hfg).symm, hr, hc, hl⟩

/-! ## Reordered logs -/

theorem le_relog (S : Spec) : S ≤ relog S := fun _ o h => ⟨o.log, h, .refl _⟩

theorem relog_mono {S T : Spec} (h : S ≤ T) : relog S ≤ relog T :=
  fun i _ ⟨l, hS, hp⟩ => ⟨l, h i _ hS, hp⟩

theorem relog_relog (S : Spec) : relog (relog S) = relog S := by
  refine le_antisymm (fun i o ⟨l, ⟨l', hS, hp'⟩, hp⟩ => ⟨l', hS, hp'.trans hp⟩) (le_relog _)

theorem logBlind_relog (S : Spec) : (relog S).LogBlind := (relog_relog S).le

/-- **A spec that ignores the log is log-blind.** -/
theorem logBlind_of {U : Spec} (h : ∀ i o l, U i { o with log := l } → U i o) : U.LogBlind :=
  fun i o ⟨l, hU, _⟩ => h i o l hU

/-! ## The pipe is the sequential pipe -/

/-- The sequential observation behind a pipe run whose programs' logs replay in sequence. -/
theorem pipeSeq_of_pipe {S T : Spec} (hS : S.Framed) (hT : T.Framed) {i : Input} {o o₁ o₂ : Obs}
    {fs₁ fs₂ f₁ : Fs} (h₁ : S { i with fs := fs₁ } o₁)
    (h₂ : T { i with stdin := o₁.stdout, fs := fs₂ } o₂) (hs : o.stdout = o₂.stdout)
    (he : Interleave o₁.stderr o₂.stderr o.stderr) (hx : o.exit = o₂.exit)
    (hc : o.consumed = o₁.consumed) (hr : o.reads = o₁.reads ++ o₂.reads)
    (hd : o.refused = (o₁.refused || o₂.refused)) (r₁ : i.fs.replay o₁.log = some f₁)
    (r₂ : f₁.replay o₂.log = some o.fs) :
    pipeSeq S T i { o with log := o₁.log ++ o₂.log } := by
  have h₁' : S i { o₁ with fs := f₁ } := hS { i with fs := fs₁ } o₁ i.fs f₁ h₁ r₁
  have h₂' : T { i with stdin := o₁.stdout, fs := f₁ } { o₂ with fs := o.fs } :=
    hT { i with stdin := o₁.stdout, fs := fs₂ } o₂ f₁ o.fs h₂ r₂
  exact ⟨_, _, h₁', h₂', hs, he, hx, hc, hr, rfl, hd, rfl⟩

/-- **The pipe is the sequential pipe, up to the order of the log**, for framed specs with
separate footprints: every run of `S | T` is a run of `pipeSeq S T` whose log is reordered. -/
theorem pipe_le_pipeSeq {S T : Spec} (hS : S.Framed) (hT : T.Framed) (hST : S.Separate T) :
    pipe S T ≤ relog (pipeSeq S T) := by
  rintro i o ⟨⟨o₁, o₂, fs₁, fs₂, h₁, h₂, hs, he, hx, hc, hr, hl, hd⟩, hcoh⟩
  have hap : Apart o₁.log o₂.log := hST _ _ _ _ h₁ h₂
  have hseq : i.fs.replay (o₁.log ++ o₂.log) = some o.fs :=
    (Fs.replay_interleave hap hl i.fs).symm.trans hcoh
  rw [Fs.replay_append] at hseq
  obtain ⟨f₁, r₁, r₂⟩ : ∃ f₁, i.fs.replay o₁.log = some f₁ ∧ f₁.replay o₂.log = some o.fs :=
    Option.bind_eq_some_iff.1 hseq
  exact ⟨_, pipeSeq_of_pipe hS hT h₁ h₂ hs he hx hc hr hd r₁ r₂, hl.perm⟩

/-- **Up to the order of the log, `S | T` and `pipeSeq S T` are the same spec**, for logged,
framed specs with separate footprints. -/
theorem relog_pipe_eq {S T : Spec} (hS : S.Logged) (hT : T.Logged) (hS' : S.Framed)
    (hT' : T.Framed) (hST : S.Separate T) : relog (pipe S T) = relog (pipeSeq S T) :=
  le_antisymm (relog_relog (pipeSeq S T) ▸ relog_mono (pipe_le_pipeSeq hS' hT' hST))
    (relog_mono (pipeSeq_le_pipe hS hT))

/-- **To meet a log-blind spec, a pipe of framed, separate specs need only be checked on the
sequential schedule.** -/
theorem pipe_le_of_pipeSeq {S T U : Spec} (hS : S.Framed) (hT : T.Framed) (hST : S.Separate T)
    (hU : U.LogBlind) (h : pipeSeq S T ≤ U) : pipe S T ≤ U :=
  (pipe_le_pipeSeq hS hT hST).trans ((relog_mono h).trans hU)

end Spec

end Silmaril.Cli
