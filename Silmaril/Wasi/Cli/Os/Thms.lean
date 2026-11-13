module

public import Silmaril.Wasi.Cli.Os.Defs
public import Silmaril.Cli.Behaviour.Thms

/-!
# CLI specifications over `IoSpec`: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Cli.Os`.

* Projections: `written_append`, `readFrom_append`, `written_prefix`, `readFrom_prefix`,
  `written_map_self`, `written_map_ne`, `readFrom_map_write`.
* **`allowed_mono`**, **`sat_mono`**: refining a CLI spec weakens nothing that was proved: an
  LPS process that meets `S` meets every `T ≥ S` (`psafeF_mono`: `PSafeF` is monotone in its
  trace predicate). `allowed_nil`: the empty trace is allowed by a spec with an allowed
  observation (the `A []` obligation of `IoSafeN`).
* **`ioSafeN_mono_pred`**: `IoSafeN` is monotone in the trace predicate (for an exit
  condition `Q` that is). So an `IoSafeN` proof for a concrete trace predicate transfers to
  `Allowed S w i` once the concrete predicate implies it.
* **`allowed_exit`** (soundness reading): a finished run `pre ++ [exitEv code lfs]` that `S`
  allows shows an observation `o` with `S i o` whose stdout, stderr, consumed stdin, exit
  code and files under the roots are those of the run.
* **`allowed_of_run`** (the converse, prefix-closed): every prefix of a finished run whose
  projections are those of an allowed observation is allowed. This is how a concrete trace
  predicate ("a prefix of this run") is shown to imply `Allowed`.
-/

@[expose] public section

namespace Silmaril.Cli.Os

open Silmaril.Process.LPS (Event Word Byte)
open Silmaril.Machine.Process.LpsBridge
open Silmaril.Machine.Process.IoSpec

/-! ## Projections -/

theorem written_append (ch : Word) (a b : List Event) :
    written ch (a ++ b) = written ch a ++ written ch b := by
  induction a with
  | nil => rfl
  | cons e a ih =>
    cases e with
    | writeEv c x => by_cases h : c = ch <;> simp [written, h, ih]
    | readEv => simp [written, ih]
    | exitEv => simp [written, ih]
    | killEv => simp [written, ih]

theorem readFrom_append (ch : Word) (a b : List Event) :
    readFrom ch (a ++ b) = readFrom ch a ++ readFrom ch b := by
  induction a with
  | nil => rfl
  | cons e a ih =>
    cases e with
    | readEv c x => by_cases h : c = ch <;> simp [readFrom, h, ih]
    | writeEv => simp [readFrom, ih]
    | exitEv => simp [readFrom, ih]
    | killEv => simp [readFrom, ih]

theorem written_prefix (ch : Word) {a b : List Event} (h : a <+: b) : written ch a <+: written ch b := by
  obtain ⟨t, rfl⟩ := h
  rw [written_append]; exact List.prefix_append _ _

theorem readFrom_prefix (ch : Word) {a b : List Event} (h : a <+: b) :
    readFrom ch a <+: readFrom ch b := by
  obtain ⟨t, rfl⟩ := h
  rw [readFrom_append]; exact List.prefix_append _ _

@[simp] theorem written_map_self (ch : Word) (bs : List Byte) :
    written ch (bs.map (.writeEv ch)) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [written, ih]

theorem written_map_ne {ch ch' : Word} (h : ch' ≠ ch) (bs : List Byte) :
    written ch' (bs.map (.writeEv ch)) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [written, ih, Ne.symm h]

@[simp] theorem readFrom_map_write (ch ch' : Word) (bs : List Byte) :
    readFrom ch' (bs.map (.writeEv ch)) = [] := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readFrom, ih]

/-! ## Monotonicity -/

theorem allowed_mono {S T : Spec} (h : S ≤ T) {w : Wiring} {i : Input} {tr : List Event} :
    Allowed S w i tr → Allowed T w i tr :=
  fun ⟨o, hs, hc⟩ => ⟨o, h i o hs, hc⟩

theorem allowed_nil {S : Spec} {w : Wiring} {i : Input} (h : ∃ o, S i o) : Allowed S w i [] := by
  obtain ⟨o, ho⟩ := h
  refine ⟨o, ho, fun _ h => (by cases h), List.nil_prefix, List.nil_prefix, List.nil_prefix, ?_⟩
  intro pre _ _ _ he
  have hl := congrArg List.length he
  simp at hl

theorem psafeF_mono {oracle : Oracle} {nstep : NStep}
    {segs : List Silmaril.Process.LPS.Segment} {refused : Silmaril.Process.LPS.RefusalFilter}
    {A B : List Event → Prop} (h : ∀ tr, A tr → B tr)
    {cfg : Silmaril.Process.LPS.Config (flagMachine oracle nstep)} :
    PSafeF segs refused A cfg → PSafeF segs refused B cfg :=
  fun ⟨hA, hs⟩ => ⟨fun tr c' hr => h tr (hA tr c' hr), hs⟩

/-- **Refinement transfers process-level satisfaction**: a process that meets `S` meets every
weaker spec. -/
theorem sat_mono {oracle : Oracle} {nstep : NStep}
    {segs : List Silmaril.Process.LPS.Segment} {refused : Silmaril.Process.LPS.RefusalFilter}
    {S T : Spec} (h : S ≤ T) {w : Wiring} {i : Input}
    {cfg : Silmaril.Process.LPS.Config (flagMachine oracle nstep)} :
    Sat segs refused S w i cfg → Sat segs refused T w i cfg :=
  psafeF_mono fun _ => allowed_mono h

/-- **`IoSafeN` is monotone in the trace predicate**, for an exit condition that is. -/
theorem ioSafeN_mono_pred {step : Silmaril.X86.MState → Option Silmaril.X86.MState} {E : SysEnv}
    {Q : Silmaril.X86.MState → E.Model → (List Event → Prop) → Prop}
    (hQ : ∀ m e (A B : List Event → Prop), (∀ t, A t → B t) → Q m e A → Q m e B) :
    ∀ (n : Nat) (m : Silmaril.X86.MState) (e : E.Model) (A B : List Event → Prop),
      (∀ t, A t → B t) → IoSafeN step E Q n m e A → IoSafeN step E Q n m e B
  | 0, _, _, _, _, _, _ => trivial
  | n + 1, m, e, A, B, hAB, h => by
    obtain ⟨h0, hq | ⟨m', hs, hn⟩ | ⟨ht, hall⟩⟩ := h
    · exact ⟨hAB _ h0, .inl (hQ m e A B hAB hq)⟩
    · exact ⟨hAB _ h0, .inr (.inl ⟨m', hs, ioSafeN_mono_pred hQ n m' e A B hAB hn⟩)⟩
    · refine ⟨hAB _ h0, .inr (.inr ⟨ht, fun ch => ⟨(hall ch).1, fun o ho => ?_⟩⟩)⟩
      have hnext : o.Next (IoSafeN step E Q n) A := (hall ch).2 o ho
      cases o with
      | resume m' e' evs =>
        exact ioSafeN_mono_pred hQ n m' e' _ _ (fun t => hAB (evs ++ t)) hnext
      | halt evs => exact hAB evs hnext

/-! ## Finished runs -/

/-- The exit of a finished run is its only exit: a trace `pre ++ [x]` with `pre` exit-free
splits around an exit only at its end. -/
theorem exit_split {pre pre' post : List Event} {x y : Event} (hpre : ∀ e ∈ pre, ¬ IsExit e)
    (hy : IsExit y) (h : pre ++ [x] = pre' ++ y :: post) : pre' = pre ∧ y = x ∧ post = [] := by
  rcases List.append_eq_append_iff.1 h with ⟨a', rfl, ha⟩ | ⟨c', hc, hc'⟩
  · cases a' with
    | nil =>
      have hyx : y = x ∧ post = [] := by simpa [eq_comm] using ha
      exact ⟨by simp, hyx⟩
    | cons a a' =>
      have hnil : a' ++ y :: post = [] := (List.cons_eq_cons.1 ha).2.symm
      simp at hnil
  · cases c' with
    | nil =>
      have hyx : y = x ∧ post = [] := by simpa using hc'
      exact ⟨by simpa using hc.symm, hyx⟩
    | cons c c' =>
      have hyc : y = c := (List.cons_eq_cons.1 hc').1
      have hmem : y ∈ pre := by rw [hc, hyc]; simp
      exact absurd hy (hpre y hmem)

/-- **A finished run that `S` allows is an allowed observation.** -/
theorem allowed_exit {S : Spec} {w : Wiring} {i : Input} {pre : List Event} {code : Word}
    {lfs : Silmaril.Process.LPS.Fs.FileSystem}
    (h : Allowed S w i (pre ++ [.exitEv code lfs])) :
    ∃ o, S i o ∧ written w.outCh pre = lpsBytes o.stdout ∧
      written w.errCh pre = lpsBytes o.stderr ∧
      readFrom w.inCh pre = lpsBytes (i.stdin.take o.consumed) ∧
      code = exitWord o.exit ∧ FsAgrees w i o.fs lfs := by
  obtain ⟨o, hs, -, -, -, -, hx⟩ := h
  obtain ⟨-, hout, herr, hin, hcode, hfs⟩ := hx pre code lfs [] rfl
  exact ⟨o, hs, hout, herr, hin, hcode, hfs⟩

/-- The hypotheses of `allowed_of_run`: `pre ++ [exitEv code lfs]` is a finished run with the
observation `o` of `i`. -/
structure Run (w : Wiring) (i : Input) (o : Obs) (pre : List Event) (code : Word)
    (lfs : Silmaril.Process.LPS.Fs.FileSystem) : Prop where
  /-- Only expected events before the exit. -/
  expected : ∀ e ∈ pre, w.Expected e
  /-- No exit before the end. -/
  noExit : ∀ e ∈ pre, ¬ IsExit e
  /-- Stdout. -/
  out : written w.outCh pre = lpsBytes o.stdout
  /-- Stderr. -/
  err : written w.errCh pre = lpsBytes o.stderr
  /-- Consumed stdin. -/
  inp : readFrom w.inCh pre = lpsBytes (i.stdin.take o.consumed)
  /-- The exit code. -/
  exit : code = exitWord o.exit
  /-- The files. -/
  fs : FsAgrees w i o.fs lfs

/-- **Every prefix of a finished run with an allowed observation is allowed.** -/
theorem allowed_of_run {S : Spec} {w : Wiring} {i : Input} {o : Obs} {pre : List Event}
    {code : Word} {lfs : Silmaril.Process.LPS.Fs.FileSystem} (hs : S i o)
    (hr : Run w i o pre code lfs) {tr : List Event} (htr : tr <+: pre ++ [.exitEv code lfs]) :
    Allowed S w i tr := by
  refine ⟨o, hs, ?_⟩
  have hexp : ∀ ev ∈ pre ++ [.exitEv code lfs], w.Expected ev := by
    intro ev hev
    rcases List.mem_append.1 hev with h | h
    · exact hr.expected ev h
    · rw [List.mem_singleton.1 h]; trivial
  have hfull : ∀ ch, written ch (pre ++ [.exitEv code lfs]) = written ch pre := fun ch => by
    simp [written_append, written]
  have hfullIn : readFrom w.inCh (pre ++ [.exitEv code lfs]) = readFrom w.inCh pre := by
    simp [readFrom_append, readFrom]
  refine ⟨fun ev hev => hexp ev (htr.subset hev), ?_, ?_, ?_, ?_⟩
  · have hp : written w.outCh tr <+: written w.outCh pre := hfull w.outCh ▸ written_prefix _ htr
    rwa [hr.out] at hp
  · have hp : written w.errCh tr <+: written w.errCh pre := hfull w.errCh ▸ written_prefix _ htr
    rwa [hr.err] at hp
  · have hp : readFrom w.inCh tr <+: readFrom w.inCh pre := hfullIn ▸ readFrom_prefix _ htr
    rwa [hr.inp] at hp
  · show ∀ pre' code' lfs' post, tr = pre' ++ .exitEv code' lfs' :: post →
      post = [] ∧ written w.outCh pre' = lpsBytes o.stdout ∧
      written w.errCh pre' = lpsBytes o.stderr ∧
      readFrom w.inCh pre' = lpsBytes (i.stdin.take o.consumed) ∧
      code' = exitWord o.exit ∧ FsAgrees w i o.fs lfs'
    intro pre' code' lfs' post htr'
    obtain ⟨t, ht⟩ := htr
    have hsplit : pre ++ [.exitEv code lfs] = pre' ++ .exitEv code' lfs' :: (post ++ t) := by
      rw [← ht, htr']; simp
    obtain ⟨rfl, hx, hpost⟩ := exit_split (y := .exitEv code' lfs') hr.noExit trivial hsplit
    have hcl : code' = code ∧ lfs' = lfs := by simpa using hx
    obtain ⟨rfl, rfl⟩ := hcl
    exact ⟨(List.append_eq_nil_iff.1 hpost).1, hr.out, hr.err, hr.inp, hr.exit, hr.fs⟩

end Silmaril.Cli.Os
