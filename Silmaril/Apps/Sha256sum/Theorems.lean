module

public import Silmaril.Apps.Sha256sum.Run

/-! # Basic theorems about the `sha256sum` specification

- `status_cases`: the exit status is always 0 or 1.
- `stdout_eq_nil_of_status`: under `--check --status`, nothing is written to standard
  output (spec.md §11.3). Diagnostics on standard error are not suppressed, and neither is
  the help text: `--status --help` prints help, which is why the statement assumes a
  completed scan.
- `stdout_full_status`: when standard output is full and anything was to be printed, the
  status is 1.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

theorem finish_status (w : World) (out err : Bytes) (s : Nat) (h : s = 0 ∨ s = 1) :
    (finish w out err s).status = 0 ∨ (finish w out err s).status = 1 := by
  unfold finish; split <;> simp_all

theorem status_cases (w : World) : (sha256sum w).status = 0 ∨ (sha256sum w).status = 1 := by
  unfold sha256sum
  split
  · exact finish_status _ _ _ _ (.inl rfl)
  · exact finish_status _ _ _ _ (.inl rfl)
  · exact finish_status _ _ _ _ (.inr rfl)
  · split
    · exact finish_status _ _ _ _ (.inr rfl)
    · exact finish_status _ _ _ _ (by split <;> simp)

/-! ## `--status` silence -/

theorem readPath_out (w : World) (st : St) (p : Bytes) : (readPath w st p).2.out = st.out := by
  unfold readPath readStdin
  split
  · split <;> rfl
  · rfl

theorem verifyLine_out (w : World) (o : Opts) (st : St) (c : Counters) (hex name : Bytes)
    (h : o.statusOnly = true) : (verifyLine w o st c hex name).1.out = st.out := by
  have hr := readPath_out w st name
  unfold verifyLine
  rcases e : readPath w st name with ⟨r, st'⟩
  rw [e] at hr
  simp only at hr
  rcases r with data | er | ⟨er, pre⟩
  · simp [h, hr]
  · cases er <;> simp [h, St.warn, hr]; split <;> simp [hr]
  · simp [h, St.warn, hr]

theorem checkLine_out (w : World) (o : Opts) (isStdin : Bool) (cname : Bytes) (st : St)
    (c : Counters) (n : Nat) (L : Bytes) (h : o.statusOnly = true) :
    (checkLine w o isStdin cname st c n L).1.out = st.out := by
  unfold checkLine
  split
  · rfl
  · simp only
    split
    · rfl
    · split
      · split
        · split <;> simp [St.warn]
        · rw [verifyLine_out _ _ _ _ _ _ h]
      · split <;> simp [St.warn]

theorem checkLinesFrom_out (w : World) (o : Opts) (isStdin : Bool) (cname : Bytes)
    (h : o.statusOnly = true) :
    ∀ (st : St) (c : Counters) (n : Nat) (Ls : List Bytes),
      (checkLinesFrom w o isStdin cname st c n Ls).1.out = st.out
  | st, c, n, [] => rfl
  | st, c, n, L :: Ls => by
    unfold checkLinesFrom
    rw [checkLinesFrom_out w o isStdin cname h, checkLine_out _ _ _ _ _ _ _ _ h]

theorem summary_out (w : World) (o : Opts) (cname : Bytes) (st : St) (c : Counters) :
    (summary w o cname st c).out = st.out := by
  unfold summary
  split
  · rfl
  · split
    · rfl
    · simp only
      split <;> split <;> split <;> split <;> rfl

theorem checkFile_out (w : World) (o : Opts) (st : St) (cf : Bytes) (h : o.statusOnly = true) :
    (checkFile w o st cf).1.out = st.out := by
  have hr := readPath_out w st cf
  unfold checkFile
  rcases e : readPath w st cf with ⟨r, st'⟩
  rw [e] at hr
  simp only at hr
  rcases r with data | er | ⟨er, pre⟩
  · simp only [summary_out, checkLinesFrom_out _ _ _ _ h, hr]
  · simp [St.warn, hr]
  · simp only [St.warn, checkLinesFrom_out _ _ _ _ h, hr]

theorem checkAll_out (w : World) (o : Opts) (h : o.statusOnly = true) :
    ∀ (st : St) (cfs : List Bytes), (checkAll w o st cfs).1.out = st.out
  | st, [] => rfl
  | st, cf :: cfs => by
    unfold checkAll
    rw [checkAll_out w o h, checkFile_out _ _ _ _ h]

/-- `--check --status` writes nothing to standard output (spec.md §11.3). -/
theorem stdout_eq_nil_of_status (w : World) (o : Opts) (ops : List Bytes)
    (hs : scan w.prog w.posix w.argv.tail = .done o ops) (hv : validate o = none)
    (hc : o.check = true) (hq : o.statusOnly = true) : (sha256sum w).stdout = [] := by
  unfold sha256sum
  rw [hs]
  simp only [hv]
  have : (runMode w o ops).1.out = [] := by
    unfold runMode
    simp only [hc, ↓reduceIte]
    rw [checkAll_out _ _ hq]
  unfold finish
  split
  · rfl
  · exact this

/-- A full standard output turns any run that prints into a failure. -/
theorem stdout_full_status (w : World) (out err : Bytes) (s : Nat) (h : w.stdoutFull = true)
    (hne : out ≠ []) : (finish w out err s).status = 1 ∧ (finish w out err s).stdout = [] := by
  unfold finish
  have : out.isEmpty = false := by cases out <;> simp_all
  simp [h, this]

end Silmaril.Apps.Sha256sum
