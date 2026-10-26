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
- The program name (`libtool_stderr`, `libtool_old_stderr_ne`): diagnostics use gnulib's
  `set_program_name` of `argv[0]` and getopt's messages `argv[0]` verbatim. The
  specification used `argv[0]` verbatim everywhere until this was fixed, which made it
  disagree with the binary for every `argv[0]` whose directory ends in `/.libs/`.
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
    (hs : scan w.argv0 w.posix w.argv.tail = .done o ops) (hv : validate o = none)
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

/-! ## The program name

gnulib's `set_program_name` (copied in `sha256sum.c`) drops the directory of an `argv[0]`
whose directory ends in `/.libs/`, and then a leading `lt-` (libtool's uninstalled
wrappers). `error` and `usage` print that name; glibc `getopt` prints `argv[0]` itself.
Measured on the pinned `sha256sum-min` (sha256 `22fa6345…d42817`), run as `./d/.libs/lt-P -x`:

```
./d/.libs/lt-P: invalid option -- 'x'
Try 'P --help' for more information.
```

with status 1. `libtool_stderr` is that output. The specification before the fix printed
`argv[0]` in both lines (`libtool_old_stderr_ne`), so `Plan.FullGoal` was false for this
`argv[0]`. On the stdin tier (`argv = [prog]`) nothing is printed to stderr and stdout does not
mention the name (`Sys.sha256sum_stdin`, for every `prog`), so that tier is unaffected. -/

/-- The counterexample world: `argv = ["./d/.libs/lt-P", "-x"]`. -/
def libtoolWorld : World :=
  { argv := [lit "./d/.libs/lt-P", lit "-x"], fs := fun _ => .openErr .ENOENT }

theorem libtool_argv0 : libtoolWorld.argv0 = lit "./d/.libs/lt-P" := rfl

theorem libtool_prog : libtoolWorld.prog = lit "P" := by decide

/-- The specification's diagnostic for `./d/.libs/lt-P -x`: the binary's (measured). -/
theorem libtool_stderr : sha256sum libtoolWorld =
    { stdout := [], status := 1,
      stderr := lit "./d/.libs/lt-P: invalid option -- 'x'\n" ++
        lit "Try 'P --help' for more information.\n" } := by
  decide

/-- **Counterexample to the old statement.** The old specification's stderr (`argv[0]` as the
program name everywhere) is not the binary's. -/
theorem libtool_old_stderr_ne : (sha256sum libtoolWorld).stderr ≠
    lit "./d/.libs/lt-P: invalid option -- 'x'\n" ++
      lit "Try './d/.libs/lt-P --help' for more information.\n" := by
  rw [libtool_stderr]; decide

/-- `progName` on ordinary names: unchanged. -/
example : progName (lit "sha256sum") = lit "sha256sum" := by decide
example : progName (lit "/usr/bin/sha256sum") = lit "/usr/bin/sha256sum" := by decide
/-- The boundary cases of `base - argv0 >= 7`. -/
example : progName (lit ".libs/lt-P") = lit ".libs/lt-P" := by decide
example : progName (lit "/.libs/P") = lit "P" := by decide
example : progName (lit "x/.libs/lt-") = [] := by decide
example : progName (lit "x/.libs/lt") = lit "lt" := by decide

theorem takeWhile_no_slash : ∀ a : Bytes, 47 ∉ a → a.takeWhile (· != 47) = a
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ 47 := fun e => h (e ▸ List.mem_cons_self)
    have hxs : 47 ∉ xs := fun m => h (List.mem_cons_of_mem _ m)
    simp [hx, takeWhile_no_slash xs hxs]

/-- A name without `/` is unchanged. -/
theorem progName_of_no_slash (a : Bytes) (h : 47 ∉ a) : progName a = a := by
  have base : (a.reverse.takeWhile (· != 47)).reverse = a := by
    rw [takeWhile_no_slash _ (by simpa using h), List.reverse_reverse]
  simp only [progName, base, Nat.sub_self, List.take_zero]
  rfl

end Silmaril.Apps.Sha256sum
