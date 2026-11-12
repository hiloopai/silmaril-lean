module

public import Silmaril.Cli.Io.Check.Defs
public import Silmaril.Cli.Io.Examples.Thms

/-!
# The checks of the example programs are sound

**`echoCheck_sound`**, **`catCheck_sound`**, **`copyCheck_sound`**: a snapshot the check passes
is shown by an observation `echoSpec`, `catSpec`, `copySpec` allows. With `echo_sat`, `cat_sat`
and `copy_sat`, a harness run of a binary built from the program that passes is consistent with the proved
program, and a run of another binary (e.g. a WASI component) that passes is a run the same
specification allows, as far as the harness sees.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io.Examples

open Silmaril.Cli Silmaril.Cli.Io Silmaril.Cli.Spec

/-- No changed file: the harness sees the input's files. -/
theorem Snap.fs_nil {s : Snap} (i : Input) (h : s.files = []) : s.fs i = i.fs := by
  funext q
  simp [Snap.fs, h]

/-- The changed files `copyFiles` are the input's files with `d` set. -/
theorem Snap.fs_copyFiles {s : Snap} (i : Input) {d : FPath} {b : Bytes} (hd : d.root = ".")
    (h : s.files = copyFiles i d b) : s.fs i = i.fs.set d (some b) := by
  funext q
  by_cases hq : q = d
  · subst hq
    by_cases hb : i.fs q = some b <;> simp [Snap.fs, h, copyFiles, hd, hb, Fs.set]
  · by_cases hr : q.root = "."
    · have hrel : (q.rel == d.rel) = false := by
        simpa using fun he : q.rel = d.rel => hq (by cases q; cases d; simp_all)
      by_cases hb : i.fs d = some b <;> simp [Snap.fs, h, copyFiles, hb, hr, Fs.set, hq,
        List.lookup, hrel]
    · simp [Snap.fs, hr, Fs.set, hq]

/-- **`echoCheck` is sound for `echoSpec`.** -/
theorem echoCheck_sound : echoCheck.Sound echoSpec := by
  intro i s h
  simp only [echoCheck, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hx, ho⟩, he⟩, hf⟩ := h
  exact ⟨{ stdout := echoOut i.args, fs := i.fs }, ⟨ho.symm, he.symm, hx.symm,
    (Snap.fs_nil i hf).symm⟩, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-- **`catCheck` is sound for `catSpec`.** -/
theorem catCheck_sound : catCheck.Sound catSpec := by
  intro i s h
  simp only [catCheck, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨hx, ho⟩, he⟩, hf⟩ := h
  exact ⟨{ stdout := i.stdin, consumed := i.stdin.length, fs := i.fs }, ⟨ho.symm, he.symm,
    hx.symm, (Snap.fs_nil i hf).symm⟩, ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, rfl⟩, rfl⟩

/-- A failing snapshot is shown by a `failure`. -/
theorem failure_of_snap (i : Input) {s : Snap} (hx : s.exit ≠ 0) (he : s.stderr ≠ [])
    (ho : s.stdout = []) (hf : s.files = []) :
    s.Agrees i { stdout := s.stdout, stderr := s.stderr, exit := s.exit, fs := i.fs } ∧
      failure i { stdout := s.stdout, stderr := s.stderr, exit := s.exit, fs := i.fs } :=
  ⟨⟨rfl, rfl, rfl, (Snap.fs_nil i hf).symm⟩, hx, he, ho, rfl, rfl, Nat.zero_le _, rfl⟩

/-- **`copyCheck` is sound for `copySpec`.** -/
theorem copyCheck_sound : copyCheck.Sound copySpec := by
  intro i s h
  simp only [copyCheck, Bool.and_eq_true, List.isEmpty_iff] at h
  obtain ⟨ho, hm⟩ := h
  rcases ha : copyArgs i.args with _ | ⟨src, dst⟩
  · have hm' : (s.exit != 0 && !s.stderr.isEmpty && s.files.isEmpty) = true := by
      simpa [ha] using hm
    have hx : s.exit ≠ 0 ∧ s.stderr ≠ [] ∧ s.files = [] := by simpa [and_assoc] using hm'
    obtain ⟨hag, hfl⟩ := failure_of_snap i hx.1 hx.2.1 ho hx.2.2
    exact ⟨_, hag, copySpec_usage ha hfl⟩
  · show ∃ o, s.Agrees i o ∧ copySpec i o
    rcases hs : i.fileAt src with _ | b
    · have hm' : (s.exit != 0 && !s.stderr.isEmpty && s.files.isEmpty) = true := by
        simpa [ha, hs] using hm
      have hx : s.exit ≠ 0 ∧ s.stderr ≠ [] ∧ s.files = [] := by simpa [and_assoc] using hm'
      obtain ⟨hag, hfl⟩ := failure_of_snap i hx.1 hx.2.1 ho hx.2.2
      exact ⟨_, hag, copySpec_unreadable ha hs hfl⟩
    · show ∃ o, s.Agrees i o ∧ copySpec i o
      rcases hd : i.resolve dst with _ | d
      · simp [ha, hs, hd] at hm
      · have hc : d.root = "." ∧ i.Writable d ∧ s.exit = 0 ∧ s.stderr = [] ∧
            s.files = copyFiles i d b := by
          simpa [ha, hs, hd, and_assoc] using hm
        obtain ⟨q, hq, hb, -⟩ := fileAt_some hs
        refine ⟨{ reads := [q], fs := i.fs.set d (some b),
                  log := [.read q (some b), .write d (some b)] }, ⟨ho.symm, hc.2.2.2.1.symm,
          hc.2.2.1.symm, (Snap.fs_copyFiles i hc.1 hc.2.2.2.2).symm⟩, ?_⟩
        exact copySpec_ok ha hq hb hd hc.2.1

end Silmaril.Cli.Io.Examples

end
