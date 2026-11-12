module

public import Silmaril.Cli.Check.Defs
public import Silmaril.Cli.Behaviour.Thms

/-!
# CLI behaviour: decidable checks decide their specs

PROVED (standard axioms), namespace `Silmaril.Cli`.

* `Recorded.keepsFiles_iff`: the file check is exact (`r.fs i = i.fs`).
* **`Decides`** lemmas: `Check.decides_exits`, `decides_succeeds`, `decides_fails`,
  `decides_stdoutIs`, `decides_stderrIs`, `decides_silent`, `decides_keepsFiles`,
  `decides_consumesAll`, `decides_prints`, `decides_pure`; `Decides.and` (`⊓`), `Decides.or`
  (`⊔`), `Decides.congr` (equal specs).
* **`Decides.orFail`**, **`Decides.orRefused`**: for a spec that fixes stdout (and exit code),
  the allowances are decided by prefix tests. `fixes_pure`, `fixes_prints`.
* `Decides.mem_iff`: a decided spec is decidable on every recorded run (`Decidable`).
-/

@[expose] public section

namespace Silmaril.Cli

/-- An entry of a list of pairs that `lookup` finds. -/
theorem List.exists_of_lookup_eq_some {l : List (FPath × Option Bytes)} {p : FPath}
    {c : Option Bytes} (h : l.lookup p = some c) : ∃ e ∈ l, e.1 = p := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons e l ih =>
    obtain ⟨k, v⟩ := e
    by_cases hp : p = k
    · exact ⟨(k, v), List.mem_cons_self, hp.symm⟩
    · have hb : (p == k) = false := beq_false_of_ne hp
      have h' : l.lookup p = some c := by simpa only [List.lookup, hb] using h
      obtain ⟨e', he', hk⟩ := ih h'
      exact ⟨e', List.mem_cons_of_mem _ he', hk⟩

namespace Recorded

@[simp] theorem toObs_stdout (r : Recorded) (i : Input) : (r.toObs i).stdout = r.stdout := rfl
@[simp] theorem toObs_stderr (r : Recorded) (i : Input) : (r.toObs i).stderr = r.stderr := rfl
@[simp] theorem toObs_exit (r : Recorded) (i : Input) : (r.toObs i).exit = r.exit := rfl
@[simp] theorem toObs_consumed (r : Recorded) (i : Input) : (r.toObs i).consumed = r.consumed := rfl
@[simp] theorem toObs_reads (r : Recorded) (i : Input) : (r.toObs i).reads = r.reads := rfl
@[simp] theorem toObs_fs (r : Recorded) (i : Input) : (r.toObs i).fs = r.fs i := rfl
@[simp] theorem toObs_refused (r : Recorded) (i : Input) : (r.toObs i).refused = r.refused := rfl
@[simp] theorem toObs_log (r : Recorded) (i : Input) : (r.toObs i).log = [] := rfl

/-- **The file check is exact**: no recorded change changes a file iff the files are as
before. -/
theorem keepsFiles_iff (r : Recorded) (i : Input) : Check.keepsFiles i r = true ↔ r.fs i = i.fs := by
  constructor
  · intro h
    have hall : ∀ e ∈ r.changes, r.fs i e.1 = i.fs e.1 := by
      simpa [Check.keepsFiles] using h
    funext p
    cases hl : r.changes.lookup p with
    | none => simp only [Recorded.fs, hl]
    | some c =>
      obtain ⟨e, he, rfl⟩ := List.exists_of_lookup_eq_some hl
      exact hall e he
  · intro h
    simp [Check.keepsFiles, h]

end Recorded

namespace Check

open Spec

theorem Decides.and {c d : Check} {S T : Spec} (hc : c.Decides S) (hd : d.Decides T) :
    (c.and d).Decides (S ⊓ T) := fun i r => by
  simp only [Check.and, Bool.and_eq_true, hc i r, hd i r]; rfl

theorem Decides.or {c d : Check} {S T : Spec} (hc : c.Decides S) (hd : d.Decides T) :
    (c.or d).Decides (S ⊔ T) := fun i r => by
  simp only [Check.or, Bool.or_eq_true, hc i r, hd i r]; rfl

theorem Decides.congr {c : Check} {S T : Spec} (hc : c.Decides S) (h : S = T) : c.Decides T :=
  h ▸ hc

/-- A decided spec is decidable on every recorded run. -/
def Decides.decidable {c : Check} {S : Spec} (hc : c.Decides S) (i : Input) (r : Recorded) :
    Decidable (S i (r.toObs i)) :=
  decidable_of_iff _ (hc i r)

theorem decides_exits (k : ExitCode) : (exits k).Decides (Spec.exits k) := fun _ _ => by
  simp [Check.exits, Spec.exits]

theorem decides_succeeds : succeeds.Decides Spec.succeeds := decides_exits 0

theorem decides_fails : fails.Decides Spec.fails := fun _ _ => by
  simp [Check.fails, Spec.fails]

theorem decides_stdoutIs (f : Input → Bytes) : (stdoutIs f).Decides (Spec.stdoutIs f) :=
  fun _ _ => by simp [Check.stdoutIs, Spec.stdoutIs]

theorem decides_stderrIs (f : Input → Bytes) : (stderrIs f).Decides (Spec.stderrIs f) :=
  fun _ _ => by simp [Check.stderrIs, Spec.stderrIs]

theorem decides_silent : silent.Decides Spec.silent := fun _ _ => by
  simp [Check.silent, Spec.silent]

theorem decides_keepsFiles : keepsFiles.Decides Spec.keepsFiles := fun i r =>
  Recorded.keepsFiles_iff r i

theorem decides_consumesAll : consumesAll.Decides Spec.consumesAll := fun _ _ => by
  simp [Check.consumesAll, Spec.consumesAll]

theorem decides_prints (f : Input → Bytes) : (prints f).Decides (Spec.prints f) := by
  refine ((decides_succeeds.and (decides_stdoutIs f)).and decides_keepsFiles).congr ?_
  funext i o
  exact propext ⟨fun ⟨⟨h0, hs⟩, hf⟩ => ⟨h0, hs, hf⟩, fun ⟨h0, hs, hf⟩ => ⟨⟨h0, hs⟩, hf⟩⟩

theorem decides_pure (f : Input → Spec.Out) : (pure f).Decides (Spec.pure f) := fun i r => by
  simp only [Check.pure, Bool.and_eq_true, decide_eq_true_eq, Recorded.keepsFiles_iff,
    List.isEmpty_iff, Spec.pure, Recorded.toObs_stdout, Recorded.toObs_stderr, Recorded.toObs_exit,
    Recorded.toObs_fs, Recorded.toObs_reads, Recorded.toObs_consumed, Recorded.toObs_log, and_true, and_assoc]

/-! ## Allowances -/

/-- For a spec that fixes stdout, "a prefix of an allowed stdout" is a prefix of `out i`. -/
theorem _root_.Silmaril.Cli.Spec.Fixes.exists_prefix_iff {S : Spec} {out : Input → Bytes} {code : Input → ExitCode}
    (hS : S.Fixes out code) (i : Input) (x : Bytes) :
    (∃ o', S i o' ∧ x <+: o'.stdout) ↔ x <+: out i := by
  constructor
  · rintro ⟨o', ho', hp⟩
    exact (hS i).2 o' ho' |>.1 ▸ hp
  · intro hp
    obtain ⟨o', ho'⟩ := (hS i).1
    exact ⟨o', ho', ((hS i).2 o' ho').1 ▸ hp⟩

theorem fixes_pure (f : Input → Spec.Out) :
    (Spec.pure f).Fixes (fun i => (f i).stdout) (fun i => (f i).exit) := fun i =>
  ⟨⟨(f i).toObs 0 i.fs, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩,
    fun _ ho => ⟨ho.1, ho.2.2.1⟩⟩

theorem fixes_prints (f : Input → Bytes) : (Spec.prints f).Fixes f (fun _ => 0) := fun i =>
  ⟨⟨{ stdout := f i, fs := i.fs }, rfl, rfl, rfl⟩, fun _ ho => ⟨ho.2.1, ho.1⟩⟩

/-- **`orFail` is decided by a prefix test.** -/
theorem Decides.orFail {c : Check} {S : Spec} {out : Input → Bytes} {code : Input → ExitCode}
    (hc : c.Decides S) (hS : S.Fixes out code) : (c.orFail out).Decides (Spec.orFail S) :=
  fun i r => by
    simp only [Check.orFail, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      List.isPrefixOf_iff_prefix, hc i r, Spec.orFail, Recorded.toObs_exit, Recorded.toObs_stdout,
      hS.exists_prefix_iff i]

/-- **`orRefused` is decided by a prefix test.** -/
theorem Decides.orRefused {c : Check} {S : Spec} {out : Input → Bytes}
    {code : Input → ExitCode} (hc : c.Decides S) (hS : S.Fixes out code) :
    (c.orRefused out code).Decides (Spec.orRefused S) := fun i r => by
  have hex : ∀ x (e : ExitCode), (∃ o', S i o' ∧ x <+: o'.stdout ∧ (e = o'.exit ∨ e ≠ 0)) ↔
      x <+: out i ∧ (e = code i ∨ e ≠ 0) := by
    intro x e
    constructor
    · rintro ⟨o', ho', hp, he⟩
      obtain ⟨hs, hx⟩ := (hS i).2 o' ho'
      exact ⟨hs ▸ hp, hx ▸ he⟩
    · rintro ⟨hp, he⟩
      obtain ⟨o', ho'⟩ := (hS i).1
      obtain ⟨hs, hx⟩ := (hS i).2 o' ho'
      exact ⟨o', ho', hs ▸ hp, hx ▸ he⟩
  simp only [Check.orRefused, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.isPrefixOf_iff_prefix, hc i r, Spec.orRefused, Recorded.toObs_refused, Recorded.toObs_exit,
    Recorded.toObs_stdout, hex, and_assoc]

end Check

end Silmaril.Cli
