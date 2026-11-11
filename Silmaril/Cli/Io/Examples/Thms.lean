module

public import Silmaril.Cli.Io.Examples.Defs
public import Silmaril.Cli.Io.Thms
public import Silmaril.Cli.Files.Thms

/-!
# Example CLI programs satisfy their behaviour specifications

* **`echo_sat`**, **`cat_sat`**: through `Prog.sat_ofCore_iff`.
* **`copy_sat`**: `copy` meets the file transformer `copySpec` up to environment refusals
  (`Spec.orRefused`), through `Prog.sat_ofTool_iff`. `copySpec_usage`, `copySpec_unreadable`,
  `copySpec_unwritable`, `copySpec_ok`: what `copySpec` allows in each case.
* `echo_confined`: `echo` stays in its footprint (refinement is transitive with the behaviour
  model's `pure_le_confined`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Io.Examples

open Silmaril.Cli Silmaril.Cli.Io Silmaril.Cli.Spec

/-- **`echo` satisfies its specification.** -/
theorem echo_sat : echoProg.Sat echoSpec :=
  (Prog.sat_ofCore_iff _ _).2 fun i => by
    rw [Result.obs_nil _ _ _ _ _ rfl]
    exact ⟨rfl, rfl, rfl, rfl, rfl, le_refl _, rfl⟩

/-- `echo` reads and writes no file. -/
theorem echo_confined : echoProg.Sat confined :=
  echo_sat.mono (pure_le_confined _)

/-- **`cat` satisfies its specification.** -/
theorem cat_sat : catProg.Sat catSpec :=
  (Prog.sat_ofCore_iff _ _).2 fun i => by
    rw [Result.obs_nil _ _ _ _ _ rfl]
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, le_refl _, rfl⟩, rfl⟩

/-! ## copy -/

/-- The usage message is not empty. -/
theorem copyUsage_ne : copyUsage ≠ [] := by
  decide +kernel

/-- The message for an unreadable source is not empty. -/
theorem copyCannot_ne (src : String) : copyCannot ++ utf8 src ++ utf8 "\n" ≠ [] := by
  have h : copyCannot ≠ [] := by decide +kernel
  simp [h]

/-- A failure with nothing read, written or consumed is a `failure`. -/
theorem failure_of (i : Input) (m : Bytes) (c : ExitCode) (hm : m ≠ []) (hc : c ≠ 0) :
    failure i { stderr := m, exit := c, fs := i.fs } :=
  ⟨hc, hm, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-- A refused run with no output is allowed by `orRefused S` when `S` allows failures here. -/
theorem orRefused_of_refused {S : Spec} {i : Input} {o : Obs} (hS : ∀ o', failure i o' → S i o')
    (hr : o.refused = true) (hx : o.exit ≠ 0) (hout : o.stdout = []) :
    orRefused S i o := by
  have hf : failure i { stderr := [0], exit := 1, fs := i.fs } :=
    failure_of i [0] 1 (List.cons_ne_nil _ _) (by decide)
  refine .inr ⟨hr, _, hS _ hf, ?_, .inr hx⟩
  rw [hout]; exact List.nil_prefix

/-- With no `SRC -o DST`, `copySpec` is a failure. -/
theorem copySpec_usage {i : Input} {o : Obs} (h : copyArgs i.args = none) (hf : failure i o) :
    copySpec i o := by
  simpa [copySpec, transform, h] using hf

/-- With an unreadable source, `copySpec` is a failure. -/
theorem copySpec_unreadable {i : Input} {o : Obs} {src dst : String}
    (h : copyArgs i.args = some (src, dst)) (hs : i.fileAt src = none) (hf : failure i o) :
    copySpec i o := by
  have hq : ∀ q, i.resolve src = some q → i.fs q = none := fun q hq => by
    simpa [Input.fileAt, hq] using hs
  rcases hr : i.resolve src with _ | q
  · simpa [copySpec, transform, h, hr] using hf
  · rcases hd : i.resolve dst with _ | d
    · simpa [copySpec, transform, h, hr, hd] using hf
    · simpa [copySpec, transform, transformAt, Source.read, h, hr, hd, hq q hr] using hf

/-- With a readable source and a destination that cannot be written, `copySpec` is a
failure. -/
theorem copySpec_unwritable {i : Input} {o : Obs} {src dst : String}
    (h : copyArgs i.args = some (src, dst)) (hd : ∀ d, i.resolve dst = some d → ¬ i.Writable d)
    (hf : failure i o) : copySpec i o := by
  rcases hr : i.resolve src with _ | q
  · simpa [copySpec, transform, h, hr] using hf
  · rcases hd' : i.resolve dst with _ | d
    · simpa [copySpec, transform, h, hr, hd'] using hf
    · have hw : ¬ i.Writable d := hd d hd'
      unfold copySpec transform transformAt
      simp only [h, hr, hd', Option.bind_some, Option.map_some]
      split
      · exact hf
      · exact .inr ⟨hw, hf⟩

/-- **The copy** is what `copySpec` allows when `SRC` is a file and `DST` writable. -/
theorem copySpec_ok {i : Input} {src dst : String} {q d : FPath} {b : Bytes}
    (h : copyArgs i.args = some (src, dst)) (hq : i.resolve src = some q) (hb : i.fs q = some b)
    (hd : i.resolve dst = some d) (hw : i.Writable d) :
    copySpec i { reads := [q], fs := i.fs.set d (some b),
                 log := [.read q (some b), .write d (some b)] } := by
  have hr : (Source.file q).read i = some b := by
    simp [Source.read, Input.resolve_under hq, hb]
  have hsp : copySpec i { reads := [q], fs := i.fs.set d (some b),
                          log := [.read q (some b), .write d (some b)] } ↔
      transformAt (.file q) (.file d) (fun x => .ok x) i
        { reads := [q], fs := i.fs.set d (some b),
          log := [.read q (some b), .write d (some b)] } := by
    simp only [copySpec, transform, h, hq, hd, Option.bind_some, Option.map_some]
  refine hsp.2 ?_
  simp only [transformAt, hr]
  exact .inl ⟨hw, by simp [Sink.write, Source.consumed, Source.reads, Source.log, hb]⟩

/-- A string naming a file reads it there. -/
theorem fileAt_some {i : Input} {s : String} {b : Bytes} (h : i.fileAt s = some b) :
    ∃ q, i.resolve s = some q ∧ i.fs q = some b ∧ i.readPath s = some q := by
  obtain ⟨q, hq, hb⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨q, hq, hb, by simp [Input.readPath, hq, hb]⟩

/-- A string naming no file reads nothing. -/
theorem readPath_none {i : Input} {s : String} (h : i.fileAt s = none) : i.readPath s = none := by
  rcases hq : i.resolve s with _ | q
  · simp [Input.readPath, hq]
  · have hb : i.fs q = none := by simpa [Input.fileAt, hq] using h
    simp [Input.readPath, hq, hb]

/-- **`copy` meets its specification up to environment refusals.** -/
theorem copy_sat : copyProg.Sat copySpec.orRefused := by
  refine (Prog.sat_ofTool_iff _ _ _).2 fun i => ?_
  rcases h : copyArgs i.args with _ | ⟨src, dst⟩
  · have ho : (copyCore i.args (Prog.readsOf copyReads i)).obs i 0
        ((copyReads i.args).filterMap i.readPath) ((copyReads i.args).filterMap i.readEv) =
          { stderr := copyUsage, exit := 2, fs := i.fs } := by
      simp [copyCore, copyReads, Prog.readsOf, h]
    rw [ho]
    exact .inl (copySpec_usage h (failure_of i _ _ copyUsage_ne (by decide)))
  · show copySpec.orRefused i _
    rcases hs : i.fileAt src with _ | b
    · have ho : (copyCore i.args (Prog.readsOf copyReads i)).obs i 0
          ((copyReads i.args).filterMap i.readPath) ((copyReads i.args).filterMap i.readEv) =
            { stderr := copyCannot ++ utf8 src ++ utf8 "\n", exit := 1, fs := i.fs } := by
        simp [copyCore, copyReads, Prog.readsOf, h, hs, readPath_none hs, Input.readEv]
      rw [ho]
      exact .inl (copySpec_unreadable h hs (failure_of i _ _ (copyCannot_ne src) (by decide)))
    · show copySpec.orRefused i _
      obtain ⟨q, hq, hb, hp⟩ := fileAt_some hs
      have hcore : copyCore i.args (Prog.readsOf copyReads i) = { files := [(dst, b)] } := by
        simp [copyCore, copyReads, Prog.readsOf, h, hs]
      have hreads : (copyReads i.args).filterMap i.readPath = [q] := by
        simp [copyReads, h, hp]
      have hlog : (copyReads i.args).filterMap i.readEv = [.read q (some b)] := by
        simp [copyReads, h, hp, hb, Input.readEv]
      rw [hcore, hreads, hlog]
      rcases hd : i.resolve dst with _ | d
      · have ho : ({ files := [(dst, b)] } : Result).obs i 0 [q] [.read q (some b)] =
            { reads := [q], refused := true, exit := 1, fs := i.fs,
              log := [.read q (some b)] } := by
          simp [Result.obs, writeAllObs, writeObs, hd]
        rw [ho]
        exact orRefused_of_refused (fun _ hf => copySpec_unwritable h (by simp [hd]) hf) rfl
          (by simp) rfl
      · show copySpec.orRefused i _
        by_cases hw : i.Writable d
        · have ho : ({ files := [(dst, b)] } : Result).obs i 0 [q] [.read q (some b)] =
              { reads := [q], fs := i.fs.set d (some b),
                log := [.read q (some b), .write d (some b)] } := by
            simp [Result.obs, writeAllObs, writeObs, hd, hw]
          rw [ho]
          exact .inl (copySpec_ok h hq hb hd hw)
        · have ho : ({ files := [(dst, b)] } : Result).obs i 0 [q] [.read q (some b)] =
              { reads := [q], refused := true, exit := 1, fs := i.fs,
                log := [.read q (some b)] } := by
            simp [Result.obs, writeAllObs, writeObs, hd, hw]
          rw [ho]
          exact orRefused_of_refused
            (fun _ hf => copySpec_unwritable h (fun d' hd' => by simp_all) hf) rfl
            (by simp) rfl

end Silmaril.Cli.Io.Examples

end
