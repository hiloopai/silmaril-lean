module

public import Silmaril.Wasm.Tools.Gen.Cmd.Args.Defs
public import Mathlib.Tactic.SplitIfs

/-!
# The option values: properties the CLI layer relies on

* `parseU64_lt`: an accepted `u64` value is below `2^64`;
* `parseVal_ranged_le`: an accepted ranged value is in range (`--fuel`, `--attempts`, …);
* `parseVal_bool`: a Boolean option accepts exactly `true` and `false`;
* `record_dup`: an option that is not counted cannot be given twice;

The command line of these subcommands is the specification's; `tools/wasm-tools/tests/gen/cli.sh`
tests it against upstream.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Gen.Cmd.Args

theorem foldDigits_lt {cs : List Char} {a n : Nat} (ha : a < 2 ^ 64)
    (h : cs.foldlM (m := Except String) (init := a) (fun acc c =>
      if c.isDigit then
        let v := acc * 10 + (c.toNat - '0'.toNat)
        if v ≥ 2 ^ 64 then .error "number too large to fit in target type" else .ok v
      else .error "invalid digit found in string") = .ok n) : n < 2 ^ 64 := by
  induction cs generalizing a with
  | nil =>
    have : a = n := by simpa [pure, Except.pure] using h
    omega
  | cons c cs ih =>
    simp only [List.foldlM_cons] at h
    split at h
    · split at h
      · simp [bind, Except.bind] at h
      · next hv =>
        exact ih (a := a * 10 + (c.toNat - '0'.toNat)) (by omega)
          (by simpa [bind, Except.bind] using h)
    · simp [bind, Except.bind] at h

set_option linter.unusedTactic false in
theorem parseU64_lt {s : String} {n : Nat} (h : parseU64 s = .ok n) : n < 2 ^ 64 := by
  unfold parseU64 at h
  dsimp only at h
  split_ifs at h <;>
    first
    | exact foldDigits_lt (by decide) h
    | exact foldDigits_lt (by decide) h.symm
    | simp at h

theorem parseVal_ranged_le {o : Opt} {hi : Nat} (hk : o.kind = .ranged hi) {v : String}
    {n : Nat} (h : parseVal o v = .ok (.num n)) : n ≤ hi := by
  unfold parseVal at h
  rw [hk] at h
  simp only at h
  split at h
  · next k _ =>
    split at h
    · next hr =>
      simp only [Except.ok.injEq, Val.num.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      omega
    · cases h
  · cases h

theorem parseVal_bool {o : Opt} (hk : o.kind = .bool) {v : String} {b : Bool}
    (h : parseVal o v = .ok (.bool b)) : v = "true" ∨ v = "false" := by
  unfold parseVal at h
  rw [hk] at h
  simp only at h
  split at h
  · next hv => exact Or.inl (by simpa using hv)
  · split at h
    · next hv => exact Or.inr (by simpa using hv)
    · cases h

theorem record_dup {sp : Spec} {p : Parsed} {o : Opt} {v : Val} (hk : o.kind ≠ .count)
    {w : Val} (hp : p.get? o.long = some w) : ∃ e, record sp p o v = .error e := by
  unfold record
  rw [hp]
  cases h : o.kind with
  | count => exact absurd h hk
  | _ => exact ⟨_, rfl⟩

end Silmaril.Wasm.Tools.Gen.Cmd.Args
