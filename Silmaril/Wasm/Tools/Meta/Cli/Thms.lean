module

public import Silmaril.Wasm.Tools.Meta.Cli.Defs

/-!
# The argument grammar: properties of `parseArgs`

* `parseArgs_help`: `--help` first is the long help; `parseArgs_h`: `-h` first is the short
  help (whatever follows, as clap stops at a help flag).
* `parseArgs_positional`: arguments that are not option-like give no options and the
  positional argument (at most one).
* `parseArgs_two_positional`: a second positional argument is the "unexpected argument" error
  (for a command without a repeated positional argument).
* `parseArgs_no_conflict`: **a successful parse has no conflicting pair** among the arguments
  given (`firstConflict` finds none).
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Cli

/-- `--help` first: the long help. -/
theorem parseArgs_help (c : Cmd) (rest : List String) :
    parseArgs c ("--help" :: rest) = .ok (.usage true) := by
  simp [parseArgs, parseGo, step, flagLike]

/-- `-h` first: the short help. -/
theorem parseArgs_h (c : Cmd) (rest : List String) :
    parseArgs c ("-h" :: rest) = .ok (.usage false) := by
  simp [parseArgs, parseGo, step, flagLike, dropS, shorts]

/-- Arguments that do not look like options, at most one: the positional argument and no
options. -/
theorem parseArgs_positional (c : Cmd) (a : String) (ha : flagLike a = false) :
    parseArgs c [a] = .ok (.ok [] (some a)) ∧ parseArgs c [] = .ok (.ok [] none) := by
  constructor
  · simp [parseArgs, parseGo, step, ha, firstConflict]
  · simp [parseArgs, parseGo, firstConflict]

/-- A second positional argument is refused (by a command without a repeated positional
argument). -/
theorem parseArgs_two_positional (c : Cmd) (a b : String) (ha : flagLike a = false)
    (hb : flagLike b = false) (hc : c.rest = none) :
    parseArgs c [a, b] = .error (errPositional c b) := by
  simp [parseArgs, parseGo, step, ha, hb, hc]

/-- The parser loop only succeeds with arguments through its last step, where the
conflict check passes. -/
theorem parseGo_no_conflict (c : Cmd) : ∀ (f : Nat) (st : St) (args : List String)
    (seen : List (String × Option String)) (input : Option String),
    parseGo c f st args = .ok (.ok seen input) → firstConflict c (seen.map (·.1)) = none
  | _, st, [], seen, input, h => by
    unfold parseGo at h
    simp only at h
    split at h
    · cases h
    · rename_i hc
      simp only [Except.ok.injEq, Parsed.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | 0, _, _ :: _, _, _, h => by simp [parseGo] at h
  | f + 1, st, a :: rest, seen, input, h => by
    unfold parseGo at h
    split at h
    · exact parseGo_no_conflict c f _ _ seen input h
    · simp at h
    · cases h

/-- **A successful parse has no two conflicting arguments.** -/
theorem parseArgs_no_conflict {c : Cmd} {args : List String}
    {seen : List (String × Option String)} {input : Option String}
    (h : parseArgs c args = .ok (.ok seen input)) : firstConflict c (seen.map (·.1)) = none :=
  parseGo_no_conflict c _ _ _ seen input h

end Silmaril.Wasm.Tools.Meta.Cli

end
