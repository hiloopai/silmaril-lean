module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Proofs.Cli.Args.Scan

@[expose] public section

/-!
# Proofs: help is complete, and what it shows parses

* `helpLines_opt`, `helpLines_pos`, `helpLines_sub`, `helpLines_exit`, `helpLines_usage`: every
  option, positional, subcommand and documented exit code of a command has a line of its help
  (the help is a function of the grammar, so it cannot drift);
* `synopsis_long`, `synopsis_short`: every name the help shows for an option parses as that
  option, in a well-formed grammar;
* `synopsis_no`: a negatable flag's `--no-` name parses as its negation;
* `interpret_scan_error`, `interpret_help`, `interpret_version`: the front end's usage errors
  exit 2, help and version exit 0;
* `scan_errorText`: **per-subcommand usage**: the text of a parse error shows the usage line of
  the subcommand where the error was found (`scan_error_walk`).

A Silmaril addition.
-/

namespace Silmaril.Cli

theorem helpTable_mem {rows : List (String × String)} {r : String × String} (hr : r ∈ rows) :
    ∃ tail, "  " ++ r.1 ++ tail ∈ helpTable rows :=
  ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩⟩

theorem helpSection_mem {title : String} {rows : List (String × String)} {r : String × String}
    (hr : r ∈ rows) : ∃ tail, "  " ++ r.1 ++ tail ∈ helpSection title rows := by
  obtain ⟨tail, ht⟩ := helpTable_mem hr
  have hne : rows.isEmpty = false := by
    cases rows with
    | nil => exact absurd hr List.not_mem_nil
    | cons _ _ => rfl
  exact ⟨tail, by simp [helpSection, hne, ht]⟩

theorem helpLines_usage (c : Command) (path : List String) : c.usage path ∈ c.helpLines path := by
  simp [Command.helpLines]

/-- Every option has a help line starting with its synopsis. -/
theorem helpLines_opt {c : Command} {o : Opt} (ho : o ∈ c.opts) (path : List String) :
    ∃ tail, "  " ++ o.synopsis ++ tail ∈ c.helpLines path := by
  obtain ⟨tail, ht⟩ := helpSection_mem (title := "Options:")
    (List.mem_map.mpr ⟨o, ho, rfl⟩ : (o.synopsis, o.helpText) ∈ c.opts.map fun o => (o.synopsis, o.helpText))
  exact ⟨tail, by simp only [Command.helpLines, List.mem_append]; exact .inl (.inr ht)⟩

/-- Every positional has a help line starting with its synopsis. -/
theorem helpLines_pos {c : Command} {p : Pos} (hp : p ∈ c.pos) (path : List String) :
    ∃ tail, "  " ++ p.synopsis ++ tail ∈ c.helpLines path := by
  obtain ⟨tail, ht⟩ := helpSection_mem (title := "Arguments:")
    (List.mem_map.mpr ⟨p, hp, rfl⟩ : (p.synopsis, p.help) ∈ c.pos.map fun p => (p.synopsis, p.help))
  exact ⟨tail, by simp only [Command.helpLines, List.mem_append]; exact .inl (.inl (.inr ht))⟩

/-- Every subcommand has a help line starting with its name. -/
theorem helpLines_sub {c s : Command} (hs : s ∈ c.subs) (path : List String) :
    ∃ tail, "  " ++ s.name ++ tail ∈ c.helpLines path := by
  obtain ⟨tail, ht⟩ := helpSection_mem (title := "Commands:")
    (List.mem_map.mpr ⟨s, hs, rfl⟩ : (s.name, s.about) ∈ c.subs.map fun s => (s.name, s.about))
  exact ⟨tail, by
    simp only [Command.helpLines, List.mem_append]; exact .inl (.inl (.inl (.inr ht)))⟩

/-- Every documented exit code has a help line. -/
theorem helpLines_exit {c : Command} {e : Nat × String} (he : e ∈ c.exits) (path : List String) :
    ∃ tail, "  " ++ toString e.1 ++ tail ∈ c.helpLines path := by
  obtain ⟨tail, ht⟩ := helpSection_mem (title := "Exit status:")
    (List.mem_map.mpr ⟨e, he, rfl⟩ : (toString e.1, e.2) ∈ c.exits.map fun e => (toString e.1, e.2))
  exact ⟨tail, by simp only [Command.helpLines, List.mem_append]; exact .inr ht⟩

/-- A long name shown in help parses as its option. -/
theorem synopsis_long {c : Command} (hwf : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) {n : String}
    (hn : n ∈ o.long) : classify ("--" ++ n) = .long n none ∧ findLong c.opts n = some o :=
  ⟨classify_long ((hwf.opt ho).2.1 n hn), (findLong_eq_some_iff hwf).mpr ⟨ho, hn⟩⟩

/-- A single-dash name shown in help parses as its option (exactly, before any cluster). -/
theorem synopsis_short {c : Command} (hwf : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) {n : String}
    (hn : n ∈ o.short) : classify ("-" ++ n) = .short n ∧ findShort c.opts n = some o :=
  ⟨classify_short ((hwf.opt ho).2.2.1 n hn), (findShort_eq_some_iff hwf).mpr ⟨ho, hn⟩⟩

/-- The `--no-` name of a negatable flag reads as its negation. -/
theorem synopsis_no {c : Command} (hwf : c.LocalWF) {o : Opt} (ho : o ∈ c.opts)
    (hneg : o.negatable = true) (y : Option String) :
    readOpt c.opts ("--no-" ++ o.long.headD o.id) y = .ok ([(o.id, .off)], false) := by
  have hw := (hwf.opt ho).2.2.2.2 hneg
  exact readOpt_off hwf ho (by simp [Opt.accepts, hneg, hw.1]) y

/-- A command line that does not parse is a usage error: exit code 2, text on stderr. -/
theorem interpret_scan_error {c : Command} {env : String → Option String} {argv : List String}
    {p : List String} {e : ArgError} (h : scan c argv = .error (p, e)) :
    interpret c env argv = .error (c.name :: p) e ∧
      (interpret c env argv).exitCode? = some 2 ∧
      (interpret c env argv).text c = some (.stderr, errorText c (c.name :: p) e) := by
  have hi : interpret c env argv = .error (c.name :: p) e := by
    simp [interpret, h, Outcome.ofLocated]
  simp [hi, Outcome.exitCode?, Outcome.text]

/-- **Per-subcommand usage**: a parse error found below the subcommand path `p` prints the usage
line of the command at `p`. -/
theorem scan_errorText {c : Command} (hwf : c.Good) {argv : List String} {p : List String}
    {e : ArgError} (h : scan c argv = .error (p, e)) :
    ∃ d, c.walk p = some d ∧ errorText c (c.name :: p) e =
      "error: " ++ e.message ++ "\n\n" ++ d.usage (c.name :: p) ++
        "\n\nFor more information, try '--help'." := by
  obtain ⟨d, hd⟩ := scan_error_walk hwf h
  exact ⟨d, hd, by simp [errorText, Command.at, hd]⟩

/-- A command line asking for help prints it on stdout and exits 0. -/
theorem interpret_help {c : Command} {env : String → Option String} {argv : List String}
    {fs : Invocation} {p : List String} (h : scan c argv = .ok fs) (hp : helpPath fs [] = some p) :
    interpret c env argv = .help p ∧ (interpret c env argv).exitCode? = some 0 ∧
      (interpret c env argv).text c = some (.stdout, (c.at p).help p) := by
  have hi : interpret c env argv = .help p := by simp [interpret, h, hp]
  simp [hi, Outcome.exitCode?, Outcome.text]

/-- A command line asking for the version prints it on stdout and exits 0. -/
theorem interpret_version {c : Command} {env : String → Option String} {argv : List String}
    {f : Frame} {rest : Invocation} {v : String} (h : scan c argv = .ok (f :: rest))
    (hp : helpPath (f :: rest) [] = none) (hv : c.version = some v)
    (hf : f.opts.any (·.1 == "version") = true) :
    interpret c env argv = .version v ∧ (interpret c env argv).exitCode? = some 0 := by
  have hi : interpret c env argv = .version v := by simp [interpret, h, hp, hv, hf]
  simp [hi, Outcome.exitCode?]

end Silmaril.Cli
