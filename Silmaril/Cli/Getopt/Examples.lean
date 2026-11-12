module

public import Silmaril.Cli.Getopt.Thms
public import Silmaril.Cli.Getopt.Front.Thms
public import Silmaril.Cli.Getopt.Stream.Thms
public meta import Silmaril.Cli.Getopt.Front.Defs
public meta import Silmaril.Cli.Getopt.Stream.Defs

/-!
# The getopt dialect: real option tables

Option tables of a few standard tools, as args grammars read by getopt, checked by evaluation
(`#guard`) against the behaviour POSIX specifies for them and GNU documents for its versions.
Each grammar is a subset of the tool's options; the tables are derived (`Table.ofCommand`).

* `head`: `-n NUM` with an attached or separate argument; GNU permutes (`head f -n 3` reads `-n
  3`), POSIX order (a set `POSIXLY_CORRECT`, or POSIX getopt) makes `-n` and `3` file names;
* `wc`: clusters of flags (`-lwc`);
* `grep`: a repeatable `-e PATTERN` whose argument may start with `-`, an optional argument
  given only attached (`--color[=WHEN]`), two long names of one option (`--color`, `--colour`),
  unambiguous and ambiguous prefixes;
* `sort`: `-k KEYDEF` repeated, `-t SEP` where the separator is any character, even `=`;
* `cut`: `-d DELIM` and `-f LIST`, attached or separate, in any order.
-/

public section

namespace Silmaril.Cli.Getopt.Examples

open Silmaril.Cli

/-- The environment without variables. -/
def noEnv : String → Option String := fun _ => none

/-- An environment with `POSIXLY_CORRECT` set (its value does not matter). -/
def posixEnv : String → Option String := fun v => if v == "POSIXLY_CORRECT" then some "" else none

/-- The matches of a run. -/
def runs? : Outcome → Option Matches
  | .run m => some m
  | _ => none

/-- The options and the operands of a getopt reading. -/
def split (e : Except Error Parsed) : Option (List (String × Given) × List String) :=
  e.toOption.map fun p => (p.opts, p.operands)

/-- Whether the outcome is a usage error. -/
def isUsageError : Outcome → Bool
  | .error _ _ => true
  | _ => false

/-- GNU's `--help`: a long name only. -/
def gnuHelp : Opt := { id := "help", long := ["help"] }

/-- GNU's `--version`: a long name only. -/
def gnuVersion : Opt := { id := "version", long := ["version"] }

/-! ## head -/

/-- GNU `head`: `-n, --lines=[-]NUM`, `-c, --bytes=[-]NUM`, `-q, --quiet, --silent`,
`-v, --verbose`, `-z, --zero-terminated`, then files (none, or `-`: standard input). The counts
are strings: a leading `-` and size suffixes are the program's business. -/
def headCmd : Command where
  name := "head"
  opts := [{ id := "lines", long := ["lines"], short := ["n"], arg := some .str },
           { id := "bytes", long := ["bytes"], short := ["c"], arg := some .str },
           { id := "quiet", long := ["quiet", "silent"], short := ["q"], repeated := true },
           { id := "verbose", long := ["verbose"], short := ["v"], repeated := true },
           { id := "zero", long := ["zero-terminated"], short := ["z"] },
           gnuHelp, { gnuVersion with }]
  pos := [{ id := "file", arity := .many }]
  version := some "9.4"

/-- GNU `head` (getopt_long, permuting). -/
def head : Tool := { grammar := headCmd }

/-- POSIX `head`: `-n number` only, POSIX getopt. -/
def posixHead : Tool where
  grammar := { name := "head",
               opts := [{ id := "n", long := [], short := ["n"], arg := some .nat }],
               pos := [{ id := "file", arity := .many }] }
  gnu := false

#guard Fits headCmd
#guard head.table.optstring == "n:c:qvz"
#guard (head.table.longs.map (·.name)) ==
  ["lines", "bytes", "quiet", "silent", "verbose", "zero-terminated", "help", "version"]
#guard posixHead.table.optstring == "n:"

-- `-n5`, `-n 5` and `--lines=5`, `--lines 5` give the same occurrence.
#guard (head.parse noEnv ["-n5", "a.txt"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard (head.parse noEnv ["-n", "5", "a.txt"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard (head.parse noEnv ["--lines=5"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard (head.parse noEnv ["--lines", "5"]).toOption.map (·.opts) == some [("lines", .val "5")]
-- The argument is the next token verbatim, even when it starts with `-`.
#guard (head.parse noEnv ["-n", "-5"]).toOption.map (·.opts) == some [("lines", .val "-5")]
-- A unique prefix of a long name: getopt_long resolves it, the pre-pass flags it.
#guard (head.parse noEnv ["--li=5"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard head.pre noEnv ["--li=5"] == some (.abbrev "--li=5" "lines")
-- `--quiet` and `--silent` are the same option.
#guard (head.parse noEnv ["--q", "--si"]).toOption.map (·.opts) ==
  some [("quiet", .on), ("quiet", .on)]

-- GNU permutes: an option after a file is an option.
#guard head.order noEnv == .permute
#guard split (head.parse noEnv ["a.txt", "-n", "3", "b.txt"]) ==
  some ([("lines", .val "3")], ["a.txt", "b.txt"])
-- With `POSIXLY_CORRECT` set, the first file ends the options: `-n` and `3` are files.
#guard head.order posixEnv == .requireOrder
#guard split (head.parse posixEnv ["a.txt", "-n", "3"]) ==
  some ([], ["a.txt", "-n", "3"])
#guard head.pre posixEnv ["a.txt", "-n", "3"] == some (.afterOperand "-n")
-- POSIX getopt never permutes, whatever the environment.
#guard posixHead.order noEnv == .requireOrder
#guard split (posixHead.parse noEnv ["-n", "3", "a", "-n", "4"]) ==
  some ([("n", .val "3")], ["a", "-n", "4"])
-- `--` ends the options; `-` is a file (standard input by convention).
#guard (head.parse noEnv ["--", "-n"]).toOption.map (·.operands) == some ["-n"]
#guard split (head.parse noEnv ["-", "-n2"]) ==
  some ([("lines", .val "2")], ["-"])
-- The permuted argument vector.
#guard (head.parse noEnv ["a", "-n", "3", "--", "-v"]).toOption.map Parsed.permuted ==
  some ["-n", "3", "--", "a", "-v"]

/-- `head a.txt -n 3` with `POSIXLY_CORRECT` set in its environment. -/
def posixInput : Input := { args := ["a.txt", "-n", "3"], env := [("POSIXLY_CORRECT", "1")] }

-- On a full invocation the environment comes from the invocation itself.
#guard (runs? (head.outcome { args := ["a.txt", "-n", "3"] })).map (·.strs "file") == some ["a.txt"]
#guard (runs? (head.outcome posixInput)).map (·.strs "file") == some ["a.txt", "-n", "3"]
#guard head.envVars == ["POSIXLY_CORRECT"]

-- The whole reading: the args checks run on what getopt read.
#guard (runs? (head.read noEnv ["a.txt", "-n", "3"])).map (·.strs "lines") == some ["3"]
#guard (runs? (head.read noEnv ["a.txt", "-n", "3"])).map (·.strs "file") == some ["a.txt"]
#guard (runs? (head.read posixEnv ["a.txt", "-n", "3"])).map (·.strs "file") ==
  some ["a.txt", "-n", "3"]
#guard head.read noEnv ["--help"] == .help ["head"]
#guard head.read noEnv ["--vers"] == .version "9.4"
-- Usage errors: a missing argument, an unknown option, an argument to a flag.
#guard head.read noEnv ["-n"] == .error ["head"] (.missingValue "-n")
#guard head.read noEnv ["-x"] == .error ["head"] (.unknownOption "-x")
#guard head.read noEnv ["--quiet=yes"] == .error ["head"] (.unexpectedValue "--quiet=yes")
/-- `head` with `W;` in the optstring: `-W lines=5` means `--lines=5`. -/
def headW : Tool := { head with wLong := true }

#guard (headW.parse noEnv ["-W", "lines=5"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard (headW.parse noEnv ["-Wlines=5"]).toOption.map (·.opts) == some [("lines", .val "5")]
#guard headW.table.optstring == "n:c:qvzW;"
-- `-Wlines 5`: a required argument in the next token.
#guard split (headW.parse noEnv ["-Wlines", "5", "f"]) == some ([("lines", .val "5")], ["f"])
-- `-W lines 5`: the model gives `-W name` no further token (an error here).
#guard (headW.parse noEnv ["-W", "lines", "5"]) matches .error (.missing "-W")

/-! ## wc -/

/-- `wc`: `-c` bytes, `-m` characters, `-l` lines, `-w` words (GNU: also long names). -/
def wcCmd : Command where
  name := "wc"
  opts := [{ id := "bytes", long := ["bytes"], short := ["c"] },
           { id := "chars", long := ["chars"], short := ["m"] },
           { id := "lines", long := ["lines"], short := ["l"] },
           { id := "words", long := ["words"], short := ["w"] }]
  pos := [{ id := "file", arity := .many }]

/-- GNU `wc`. -/
def wc : Tool := { grammar := wcCmd }

#guard wc.table.optstring == "cmlw"
-- A cluster is its characters in order.
#guard split (wc.parse noEnv ["-lwc", "f"]) ==
  some ([("lines", .on), ("words", .on), ("bytes", .on)], ["f"])
#guard (runs? (wc.read noEnv ["-lw", "f"])).map
    (fun m => (m.flag "lines", m.flag "words", m.flag "bytes")) ==
  some (true, true, false)
-- An unknown character anywhere in a cluster is an error.
#guard wc.read noEnv ["-lx"] == .error ["wc"] (.unknownOption "-lx")

/-! ## grep -/

/-- GNU `grep` (a subset): `-e, --regexp=PATTERNS` (repeatable), `-F, --fixed-strings`,
`-i, --ignore-case`, `-v, --invert-match`, `--color[=WHEN]` and `--colour[=WHEN]` (an optional
argument: `never`, `always` or `auto`), `--include=GLOB` (repeatable), then patterns and files. -/
def grepCmd : Command where
  name := "grep"
  opts := [{ id := "regexp", long := ["regexp"], short := ["e"], arg := some .str,
             repeated := true },
           { id := "fixed", long := ["fixed-strings"], short := ["F"] },
           { id := "icase", long := ["ignore-case"], short := ["i"] },
           { id := "invert", long := ["invert-match"], short := ["v"] },
           { id := "color", long := ["color", "colour"],
             arg := some (.enum ["never", "always", "auto"]), valueOptional := true },
           { id := "include", long := ["include"], arg := some .str, repeated := true }]
  pos := [{ id := "args", arity := .many }]

/-- GNU `grep`. -/
def grep : Tool := { grammar := grepCmd }

#guard Fits grepCmd
#guard grep.table.optstring == "e:Fiv"
-- `-e` takes the next token, even `-v`: a pattern that starts with `-`.
#guard split (grep.parse noEnv ["-e", "-v", "f"]) ==
  some ([("regexp", .val "-v")], ["f"])
#guard (grep.parse noEnv ["-ivF", "x"]).toOption.map (·.opts) ==
  some [("icase", .on), ("invert", .on), ("fixed", .on)]
-- An optional argument is given only attached: `--color always` is a bare `--color` and an
-- operand `always`.
#guard (grep.parse noEnv ["--color=always", "x"]).toOption.map (·.opts) ==
  some [("color", .val "always")]
#guard split (grep.parse noEnv ["--color", "always", "x"]) ==
  some ([("color", .on)], ["always", "x"])
-- `--col` is a prefix of `--color` and `--colour`, which are one option: not ambiguous.
#guard (grep.parse noEnv ["--col=auto"]).toOption.map (·.opts) == some [("color", .val "auto")]
-- `--in` is a prefix of `--invert-match` and `--include`: ambiguous.
#guard (grep.parse noEnv ["--in"]) matches .error (.ambiguous "--in" ["invert-match", "include"])
#guard isUsageError (grep.read noEnv ["--in", "x"])
-- The value of `--color` is checked by the args front end.
#guard isUsageError (grep.read noEnv ["--color=sometimes", "x"])
#guard (runs? (grep.read noEnv ["-e", "a", "-e", "b", "f"])).map (·.strs "regexp") ==
  some ["a", "b"]

/-! ## sort -/

/-- `sort` (a subset): `-k, --key=KEYDEF` (repeatable), `-t, --field-separator=SEP`,
`-n, --numeric-sort`, `-r, --reverse`, then files. -/
def sortCmd : Command where
  name := "sort"
  opts := [{ id := "key", long := ["key"], short := ["k"], arg := some .str, repeated := true },
           { id := "sep", long := ["field-separator"], short := ["t"], arg := some .str },
           { id := "numeric", long := ["numeric-sort"], short := ["n"] },
           { id := "reverse", long := ["reverse"], short := ["r"] }]
  pos := [{ id := "file", arity := .many }]

/-- GNU `sort`. -/
def sort : Tool := { grammar := sortCmd }

#guard (sort.parse noEnv ["-k", "2,2", "-t:", "f"]).toOption.map (·.opts) ==
  some [("key", .val "2,2"), ("sep", .val ":")]
#guard (sort.parse noEnv ["-nrk2n"]).toOption.map (·.opts) ==
  some [("numeric", .on), ("reverse", .on), ("key", .val "2n")]
-- `-t=`: the separator is `=` for getopt; the args dialect would read `-t=x` as `x`, so the
-- pre-pass flags it.
#guard (sort.parse noEnv ["-t=", "f"]).toOption.map (·.opts) == some [("sep", .val "=")]
#guard sort.pre noEnv ["-t=", "f"] == some (.attachedEq "-t=")
#guard (runs? (sort.read noEnv ["-t=", "f"])).map (·.str? "sep") == some (some "=")

/-! ## cut -/

/-- `cut` (a subset): `-b, --bytes=LIST`, `-c, --characters=LIST`, `-d, --delimiter=DELIM`,
`-f, --fields=LIST`, `-s, --only-delimited`, then files. -/
def cutCmd : Command where
  name := "cut"
  opts := [{ id := "bytes", long := ["bytes"], short := ["b"], arg := some .str },
           { id := "chars", long := ["characters"], short := ["c"], arg := some .str },
           { id := "delim", long := ["delimiter"], short := ["d"], arg := some .str },
           { id := "fields", long := ["fields"], short := ["f"], arg := some .str },
           { id := "only", long := ["only-delimited"], short := ["s"] }]
  pos := [{ id := "file", arity := .many }]

/-- GNU `cut`. -/
def cut : Tool := { grammar := cutCmd }

#guard cut.table.optstring == "b:c:d:f:s"
#guard (runs? (cut.read noEnv ["-d,", "-f1,3", "f"])).map
    (fun m => (m.str? "delim", m.str? "fields")) ==
  some (some ",", some "1,3")
#guard (runs? (cut.read noEnv ["-f", "2", "-d", " ", "f"])).map
    (fun m => (m.str? "delim", m.str? "fields")) ==
  some (some " ", some "2")
#guard (runs? (cut.read noEnv ["f", "-sf2"])).map (fun m => (m.flag "only", m.strs "file")) ==
  some (true, ["f"])

/-! ## Optstrings -/

#guard (Table.ofOptstring "+n:c:qv").optstring == "+n:c:qv"
#guard (Table.ofOptstring "ab::W;c").shorts ==
  [⟨'a', .none, "a"⟩, ⟨'b', .optional, "b"⟩, ⟨'c', .none, "c"⟩]
#guard (Table.ofOptstring "ab::W;c").wLong
-- An optional argument is only attached.
#guard split (parse (Table.ofOptstring "ab::") .permute ["-ab", "x"]) ==
  some ([("a", .on), ("b", .on)], ["x"])
#guard (parse (Table.ofOptstring "ab::") .permute ["-abx"]).toOption.map (·.opts) ==
  some [("a", .on), ("b", .val "x")]

/-! ## getopt_long_only -/

/-- An optstring `ab:` with long options `all` and `bytes=`, read by `getopt_long_only`. -/
def longOnly : Table :=
  { Table.ofOptstring "ab:" [{ name := "all" }, { name := "bytes", arg := .required }] with
    longOnly := true }

-- A single dash names a long option, prefixes included.
#guard (parse longOnly .permute ["-all"]).toOption.map (·.opts) == some [("all", .on)]
#guard (parse longOnly .permute ["-al"]).toOption.map (·.opts) == some [("all", .on)]
#guard (parse longOnly .permute ["-by", "3"]).toOption.map (·.opts) == some [("bytes", .val "3")]
#guard (parse longOnly .permute ["-bytes=3"]).toOption.map (·.opts) == some [("bytes", .val "3")]
-- One optstring character stays a short option, though `-a` is a prefix of `-all`.
#guard (parse longOnly .permute ["-a"]).toOption.map (·.opts) == some [("a", .on)]
-- No long name has the prefix: the token is a cluster.
#guard (parse longOnly .permute ["-ab5"]).toOption.map (·.opts) ==
  some [("a", .on), ("b", .val "5")]
#guard (parse longOnly .permute ["-x"]) matches .error (.unknown "-x")
-- `--` long names read as with getopt_long.
#guard (parse longOnly .permute ["--al"]).toOption.map (·.opts) == some [("all", .on)]

/-! ## Going on after errors -/

-- getopt reports `-x` and goes on with the rest of the cluster and the next tokens.
#guard (wc.parseAll noEnv ["-xl", "--bogus", "-w", "f"]).events ==
  [.error (.unknown "-xl"), .opt "lines" .on, .error (.unknown "--bogus"), .opt "words" .on]
#guard (wc.parseAll noEnv ["-xl", "--bogus", "-w", "f"]).opts == [("lines", .on), ("words", .on)]
#guard (wc.parseAll noEnv ["-xl", "--bogus", "-w", "f"]).operands == ["f"]
-- The first diagnostic is where `parse` stops.
#guard (wc.parse noEnv ["-xl", "--bogus", "-w", "f"]) matches .error (.unknown "-xl")
-- A missing argument at the end.
#guard (head.parseAll noEnv ["-v", "-n"]).events == [.opt "verbose" .on, .error (.missing "-n")]

/-! ## Operands in order -/

-- With an optstring starting with `-`, operands come back in place (`-` among them); only the
-- tokens after `--` stay operands.
#guard (head.parseInOrder ["a", "-n", "3", "-", "--", "-v"]).toOption ==
  some ([.operand "a", .opt "lines" (.val "3"), .operand "-"], ["-v"])
#guard ((head.parseInOrder ["a", "-n", "3", "-", "--", "-v"]).map splitInOrder).toOption ==
  some ([("lines", .val "3")], ["a", "-", "-v"])

end Silmaril.Cli.Getopt.Examples
