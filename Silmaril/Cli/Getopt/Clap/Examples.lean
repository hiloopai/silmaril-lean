module

public import Silmaril.Cli.Getopt.Clap.Thms
public meta import Silmaril.Cli.Getopt.Clap.Defs
public meta import Silmaril.Cli.Clap.Defs

/-!
# The getopt and clap dialects of one grammar: where they differ

One grammar (`demo`: `-n, --lines NUM`, `-v, --verbose`, `--color[=WHEN]`, `-h, --help`, then
files), read by GNU getopt_long (`getopt`), by POSIX getopt (`posix`) and by clap (`clap`),
checked by evaluation (`#guard`). Where both pre-passes pass, the readings agree
(`Silmaril.Cli.Getopt.read_clap`); every difference below is a command line where one of them
stops.
-/

public section

namespace Silmaril.Cli.Getopt.ClapExamples

open Silmaril.Cli

/-- The demo grammar. -/
def demoCmd : Command where
  name := "demo"
  opts := [{ id := "lines", long := ["lines"], short := ["n"], arg := some .str },
           { id := "verbose", long := ["verbose"], short := ["v"] },
           { id := "color", long := ["color"], arg := some (.enum ["never", "always", "auto"]),
             valueOptional := true },
           helpOpt]
  pos := [{ id := "file", arity := .many }]

/-- GNU getopt_long. -/
def getopt : Tool := { grammar := demoCmd }

/-- POSIX getopt (never permutes). -/
def posix : Tool := { grammar := demoCmd, gnu := false }

/-- clap. -/
def clap : Clap.Tool := getopt.clap

/-- The environment without variables. -/
def noEnv : String → Option String := fun _ => none

/-- The values of `id` in a getopt run. -/
def gStrs (id : String) : Outcome → Option (List String)
  | .run m => some (m.strs id)
  | _ => none

/-- The values of `id` in a clap run. -/
def cStrs (id : String) : Clap.Outcome → Option (List String)
  | .run _ m => some (m.strs id)
  | _ => none

/-- A usage error of the args dialect. -/
def gError : Outcome → Bool
  | .error _ _ => true
  | _ => false

/-- A usage error of the clap dialect. -/
def cError : Clap.Outcome → Bool
  | .error _ => true
  | _ => false

#guard Fits demoCmd
#guard demoCmd.WF
#guard Clap.HelpFlags demoCmd

-- Where both pre-passes pass, the readings agree: clusters, attached and separate arguments,
-- options after files (GNU order), `--`, `-` and a bare optional value.
#guard getopt.pre noEnv ["-vn5", "a", "--color", "-", "--", "-v"] == none
#guard Clap.pre clap demoCmd ["demo"] ["-vn5", "a", "--color", "-", "--", "-v"] ==
  none
#guard gStrs "file" (getopt.read noEnv ["-vn5", "a", "--color", "-", "--", "-v"]) ==
  some ["a", "-", "-v"]
#guard cStrs "file" (clap.read noEnv ["-vn5", "a", "--color", "-", "--", "-v"]) ==
  some ["a", "-", "-v"]
-- An optional value is only attached in both: `--color always` is a bare `--color` and a file.
#guard gStrs "file" (getopt.read noEnv ["--color", "always"]) == some ["always"]
#guard cStrs "file" (clap.read noEnv ["--color", "always"]) == some ["always"]

-- 1. Order. clap and GNU getopt read options after operands; POSIX getopt (and GNU getopt with
-- `POSIXLY_CORRECT` set or a `+` optstring) stops at the first operand.
#guard gStrs "lines" (getopt.read noEnv ["a", "-n", "3"]) == some ["3"]
#guard cStrs "lines" (clap.read noEnv ["a", "-n", "3"]) == some ["3"]
#guard gStrs "file" (posix.read noEnv ["a", "-n", "3"]) == some ["a", "-n", "3"]
#guard posix.pre noEnv ["a", "-n", "3"] == some (.afterOperand "-n")

-- 2. Abbreviations. getopt_long accepts an unambiguous prefix of a long name; clap (by
-- default) does not.
#guard gStrs "lines" (getopt.read noEnv ["--li", "3"]) == some ["3"]
#guard cError (clap.read noEnv ["--li", "3"])
#guard getopt.pre noEnv ["--li", "3"] == some (.abbrev "--li" "lines")
#guard gStrs "lines" (posix.read noEnv ["--li", "3"]) == some ["3"]

-- 3. An argument that starts with `-`. getopt takes the next token verbatim; clap refuses a
-- value that looks like an option.
#guard gStrs "lines" (getopt.read noEnv ["-n", "-5"]) == some ["-5"]
#guard cError (clap.read noEnv ["-n", "-5"])
#guard gStrs "lines" (posix.read noEnv ["-n", "-5"]) == some ["-5"]

-- 4. An attached `=`. getopt reads `-n=5` as the argument `=5`; clap (and the args dialect)
-- as `5`. `-n5` and `--lines=5` mean `5` in both.
#guard gStrs "lines" (getopt.read noEnv ["-n=5"]) == some ["=5"]
#guard cStrs "lines" (clap.read noEnv ["-n=5"]) == some ["5"]
#guard getopt.pre noEnv ["-n=5"] == some (.attachedEq "-n=5")
#guard gStrs "lines" (getopt.read noEnv ["-n5"]) == cStrs "lines" (clap.read noEnv ["-n5"])
#guard gStrs "lines" (getopt.read noEnv ["--lines=5"]) ==
  cStrs "lines" (clap.read noEnv ["--lines=5"])

-- 5. Help before a usage error. clap answers `-h` before it reads the rest; getopt reads the
-- whole line first, and its first usage error ends the reading.
#guard clap.read noEnv ["-h", "--bogus"] == .help ["demo"]
#guard gError (getopt.read noEnv ["-h", "--bogus"])
#guard gError (posix.read noEnv ["-h", "--bogus"])
#guard getopt.read noEnv ["-h", "a"] == .help ["demo"]

end Silmaril.Cli.Getopt.ClapExamples
