module

public import Silmaril.Apps.Sha256sum.Basic

/-! # The command line

spec.md §3. glibc `getopt_long` with optstring `"bctwz"` and the twelve long options of
digest.c, followed by the nine option-combination checks.

Options take effect in the order they are scanned. `--help` and `--version` act as soon as
they are scanned; a scanning error (unknown, ambiguous, or argument given to a flag) ends
the run with a usage failure. With GNU permutation (no `POSIXLY_CORRECT`) operands may be
interleaved with options; with `POSIXLY_CORRECT` the first operand ends option scanning.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-- What an option does. -/
inductive Opt where
  | check | ignoreMissing | quiet | status | warn | strict | tag | zero | binary | text
  | help | version
  deriving DecidableEq, Repr

/-- The long-option table, in digest.c order (the order of the "possibilities" listing). -/
def longOpts : List (String × Opt) :=
  [("check", .check), ("ignore-missing", .ignoreMissing), ("quiet", .quiet),
   ("status", .status), ("warn", .warn), ("strict", .strict), ("tag", .tag),
   ("zero", .zero), ("binary", .binary), ("text", .text), ("help", .help),
   ("version", .version)]

/-- The short options `b c t w z`. -/
def shortOpt (c : UInt8) : Option Opt :=
  if c = 98 then some .binary else if c = 99 then some .check else if c = 116 then some .text
  else if c = 119 then some .warn else if c = 122 then some .zero else none

/-- The option state of digest.c. `binary` is `none` until `-b`, `-t` or `--tag`. -/
structure Opts where
  check : Bool := false
  binary : Option Bool := none
  tag : Bool := false
  zero : Bool := false
  statusOnly : Bool := false
  warn : Bool := false
  quiet : Bool := false
  ignoreMissing : Bool := false
  strict : Bool := false
  deriving DecidableEq, Repr

/-- The effect of one (non-help, non-version) option. -/
def Opts.apply (o : Opts) : Opt → Opts
  | .check => { o with check := true }
  | .binary => { o with binary := some true }
  | .text => { o with binary := some false }
  | .tag => { o with tag := true, binary := some true }
  | .zero => { o with zero := true }
  | .status => { o with statusOnly := true, warn := false, quiet := false }
  | .warn => { o with statusOnly := false, warn := true, quiet := false }
  | .quiet => { o with statusOnly := false, warn := false, quiet := true }
  | .ignoreMissing => { o with ignoreMissing := true }
  | .strict => { o with strict := true }
  | .help | .version => o

/-- The result of scanning the command line. -/
inductive Scan where
  /-- Scanning finished: the final option state and the operands, in order. -/
  | done (opts : Opts) (operands : List Bytes)
  | help
  | version
  /-- A getopt error: the message (already complete, `P: …\n`) precedes the usage tail. -/
  | usage (msg : Bytes)
  deriving DecidableEq, Repr

/-- Resolve a long option `--BODY` (the bytes after `--`). -/
def resolveLong (prog body : Bytes) : Except Bytes Opt :=
  let name := body.takeWhile (· != 61)
  let hasArg := body.contains 61
  let exact := longOpts.filter fun (n, _) => lit n = name
  let cands := if exact.isEmpty then longOpts.filter fun (n, _) => name.isPrefixOf (lit n)
    else exact
  match cands with
  | [] => .error (prog ++ lit ": unrecognized option '--" ++ body ++ lit "'\n")
  | [(n, o)] =>
    if hasArg then .error (prog ++ lit ": option '--" ++ lit n ++ lit "' doesn't allow an argument\n")
    else .ok o
  | _ =>
    .error (prog ++ lit ": option '--" ++ body ++ lit "' is ambiguous; possibilities:" ++
      cands.flatMap (fun (n, _) => lit " '--" ++ lit n ++ lit "'") ++ lit "\n")

/-- Apply one option, unless it is `--help` or `--version`, which end the scan. -/
def applyOpt (o : Opts) (x : Opt) (k : Opts → Scan) : Scan :=
  match x with
  | .help => .help
  | .version => .version
  | x => k (o.apply x)

/-- A cluster of short options `-xyz`. -/
def scanCluster (prog : Bytes) (operands : List Bytes) : Opts → Bytes → (Opts → Scan) → Scan
  | o, [], k => k o
  | o, c :: cs, k =>
    match shortOpt c with
    | some x => applyOpt o x fun o' => scanCluster prog operands o' cs k
    | none => .usage (prog ++ lit ": invalid option -- '" ++ [c] ++ lit "'\n")

/-- Scan `argv[1..]`. `operands` collects operands in reverse. -/
def scanArgs (prog : Bytes) (posix : Bool) : Opts → List Bytes → List Bytes → Scan
  | o, operands, [] => .done o operands.reverse
  | o, operands, a :: rest =>
    if a = [45, 45] then .done o (operands.reverse ++ rest)
    else match a with
      | 45 :: 45 :: body =>
        match resolveLong prog body with
        | .error msg => .usage msg
        | .ok x => applyOpt o x fun o' => scanArgs prog posix o' operands rest
      | 45 :: c :: cs =>
        scanCluster prog operands o (c :: cs) fun o' => scanArgs prog posix o' operands rest
      | _ =>
        if posix then .done o (operands.reverse ++ a :: rest)
        else scanArgs prog posix o (a :: operands) rest

def scan (prog : Bytes) (posix : Bool) (args : List Bytes) : Scan := scanArgs prog posix {} [] args

/-- The nine combination checks of digest.c, in order; the first failing one gives its
message. Only the final flag values count. -/
def validate (o : Opts) : Option String :=
  if o.tag && o.binary = some false then some "--tag does not support --text mode"
  else if o.zero && o.check then some "the --zero option is not supported when verifying checksums"
  else if o.tag && o.check then some "the --tag option is meaningless when verifying checksums"
  else if o.binary.isSome && o.check then
    some "the --binary and --text options are meaningless when verifying checksums"
  else if o.ignoreMissing && !o.check then
    some "the --ignore-missing option is meaningful only when verifying checksums"
  else if o.statusOnly && !o.check then
    some "the --status option is meaningful only when verifying checksums"
  else if o.warn && !o.check then
    some "the --warn option is meaningful only when verifying checksums"
  else if o.quiet && !o.check then
    some "the --quiet option is meaningful only when verifying checksums"
  else if o.strict && !o.check then
    some "the --strict option is meaningful only when verifying checksums"
  else none

/-! ## Spot checks -/

example : scan (lit "P") false [lit "--st"] =
    .usage (lit "P: option '--st' is ambiguous; possibilities: '--status' '--strict'\n") := by
  decide
example : scan (lit "P") false [lit "--sta"] = .done { statusOnly := true } [] := by decide
example : scan (lit "P") false [lit "a", lit "-c", lit "--", lit "-b"] =
    .done { check := true } [lit "a", lit "-b"] := by decide
example : scan (lit "P") true [lit "a", lit "-c"] = .done {} [lit "a", lit "-c"] := by decide
example : scan (lit "P") false [lit "--help", lit "--bogus"] = .help := by decide
example : scan (lit "P") false [lit "--bogus", lit "--help"] =
    .usage (lit "P: unrecognized option '--bogus'\n") := by decide
example : scan (lit "P") false [lit "--tag=1"] =
    .usage (lit "P: option '--tag' doesn't allow an argument\n") := by decide

end Silmaril.Apps.Sha256sum
