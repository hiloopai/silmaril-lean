module

public import Silmaril.Apps.Sha256sum.Quote
public import Silmaril.Apps.Sha256sum.Options
public import Silmaril.Apps.Sha256sum.CheckLine

/-! # `sha256sum` as a function of the world

`sha256sum : World → Outcome` is the executable specification of GNU coreutils 9.4
`sha256sum` (GNU/Linux, C locale): the exact bytes on standard output, the exact bytes on
standard error, and the exit status, for any command line, file system, standard input,
and choice of whether standard output is full. Section numbers refer to the research note
`spec.md`.

It is written as plain recursion over an explicit state `St` (output so far, error output
so far, what is left of standard input, the format lock), so that statements about it can
be proved by induction on operands and on check lines.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-! ## Constant texts (spec.md Appendix A) -/

def helpText (prog : Bytes) : Bytes :=
  lit "Usage: " ++ prog ++ lit " [OPTION]... [FILE]...\n" ++ lit "Print or check SHA256 (256-bit) checksums.

With no FILE, or when FILE is -, read standard input.
  -b, --binary          read in binary mode
  -c, --check           read checksums from the FILEs and check them
      --tag             create a BSD-style checksum
  -t, --text            read in text mode (default)
  -z, --zero            end each output line with NUL, not newline,
                          and disable file name escaping

The following five options are useful only when verifying checksums:
      --ignore-missing  don't fail or report status for missing files
      --quiet           don't print OK for each successfully verified file
      --status          don't output anything, status code shows success
      --strict          exit non-zero for improperly formatted checksum lines
  -w, --warn            warn about improperly formatted checksum lines

      --help        display this help and exit
      --version     output version information and exit

The sums are computed as described in FIPS-180-2.
When checking, the input should be a former output of this program.
The default mode is to print a line with: checksum, a space,
a character indicating input mode ('*' for binary, ' ' for text
or where binary is insignificant), and name for each FILE.

Note: There is no difference between binary mode and text mode on GNU systems.

GNU coreutils online help: <https://www.gnu.org/software/coreutils/>
Report any translation bugs to <https://translationproject.org/team/>
Full documentation <https://www.gnu.org/software/coreutils/sha256sum>
or available locally via: info '(coreutils) sha2 utilities'
"

def versionText : Bytes := lit "sha256sum (GNU coreutils) 9.4
Copyright (C) 2023 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <https://gnu.org/licenses/gpl.html>.
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

Written by Ulrich Drepper, Scott Miller, and David Madore.
"

/-! ## Diagnostics -/

/-- glibc `error (0, 0, msg)`. -/
def diag (prog msg : Bytes) : Bytes := prog ++ lit ": " ++ msg ++ [10]

/-- glibc `error (0, e, msg)`. -/
def diagE (prog msg : Bytes) (e : Errno) : Bytes := prog ++ lit ": " ++ msg ++ lit ": " ++ lit e.text ++ [10]

/-- The usage-failure tail. -/
def tryHelp (prog : Bytes) : Bytes := lit "Try '" ++ prog ++ lit " --help' for more information.\n"

/-! ## Run state -/

structure St where
  out : Bytes := []
  err : Bytes := []
  stdin : Stdin
  mode : BsdMode := .unknown

def St.emit (st : St) (b : Bytes) : St := { st with out := st.out ++ b }
def St.warn (st : St) (b : Bytes) : St := { st with err := st.err ++ b }

/-- Read standard input: everything that is left, after which it is empty. -/
def readStdin (st : St) : ReadResult × St :=
  match st.stdin with
  | .bytes b => (.ok b, { st with stdin := .bytes [] })
  | .dir => (.readErr .EISDIR [], st)

def dash : Bytes := [45]

/-- Read an operand or a listed name: `-` is standard input, anything else the oracle. -/
def readPath (w : World) (st : St) (path : Bytes) : ReadResult × St :=
  if path = dash then readStdin st else (w.fs path, st)

/-! ## Compute mode (spec.md §4) -/

/-- The output record for one successfully read operand, without its terminator. -/
def recordBody (o : Opts) (f data : Bytes) : Bytes :=
  let esc := !o.zero && problematic f
  let name := if esc then escapeName f else f
  let lead : Bytes := if esc then [92] else []
  if o.tag then lead ++ lit "SHA256 (" ++ name ++ lit ") = " ++ hexDigest data
  else lead ++ hexDigest data ++ [32, if o.binary = some true then 42 else 32] ++ name

/-- The record terminator: NUL with `-z`, LF otherwise. -/
def delim (o : Opts) : Bytes := if o.zero then [0] else [10]

/-- The output record for one successfully read operand. -/
def computeLine (o : Opts) (f data : Bytes) : Bytes := recordBody o f data ++ delim o

def computeOne (w : World) (o : Opts) (st : St) (f : Bytes) : St × Bool :=
  match readPath w st f with
  | (.ok data, st) => (st.emit (computeLine o f data), true)
  | (.openErr e, st) => (st.warn (diagE w.prog (quotef f) e), false)
  | (.readErr e _, st) => (st.warn (diagE w.prog (quotef f) e), false)

/-- Every operand is processed; the result is the conjunction. -/
def computeAll (w : World) (o : Opts) : St → List Bytes → St × Bool
  | st, [] => (st, true)
  | st, f :: fs =>
    let (st, ok₁) := computeOne w o st f
    let (st, ok₂) := computeAll w o st fs
    (st, ok₁ && ok₂)

/-! ## Check mode (spec.md §7) -/

/-- Per-check-file counters. -/
structure Counters where
  misformatted : Nat := 0
  mismatched : Nat := 0
  failures : Nat := 0
  properlyFormatted : Bool := false
  matched : Bool := false
  deriving DecidableEq, Repr

/-- The lines of a check file: split on LF, without the empty segment after a final LF. -/
def checkLines (data : Bytes) : List Bytes :=
  let segs := splitOn 10 data
  if segs.getLast? = some [] then segs.dropLast else segs

/-- Drop one trailing CR. -/
def dropCR (L : Bytes) : Bytes := if L.getLast? = some 13 then L.dropLast else L

/-- How a verified name is shown on standard output. -/
def shownName (o : Opts) (name : Bytes) : Bytes :=
  if !o.statusOnly && problematic name then 92 :: escapeName name else name

/-- Verify one parsed line `(hex, name)` (spec.md §7.4). -/
def verifyLine (w : World) (o : Opts) (st : St) (c : Counters) (hex name : Bytes) :
    St × Counters :=
  let c := { c with properlyFormatted := true }
  let shown := shownName o name
  match readPath w st name with
  | (.openErr .ENOENT, st) =>
    if o.ignoreMissing then (st, c)
    else
      let st := st.warn (diagE w.prog (quotef name) .ENOENT)
      let st := if o.statusOnly then st else st.emit (shown ++ lit ": FAILED open or read\n")
      (st, { c with failures := c.failures + 1 })
  | (.openErr e, st) =>
      let st := st.warn (diagE w.prog (quotef name) e)
      let st := if o.statusOnly then st else st.emit (shown ++ lit ": FAILED open or read\n")
      (st, { c with failures := c.failures + 1 })
  | (.readErr e _, st) =>
      let st := st.warn (diagE w.prog (quotef name) e)
      let st := if o.statusOnly then st else st.emit (shown ++ lit ": FAILED open or read\n")
      (st, { c with failures := c.failures + 1 })
  | (.ok data, st) =>
    let ok := hex.map lowerAscii = hexDigest data
    let c := if ok then { c with matched := true } else { c with mismatched := c.mismatched + 1 }
    let st :=
      if o.statusOnly then st
      else if !ok then st.emit (shown ++ lit ": FAILED\n")
      else if !o.quiet then st.emit (shown ++ lit ": OK\n")
      else st
    (st, c)

/-- Handle one line of a check file (spec.md §7.2). -/
def checkLine (w : World) (o : Opts) (isStdin : Bool) (cname : Bytes) (st : St)
    (c : Counters) (lineno : Nat) (raw : Bytes) : St × Counters :=
  if raw.head? = some 35 then (st, c)
  else
    let L := dropCR raw
    if L = [] then (st, c)
    else
      let (mode, parsed) := parseLine st.mode L
      let st := { st with mode := mode }
      match parsed with
      | some (hex, name) =>
        if isStdin && name = dash then
          let st := if o.warn then st.warn (diag w.prog (quotef cname ++ lit ": " ++
            decimal lineno ++ lit ": improperly formatted SHA256 checksum line")) else st
          (st, { c with misformatted := c.misformatted + 1 })
        else verifyLine w o st c hex name
      | none =>
        let st := if o.warn then st.warn (diag w.prog (quotef cname ++ lit ": " ++
          decimal lineno ++ lit ": improperly formatted SHA256 checksum line")) else st
        (st, { c with misformatted := c.misformatted + 1 })

def checkLinesFrom (w : World) (o : Opts) (isStdin : Bool) (cname : Bytes) :
    St → Counters → Nat → List Bytes → St × Counters
  | st, c, _, [] => (st, c)
  | st, c, n, L :: Ls =>
    let (st, c) := checkLine w o isStdin cname st c n L
    checkLinesFrom w o isStdin cname st c (n + 1) Ls

/-- English plural of the summary warnings. -/
def plural (n : Nat) (one many : String) : Bytes :=
  decimal n ++ [32] ++ lit (if n = 1 then one else many)

/-- The end-of-file summary (spec.md §7.5). -/
def summary (w : World) (o : Opts) (cname : Bytes) (st : St) (c : Counters) : St :=
  if !c.properlyFormatted then
    st.warn (diag w.prog (quotef cname ++ lit ": no properly formatted checksum lines found"))
  else if o.statusOnly then st
  else
    let st := if c.misformatted ≠ 0 then st.warn (diag w.prog (lit "WARNING: " ++
      plural c.misformatted "line is" "lines are" ++ lit " improperly formatted")) else st
    let st := if c.failures ≠ 0 then st.warn (diag w.prog (lit "WARNING: " ++
      plural c.failures "listed file" "listed files" ++ lit " could not be read")) else st
    let st := if c.mismatched ≠ 0 then st.warn (diag w.prog (lit "WARNING: " ++
      plural c.mismatched "computed checksum" "computed checksums" ++ lit " did NOT match"))
      else st
    if o.ignoreMissing && !c.matched then
      st.warn (diag w.prog (quotef cname ++ lit ": no file was verified"))
    else st

/-- The result of one check file. -/
def Counters.ok (o : Opts) (c : Counters) : Bool :=
  c.properlyFormatted && c.matched && c.mismatched == 0 && c.failures == 0 &&
    (!o.strict || c.misformatted == 0)

/-- Process one check file (spec.md §7.1–7.5). -/
def checkFile (w : World) (o : Opts) (st : St) (cf : Bytes) : St × Bool :=
  let isStdin := cf = dash
  let cname := if isStdin then lit "standard input" else cf
  match readPath w st cf with
  | (.openErr e, st) => (st.warn (diagE w.prog (quotef cf) e), false)
  | (.readErr _ pre, st) =>
    let (st, _) := checkLinesFrom w o isStdin cname st {} 1 (checkLines pre)
    (st.warn (diag w.prog (quotef cname ++ lit ": read error")), false)
  | (.ok data, st) =>
    let (st, c) := checkLinesFrom w o isStdin cname st {} 1 (checkLines data)
    (summary w o cname st c, c.ok o)

def checkAll (w : World) (o : Opts) : St → List Bytes → St × Bool
  | st, [] => (st, true)
  | st, f :: fs =>
    let (st, ok₁) := checkFile w o st f
    let (st, ok₂) := checkAll w o st fs
    (st, ok₁ && ok₂)

/-! ## Top level (spec.md §8, §9) -/

/-- gnulib `close_stdout` (spec.md §8): on a full standard output, every byte written is
lost, a diagnostic is appended, and the status is 1. The diagnostic has no errno text when
the output ended in a newline (the last line flush failed, and `fclose` found nothing
pending), and `ENOSPC` otherwise. -/
def finish (w : World) (out err : Bytes) (status : Nat) : Outcome :=
  if w.stdoutFull && !out.isEmpty then
    { stdout := [], status := 1
      stderr := err ++ (if out.getLast? = some 10 then diag w.prog (lit "write error")
        else diagE w.prog (lit "write error") .ENOSPC) }
  else { stdout := out, stderr := err, status := status }

/-- The operands, defaulting to standard input. -/
def operandsOrStdin (ops : List Bytes) : List Bytes := if ops = [] then [dash] else ops

/-- The main mode, after a successful scan and validation. -/
def runMode (w : World) (o : Opts) (ops : List Bytes) : St × Bool :=
  let st : St := { stdin := w.stdin }
  if o.check then checkAll w o st (operandsOrStdin ops)
  else computeAll w o st (operandsOrStdin ops)

def sha256sum (w : World) : Outcome :=
  match scan w.prog w.posix w.argv.tail with
  | .help => finish w (helpText w.prog) [] 0
  | .version => finish w versionText [] 0
  | .usage msg => finish w [] (msg ++ tryHelp w.prog) 1
  | .done o ops =>
    match validate o with
    | some m => finish w [] (diag w.prog (lit m) ++ tryHelp w.prog) 1
    | none =>
      let (st, ok) := runMode w o ops
      finish w st.out st.err (if ok then 0 else 1)

end Silmaril.Apps.Sha256sum
