module

public import Silmaril.Formats.Compression.Inflate.Common

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate.Stream.Protocol

/-!
# The shared `inflate` return protocol

A source-style mathematical translation of the two
pinned versions' identical `inf_leave` protocol and its immediate-return paths.
The complete source mode enumeration and all flush codes are observed here.
Unknown integer flush codes follow the source's comparisons as well.

This module observes logical cursors/counters rather than C pointers. Window
updates and checksum folds are explicit parameters, not verified callbacks.
It does not prove C execution or supply the inflater's decoder invariant.
LP64 unsigned counter arithmetic is explicit; mathematical conservation laws
state the bounds needed to eliminate subtraction wraparound.

`savedOut` is the *current local* `out`, not necessarily the call's initial
capacity: CHECK commits output/checksums and rebases it to `left`. Consequently
the final no-progress test can see zero pending output after CHECK even if the
call emitted bytes. NEED_DICT restores registers but skips this epilogue;
MEM/SYNC/invalid-entry paths skip both restore and the epilogue. Allocation
failure restores registers, then returns before final counter/check updates.

Source anchors: zlib 1.3.1 `inflate.c`: DICT 816, CHECK 1183, LENGTH 1208,
`inf_leave` 1242; pinned develop `767c4c947852`: 700, 1072, 1097, 1131.
The source routines agree on these operations. This observation omits diagnostic
message pointers, allocator effects, and the representation of window memory.
-/

def noFlush : Int := 0
def partialFlush : Int := 1
def syncFlush : Int := 2
def fullFlush : Int := 3
def finish : Int := 4
def block : Int := 5
def trees : Int := 6

def ok : Int := 0
def streamEnd : Int := 1
def needDict : Int := 2
def streamError : Int := -2
def dataError : Int := -3
def memError : Int := -4
def bufError : Int := -5

/-- Offsets from HEAD = 16180, as declared in both pinned `inflate.h` files. -/
def modeRank : Mode → Nat
  | .head => 0 | .flags => 1 | .time => 2 | .os => 3 | .exlen => 4
  | .extra => 5 | .name => 6 | .comment => 7 | .hcrc => 8 | .dictid => 9
  | .dict => 10 | .type_ => 11 | .typedo => 12 | .stored => 13
  | .copyFirst => 14 | .copy => 15 | .table => 16 | .lenlens => 17
  | .codelens => 18 | .lenFirst => 19 | .len => 20 | .lenext => 21
  | .dist => 22 | .distext => 23 | .match_ => 24 | .lit => 25
  | .check => 26 | .length => 27 | .done => 28 | .bad => 29
  | .mem => 30 | .sync => 31

def modeNumber (mode : Mode) : Nat := 16180 + modeRank mode

/-- An existing TYPE state skips the block-boundary flush check on entry. -/
def entryMode (mode : Mode) : Mode := if mode = .type_ then .typedo else mode

def stopAtBlockBoundary (flush : Int) : Bool := decide (flush = block ∨ flush = trees)
def stopAfterBlockHeader (flush : Int) : Bool := decide (flush = trees)

/-- The source's low bit count and independently documented boundary flags. -/
def dataType (mode : Mode) (bits : Nat) (last : Bool) : Nat :=
  bits + (if last then 64 else 0) + (if mode = .type_ then 128 else 0) +
    (if mode = .lenFirst ∨ mode = .copyFirst then 256 else 0)

def word32 : Nat := 2 ^ 32
def word64 : Nat := 2 ^ 64
def sub32 (initial remaining : Nat) : Nat :=
  (initial % word32 + word32 - remaining % word32) % word32
def add64 (initial increment : Nat) : Nat := (initial + increment) % word64

/-- The source's final return-code conditional, before any abstraction of errors. -/
def returnCode131 (ret flush : Int) (consumed produced : Nat) : Int :=
  if ((consumed = 0 ∧ produced = 0) ∨ flush = finish) ∧ ret = ok then bufError else ret

/-- The same control decision factored by the existing return code first. -/
def returnCodeDevelop (ret flush : Int) (consumed produced : Nat) : Int :=
  if ret = ok then
    if consumed = 0 ∧ produced = 0 then bufError
    else if flush = finish then bufError else ok
  else ret

inductive ChecksumKind where | adler32 | crc32
deriving Repr, DecidableEq

/-- A callback's mathematical seed/bytes interface; soundness is a separate
contract, rather than assuming that this arbitrary function computes a checksum. -/
abbrev UpdateCheck := ChecksumKind → Nat → List UInt8 → Nat

structure PublicFields where
  nextIn : Nat
  nextOut : Nat
  availIn : Nat
  availOut : Nat
  totalIn : Nat
  totalOut : Nat
  adler : Nat
  dataType : Nat
deriving Repr, DecidableEq

/-- Logical fields at a selected return point. Window contents are deliberately
outside this protocol observation, owned by the window-operation contract.
`windowSizeAtExit` is the guard's pre-update snapshot, not the resulting size.
The decoder-to-protocol bridge must establish cursor/byte coherence. -/
structure ExitFields where
  publicFields : PublicFields
  mode : Mode
  privateTotal : Nat
  check : Nat
  savedIn : Nat
  savedOut : Nat
  nextIn : Nat
  nextOut : Nat
  inputLeft : Nat
  left : Nat
  hold : Nat
  bits : Nat
  storedHold : Nat
  storedBits : Nat
  last : Bool
  wrap : Nat
  flags : Int
  windowSizeAtExit : Nat
  flush : Int
  gzipEnabled : Bool
  pendingOutput : List UInt8
deriving Repr, DecidableEq

def consumed (f : ExitFields) : Nat := sub32 f.savedIn f.inputLeft
def produced (f : ExitFields) : Nat := sub32 f.savedOut f.left

/-- Obligations needed when interpreting the observed counts as byte lengths.
Pointer validity, aliasing, and the actual bytes in memory belong to a separate
C memory relation. This predicate alone does not establish them. -/
def CountsCoherent (f : ExitFields) : Prop :=
  f.inputLeft ≤ f.savedIn ∧ f.savedIn < word32 ∧
  f.left ≤ f.savedOut ∧ f.savedOut < word32 ∧
  f.pendingOutput.length = produced f

def validateChecks (f : ExitFields) : Bool := f.wrap.testBit 2
def checksumKind (f : ExitFields) : ChecksumKind :=
  if f.gzipEnabled ∧ f.flags ≠ 0 then .crc32 else .adler32

/-- The precise source condition, including updates with zero bytes when an
existing window has nonzero size. CHECK+Z_FINISH can avoid fresh allocation. -/
def windowWanted (f : ExitFields) : Bool :=
  decide (f.windowSizeAtExit ≠ 0 ∨
    (f.savedOut ≠ f.left ∧ modeRank f.mode < modeRank .bad ∧
      (modeRank f.mode < modeRank .check ∨ f.flush ≠ finish)))

/-- RESTORE writes cursor/capacity and accumulator fields, not total counters. -/
def restore (f : ExitFields) : ExitFields :=
  { f with
    publicFields := { f.publicFields with
      nextIn := f.nextIn, nextOut := f.nextOut, availIn := f.inputLeft, availOut := f.left }
    storedHold := f.hold, storedBits := f.bits }

/-- CHECK's early commit. It must rebase the saved output and pending-byte view
so final `inf_leave` neither double counts nor hashes the same bytes twice. -/
def checkOutput (update : UpdateCheck) (f : ExitFields) : ExitFields :=
  if f.wrap = 0 then f else
    let amount := produced f
    let changed := validateChecks f && decide (amount ≠ 0)
    let nextCheck := if changed then update (checksumKind f) f.check f.pendingOutput % word64
      else f.check
    { f with
      publicFields := { f.publicFields with
        totalOut := add64 f.publicFields.totalOut amount
        adler := if changed then nextCheck else f.publicFields.adler }
      privateTotal := add64 f.privateTotal amount
      check := nextCheck
      savedOut := f.left
      pendingOutput := [] }

/-- The source's `ZSWAP32`, expressed without machine-word bit operations. -/
def swap32 (value : Nat) : Nat :=
  value % 256 * 16777216 + value / 256 % 256 * 65536 +
    value / 65536 % 256 * 256 + value / 16777216 % 256

def trailerCheck (f : ExitFields) : Nat :=
  if f.gzipEnabled ∧ f.flags ≠ 0 then f.hold else swap32 f.hold

/-- CHECK after its `NEEDBITS(32)` has succeeded when wrapped. The caller
supplies the ready bit accumulator; this operation does not read input.
A failed checksum retains the accumulator, just as the source's `break` does.
The successful raw path leaves it untouched because there was no trailer. -/
def checkReady (update : UpdateCheck) (f : ExitFields) : ExitFields :=
  let accounted := checkOutput update f
  if f.wrap ≠ 0 ∧ validateChecks f ∧ trailerCheck f ≠ accounted.check then
    { accounted with mode := .bad }
  else
    let nextMode : Mode := if f.gzipEnabled then .length else .done
    if f.wrap = 0 then { accounted with mode := nextMode }
    else { accounted with mode := nextMode, hold := 0, bits := 0 }

/-- LENGTH after its conditional `NEEDBITS(32)` has succeeded. Gzip's ISIZE
comparison is modulo 2^32 even though the accumulated total is LP64. -/
def lengthReady (f : ExitFields) : ExitFields :=
  if f.gzipEnabled ∧ f.wrap ≠ 0 ∧ f.flags ≠ 0 then
    if validateChecks f ∧ f.hold ≠ f.privateTotal % word32 then { f with mode := .bad }
    else { f with mode := .done, hold := 0, bits := 0 }
  else { f with mode := .done }

inductive Stage where | immediate | restored | committed
deriving Repr, DecidableEq

structure Return where
  status : Int
  fields : ExitFields
  stage : Stage
  windowAttempted : Bool
deriving Repr, DecidableEq

/-- Shared epilogue arithmetic, parameterized by the proved-equivalent
version-specific final status conditional. `windowFailed` is observed only
when the actual source guard requests a window operation. -/
def infLeaveWith (status : Int → Int → Nat → Nat → Int) (update : UpdateCheck)
    (windowFailed : Bool) (ret : Int) (f : ExitFields) : Return :=
  let restored := restore f
  let needsWindow := windowWanted restored
  if needsWindow && windowFailed then
    ⟨memError, { restored with mode := .mem }, .restored, true⟩
  else
    let inputCount := consumed restored
    let outputCount := produced restored
    let changed := validateChecks restored && decide (outputCount ≠ 0)
    let nextCheck := if changed then
        update (checksumKind restored) restored.check restored.pendingOutput % word64
      else restored.check
    let after := { restored with
      publicFields := { restored.publicFields with
        totalIn := add64 restored.publicFields.totalIn inputCount
        totalOut := add64 restored.publicFields.totalOut outputCount
        adler := if changed then nextCheck else restored.publicFields.adler
        dataType := dataType restored.mode restored.bits restored.last }
      privateTotal := add64 restored.privateTotal outputCount
      check := nextCheck }
    ⟨status ret restored.flush inputCount outputCount, after, .committed, needsWindow⟩

def infLeave131 := infLeaveWith returnCode131
def infLeaveDevelop := infLeaveWith returnCodeDevelop

/-- Routes deliberately distinguish the source's early returns from a normal
yield through `inf_leave`. `continue` is represented by `none` below. -/
inductive Route where
  | leave (ret : Int)
  | dictionary
  | immediateMemory
  | immediateStreamError
deriving Repr, DecidableEq

def terminalRoute (mode : Mode) (hasDictionary : Bool) : Option Route :=
  match mode with
  | .dict => if hasDictionary then none else some .dictionary
  | .done => some (.leave streamEnd)
  | .bad => some (.leave dataError)
  | .mem => some .immediateMemory
  | .sync => some .immediateStreamError
  | _ => none

def returnVia (update : UpdateCheck) (windowFailed : Bool) (route : Route)
    (f : ExitFields) : Return :=
  match route with
  | .leave ret => infLeave131 update windowFailed ret f
  | .dictionary => ⟨needDict, restore f, .restored, false⟩
  | .immediateMemory => ⟨memError, f, .immediate, false⟩
  | .immediateStreamError => ⟨streamError, f, .immediate, false⟩

end Silmaril.Formats.Compression.Inflate.Stream.Protocol
