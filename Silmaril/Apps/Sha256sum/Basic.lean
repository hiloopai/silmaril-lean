module

public import Silmaril.Crypto.SHA256

/-! # `sha256sum`: bytes, the world and the observable result

The executable specification of GNU coreutils 9.4 `sha256sum` (GNU/Linux, C locale) lives
in `Silmaril.Apps.Sha256sum`. This file holds the pieces every other part uses: byte
strings, the error numbers the program can report and their C-locale `strerror` texts,
the abstract world the program runs in, and the observable outcome.

The world is the one of the research note `spec.md` §2 (in
`/srv/scratch/campaigns/research/sha256sum/`): `argv`, whether `POSIXLY_CORRECT` is set,
a read oracle for the file system, standard input as a once-consumable stream, and whether
standard output is a full device. The outcome is the exact bytes written to standard
output and to standard error, and the exit status.

What the world fixes rather than models (spec.md §1): the C locale, `O_BINARY = 0`,
descriptors 0, 1 and 2 open, the default `SIGPIPE` disposition, a file system that does
not change during the run, and a non-root user.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-- The bytes of an ASCII string literal (each character's code point, truncated to a byte;
every literal in this specification is ASCII). Written with `String.toList` rather than
`String.toUTF8` so that the kernel can evaluate it in `decide` proofs. -/
def lit (s : String) : Bytes := s.toList.map fun c => UInt8.ofNat c.toNat

/-! ## Errors -/

/-- The error numbers a read can report in this world. -/
inductive Errno where
  | ENOENT | EACCES | EISDIR | ENOTDIR | ELOOP | ENAMETOOLONG | EIO | ENOSPC | EBADF
  deriving DecidableEq, Repr

/-- glibc `strerror` in the C locale. -/
def Errno.text : Errno → String
  | .ENOENT => "No such file or directory"
  | .EACCES => "Permission denied"
  | .EISDIR => "Is a directory"
  | .ENOTDIR => "Not a directory"
  | .ELOOP => "Too many levels of symbolic links"
  | .ENAMETOOLONG => "File name too long"
  | .EIO => "Input/output error"
  | .ENOSPC => "No space left on device"
  | .EBADF => "Bad file descriptor"

/-! ## The world -/

/-- What happens when the program opens a path read-only and reads it to the end. -/
inductive ReadResult where
  /-- The open and every read succeeded. -/
  | ok (data : Bytes)
  /-- The open failed. -/
  | openErr (e : Errno)
  /-- The open succeeded; the reads delivered `pre` and then failed with `e`. A directory
  is `readErr .EISDIR []`. -/
  | readErr (e : Errno) (pre : Bytes)
  deriving DecidableEq, Repr

/-- Standard input. A directory fails every read with `EISDIR`. -/
inductive Stdin where
  | bytes (b : Bytes)
  | dir
  deriving DecidableEq, Repr

structure World where
  /-- `argv[0]` is the program name used in every diagnostic. -/
  argv : List Bytes
  /-- `POSIXLY_CORRECT` is set: no argument permutation. -/
  posix : Bool := false
  /-- The read oracle. It is never consulted for the operand `-`. -/
  fs : Bytes → ReadResult
  stdin : Stdin := .bytes []
  /-- Standard output is a device on which every write fails with `ENOSPC`. -/
  stdoutFull : Bool := false

/-- The program name, `argv[0]`. -/
def World.prog (w : World) : Bytes := w.argv.headD []

/-- The observable result of a run. -/
structure Outcome where
  stdout : Bytes
  stderr : Bytes
  status : Nat
  deriving DecidableEq, Repr

/-! ## Small byte utilities -/

/-- Lower-case hexadecimal digit of `n < 16`. -/
def hexDigit (n : Nat) : UInt8 := if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (87 + n)

/-- Lower-case hexadecimal rendering, two digits per byte. -/
def hexLower (d : Bytes) : Bytes :=
  d.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- The 64 lower-case hex digits of the SHA-256 of `data`. -/
def hexDigest (data : Bytes) : Bytes := hexLower (Silmaril.Crypto.SHA256.digest data)

/-- `[0-9A-Fa-f]`. -/
def isHex (c : UInt8) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)

/-- ASCII lower-casing. -/
def lowerAscii (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- The decimal rendering of a natural number. -/
def decimal (n : Nat) : Bytes := lit (toString n)

/-- Space or tab: the separator set of `--check` lines. -/
def isWS (c : UInt8) : Bool := c == 32 || c == 9

/-- The prefix before the first NUL (C-string semantics). -/
def beforeNul (s : Bytes) : Bytes := s.takeWhile (· != 0)

/-- Split on a separator byte. `splitOn c []` is `[[]]`, like Python's `bytes.split`. -/
def splitOn (c : UInt8) : Bytes → List Bytes
  | [] => [[]]
  | x :: rest =>
    if x = c then [] :: splitOn c rest
    else match splitOn c rest with
      | [] => [[x]]
      | first :: more => (x :: first) :: more

theorem hexDigit_props : ∀ n : Fin 16,
    isHex (hexDigit n) = true ∧ lowerAscii (hexDigit n) = hexDigit n := by decide

theorem hexLower_length (d : Bytes) : (hexLower d).length = 2 * d.length := by
  induction d with
  | nil => rfl
  | cons b rest ih => simp [hexLower, List.flatMap_cons] at *; omega

theorem hexDigest_length (data : Bytes) : (hexDigest data).length = 64 := by
  simp [hexDigest, hexLower_length, Silmaril.Crypto.SHA256.digest_length]

/-- Every byte of `hexLower d` is a lower-case hex digit. -/
theorem hexLower_all (d : Bytes) : ∀ c ∈ hexLower d, isHex c = true ∧ lowerAscii c = c := by
  intro c hc
  simp only [hexLower, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨b, -, hb | hb⟩ := hc
  · have := hexDigit_props ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩
    exact hb ▸ this
  · have := hexDigit_props ⟨b.toNat % 16, by omega⟩
    exact hb ▸ this

end Silmaril.Apps.Sha256sum
