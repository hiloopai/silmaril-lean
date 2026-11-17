module

public import Silmaril.Elf.Parse.Defs

/-! # Three-valued reads and decoding: unsupported, invalid and incomplete are different answers (`Silmaril.Elf.Decode`)

The parse specification `Silmaril.Elf.read : Rd File` runs against an oracle
`Nat → Nat → Option Nat`, so a failed parse says only `none`. That conflates four answers a
consumer must keep apart:

| answer | meaning | example |
|---|---|---|
| `ok A` | the bytes parse to `A` | every parsed file, any `e_machine` |
| `unsupported u` | a well-identified ELF file outside the domain the specification reads | `ELFCLASS32`, big-endian, an `e_ident` version other than `EV_CURRENT` |
| `invalid i` | the bytes present are not such a file: not ELF, truncated, or rejected by a table check | a cut file, a bad magic |
| `incomplete o w` | the view does not hold the `w` bytes at `o`: **no** fact about the file | a 64-byte download prefix |

* `Avail` is what a three-valued source says about a read: the value, `eof` (the source *knows*
  the bytes end first) or `unknown` (this view does not hold them).
* `runD r p` runs any existing reading program `p : Rd α` three-valued; `parseD r` is the parse
  specification, and `decode r` refines its rejections with the reason (`identify`).
* Sources: `whole F` (a whole file: never `unknown`), `prefixOf F k` (the first `k` bytes of
  `F`), `windows ws r` (the byte ranges `ws` of an oracle, as `Staged.Reader.window`).
* `Refines v w`: `w` answers everything `v` does, identically. `Thms.runD_refines`: only
  `incomplete` can change when the view grows.

On whole files nothing is lost or added (`Thms`): `decode (whole F) = .ok A ↔ Parses F A`
(`decode_whole_ok_iff`), a whole file is never `incomplete`, and an `unsupported` or `invalid`
answer means the file has no parse. The `unsupported` set is exactly the identification bytes the
specification's header reader rejects; `e_machine` is not among them: an unknown machine is
recorded (`MachineIs`), never reported as malformed. Whether there is an instruction model for a
machine is a separate question (`Silmaril.Elf.Asm.Isa`).

Ported from the authors' prototype of three-valued ELF decoding, with the `unsupported` answer
split out of `invalid` and the byte source taken as a plain oracle (no second byte-source class:
`Silmaril.ByteSource` and `Blob` are the carriers, `ElfLike` the interface).
-/

@[expose] public section

namespace Silmaril.Elf.Decode

open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.DynElf (Rd blobRead)

/-! ## Three-valued sources -/

/-- **What a source says about a read** of `w` little-endian bytes. -/
inductive Avail where
  /-- The bytes are present; their little-endian value. -/
  | val (n : Nat)
  /-- The source ends before the read does: a fact about the bytes (the file is shorter). -/
  | eof
  /-- This view does not hold (all of) the bytes: no fact about the file. -/
  | unknown
  deriving DecidableEq, Repr

/-- A three-valued byte oracle. -/
abbrev ASrc := Nat → Nat → Avail

/-- **A whole file**: every read is answered (`val` or `eof`). -/
def whole (F : Blob) : ASrc := fun o w =>
  match blobRead F o w with
  | some n => .val n
  | none => .eof

/-- **The first `k` bytes of `F`** (a download prefix). A read inside them is answered; a read past
them is `unknown`, unless the whole file lies inside the prefix (`F.len ≤ k`), in which case the
end is known and the read is `eof`. -/
def prefixOf (F : Blob) (k : Nat) : ASrc := fun o w =>
  if o + w ≤ k ∨ F.len ≤ k then whole F o w else .unknown

/-- **The byte ranges `ws` of an oracle** `r` (`none` inside a range: the bytes there end). Reads
outside every range are `unknown`. -/
def windows (ws : List Span) (r : Nat → Nat → Option Nat) : ASrc := fun o w =>
  if ws.any (fun s => decide (s.Contains o w)) then
    match r o w with
    | some n => .val n
    | none => .eof
  else .unknown

/-- `w` is a fuller view than `v`: every answer of `v` that is not `unknown` is `w`'s too. -/
def Refines (v w : ASrc) : Prop := ∀ o n, v o n ≠ .unknown → w o n = v o n

/-- A source that never answers `unknown`: it stands for a whole file. -/
def Whole (v : ASrc) : Prop := ∀ o n, v o n ≠ .unknown

/-! ## Answers -/

/-- Why a well-identified ELF file is outside the domain the specification reads. -/
inductive Unsupported where
  /-- `ELFCLASS32`. -/
  | elf32
  /-- `ELFDATA2MSB`. -/
  | bigEndian
  /-- `e_ident[EI_VERSION]` is not `EV_CURRENT` (1). -/
  | version (v : Nat)
  deriving DecidableEq, Repr

/-- Why the bytes present are not a file the specification reads. -/
inductive Invalid where
  /-- The first four bytes are not `\x7fELF`. -/
  | notElf
  /-- `e_ident[EI_CLASS]` or `e_ident[EI_DATA]` is none of the values the gABI defines. -/
  | badIdent
  /-- A read of `w` bytes at `o` ran past the end of the source. -/
  | truncated (o w : Nat)
  /-- A format check of the reading program failed (a malformed table; `Rd.fail`). -/
  | rejected
  deriving DecidableEq, Repr

/-- **The result of decoding a possibly partial source.** -/
inductive Decoded (α : Type) where
  | ok (a : α)
  | unsupported (why : Unsupported)
  | invalid (why : Invalid)
  /-- A read of `w` bytes at `o` is needed and this view does not hold it. -/
  | incomplete (o w : Nat)
  deriving DecidableEq, Repr

namespace Decoded

def toOption {α : Type} : Decoded α → Option α
  | .ok a => some a
  | _ => none

/-- The answer is final: no fuller view of the same bytes can change it (`Thms.runD_refines`). -/
def Final {α : Type} : Decoded α → Prop
  | .incomplete _ _ => False
  | _ => True

def isOk {α : Type} : Decoded α → Bool
  | .ok _ => true | _ => false
def isIncomplete {α : Type} : Decoded α → Bool
  | .incomplete _ _ => true | _ => false

end Decoded

/-! ## Runs -/

/-- **Run a reading program three-valued**: `Rd.fail` is `invalid rejected`, a read past the end
is `invalid (truncated o w)`, an unavailable read is `incomplete o w`. -/
def runD {α : Type} (r : ASrc) : Rd α → Decoded α
  | .pure a => .ok a
  | .fail => .invalid .rejected
  | .read o w k => match r o w with
    | .val n => runD r (k n)
    | .eof => .invalid (.truncated o w)
    | .unknown => .incomplete o w

/-- **The ELF parse specification, three-valued.** -/
def parseD (r : ASrc) : Decoded File := runD r read

/-- The identification bytes `e_ident[0..7]`: class, data encoding, version, OS ABI. -/
structure Ident where
  cls : Nat
  data : Nat
  version : Nat
  osABI : Nat
  deriving DecidableEq, Repr

/-- The identification, `none` when the magic is not `\x7fELF`. -/
def readIdent : Rd (Option Ident) := do
  let magic ← Rd.le 0 4
  if magic = 0x464c457f then
    let cls ← Rd.le 4 1
    let data ← Rd.le 5 1
    let version ← Rd.le 6 1
    let osABI ← Rd.le 7 1
    pure (some ⟨cls, data, version, osABI⟩)
  else pure none

/-- What the identification alone says, when it is not the supported ELF64 little-endian
`EV_CURRENT`: the answer `decode` gives instead of a bare rejection. -/
def Ident.verdict (i : Ident) : Option (Decoded File) :=
  if i.cls = 1 then some (.unsupported .elf32)
  else if i.cls ≠ 2 then some (.invalid .badIdent)
  else if i.data = 2 then some (.unsupported .bigEndian)
  else if i.data ≠ 1 then some (.invalid .badIdent)
  else if i.version ≠ 1 then some (.unsupported (.version i.version))
  else none

/-- The verdict on a rejection `why`, given what the identification bytes say. -/
def diagnose (why : Invalid) : Decoded (Option Ident) → Decoded File
  | .ok none => .invalid .notElf
  | .ok (some i) => i.verdict.getD (.invalid why)
  | .incomplete o w => .incomplete o w
  | _ => .invalid why

/-- **Decode an ELF file from a three-valued source.** The parse specification decides; when it
rejects the bytes (`invalid`), the identification says whether they are not ELF, an unsupported
ELF form, or a malformed supported one; when the view does not hold the identification, the
answer is `incomplete` (a fuller view could still say `unsupported`). -/
def decode (r : ASrc) : Decoded File :=
  match parseD r with
  | .invalid why => diagnose why (runD r readIdent)
  | d => d

end Silmaril.Elf.Decode
