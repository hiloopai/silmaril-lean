module

public import Silmaril.X86.Machine

/-!
# Shallow separation logic over x86 machine fragments

The assertion language of the compositional ELF work (DESIGN §3, WP4). It is a shallow
embedding: an assertion is a predicate on partial machine states (`Frag`), separating
conjunction splits a fragment into two fragments with disjoint domains, and there is no
step index, no ghost state and no Iris.

* `Loc`: the observable locations of an `MState` — the sixteen registers, `rip`, the
  arithmetic flags (one location for the whole `Flags` record), every byte address, and the
  mapping list `regions`. The FS base (`State.fsBase`) is **not** a location: no assertion
  can mention it, and a triple says nothing about it.
* `Cell`: what a byte address holds — the backing byte, if any, and the permissions the
  mappings grant there (`Memory.permits`). Permissions are part of the cell, so owning a
  byte means knowing whether it may be read, written or executed.
* `Frag`: a partial map from locations to values; `MState.toFrag` is the total fragment of
  a machine state.
* `SProp`: assertions. Connectives: `sep` (`P ∗ Q`), `emp`, `spure` (`⌜φ⌝`), `sexists`,
  `sand`, `wand`; entailment `Entails` (`P ⊢ Q`).
* Points-to atoms: `regPt`, `ripPt`, `flagsPt`/`flagsAny`, `regionsPt`, and for memory
  `byteAt` with a permission requirement: `bytePt` (readable and writable), `bytePtRO`
  (readable), `codeByte` (executable), their lists `bytesPt`, `bytesPtRO`, `codePt`, the
  eight-byte little-endian `wordPt`, and `byteAny`/`blockAny` (owned, readable and
  writable, contents unknown and possibly unbacked: a stack budget).

Every byte atom carries `address < 2 ^ 64`, so a non-empty list atom gives a non-wrapping
access span. Algebraic laws and the bridge from atoms to `Memory.readBytes` and friends are
in `Sep/Thms.lean`; triples are in `Sep/Spec`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Sep

open Silmaril.X86 (State MState Word Byte Reg Flags)
open Silmaril.Process (Memory Region Permissions Access addressLimit)

/-- The observable locations of a machine state. -/
inductive Loc where
  | reg (r : Reg)
  | rip
  | flags
  | mem (address : Nat)
  | regions
  deriving DecidableEq

/-- The contents of one byte address: its backing byte and the permissions there. -/
structure Cell where
  byte : Option Byte
  perms : Permissions
  deriving DecidableEq

/-- Location values. A well-formed fragment stores a `word` at registers and `rip`, `flags`
at `flags`, a `cell` at byte addresses and `regions` at `regions`; `toFrag` does. -/
inductive Val where
  | word (w : Word)
  | flags (f : Flags)
  | cell (c : Cell)
  | regions (rs : List Region)
  deriving DecidableEq

/-- A partial machine state. -/
abbrev Frag := Loc → Option Val

namespace Frag

/-- The empty fragment. -/
def empty : Frag := fun _ => none

/-- The fragment with one location. -/
def single (l : Loc) (v : Val) : Frag := fun l' => if l' = l then some v else none

/-- Disjoint domains. -/
def Disjoint (h₁ h₂ : Frag) : Prop := ∀ l, h₁ l = none ∨ h₂ l = none

/-- Union, left-biased (only used on disjoint fragments). -/
def union (h₁ h₂ : Frag) : Frag := fun l =>
  match h₁ l with
  | some v => some v
  | none => h₂ l

/-- `h` is contained in `s`: every location of `h` holds the same value in `s`. -/
def Le (h s : Frag) : Prop := ∀ l v, h l = some v → s l = some v

/-- The fragment with the domain of `h` and the values of `s`. -/
def reval (h s : Frag) : Frag := fun l => if (h l).isSome then s l else none

/-- The part of `s` outside the domain of `h`. -/
def diff (s h : Frag) : Frag := fun l => if (h l).isSome then none else s l

end Frag

/-- Assertions on fragments. -/
abbrev SProp := Frag → Prop

/-- Separating conjunction. -/
def sep (P Q : SProp) : SProp := fun h =>
  ∃ h₁ h₂, Frag.Disjoint h₁ h₂ ∧ h = Frag.union h₁ h₂ ∧ P h₁ ∧ Q h₂

/-- The empty heap. -/
def emp : SProp := fun h => h = Frag.empty

/-- A pure fact, owning nothing. -/
def spure (φ : Prop) : SProp := fun h => h = Frag.empty ∧ φ

/-- Existential quantification. -/
def sexists {α : Sort _} (P : α → SProp) : SProp := fun h => ∃ x, P x h

/-- Non-separating conjunction. -/
def sand (P Q : SProp) : SProp := fun h => P h ∧ Q h

/-- Magic wand. -/
def wand (P Q : SProp) : SProp := fun h =>
  ∀ h', Frag.Disjoint h h' → P h' → Q (Frag.union h h')

/-- Entailment. -/
def Entails (P Q : SProp) : Prop := ∀ h, P h → Q h

@[inherit_doc] scoped infixr:35 " ∗ " => sep
@[inherit_doc] scoped infix:25 " ⊢ₛ " => Entails
@[inherit_doc] scoped notation "⌜" φ "⌝" => spure φ
@[inherit_doc] scoped infixr:30 " -∗ " => wand

/-! ## Points-to atoms -/

/-- Register `r` holds `v`. -/
def regPt (r : Reg) (v : Word) : SProp := fun h => h = Frag.single (.reg r) (.word v)

/-- Register `r` is owned, with an unknown value. -/
def regAny (r : Reg) : SProp := sexists (regPt r)

/-- The program counter holds `v`. -/
def ripPt (v : Word) : SProp := fun h => h = Frag.single .rip (.word v)

/-- The arithmetic flags hold `f`. -/
def flagsPt (f : Flags) : SProp := fun h => h = Frag.single .flags (.flags f)

/-- The arithmetic flags are owned, with unknown values. -/
def flagsAny : SProp := sexists flagsPt

/-- The mapping list is `rs`. -/
def regionsPt (rs : List Region) : SProp := fun h => h = Frag.single .regions (.regions rs)

/-- Byte address `a` (below `2 ^ 64`) holds `b`, with permissions satisfying `need`. -/
def byteAt (need : Permissions → Prop) (a : Nat) (b : Byte) : SProp := fun h =>
  a < addressLimit ∧ ∃ p, need p ∧ h = Frag.single (.mem a) (.cell ⟨some b, p⟩)

/-- Readable and writable. -/
def RW (p : Permissions) : Prop := p.read = true ∧ p.write = true
/-- Readable. -/
def RO (p : Permissions) : Prop := p.read = true
/-- Executable. -/
def EX (p : Permissions) : Prop := p.execute = true

/-- A readable, writable byte. -/
def bytePt (a : Nat) (b : Byte) : SProp := byteAt RW a b
/-- A readable byte. -/
def bytePtRO (a : Nat) (b : Byte) : SProp := byteAt RO a b
/-- An executable byte (code). -/
def codeByte (a : Nat) (b : Byte) : SProp := byteAt EX a b

/-- Consecutive bytes from `a`. -/
def bytesAt (need : Permissions → Prop) : Nat → List Byte → SProp
  | _, [] => emp
  | a, b :: bs => byteAt need a b ∗ bytesAt need (a + 1) bs

/-- Readable, writable bytes. -/
def bytesPt (a : Nat) (bs : List Byte) : SProp := bytesAt RW a bs
/-- Readable bytes. -/
def bytesPtRO (a : Nat) (bs : List Byte) : SProp := bytesAt RO a bs
/-- Code bytes: executable, read-only by convention (a triple returns them unchanged). -/
def codePt (a : Nat) (bs : List Byte) : SProp := bytesAt EX a bs

/-- An eight-byte little-endian word. -/
def wordPt (a : Nat) (w : Word) : SProp := bytesPt a (Silmaril.Machine.LittleEndian.encodeWords [w])

/-- A readable, writable byte address (below `2 ^ 64`) with unknown, possibly unbacked,
contents. -/
def byteAny (a : Nat) : SProp := fun h =>
  a < addressLimit ∧ ∃ c : Cell, RW c.perms ∧ h = Frag.single (.mem a) (.cell c)

/-- `n` readable, writable byte addresses from `a`, contents unknown: a stack budget or an
output buffer before it is written. -/
def blockAny : Nat → Nat → SProp
  | _, 0 => emp
  | a, n + 1 => byteAny a ∗ blockAny (a + 1) n

/-! ## Machine states as fragments -/

/-- The permissions at a byte address. -/
def permsAt (memory : Memory) (a : Nat) : Permissions :=
  ⟨memory.permits .read a, memory.permits .write a, memory.permits .execute a⟩

/-- The total fragment of a machine state (everything but `fsBase`). -/
def toFrag (m : MState) : Frag
  | .reg r => some (.word (m.core.read r))
  | .rip => some (.word m.core.rip)
  | .flags => some (.flags m.core.flags)
  | .mem a => some (.cell ⟨m.memory.bytes.get? a, permsAt m.memory a⟩)
  | .regions => some (.regions m.memory.regions)

/-- An assertion holds of a part of the machine state. -/
def Holds (P : SProp) (m : MState) : Prop := ∃ h, P h ∧ Frag.Le h (toFrag m)

end Silmaril.Machine.X86.Sep
