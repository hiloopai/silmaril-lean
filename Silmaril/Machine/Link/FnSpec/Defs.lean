module

public import Silmaril.Machine.Link.Contract.Defs
public import Silmaril.Machine.Link.Validate.Defs
public import Silmaril.Machine.X86.Sep.SysV.Defs
public import Silmaril.Process.LPS.MemImage
public import Silmaril.Machine.X86.Safe.Defs

/-! # The System V `FnSpec` logic for `link_compose`

The instance of the spec-agnostic `Contract.Logic` by the System V
separation-logic specs `FnSpec` of the separation-logic layer (`Silmaril.Machine.X86.Sep.SysV`), over the open x86
machine `Silmaril.Machine.X86.Open.step` (where `ret` is an ordinary pop and jump, and "returned"
is the postcondition template `rip ↦ ret ∗ rsp ↦ sp + 8 ∗ …`).

**generic in the machine.** `SafeN`, `STriple` (and `Progress`) are the generic
`Silmaril.Machine.X86.Safe` definitions at `Open.step`. `SafeOn step` is the safety predicate on
any machine `step`; `Safe := SafeOn Open.step`. The logic `logicOn step`, its laws and the
link bridges (`validated_compose`, `tu_sat_of_code`, `scall_rule`) hold for every `step` with
`[ExtendsOpen step]`, in particular `Open9.step` (and `JumpTable.step = Open9.step`).

* `SafeN Q n m`: **step-indexed partial correctness.** Within `n` open steps from `m`, the
  machine does not get stuck before it reaches a state satisfying `Q`. (`SafeN Q (n+1) m` is
  `Q m`, or one step to some `m'` with `SafeN Q n m'`.) On the deterministic open machine,
  `∀ n, SafeN Q n m` says: the run from `m` is infinite, or it passes through a state
  satisfying `Q` before it stops. It says nothing after that state.
* `STriple n P Q`: the frame-quantified, step-indexed triple: for every frame `F` and every
  state whose total fragment splits as `P ∗ F`, `SafeN` towards `Q ∗ F`.
* `Code D bs`: ownership of the code bytes. Exactly the byte locations `D`, each holding
  `bs a` with an **executable** permission. A triple keeps `Code D bs` in its pre- and
  postcondition, so code is returned unchanged.
* `Covers ctx D bs`: `D`/`bs` agree with every byte of an executable section of `ctx`.
* `Safe n a S ctx`: for every code region covering `ctx`, every logical argument `x`, every
  System V entry stack pointer `sp` (`rsp ≡ 8 mod 16`, room for the budget) and return address
  `ret`: `STriple n (Code ∗ SysVPre S x a sp ret) (Code ∗ SysVPost S x sp ret)`.

The logic itself (`logic : Logic FnSpec`, with `Sub := FnSpec.Sub`) and its laws are in
`Silmaril.Machine.Link.FnSpec.Thms`.

**Code and data (F3; REVIEW M14).** `Code` covers exactly the bytes of the image's
*executable* sections (`ContainsX`, through the flag-aware `Contract.Extends`), each with an
executable permission. Bytes of read-only (`.rodata`, flags A) and writable (`.data`,
`.bss`, flags AW) sections are **not** part of `Code`: in a loaded executable they are in the
frame, where a function's precondition claims them with `bytesPtRO`/`bytesPt`
(`Silmaril.Proofs.Machine.Link.FnSpec.data_loaded` gives `DataPt` for every data section of a
validated link). Earlier rounds required every allocated section to be executable.

**Loaded executables.** `ImageLoaded image m`: the machine state `m` holds every byte the
loader image `image` (`Silmaril.Process.LPS.Image`, from the checked `ELFImage.parse`) places,
with an executable permission wherever the segment is executable. This is our reading of
"the program is loaded", not a model of the Linux loader.
-/

@[expose] public section

namespace Silmaril.Machine.Link.FnSpec

open Silmaril.X86 (MState Word Byte)
open Silmaril.Process (addressLimit)
open Silmaril.Machine.X86.Sep
open Silmaril.Machine.Link.Unit (Contains)

/-- **Step-indexed partial correctness** on the open machine: the generic
`Silmaril.Machine.X86.Safe.SafeN` at `Open.step` (the definition moved to the
`Machine/X86/Safe` topic). -/
abbrev SafeN (Q : MState → Prop) : Nat → MState → Prop :=
  Silmaril.Machine.X86.Safe.SafeN Silmaril.Machine.X86.Open.step Q

/-- **A step-indexed triple** on the open machine, frame built in: the generic
`Silmaril.Machine.X86.Safe.STriple` at `Open.step`. -/
abbrev STriple (n : Nat) (P Q : SProp) : Prop :=
  Silmaril.Machine.X86.Safe.STriple Silmaril.Machine.X86.Open.step n P Q

/-- Exactly the byte locations `D`, holding `bs`, executable. -/
def Code (D : Nat → Prop) (bs : Nat → Byte) : SProp := fun h =>
  (∀ a, D a → a < addressLimit ∧ ∃ p, EX p ∧ h (.mem a) = some (.cell ⟨some (bs a), p⟩)) ∧
    ∀ l, (∀ a, D a → l ≠ .mem a) → h l = none

/-- `ctx` holds byte `b` at `a` in an executable (`SHF_EXECINSTR`) section. -/
def ContainsX (ctx : Contract.Image) (a : Nat) (b : Byte) : Prop :=
  ∃ f, f &&& 4 ≠ 0 ∧ Contract.ContainsF ctx a b f

/-- `D`/`bs` hold every byte of the image's executable sections. -/
def Covers (ctx : Contract.Image) (D : Nat → Prop) (bs : Nat → Byte) : Prop :=
  ∀ a b, ContainsX ctx a b → D a ∧ bs a = b

/-- **The safety predicate of the `FnSpec` logic on the machine `step`** (any machine; the
laws are proved for every `step`, the bridges from the separation-logic layer's triples for every `step` that
extends the open machine). -/
def SafeOn (step : MState → Option MState) (n a : Nat) (S : FnSpec) (ctx : Contract.Image) :
    Prop :=
  ∀ (D : Nat → Prop) (bs : Nat → Byte), Covers ctx D bs →
    ∀ (x : S.Arg) (sp ret : Word), FnSpec.EntryAligned sp → S.stack ≤ sp.toNat →
      Silmaril.Machine.X86.Safe.STriple step n (Code D bs ∗ S.SysVPre x (BitVec.ofNat 64 a) sp ret)
        (Code D bs ∗ S.SysVPost x sp ret)

/-- **The safety predicate of the `FnSpec` logic** on the open machine. -/
abbrev Safe : Nat → Nat → FnSpec → Contract.Image → Prop :=
  SafeOn Silmaril.Machine.X86.Open.step

/-- A spec nothing can call: its precondition is unsatisfiable. Used for exports that are
present in an object (and so must be declared, `AbiCompatible`) but not verified. -/
def unverified : FnSpec where
  Arg := Unit
  args _ := []
  stack := 0
  pre _ := fun _ => False
  post _ _ := emp

/-! ## Loaded executables -/

/-- The machine holds the loader image: every byte every segment places, executable where
the segment is. -/
def ImageLoaded (image : Silmaril.Process.LPS.Image) (m : MState) : Prop :=
  ∀ seg ∈ image.segments, ∀ i < seg.size, ∀ b, seg.bytes[i]? = some b →
    m.memory.bytes.get? (seg.base + i) = some b ∧
      (seg.executable = true → m.memory.permits .execute (seg.base + i) = true)

/-- The code locations of an image: the bytes of its executable sections. -/
def Dom (ctx : Contract.Image) (a : Nat) : Prop := ∃ b, ContainsX ctx a b

/-- The byte a machine holds at `a` (`0` if unbacked). -/
def byteOf (m : MState) (a : Nat) : Byte := (m.memory.bytes.get? a).getD 0

open Classical in
/-- The part of a fragment on the byte locations `D`. -/
noncomputable def onBytes (D : Nat → Prop) (h : Frag) : Frag
  | .mem a => if D a then h (.mem a) else none
  | _ => none

open Classical in
/-- The part of a fragment off the byte locations `D`. -/
noncomputable def offBytes (D : Nat → Prop) (h : Frag) : Frag
  | .mem a => if D a then none else h (.mem a)
  | l => h l

/-! ## Data sections (F3) -/

open Silmaril.Process (Permissions) in
/-- Exactly the byte locations `D`, holding `bs`, each with a permission satisfying
`need a`. (`Code D bs` is the case `need _ = EX`.) -/
def Region (need : Nat → Silmaril.Process.Permissions → Prop) (D : Nat → Prop) (bs : Nat → Byte) : SProp :=
  fun h => (∀ a, D a → a < addressLimit ∧ ∃ p, need a p ∧ h (.mem a) = some (.cell ⟨some (bs a), p⟩)) ∧
    ∀ l, (∀ a, D a → l ≠ .mem a) → h l = none

/-- `ctx` holds byte `b` at `a` **in memory**, in a section with flags `f`: the section's data
or its zero fill up to `memorySize` (`Validate.expected`). Unlike `Contract.ContainsF`, this
covers `.bss` (`SHT_NOBITS`, empty data) and the zero tail of a section. -/
def ContainsM (ctx : Contract.Image) (a : Nat) (b : Byte) (f : Nat) : Prop :=
  ∃ s ∈ ctx, s.flags = f ∧ s.address ≤ a ∧ (Validate.expected s)[a - s.address]? = some b

/-- The data locations of an image: in-memory bytes (data and zero fill) of non-executable
sections that are not code. -/
def DataDom (ctx : Contract.Image) (a : Nat) : Prop :=
  (∃ b f, f &&& 4 = 0 ∧ ContainsM ctx a b f) ∧ ¬ Dom ctx a

/-- Data permissions: readable, and writable where a writable (`SHF_WRITE`) section holds the
byte. -/
def DataNeed (ctx : Contract.Image) (a : Nat) (p : Silmaril.Process.Permissions) : Prop :=
  RO p ∧ ∀ b f, ContainsM ctx a b f → f &&& 1 ≠ 0 → RW p

/-- **Ownership of an image's data sections** (`.rodata`, `.data`, `.bss`): exactly the data
locations, holding `bs`, readable, and writable where the section is. -/
def DataPt (ctx : Contract.Image) (bs : Nat → Byte) : SProp :=
  Region (DataNeed ctx) (DataDom ctx) bs

/-- The machine grants the loader image's read and write permissions. -/
def ImagePerms (image : Silmaril.Process.LPS.Image) (m : MState) : Prop :=
  ∀ seg ∈ image.segments, ∀ i < seg.size,
    (seg.readable = true → m.memory.permits .read (seg.base + i) = true) ∧
    (seg.writable = true → m.memory.permits .write (seg.base + i) = true)

end Silmaril.Machine.Link.FnSpec
