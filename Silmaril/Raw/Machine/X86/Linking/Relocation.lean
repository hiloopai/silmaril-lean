module

public import Silmaril.Machine.Link.Defs

/-! # A checked x86-64 static RELA profile

Instantiates the shared ELF AST linker, with no PLT/GOT synthesis or relaxation.
`PLT32` is resolved directly to the unique non-interposable definition, just as
in a static link. Unsupported kinds and failed range/bounds checks are explicit
residuals. This is section linking, not an ELF executable writer or an ISA proof.
-/

@[expose] public section

namespace Silmaril.X86.Linking.Relocation

open Formats.ELF Formats.ELF.Link

def accepts (header : Header) : Bool :=
  header.machine == 62 && header.flags == 0 && header.osABI == 0 && header.abiVersion == 0

/-- The only kinds in this profile: 64, PC32, PLT32, 32 and 32S. -/
def supported (kind : Nat) : Prop := kind = 1 ∨ kind = 2 ∨ kind = 4 ∨ kind = 10 ∨ kind = 11

instance (kind : Nat) : Decidable (supported kind) := inferInstanceAs (Decidable (_ ∨ _))

def width (kind : Nat) : Nat := if kind = 1 then 8 else 4

/-- S+A-P for PC32/PLT32; S+A for the absolute kinds. -/
def value (r : ResolvedRelocation) : Int :=
  (r.symbolValue : Int) + r.addend - (if r.kind = 2 ∨ r.kind = 4 then (r.place : Int) else 0)

/-- This deliberately strict subset rejects absolute64 arithmetic wraparound.
32S accepts signed integer expressions; high unsigned representatives of negative
64-bit addresses are outside the profile. -/
def Fits (kind : Nat) (v : Int) : Prop :=
  if kind = 1 then 0 ≤ v ∧ v < 2 ^ 64
  else if kind = 10 then 0 ≤ v ∧ v < 2 ^ 32
  else -(2 ^ 31) ≤ v ∧ v < 2 ^ 31

instance (kind : Nat) (v : Int) : Decidable (Fits kind v) := by unfold Fits; infer_instance

def encodeLE : Nat → Nat → List (BitVec 8)
  | 0, _ => []
  | n + 1, v => BitVec.ofNat 8 v :: encodeLE n (v / 256)

def decodeLE : List (BitVec 8) → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * decodeLE rest

def encoded (kind : Nat) (v : Int) : Bytes :=
  (encodeLE (width kind) (v % (256 ^ width kind)).toNat).toArray

inductive Error where
  | unsupportedKind (kind : Nat)
  | invalidAddress
  | overflow (kind : Nat) (value : Int)
  | outOfBounds (offset width available : Nat)
  deriving DecidableEq, Repr

/-- A reusable diagnostic operation; the shared linker consumes its Option view. -/
def patch (r : ResolvedRelocation) (bytes : Bytes) : Except Error Patch :=
  if ¬ supported r.kind then .error (.unsupportedKind r.kind)
  else if ¬ (r.place < 2 ^ 64 ∧ r.symbolValue < 2 ^ 64) then .error .invalidAddress
  else if ¬ Fits r.kind (value r) then .error (.overflow r.kind (value r))
  else if ¬ (r.offset + width r.kind ≤ bytes.size) then
    .error (.outOfBounds r.offset (width r.kind) bytes.size)
  else .ok ⟨r.offset, encoded r.kind (value r)⟩

def relocate : Relocator := fun _ r bytes => (patch r bytes).toOption

/-- Reject selection/linkage mechanisms this static profile does not implement,
including unreferenced weak/COMMON/IFUNC/TLS symbols and section groups. -/
def staticObject (object : ObjectFile) : Bool :=
  object.symbols.all (fun symbol => symbol.binding ≤ 1 && symbol.kind ≤ 4 &&
    symbol.raw.other == 0 && (symbol.raw.sectionIndex < object.sections.length ||
      symbol.raw.sectionIndex == 0xfff1)) &&
  object.sections.all (fun part => part.header.kind != 17 &&
    (part.header.flags &&& 0x400) == 0)

/-- Checked linking of the shared section/symbol/relocation AST. -/
def link (objects : List ObjectFile) (layout : Layout) (absolute : AbsoluteSymbols := []) :
    Option (List LinkedSection) := do
  guard (objects.all staticObject)
  Formats.ELF.Link.link accepts relocate objects layout absolute

/-- The same operation on complete ET_REL byte inputs; parse failures remain failures. -/
def linkBytes (objects : List Bytes) (layout : Layout) (absolute : AbsoluteSymbols := []) :
    Option (List LinkedSection) := do
  let parsed ← objects.mapM readObject
  link parsed layout absolute

/-- Byte/AST parser certificates compose with linking without trusting the
external AST producer. A lossless concrete AST uses its serialized bytes here. -/
theorem linkBytes_of_parse {raw : List Bytes} {objects : List ObjectFile}
    (parsed : raw.mapM readObject = some objects) (layout : Layout)
    (absolute : AbsoluteSymbols) : linkBytes raw layout absolute = link objects layout absolute := by
  simp [linkBytes, parsed]

@[simp] theorem encodeLE_length (n v : Nat) : (encodeLE n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [encodeLE, ih]

/-- Byte encoding is exact for every in-range unsigned value, not just fixtures. -/
theorem decodeLE_encodeLE (n v : Nat) (fits : v < 256 ^ n) :
    decodeLE (encodeLE n v) = v := by
  induction n generalizing v with
  | zero =>
    have : v = 0 := by simpa using fits
    subst v
    rfl
  | succ n ih =>
    have quotient : v / 256 < 256 ^ n := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa [Nat.pow_succ, Nat.mul_comm] using fits
    simp only [encodeLE, decodeLE, BitVec.toNat_ofNat]
    rw [ih _ quotient]
    exact Nat.mod_add_div v 256

/-- Every emitted field has exactly its specified width. -/
@[simp] theorem encoded_size (kind : Nat) (v : Int) :
    (encoded kind v).size = width kind := by simp [encoded]

/-- The actual emitted bytes decode to the specified two's-complement residue. -/
theorem decodeLE_encoded (kind : Nat) (v : Int) :
    decodeLE (encoded kind v).toList = (v % (256 ^ width kind)).toNat := by
  simp only [encoded, List.toList_toArray]
  apply decodeLE_encodeLE
  apply (Int.toNat_lt' (Nat.pow_pos (by decide : 0 < 256))).2
  simpa using Int.emod_lt_of_pos v (Int.pow_pos (by decide : (0 : Int) < 256) :
    (0 : Int) < 256 ^ width kind)

/-- Unsupported relocation kinds cannot silently acquire bytes. -/
theorem unsupported (all : List ResolvedRelocation) (r : ResolvedRelocation)
    (bytes : Bytes) (h : ¬ supported r.kind) : relocate all r bytes = none := by
  simp [relocate, patch, h, Except.toOption]

/-- Successful patches have the prescribed offset, width, exact arithmetic
encoding, supported kind and signedness range, and stay within their section. -/
theorem patch_spec {r : ResolvedRelocation} {bytes : Bytes} {p : Patch}
    (success : patch r bytes = .ok p) :
    supported r.kind ∧ Fits r.kind (value r) ∧
      p.offset = r.offset ∧ p.bytes = encoded r.kind (value r) ∧
      p.bytes.size = width r.kind ∧ p.offset + p.bytes.size ≤ bytes.size := by
  unfold patch at success
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  split at success <;> simp_all
  subst p
  simp_all

theorem patch_decoded {r : ResolvedRelocation} {bytes : Bytes} {p : Patch}
    (success : patch r bytes = .ok p) :
    decodeLE p.bytes.toList = (value r % (256 ^ width r.kind)).toNat := by
  rw [(patch_spec success).2.2.2.1]
  exact decodeLE_encoded r.kind (value r)

/-- The shared linker's Option callback cannot hide a diagnostic failure. -/
theorem relocate_success {all : List ResolvedRelocation} {r : ResolvedRelocation}
    {bytes : Bytes} {p : Patch} (success : relocate all r bytes = some p) :
    patch r bytes = .ok p := by
  cases actual : patch r bytes with
  | error error => simp [relocate, actual, Except.toOption] at success
  | ok candidate =>
    have equal : candidate = p := by simpa [relocate, actual, Except.toOption] using success
    simp [equal]

/-- Range boundaries and error classifications are exercised independently of ELF parsing. -/
example : patch ⟨⟨0, 1⟩, 0, 0x1000, 0x1100, 4, -4⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0xfc, 0, 0, 0]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0x80000000, 2, 0⟩ #[0, 0, 0, 0] =
    .error (.overflow 2 0x80000000) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0x80000000, 0, 2, 0⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0, 0, 0, 0x80]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 11, -1⟩ #[0, 0, 0, 0] =
    .ok ⟨0, #[0xff, 0xff, 0xff, 0xff]⟩ := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 10, -1⟩ #[0, 0, 0, 0] =
    .error (.overflow 10 (-1)) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 1, -1⟩ #[0, 0, 0, 0, 0, 0, 0, 0] =
    .error (.overflow 1 (-1)) := by rfl
example : patch ⟨⟨0, 1⟩, 1, 0, 0, 1, 0⟩ #[0, 0, 0, 0] =
    .error (.outOfBounds 1 8 4) := by rfl
example : patch ⟨⟨0, 1⟩, 0, 0, 0, 9, 0⟩ #[] =
    .error (.unsupportedKind 9) := by rfl

end Silmaril.X86.Linking.Relocation
