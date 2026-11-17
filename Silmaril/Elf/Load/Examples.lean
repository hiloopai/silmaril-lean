module

public import Silmaril.Elf.Load.Thms
public import Silmaril.Elf.Image.Thms

/-! # The boundaries of `ReadOnlyAt` and `ImageLoaded`, on small parses

Three synthetic file metadata values (`File` literals, two `PT_LOAD`s or one, no sections and so
no relocations), each closed by `decide +kernel` or a short proof:

* **First match is not uniqueness** (`overlapA`): a read-only segment and a writable one map
  the same address. `roSeg`'s first match finds the read-only one (`overlap_first`), but the
  address is ambiguous (`overlap_ambiguous`: `File.resolve` lists the writable segment too), so
  `ReadOnlyAt` alone does not say the bytes are only mapped read-only. `Load.readOnlyAt_unique`
  needs `Unambiguous` for that.
* **`ImageLoaded` can be unsatisfiable** (`conflictA`): two segments map the same address from
  file bytes that differ; no memory holds both (`conflict_no_memory`), so every statement
  conditional on `ImageLoaded` is vacuous for that file. Such statements are conditional, never
  universal.
* **`ImageLoaded` is satisfiable, and the read-back is not vacuous** (`oneA`): one segment of two
  file bytes and one zero-filled byte; the memory `oneMem` holds the image (`one_loaded`), and
  `readWith_of_segBytes` then reads the file's bytes back from it (`one_read`).
-/

@[expose] public section

namespace Silmaril.Elf.Load.Examples

open Silmaril.Elf.Image
open Silmaril.Formats.ELF (Header ProgramHeader)
open Silmaril.Process (Memory Region)
open Silmaril.X86.Link (Blob)

/-- An `ET_EXEC` x86-64 header with `n` program headers and no sections. -/
def hdr (n : Nat) : Header := ⟨0, 0, 2, 62, 1, 0x1000, 64, 0, 0, 64, 56, n, 64, 0, 0⟩

/-- Metadata with the given program headers and nothing else. -/
def withPhdrs (phs : List ProgramHeader) : File :=
  ⟨hdr phs.length, phs, [], [], none, [], none, none⟩

/-! ## First match is not uniqueness -/

/-- A readable, non-writable `PT_LOAD` of `[0x1000, 0x1010)`. -/
def roPh : ProgramHeader := ⟨PT_LOAD, 4, 0x100, 0x1000, 0x1000, 0x10, 0x10, 0x1000⟩
/-- A writable `PT_LOAD` over the same addresses. -/
def rwPh : ProgramHeader := ⟨PT_LOAD, 6, 0x200, 0x1000, 0x1000, 0x10, 0x10, 0x1000⟩

def overlapA : File := withPhdrs [roPh, rwPh]

theorem overlap_first : overlapA.phdrs.find? (roSeg 0x1000 4) = some roPh := by decide +kernel

theorem overlap_ambiguous :
    overlapA.resolve 0x1000 = .ambiguous [(0, .file 0x100), (1, .file 0x200)] ∧
      ¬ Unambiguous overlapA 0x1000 4 := by
  decide +kernel

/-! ## An unsatisfiable `ImageLoaded` -/

/-- Two segments mapping `0x1000` from file offsets `0` and `1`. -/
def conflictA : File := withPhdrs [⟨PT_LOAD, 4, 0, 0x1000, 0x1000, 1, 1, 0x1000⟩,
  ⟨PT_LOAD, 4, 1, 0x1000, 0x1000, 1, 1, 0x1000⟩]

/-- A two-byte file whose bytes differ (`0x01`, `0x02`). -/
def conflictF : Blob := ⟨0x0201, 2⟩

/-- **No memory holds the image of `conflictF` at any base.** -/
theorem conflict_no_memory (base : Nat) (mem : Memory) : ¬ ImageLoaded conflictF conflictA base mem := by
  intro h
  have hu : Untouched conflictA 0x1000 1 := by decide +kernel
  have h0 := (h 0x1000 0 0 hu).1 (by decide +kernel)
  have h1 := (h 0x1000 1 1 hu).1 (by decide +kernel)
  rw [h0] at h1
  exact absurd (Option.some_inj.mp h1) (by decide +kernel)

/-! ## A satisfiable `ImageLoaded`, read back -/

/-- One segment: two file bytes at `0x1000` (file offset `0`), one zero-filled byte at `0x1002`. -/
def onePh : ProgramHeader := ⟨PT_LOAD, 5, 0, 0x1000, 0x1000, 2, 3, 0x1000⟩
def oneA : File := withPhdrs [onePh]

/-- The file: `0xc3` (`ret`), `0x90` (`nop`). -/
def oneF : Blob := ⟨0x90c3, 2⟩

/-- A memory with every address readable, writable and executable, holding the image at base 0. -/
def oneMem : Memory :=
  ⟨[⟨0, 2 ^ 64, ⟨true, true, true⟩⟩], Memory.install ∅ 0x1000 [0xc3, 0x90, 0]⟩

theorem onePh_origin {u : Nat} {x : Origin} (h : segOrigin onePh u = some x) :
    (u = 0x1000 ∧ x = .file 0) ∨ (u = 0x1001 ∧ x = .file 1) ∨ (u = 0x1002 ∧ x = .zeroFill) := by
  unfold segOrigin at h
  split_ifs at h with h1 h2 h3
  · cases h
    have hlo : 0x1000 ≤ u := h1.2
    have hhi : u < 0x1000 + 2 := h2
    by_cases hu : u = 0x1000
    · left; subst hu; exact ⟨rfl, rfl⟩
    · right; left
      obtain rfl : u = 0x1001 := by omega
      exact ⟨rfl, rfl⟩
  · cases h
    have hlo : 0x1000 ≤ u := h1.2
    have hfs : ¬ u < 0x1000 + 2 := h2
    have hms : u < 0x1000 + 3 := h3
    right; right; exact ⟨by omega, rfl⟩

theorem one_loaded : ImageLoaded oneF oneA 0 oneMem := by
  intro u i o _
  have seg : ∀ {x : Origin}, (i, x) ∈ oneA.origins u →
      (u = 0x1000 ∧ x = .file 0) ∨ (u = 0x1001 ∧ x = .file 1) ∨ (u = 0x1002 ∧ x = .zeroFill) := by
    intro x hx
    obtain ⟨ph, hph, hs⟩ := mem_origins.mp hx
    cases i with
    | zero =>
      simp only [oneA, withPhdrs, List.getElem?_cons_zero, Option.some.injEq] at hph
      subst hph
      exact onePh_origin hs
    | succ j => simp [oneA, withPhdrs] at hph
  have get : ∀ k (hk : k < 3), oneMem.bytes.get? (0x1000 + k) = some ([0xc3, 0x90, 0] : List (BitVec 8))[k] :=
    fun k hk => Memory.install_get _ _ _ _ hk
  constructor
  · intro hx
    rcases seg hx with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨-, h⟩
    · cases h; rw [Nat.zero_add, show (0x1000 : Nat) = 0x1000 + 0 from rfl, get 0 (by decide)]; decide +kernel
    · cases h; rw [Nat.zero_add, show (0x1001 : Nat) = 0x1000 + 1 from rfl, get 1 (by decide)]; decide +kernel
    · cases h
  · intro hx
    rcases seg hx with ⟨-, h⟩ | ⟨-, h⟩ | ⟨rfl, -⟩
    · cases h
    · cases h
    · rw [Nat.zero_add, show (0x1002 : Nat) = 0x1000 + 2 from rfl, get 2 (by decide)]; rfl

/-- **The read-back, on a memory that holds the image**: the two file bytes, from `0x1000`. -/
theorem one_read : oneMem.readWith .execute 0x1000 2 = some [0xc3, 0x90] := by
  have hs : SegBytes oneF oneA 0 0x1000 0 [0xc3, 0x90] :=
    ⟨⟨onePh, rfl, rfl, by decide, by decide, rfl⟩, by unfold FileBytes; decide +kernel⟩
  exact readWith_of_segBytes one_loaded hs (by decide +kernel) (by decide +kernel)

end Silmaril.Elf.Load.Examples
