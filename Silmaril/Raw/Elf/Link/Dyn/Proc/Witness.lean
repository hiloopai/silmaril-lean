module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Run
public import Silmaril.Elf.Link.Dyn.Image.Thms

/-! # Building non-vacuity witnesses (generic)

The pieces of Hello's `gcc_nonvacuous`, for any executable and any contract table:

* **files** (`blobOf`): a library file holding exactly the pinned chunks (zeros elsewhere), so
  that `ChunksOf (blobOf cs) cs` is a kernel computation;
* **the loaded image** (`imgOf`, `tableOk`, `imageOk_of_tableOk`): the bytes the loader relation
  asks for, and a single Boolean check (per byte: the segment, a value in the model, the
  permissions in the memory) from which `ImageOk` follows once the memory holds `imgOf` at the base;
* **a world from a contract table** (`namedOf`, `namedOf_eq`, `namedOf_total`): the `named` field
  looking contracts up by name, the contract of each entry, and the totality
  `hN` of `proc_progressG` from each entry's totality.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc.Witness

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Link (Blob)
open Silmaril.X86.RelIsa (Res)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc

/-! ## Files -/

/-- A file holding the chunks, zeros elsewhere. -/
def blobOf (cs : List Chunk) : Blob :=
  ⟨cs.foldr (fun c n => n ||| ((c.n % 2 ^ (8 * c.len)) <<< (8 * c.off))) 0,
    (cs.map fun c => c.off + c.len).foldr max 0⟩

/-! ## The loaded image -/

section Image

variable (f : Blob) (i : Elf.DynInfo) (T : List (Nat × Option Word))

/-- The `PT_LOAD` headers. -/
def loads : List Elf.Phdr := i.phs.filter (·.kind == 1)

/-- The segment holding `v`. -/
def segOf (v : Nat) : Option Elf.Phdr := (loads i).find? fun ph => ph.vaddr ≤ v && v < ph.vaddr + ph.memsz

/-- The byte the loader relation asks for at `v` (0 where it asks for none). -/
def byteAt (v : Nat) : Byte :=
  match segOf i v with
  | some ph => match expectedByte f T ph v with
    | some (some x) => x
    | _ => 0
  | none => 0

/-- The image: `N` bytes from the base. -/
def imgOf (N : Nat) : List Byte := (List.range N).map (byteAt f i T)

theorem imgOf_length (N : Nat) : (imgOf f i T N).length = N := by simp [imgOf]

theorem imgOf_get {N v : Nat} (hv : v < N) : (imgOf f i T N)[v]? = some (byteAt f i T v) := by
  simp [imgOf, hv]

/-- **The per-byte check** of byte `k` of segment `ph`: in that segment alone, a value in the
model, and the segment's permissions in a memory with the regions `regs` (base `b`; only the
regions matter, so the check does not evaluate any bytes). -/
def byteOk (b : Word) (regs : List Region) (ph : Elf.Phdr) (k : Nat) : Bool :=
  let mem : Memory := ⟨regs, ∅⟩
  let v := ph.vaddr + k
  segOf i v == some ph && (expectedByte f T ph v).isSome &&
  mem.permits .read (b.toNat + v) == (ph.flags / 4 % 2 == 1) &&
  mem.permits .execute (b.toNat + v) == (ph.flags % 2 == 1) &&
  mem.permits .write (b.toNat + v) == (ph.flags / 2 % 2 == 1 && !inRelro i v)

/-- The check of the whole image: every `PT_LOAD` ends below `N` and all its bytes pass. -/
def tableOk (b : Word) (regs : List Region) (N : Nat) : Bool :=
  (loads i).all fun ph => decide (ph.vaddr + ph.memsz ≤ N) && (List.range ph.memsz).all (byteOk f i T b regs ph)

/-- A range check, split in blocks of `c` (each block a separate kernel computation). -/
theorem all_range_of_blocks {p : Nat → Bool} {n c m : Nat} (hn : n ≤ c * m)
    (h : ∀ j, j < m → (List.range' (c * j) c).all (fun k => !decide (k < n) || p k) = true) :
    (List.range n).all p = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hn; omega
    · exact h0
  have hj : k / c < m := by
    rw [Nat.div_lt_iff_lt_mul hc]; rw [Nat.mul_comm] at hn; omega
  have := List.all_eq_true.mp (h (k / c) hj) k (by
    rw [List.mem_range']
    refine ⟨k % c, Nat.mod_lt _ hc, ?_⟩
    have := Nat.div_add_mod k c
    simp; omega)
  simpa [hk] using this

/-- **`ImageOk` from the check**, for a memory holding `imgOf` at the base. -/
theorem imageOk_of_tableOk {b : Word} {mem : Memory} {N : Nat} {regs : List Region}
    (hb : b.toNat + N < 2 ^ 64) (hr : mem.regions = regs)
    (hget : ∀ v, v < N → mem.bytes.get? (b.toNat + v) = some (byteAt f i T v))
    (h : tableOk f i T b regs N = true) : ImageOk ⟨f, b⟩ i T mem := by
  have hp : ∀ acc a, mem.permits acc a = (⟨regs, ∅⟩ : Memory).permits acc a := by
    intro acc a; simp only [Memory.permits, hr]
  intro ph hph hk v h1 h2
  have hl : ph ∈ loads i := List.mem_filter.mpr ⟨hph, by simp [hk]⟩
  have hall := List.all_eq_true.mp h ph hl
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨hlt, hall⟩ := hall
  have ht := List.all_eq_true.mp hall (v - ph.vaddr) (List.mem_range.mpr (by omega))
  simp only [byteOk, Nat.add_sub_cancel' h1, Bool.and_eq_true, beq_iff_eq] at ht
  obtain ⟨⟨⟨⟨hseg, hsome⟩, hr'⟩, hx⟩, hw⟩ := ht
  have haddr : (b + BitVec.ofNat 64 v).toNat = b.toNat + v := addr_toNat (by omega)
  dsimp only
  rw [haddr, hp, hp, hp]
  refine ⟨by omega, hr', hx, hw, ?_⟩
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨e, he, by rw [hget v (by omega)]; rfl, fun x hx' => ?_⟩
  rw [hget v (by omega)]
  subst hx'
  simp [byteAt, hseg, he]

end Image

/-! ## A world from a contract table -/

/-- A contract table: names and contracts. -/
abbrev Table := List (Name × (PState → Res PState → Prop))

/-- The `named` field of a world with the table `tb`: the first entry of that name (a name without
an entry stops, as by default). -/
def namedOf (tb : Table) (n : Name) : PState → Res PState → Prop :=
  match tb.find? (·.1 == n) with
  | some e => e.2
  | none => fun _ r => r = .stop

theorem namedOf_eq {tb : Table} {n : Name} {c : PState → Res PState → Prop}
    (h : tb.find? (·.1 == n) = some (n, c)) : namedOf tb n = c := by
  simp [namedOf, h]

/-- **Totality of a table-world's contracts**, from each entry's. -/
theorem namedOf_total {tb : Table} (h : ∀ e ∈ tb, ∀ s, ∃ r, e.2 s r) (n : Name) (s : PState) :
    ∃ r, namedOf tb n s r := by
  unfold namedOf
  cases hf : tb.find? (·.1 == n) with
  | none => exact ⟨.stop, rfl⟩
  | some e => exact h e (List.mem_of_find?_eq_some hf) s

end Silmaril.Elf.Link.Dyn.Proc.Witness
