module

public import Silmaril.Elf.Abi.LeafArith.Defs
public import Silmaril.Elf.Staged.Pinned.LeafArith.Thms
public import Silmaril.Elf.Staged.Reader.Thms
public import Silmaril.Machine.Abi.Conformance.LeafArith.Thms
public import Silmaril.Elf.Abi.Thms

/-! # ABI conformance rows of `leaf-arith`: proofs

The file facts are kernel reads on the file's kernel bytes (the per-part reader's `parses` and
`codeAt_of_kbytes`) and computations on the parse it gives; the conformance is
`Machine.Abi.Conformance.LeafArith`. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.LeafArith

open Silmaril.Elf Silmaril.Elf.Staged Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Pinned.LeafArith
open Silmaril.Elf.Abi Silmaril.Elf.Abi.LeafArith
open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.Abi.Conformance.LeafArith

/-- The parse. -/
abbrev A0 : File := L.assemble bodies ld

/-! ## Decidable forms of the symbol facts -/

def funcSymB (A : File) (t : Table) (i : Nat) (f : String) : Bool :=
  match (A.symbols t)[i]? with
  | some s => s.name == nameOf f && s.kind == 2
  | none => false

theorem funcSym {t : Table} {i : Nat} {f : String} (h : funcSymB A0 t i f = true) :
    ∃ s, SymbolAt F t i s ∧ s.name = nameOf f ∧ s.kind = 2 := by
  unfold funcSymB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, ⟨_, parses, hs⟩, h.1, h.2⟩
  · exact absurd h (by simp)

def absentB (A : File) (f : String) : Bool :=
  [Table.symtab, Table.dynsym].all fun t =>
    (A.symbols t).all fun s => s.name != nameOf f || s.raw.sectionIndex == 0

theorem absent_of {f : String} (h : absentB A0 f = true) : Absent F f := by
  refine ⟨_, parses, fun t s hs hn => ?_⟩
  simp only [absentB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  cases t
  · exact (h.1 s hs).resolve_left (by simpa using hn)
  · exact (h.2 s hs).resolve_left (by simpa using hn)

def presentB (A : File) (f : String) : Bool :=
  [Table.symtab, Table.dynsym].any fun t =>
    (A.symbols t).any fun s => s.name == nameOf f && s.raw.sectionIndex != 0 &&
      (s.kind == 2 || s.kind == 10)

theorem present_of {f : String} (h : presentB A0 f = true) : Present F f := by
  simp only [presentB, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ⟨s, hs, ⟨hn, hi⟩, hk⟩ | ⟨s, hs, ⟨hn, hi⟩, hk⟩
  · exact ⟨_, parses, .symtab, s, hs, hn, hi, by simpa using hk⟩
  · exact ⟨_, parses, .dynsym, s, hs, hn, hi, by simpa using hk⟩

/-! ## The code -/

/-- The file maps the 181 transcribed bytes at `0x401370`. -/
theorem codeAt : CodeAt F 0x401370 Silmaril.X86.Ladder.LeafArith.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1) (by decide) (by decide +kernel)

theorem image_eq : ∃ A, Parses F A ∧
    image = A.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize) :=
  ⟨_, parses, by decide +kernel⟩

theorem codeOf (f : String) (i v n off : Nat) (hl : A0.select (Binding.symtab.sel f) =
      some (some ⟨i, v, n, false, false⟩))
    (hv : v = (region off n).base.toNat + off) (hs : funcSymB A0 .symtab i f = true) :
    CodeOf F .symtab f (region off n) :=
  ⟨⟨_, ⟨_, parses, hl⟩, hv, rfl, rfl, rfl, funcSym hs⟩, codeAt, (fun _ h => nomatch h), image_eq⟩

theorem relocs_empty : A0.relocs .dynamic = [] := by decide +kernel

theorem untouched (off n : Nat) : Untouched F (region off n) :=
  ⟨_, parses, by decide +kernel, by rw [relocs_empty]; simp⟩

/-- `leaf-arith` is `ET_EXEC`: its only load base is `0`. -/
theorem placement_zero {b : Nat} (h : Placement F b) : b = 0 := by
  obtain ⟨A, hA, hk, -⟩ := h
  have : A = A0 := Option.some.inj (hA.symm.trans parses)
  subst this
  rcases hk with ⟨-, h0⟩ | ⟨ht, -⟩
  · exact h0
  · exact absurd ht (by decide +kernel)

/-- `leaf-arith` admits load base `0`. -/
theorem placement_zero_ok : Placement F 0 :=
  ⟨_, parses, .inl ⟨by decide +kernel, rfl⟩, fun ph h => by revert ph; decide +kernel⟩

theorem rebase_zero (c : Code) : c.rebase 0 = c := by
  cases c; simp [Code.rebase]

theorem row (f : String) (i v n off : Nat) (hl : A0.select (Binding.symtab.sel f) =
      some (some ⟨i, v, n, false, false⟩))
    (hv : v = (region off n).base.toNat + off) (hs : funcSymB A0 .symtab i f = true)
    {p : Silmaril.Machine.Abi.SystemV.Proto} {S : CallSpec sysvInt.V p}
    (h : Conforms sysvInt (Mach.ofInt Silmaril.X86.Open.isa) .total hdr f p (region off n) 0 S) :
    AbiConforms sysvInt (Mach.ofInt Silmaril.X86.Open.isa) .total hdr f p F .symtab (region off n) 0 S :=
  ⟨codeOf f i v n off hl hv hs, untouched off n, ⟨0, placement_zero_ok⟩, fun b hb => by
    rw [placement_zero hb, rebase_zero]; exact h⟩

theorem clamp_row : silmaril.elf.abi.leaf_arith.clamp_i32 :=
  row "clamp_i32" 19 4199328 19 0x30 (by decide +kernel) (by decide) (by decide +kernel)
    (clamp_conforms .total)

theorem sat_row : silmaril.elf.abi.leaf_arith.sat_add_u32 :=
  row "sat_add_u32" 10 4199424 29 0x90 (by decide +kernel) (by decide) (by decide +kernel)
    (sat_conforms .total)

theorem gcd_row_of (h : Task.gcd_conforms) : silmaril.elf.abi.leaf_arith.gcd_u32 :=
  row "gcd_u32" 11 4199280 37 0 (by decide +kernel) (by decide) (by decide +kernel) h

theorem bswap_row_of (h : Task.bswap_conforms) : silmaril.elf.abi.leaf_arith.bswap32_manual :=
  row "bswap32_manual" 9 4199456 5 0xb0 (by decide +kernel) (by decide) (by decide +kernel) h

theorem excluded_ok : ∀ e ∈ coverage.excluded,
    (match e.2 with
      | .absent _ => absentB A0 e.1
      | .unclaimed _ => presentB A0 e.1
      | _ => true) = true := by
  decide +kernel

theorem header_row : silmaril.elf.abi.leaf_arith.arith_h := by
  refine ⟨by decide, coverage_check, fun _ _ h => absent_of (excluded_ok _ h),
    fun _ _ h => present_of (excluded_ok _ h), fun f hf => ?_⟩
  simp only [coverage, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨_, rfl, clamp_row⟩
  · exact ⟨_, rfl, sat_row⟩

/-! ## Negative: a non-symbol entry -/

/-- **An entry that is not the symbol's is rejected**: no code entered one byte into
`clamp_i32` is the function `clamp_i32` of the file. -/
theorem not_codeOf_offset {n : Nat} : ¬ CodeOf F .symtab "clamp_i32" (region 0x31 n) := by
  rintro ⟨⟨d, ⟨A, hA, hl⟩, hv, -⟩, -⟩
  have : A = A0 := Option.some.inj (hA.symm.trans parses)
  subst this
  have hd : A0.select (Binding.symtab.sel "clamp_i32") = some (some ⟨19, 4199328, 19, false, false⟩) := by
    decide +kernel
  rw [hd] at hl
  cases hl
  change (4199328 : Nat) = (0x401370 : Silmaril.X86.Word).toNat + 0x31 at hv
  exact absurd hv (by decide)


/-- **A wrong symbol is rejected**: `clamp_i32`'s code is not the file's `sat_add_u32` (that
symbol's `st_value` is `0x401400`). -/
theorem not_codeOf_symbol : ¬ CodeOf F .symtab "sat_add_u32" clampCode := by
  rintro ⟨⟨d, ⟨A, hA, hl⟩, hv, -⟩, -⟩
  have : A = A0 := Option.some.inj (hA.symm.trans parses)
  subst this
  have hd : A0.select (Binding.symtab.sel "sat_add_u32") = some (some ⟨10, 4199424, 29, false, false⟩) := by
    decide +kernel
  rw [hd] at hl
  cases hl
  change (4199424 : Nat) = (0x401370 : Silmaril.X86.Word).toNat + 0x30 at hv
  exact absurd hv (by decide)

/-- **Wrong code bytes are rejected**: code differing from the file's bytes in one byte is the
function of no binding and no name of the file. -/
theorem not_codeOf_bytes {b : Binding} {f : String} : ¬ CodeOf F b f patched :=
  not_codeOf_of_bytes (codeOf "clamp_i32" 19 4199328 19 0x30 (by decide +kernel) (by decide)
    (by decide +kernel)) rfl (by simp [patched, region]) (by decide +kernel)

/-- **The `arith.h` row is partial**: it leaves functions of the file unclaimed, so it is
neither available nor complete header satisfaction, whatever the implementations. -/
theorem not_available {A : AbiDef} {M : Mach} {bind : String → Binding}
    {impl : String → Option (Impl A)} :
    ¬ AbiHeaderSatAvailable A M hdr coverage F bind impl :=
  fun h => absurd h.2.1 (by decide +kernel)

end Silmaril.Proofs.Elf.Abi.LeafArith

end
