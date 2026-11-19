module

public import Silmaril.Elf.Load.Defs
public import Silmaril.Elf.Image.Thms
public import Silmaril.Elf.Facts.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # Proofs of `Silmaril.Elf.Load` -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Load

open Silmaril.Elf
open Silmaril.Elf.Load
open Silmaril.Elf.Image
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

/-- The bytes of a little-endian value. -/
theorem getElem_of_valueLE : ∀ (l : List (BitVec 8)) (x : Nat),
    Blob.valueLE l = x % 2 ^ (8 * l.length) →
    ∀ k (hk : k < l.length), l[k] = BitVec.ofNat 8 (x >>> (8 * k))
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | b :: r, x, hv, k, hk => by
    have hb := b.isLt
    have hpow : 2 ^ (8 * (r.length + 1)) = 256 * 2 ^ (8 * r.length) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    simp only [Blob.valueLE, List.length_cons] at hv
    rw [hpow] at hv
    have h0 : b.toNat = x % 256 := by
      have := congrArg (· % 256) hv
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _)] at this
      omega
    have h1 : Blob.valueLE r = x / 256 % 2 ^ (8 * r.length) := by
      have := congrArg (· / 256) hv
      rw [Nat.mod_mul_right_div_self] at this
      omega
    cases k with
    | zero =>
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_ofNat, h0]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [getElem_of_valueLE r (x / 256) h1 k (by simpa using hk)]
      congr 1
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        show 8 * (k + 1) = 8 + 8 * k by omega, Nat.pow_add]

theorem byteAt_of_fileBytes {F : Blob} {o : Nat} {bytes : List (BitVec 8)}
    (h : FileBytes F o bytes) (k : Nat) (hk : k < bytes.length) :
    Blob.byteAt F.n (o + k) = bytes[k] := by
  unfold FileBytes blobRead Blob.readLEN at h
  split at h
  · have hv := (Option.some_inj.mp h).symm
    rw [getElem_of_valueLE bytes _ hv k hk, ← Nat.shiftRight_add, ← Nat.mul_add]
    rfl
  · cases h

theorem untouched_sub {A : File} {v n k : Nat} (h : Untouched A v n) (hk : k < n) :
    Untouched A (v + k) 1 := by
  intro r hr
  obtain ⟨w, hw, hm⟩ := h r hr
  refine ⟨w, hw, ?_⟩
  simp only [Misses, Bool.or_eq_true, decide_eq_true_eq] at hm ⊢
  omega

theorem readWith_of_segBytes {F : Blob} {A : File} {base : Nat} {mem : Silmaril.Process.Memory}
    (hL : ImageLoaded F A base mem) {i v o : Nat} {bytes : List (BitVec 8)}
    (hs : SegBytes F A i v o bytes) (hu : Untouched A v bytes.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) bytes.length) :
    mem.readWith acc (base + v) bytes.length = some bytes := by
  apply Silmaril.Process.Memory.readWith_eq _ _ _ _ hp
  intro k hk
  have horig := mapsFile_origins hs.1 hk
  have := (hL (v + k) i (o + k) (untouched_sub hu hk)).1 horig
  rw [show base + v + k = base + (v + k) by omega, this, byteAt_of_fileBytes hs.2 k hk]

theorem definesName_of_definesFn {A : File} {n : Formats.ELF.NameBytes}
    (h : A.definesFn n = true) : A.definesName n = true := by
  simp only [File.definesFn, File.definesName, List.any_eq_true, Bool.and_eq_true] at h ⊢
  obtain ⟨t, ht, s, hs, ⟨hn, hi⟩, -⟩ := h
  exact ⟨t, ht, s, hs, hn, hi⟩

theorem not_present_of_absent {F : Blob} {n : Formats.ELF.NameBytes} (ha : AbsentName F n) :
    ¬ PresentFn F n := by
  rintro ⟨A, hA, hp⟩
  obtain ⟨B, hB, hb⟩ := ha
  cases parses_unique hA hB
  rw [definesName_of_definesFn hp] at hb
  cases hb

theorem readOnlyAt_segBytes {F : Blob} {v : Nat} {bytes : List (BitVec 8)}
    (h : ReadOnlyAt F v bytes) :
    ∃ A, Parses F A ∧ ∃ i ph, A.phdrs[i]? = some ph ∧ roSeg v bytes.length ph = true ∧
      SegBytes F A i v (ph.offset + (v - ph.virtualAddress)) bytes := by
  obtain ⟨A, hA, ph, hf, hr⟩ := h
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (List.mem_of_find?_eq_some hf)
  have hc := List.find?_some hf
  refine ⟨A, hA, i, ph, hi, hc, ⟨ph, hi, ?_, ?_, ?_, rfl⟩, hr⟩ <;>
    simp only [roSeg, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc <;> omega

theorem lookup_sym_entry {F : Blob} {n : Formats.ELF.NameBytes} {d : Def}
    (h : Lookup F (.sym n) (some d)) :
    ∃ A, Parses F A ∧ ∃ s, (A.symbols .symtab)[d.index]? = some s ∧ s.name = n ∧
      s.raw.sectionIndex ≠ 0 ∧ (s.raw.kind = 2 ∨ s.raw.kind = 10) := by
  obtain ⟨A, hA, hs⟩ := h
  refine ⟨A, hA, ?_⟩
  simp only [File.select, File.symtabFind] at hs
  cases hsec : A.sectionOfType SHT_SYMTAB with
  | none => rw [hsec] at hs; cases hs
  | some sec =>
    rw [hsec] at hs
    simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hs
    obtain ⟨⟨s, i⟩, hm, hf⟩ := List.exists_of_findSome?_eq_some hs
    rw [List.mem_zipIdx_iff_getElem?] at hm
    simp only at hm hf
    split at hf
    · rename_i hn
      unfold File.funcDef at hf
      split at hf
      · rename_i hc
        simp only [Option.some.injEq] at hf
        subst hf
        exact ⟨s, hm, hn, hc.1, hc.2.2⟩
      · cases hf
    · cases hf

theorem readWith_of_codeAt {F : Blob} {A : File} (hA : Parses F A) {base : Nat}
    {mem : Silmaril.Process.Memory} (hL : ImageLoaded F A base mem) {v : Nat}
    {code : List (BitVec 8)} (hc : CodeAt F v code) (hu : Untouched A v code.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) code.length) :
    mem.readWith acc (base + v) code.length = some code := by
  obtain ⟨B, hB, i, ph, -, -, hs⟩ := codeAt_segBytes hc
  cases parses_unique hA hB
  exact readWith_of_segBytes hL hs hu hp

theorem readWith_of_readOnlyAt {F : Blob} {A : File} (hA : Parses F A) {base : Nat}
    {mem : Silmaril.Process.Memory} (hL : ImageLoaded F A base mem) {v : Nat}
    {bytes : List (BitVec 8)} (hr : ReadOnlyAt F v bytes) (hu : Untouched A v bytes.length)
    {acc : Silmaril.Process.Access} (hp : mem.Permitted acc (base + v) bytes.length) :
    mem.readWith acc (base + v) bytes.length = some bytes := by
  obtain ⟨B, hB, i, ph, -, -, hs⟩ := readOnlyAt_segBytes hr
  cases parses_unique hA hB
  exact readWith_of_segBytes hL hs hu hp

theorem readOnlyAt_unique {F : Blob} {A : File} (hA : Parses F A) {v : Nat}
    {bytes : List (BitVec 8)} (hr : ReadOnlyAt F v bytes) (hu : Unambiguous A v bytes.length) :
    ∃ i ph, A.phdrs[i]? = some ph ∧ roSeg v bytes.length ph = true ∧
      ∀ k, k < bytes.length →
        A.origins (v + k) = [(i, Origin.file (ph.offset + (v - ph.virtualAddress) + k))] := by
  obtain ⟨B, hB, i, ph, hph, hro, hs⟩ := readOnlyAt_segBytes hr
  cases parses_unique hA hB
  refine ⟨i, ph, hph, hro, fun k hk => ?_⟩
  have hm := mapsFile_origins hs.1 hk
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp (hu k hk)
  rw [hx] at hm ⊢
  rw [List.mem_singleton.mp hm]

end Silmaril.Proofs.Elf.Load
