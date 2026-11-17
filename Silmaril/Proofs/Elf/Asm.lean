module

public import Silmaril.Elf.Asm.Defs
public import Silmaril.Elf.Image.Thms
public import Silmaril.Elf.Facts.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # Proofs of `Silmaril.Elf.Asm` -/

@[expose] public section

namespace Silmaril.Proofs.Elf.Asm

open Silmaril.Elf
open Silmaril.Elf.Asm
open Silmaril.Elf.Image
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

theorem valueLE_inj : ∀ {a b : List (BitVec 8)}, a.length = b.length →
    Blob.valueLE a = Blob.valueLE b → a = b
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, hv => by
    simp only [Blob.valueLE] at hv
    have hx := x.isLt
    have hy := y.isLt
    have h1 : x.toNat = y.toNat := by omega
    have h2 : Blob.valueLE xs = Blob.valueLE ys := by omega
    rw [BitVec.eq_of_toNat_eq h1, valueLE_inj (by simpa using hl) h2]

theorem decodes_unique (isa : Isa) : ∀ {bs : List Byte} {d₁ d₂ : List (Nat × isa.Instr)},
    decodes isa bs d₁ = true → decodes isa bs d₂ = true → d₁ = d₂
  | [], [], [], _, _ => rfl
  | [], [], _ :: _, _, h => by
    obtain ⟨n, i⟩ := ‹Nat × isa.Instr›
    simp [decodes] at h; omega
  | [], (n, i) :: _, [], h, _ => by simp [decodes] at h; omega
  | _ :: _, [], _, h, _ => by simp [decodes] at h
  | b :: bs, (n, i) :: d₁, [], _, h => by simp [decodes] at h
  | bs, (n₁, i₁) :: d₁, (n₂, i₂) :: d₂, h₁, h₂ => by
    simp only [decodes, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
    obtain ⟨⟨⟨-, -⟩, hd₁⟩, hr₁⟩ := h₁
    obtain ⟨⟨⟨-, -⟩, hd₂⟩, hr₂⟩ := h₂
    cases hdec : isa.decode bs with
    | none => rw [hdec] at hd₁; cases hd₁
    | some p =>
      obtain ⟨i', n'⟩ := p
      rw [hdec] at hd₁ hd₂
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hd₁ hd₂
      obtain ⟨rfl, rfl⟩ := hd₁
      obtain ⟨rfl, rfl⟩ := hd₂
      rw [decodes_unique isa hr₁ hr₂]

theorem decodes_sum (isa : Isa) : ∀ {bs : List Byte} {d : List (Nat × isa.Instr)},
    decodes isa bs d = true → (d.map (·.1)).sum = bs.length
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [decodes] at h
  | bs, (n, i) :: d, h => by
    simp only [decodes, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨-, hn⟩, -⟩, hr⟩ := h
    have := decodes_sum isa hr
    simp only [List.map_cons, List.sum_cons, List.length_drop] at this ⊢
    omega

theorem decodeAllF_sound (isa : Isa) : ∀ {fuel : Nat} {bs : List Byte}
    {d : List (Nat × isa.Instr)}, decodeAllF isa fuel bs = some d → decodes isa bs d = true
  | _, [], d, h => by
    simp only [decodeAllF, Option.some.injEq] at h; subst h; rfl
  | 0, _ :: _, _, h => by simp [decodeAllF] at h
  | fuel + 1, b :: bs, d, h => by
    simp only [decodeAllF] at h
    split at h
    · rename_i i n hdec
      split at h
      · rename_i hn
        cases hr : decodeAllF isa fuel ((b :: bs).drop n) with
        | none => rw [hr] at h; cases h
        | some d' =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          simp only [decodes, hdec, Bool.and_eq_true, decide_eq_true_eq, and_self]
          exact ⟨⟨hn, trivial⟩, decodeAllF_sound isa hr⟩
      · cases h
    · cases h

theorem decodeAllF_complete (isa : Isa) : ∀ {d : List (Nat × isa.Instr)} {fuel : Nat}
    {bs : List Byte}, decodes isa bs d = true → bs.length ≤ fuel → decodeAllF isa fuel bs = some d
  | [], _, [], _, _ => by cases ‹Nat› <;> rfl
  | [], _, _ :: _, h, _ => by simp [decodes] at h
  | (n, i) :: d, fuel, bs, h, hf => by
    simp only [decodes, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hn0, hn⟩, hd⟩, hr⟩ := h
    cases bs with
    | nil => simp at hn; omega
    | cons b bs =>
      cases fuel with
      | zero => simp at hf
      | succ fuel =>
        cases hdec : isa.decode (b :: bs) with
        | none => rw [hdec] at hd; cases hd
        | some p =>
          obtain ⟨i', n'⟩ := p
          rw [hdec] at hd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          have := decodeAllF_complete isa hr (fuel := fuel)
            (by simp only [List.length_drop, List.length_cons] at hf ⊢; omega)
          simp only [decodeAllF, hdec, hn0, hn, and_self, ↓reduceIte, this, Option.map_some]

theorem decodes_iff_decodeAll (isa : Isa) (bs : List Byte) (d : List (Nat × isa.Instr)) :
    decodes isa bs d = true ↔ decodeAll isa bs = some d :=
  ⟨fun h => decodeAllF_complete isa h (Nat.le_refl _), decodeAllF_sound isa⟩

theorem tiles_sum : ∀ {o : Nat} {ls : List Line} {n : Nat}, tiles o ls n = true →
    o + (ls.map (·.len)).sum = n
  | o, [], n, h => by simp [tiles] at h; simp [h]
  | o, l :: ls, n, h => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have := tiles_sum h.2
    simp only [List.map_cons, List.sum_cons]
    omega

theorem bytesAt_codeAt {F : Blob} {f : AsmFunction} (h : BytesAt F f)
    (hf : ∃ A i, Parses F A ∧ f.extent.segment = some i ∧
      A.phdrs.find? (codeSeg f.extent.vaddr f.bytes.length) = A.phdrs[i]?) :
    CodeAt F f.extent.vaddr f.bytes := by
  obtain ⟨-, A, i, o, hA, hi, -, hs⟩ := h
  obtain ⟨A', i', hA', hi', hfind⟩ := hf
  cases parses_unique hA hA'
  rw [hi] at hi'
  cases hi'
  exact codeAt_of_segBytes hA hs hfind

theorem codeAt_bytesAt {F : Blob} {f : AsmFunction} (h : CodeAt F f.extent.vaddr f.bytes)
    (hz : f.extent.size = f.bytes.length) :
    ∃ i o, BytesAt F { f with extent := { f.extent with segment := some i, fileOff := some o } } := by
  obtain ⟨A, hA, i, ph, -, -, hs⟩ := codeAt_segBytes h
  exact ⟨i, _, hz, A, i, _, hA, rfl, rfl, hs⟩

theorem bytesAt_unique {F : Blob} {f g : AsmFunction} (hf : BytesAt F f) (hg : BytesAt F g)
    (he : f.extent = g.extent) : f.bytes = g.bytes := by
  obtain ⟨hzf, A, i, o, -, hi, ho, -, hb⟩ := hf
  obtain ⟨hzg, B, j, p, -, hj, hp, -, hb'⟩ := hg
  rw [he] at hi ho hzf
  rw [hi] at hj; rw [ho] at hp
  cases hj; cases hp
  have hl : f.bytes.length = g.bytes.length := hzf.symm.trans hzg
  unfold FileBytes at hb hb'
  rw [hl, hb'] at hb
  exact valueLE_inj hl (Option.some_inj.mp hb).symm

theorem bytesAt_origins {F : Blob} {f : AsmFunction} (h : BytesAt F f) {k : Nat}
    (hk : k < f.extent.size) : ∃ A i o, Parses F A ∧ f.extent.segment = some i ∧
      f.extent.fileOff = some o ∧ (i, Origin.file (o + k)) ∈ A.origins (f.extent.vaddr + k) := by
  obtain ⟨hz, A, i, o, hA, hi, ho, hm, -⟩ := h
  exact ⟨A, i, o, hA, hi, ho, mapsFile_origins hm (by omega)⟩

theorem archOf_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : archOk A f = true) : ArchOf F f := by
  simp only [archOk, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨A, hp, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem symbolOf_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : symbolOk A f = true) : SymbolOf F f := by
  unfold symbolOk at h
  split at h
  · rename_i r hr
    split at h
    · rename_i s hs
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
      exact ⟨r, s, hr, ⟨A, hp, hs⟩, h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    · cases h
  · cases h

theorem bytesAt_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : extentOk A f = true)
    (hr : ∀ o, f.extent.fileOff = some o → FileBytes F o f.bytes) : BytesAt F f := by
  unfold extentOk at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, h⟩ := h
  split at h
  · rename_i i o hi ho
    split at h
    · rename_i ph hph
      simp only [mapsOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hk, hlo⟩, hhi⟩, ho'⟩ := h
      exact ⟨hz, A, i, o, hp, hi, ho, ⟨ph, hph, hk, hlo, hhi, ho'⟩, hr o ho⟩
    · cases h
  · cases h

theorem refGrounded_of_check {F : Blob} {f : AsmFunction} {isa : Isa}
    {d : List (Nat × isa.Instr)} {r : CodeRef} (ho : r.origin = .decoded) (hd : DecodesAs isa f d)
    (h : decodedRefOk f isa d r = true) : RefGrounded F f isa d r := by
  unfold RefGrounded; rw [ho]
  unfold decodedRefOk at h
  split at h
  · rename_i n i hi
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨hd, n, i, hi, h.1, h.2⟩
  · cases h

theorem sectionBytesAt_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : secOk A f = true)
    (hr : ∀ o, f.extent.fileOff = some o → FileBytes F o f.bytes) : SectionBytesAt F f := by
  unfold secOk at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, h⟩ := h
  split at h
  · rename_i k o hk ho
    split at h
    · rename_i s hs
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hn, hlo⟩, hhi⟩, ho'⟩ := h
      exact ⟨hz, A, k, o, hp, hk, ho, ⟨s, hs, hn, hlo, hhi, ho'⟩, hr o ho⟩
    · cases h
  · cases h

theorem refGrounded_reloc_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    {isa : Isa} {d : List (Nat × isa.Instr)} {r : CodeRef} (h : relocRefOk A f r = true) :
    RefGrounded F f isa d r := by
  unfold relocRefOk at h
  unfold RefGrounded
  split at h
  · rename_i sel k ho
    rw [ho]
    split at h
    · rename_i rel hrel
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      refine ⟨A, rel, hp, hrel, h1, h2, h3, fun n hn => ?_⟩
      rw [hn] at h4
      simpa using h4
    · cases h
  · cases h

theorem fileBytes_of_kbytes {x : Silmaril.KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {o : Nat} {bytes : List (BitVec 8)}
    (hc : Silmaril.Elf.Staged.Reader.kread x o bytes.length = some (Blob.valueLE bytes)) :
    FileBytes (blobOf ⟨raw⟩) o bytes :=
  Silmaril.Elf.Staged.Reader.sub_kbytes hx h _ _ _ hc

end Silmaril.Proofs.Elf.Asm
