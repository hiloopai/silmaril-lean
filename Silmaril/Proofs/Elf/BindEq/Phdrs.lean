module

public import Silmaril.Elf.Bridge.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # The API's program headers are the loader's (`DynElf.Elf.phdrs`)

`phdrs_rd`: on a file that parses to `A`, with `e_machine = EM_X86_64` and `e_phentsize = 56`,
the loader's reader `DynElf.Elf.phdrs` returns `A.phdrs` (as `DynElf.Elf.Phdr`s). The proof
inverts the runs of the parse specification (`header_inv`, `phdrs_inv`) and replays the loader's
reads at the same offsets. -/

@[expose] public section

namespace Silmaril.Proofs.Elf.BindEq

open Silmaril.Elf
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.DynElf.Elf (u8 u16 u32 u64)
open Silmaril.Formats.ELF (Header ProgramHeader)

abbrev Src := Nat → Nat → Option Nat

variable {r : Src}

/-! ## Running and inverting reading programs -/

theorem bind_eq {α β : Type} (p : Rd α) (f : α → Rd β) : (p >>= f) = p.bind f := rfl

theorem run_le (r : Src) (o w : Nat) : (Rd.le o w).run r = r o w := by
  unfold Rd.le Rd.run
  cases r o w <;> rfl

theorem bind_inv {α β : Type} {p : Rd α} {f : α → Rd β} {b : β} (h : (p >>= f).run r = some b) :
    ∃ a, p.run r = some a ∧ (f a).run r = some b := by
  rw [bind_eq, Rd.run_bind] at h
  cases e : p.run r with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; exact ⟨a, rfl, h⟩

theorem read_inv {β : Type} {o w : Nat} {f : Nat → Rd β} {b : β}
    (h : (Rd.le o w >>= f).run r = some b) : ∃ v, r o w = some v ∧ (f v).run r = some b := by
  obtain ⟨v, hv, h⟩ := bind_inv h
  rw [run_le] at hv
  exact ⟨v, hv, h⟩

theorem guard_inv {β : Type} {c : Prop} [Decidable c] {f : Unit → Rd β} {b : β}
    (h : (Rd.guard c >>= f).run r = some b) : c ∧ (f ()).run r = some b := by
  unfold Rd.guard at h
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp only [hc, ↓reduceIte] at h; cases h

theorem pure_inv {α : Type} {a b : α} (h : (pure a : Rd α).run r = some b) : a = b :=
  Option.some.inj h

theorem run_bind_of {α β : Type} {p : Rd α} {a : α} (f : α → Rd β)
    (h : p.run r = some a) : (p >>= f).run r = (f a).run r := by
  rw [bind_eq, Rd.run_bind, h]
  rfl

theorem run_read_of {β : Type} {o w v : Nat} (f : Nat → Rd β) (h : r o w = some v) :
    (Rd.le o w >>= f).run r = (f v).run r :=
  run_bind_of f (by rw [run_le]; exact h)

theorem run_guard_of {β : Type} {c : Prop} [Decidable c] (f : Unit → Rd β) (h : c) :
    (Rd.guard c >>= f).run r = (f ()).run r := by
  unfold Rd.guard
  simp only [h, ↓reduceIte]
  rfl

theorem run_guard_none {β : Type} {c : Prop} [Decidable c] (f : Unit → Rd β) (h : ¬c) :
    (Rd.guard c >>= f).run r = none := by
  unfold Rd.guard
  simp only [h, ↓reduceIte]
  rfl

theorem mapM_loop_inv {α β : Type} (f : α → Rd β) : ∀ (l : List α) (acc out : List β),
    (List.mapM.loop f l acc).run r = some out →
      ∃ bs, out = acc.reverse ++ bs ∧ List.Forall₂ (fun a b => (f a).run r = some b) l bs
  | [], acc, out, h => by
    have : acc.reverse = out := Option.some.inj h
    exact ⟨[], by simp [this], .nil⟩
  | a :: l, acc, out, h => by
    obtain ⟨b, hb, h⟩ := bind_inv (f := fun x => List.mapM.loop f l (x :: acc)) h
    obtain ⟨bs, rfl, hl⟩ := mapM_loop_inv f l (b :: acc) out h
    exact ⟨b :: bs, by simp, .cons hb hl⟩

theorem mapM_inv {α β : Type} {f : α → Rd β} {l : List α} {out : List β}
    (h : (l.mapM f).run r = some out) : List.Forall₂ (fun a b => (f a).run r = some b) l out := by
  obtain ⟨bs, rfl, hl⟩ := mapM_loop_inv f l [] out h
  simpa using hl

theorem run_mapM_loop {α β : Type} (f : α → Rd β) : ∀ (l : List α) (out acc : List β),
    List.Forall₂ (fun a b => (f a).run r = some b) l out →
    (List.mapM.loop f l acc).run r = some (acc.reverse ++ out)
  | [], [], acc, .nil => by
    show (Rd.pure acc.reverse).run r = _
    simp [Rd.run]
  | a :: l, b :: out, acc, .cons hab hl => by
    show (f a >>= fun x => List.mapM.loop f l (x :: acc)).run r = _
    rw [run_bind_of _ hab, run_mapM_loop f l out (b :: acc) hl]
    simp

theorem run_mapM {α β : Type} {f : α → Rd β} {l : List α} {out : List β}
    (h : List.Forall₂ (fun a b => (f a).run r = some b) l out) : (l.mapM f).run r = some out := by
  show (List.mapM.loop f l []).run r = some out
  simpa using run_mapM_loop f l out [] h

/-! ## The header -/

/-- The header fields the loader reads, from a run of `Parse.header`. -/
theorem header_inv {h : Header} (hh : Parse.header.run r = some h) :
    r 0 4 = some 0x464c457f ∧ r 4 1 = some 2 ∧ r 5 1 = some 1 ∧ r 16 2 = some h.fileType ∧
      r 18 2 = some h.machine ∧ r 32 8 = some h.programOffset ∧
      r 54 2 = some h.programEntrySize ∧ r 56 2 = some h.programCount := by
  unfold Parse.header at hh
  obtain ⟨m0, h0, hh⟩ := read_inv hh
  obtain ⟨g0, hh⟩ := guard_inv hh
  obtain ⟨m4, h4, hh⟩ := read_inv hh
  obtain ⟨g4, hh⟩ := guard_inv hh
  obtain ⟨m5, h5, hh⟩ := read_inv hh
  obtain ⟨g5, hh⟩ := guard_inv hh
  obtain ⟨m6, h6, hh⟩ := read_inv hh
  obtain ⟨g6, hh⟩ := guard_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨ft, hft, hh⟩ := read_inv hh
  obtain ⟨mc, hmc, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨po, hpo, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨pe, hpe, hh⟩ := read_inv hh
  obtain ⟨pc, hpc, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  obtain ⟨_, _, hh⟩ := read_inv hh
  cases pure_inv hh
  subst g0 g4 g5
  exact ⟨h0, h4, h5, hft, hmc, hpo, hpe, hpc⟩

/-! ## Program headers -/

/-- A program header, read by the loader at the same offset. -/
theorem phdr_rd {o : Nat} {ph : ProgramHeader} (h : (Parse.phdr o).run r = some ph) :
    (Silmaril.Elf.Link.DynElf.Elf.phdr o).run r = some (Bridge.phdrToDyn ph) := by
  unfold Parse.phdr at h
  obtain ⟨k, hk, h⟩ := read_inv h
  obtain ⟨fl, hfl, h⟩ := read_inv h
  obtain ⟨of, hof, h⟩ := read_inv h
  obtain ⟨va, hva, h⟩ := read_inv h
  obtain ⟨_, _, h⟩ := read_inv h
  obtain ⟨fs, hfs, h⟩ := read_inv h
  obtain ⟨ms, hms, h⟩ := read_inv h
  obtain ⟨_, _, h⟩ := read_inv h
  cases pure_inv h
  unfold Silmaril.Elf.Link.DynElf.Elf.phdr
  simp only [u32, u64]
  rw [run_read_of _ hk, run_read_of _ hfl, run_read_of _ hof, run_read_of _ hva,
    run_read_of _ hfs, run_read_of _ hms]
  rfl

/-- The header and program headers of a parse. -/
theorem read_inv' {A : File} (h : Silmaril.Elf.read.run r = some A) :
    Parse.header.run r = some A.header ∧ (Parse.phdrs A.header).run r = some A.phdrs := by
  unfold Silmaril.Elf.read at h
  obtain ⟨hd, hhd, h⟩ := bind_inv h
  obtain ⟨phs, hphs, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  obtain ⟨_, _, h⟩ := bind_inv h
  cases pure_inv h
  exact ⟨hhd, hphs⟩

/-- **The loader's program headers are the API's** (x86-64, `e_phentsize = 56`). -/
theorem phdrs_rd {A : File} (hA : Silmaril.Elf.read.run r = some A) (hm : A.header.machine = 62)
    (he : A.header.programEntrySize = 56) :
    Silmaril.Elf.Link.DynElf.Elf.phdrs.run r = some (A.phdrs.map Bridge.phdrToDyn) := by
  obtain ⟨hh, hp⟩ := read_inv' hA
  obtain ⟨h0, h4, h5, -, h18, h32, h54, h56⟩ := header_inv hh
  unfold Silmaril.Elf.Link.DynElf.Elf.phdrs
  simp only [u8, u16, u32, u64]
  rw [run_read_of _ h0, run_guard_of _ rfl, run_read_of _ h4, run_guard_of _ rfl,
    run_read_of _ h5, run_guard_of _ rfl, run_read_of _ h18, run_guard_of _ hm,
    run_read_of _ h32, run_read_of _ h54, run_guard_of _ he, run_read_of _ h56]
  unfold Parse.phdrs at hp
  split at hp
  · rename_i h0'
    rw [h0', ← pure_inv hp]
    rfl
  · obtain ⟨-, hp⟩ := guard_inv hp
    apply run_mapM
    have hf := mapM_inv hp
    rw [List.forall₂_map_right_iff]
    exact hf.imp fun _ _ hph => phdr_rd hph

/-- A parse with program headers has `e_phentsize = 56`. -/
theorem phentsize_of_phdrs {A : File} (hA : Silmaril.Elf.read.run r = some A) (hne : A.phdrs ≠ []) :
    A.header.programEntrySize = 56 := by
  obtain ⟨-, hp⟩ := read_inv' hA
  unfold Parse.phdrs at hp
  split at hp
  · exact absurd (pure_inv hp).symm hne
  · exact (guard_inv hp).1

/-- Without `e_phentsize = 56` the loader reads no program headers. -/
theorem phdrs_rd_none {A : File} (hA : Silmaril.Elf.read.run r = some A) (he : A.header.programEntrySize ≠ 56) :
    Silmaril.Elf.Link.DynElf.Elf.phdrs.run r = none := by
  obtain ⟨hh, -⟩ := read_inv' hA
  obtain ⟨h0, h4, h5, -, h18, h32, h54, -⟩ := header_inv hh
  unfold Silmaril.Elf.Link.DynElf.Elf.phdrs
  simp only [u8, u16, u32, u64]
  rw [run_read_of _ h0, run_guard_of _ rfl, run_read_of _ h4, run_guard_of _ rfl,
    run_read_of _ h5, run_guard_of _ rfl, run_read_of _ h18]
  by_cases hm : A.header.machine = 62
  · rw [run_guard_of _ hm, run_read_of _ h32, run_read_of _ h54, run_guard_none _ he]
  · rw [run_guard_none _ hm]

/-- `e_type`, as the loader reads it. -/
theorem etype_rd {A : File} (hA : Silmaril.Elf.read.run r = some A) :
    Silmaril.Elf.Link.ElfBind.Elf.etype.run r = some A.header.fileType := by
  obtain ⟨hh, -⟩ := read_inv' hA
  obtain ⟨-, -, -, h16, -⟩ := header_inv hh
  unfold Silmaril.Elf.Link.ElfBind.Elf.etype
  rw [u16, run_le]
  exact h16

end Silmaril.Proofs.Elf.BindEq
