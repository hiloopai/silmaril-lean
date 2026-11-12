module

public import Silmaril.Elf.Bridge.Defs
public import Silmaril.Elf.Check.Thms
public import Silmaril.X86.Link.Blob.Thms

/-! # The parse against silmaril-lean's ELF header reader

`header_silmaril` (`Bridge.Task.header_silmaril`): the header of the parse is what
`Silmaril.Formats.ELF.readHeader` reads from the same bytes. Through silmaril's
`Blob.readHeader_bytesOf` (the public reader equals its blob form `readHeaderN`), the two are the
same sequence of reads; the parse's last header read (`e_shstrndx` at 62) gives silmaril's
`64 ≤ size` guard. Standard axioms only.
-/

@[expose] public section

namespace Silmaril.Elf.Check

open Silmaril.Formats.ELF (Header SectionHeader)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Link.DynElf.Elf (u8 u16 u32 u64)
open Silmaril.X86.Link (Blob)

theorem run_bind_some {α β : Type} {r : Src} {p : Rd α} {f : α → Rd β} {b : β}
    (h : (p >>= f).run r = some b) : ∃ a, p.run r = some a ∧ (f a).run r = some b := by
  rw [bind_eq, Rd.run_bind] at h
  cases e : p.run r with
  | none => rw [e] at h; cases h
  | some a => rw [e] at h; exact ⟨a, rfl, h⟩

theorem run_le_bind_some {β : Type} {r : Src} {o w : Nat} {f : Nat → Rd β} {b : β}
    (h : (Rd.le o w >>= f).run r = some b) : ∃ v, r o w = some v ∧ (f v).run r = some b := by
  obtain ⟨v, hv, h⟩ := run_bind_some h
  rw [run_le] at hv
  exact ⟨v, hv, h⟩

theorem run_guard_bind_some {β : Type} {r : Src} {c : Prop} [Decidable c] {f : Unit → Rd β} {b : β}
    (h : (Rd.guard c >>= f).run r = some b) : c ∧ (f ()).run r = some b := by
  by_cases hc : c
  · rw [run_guard_of _ hc] at h; exact ⟨hc, h⟩
  · unfold Rd.guard at h; rw [ite_f hc] at h; cases h

/-- The header of the parse is its first step. -/
theorem header_of_parses {F : Blob} {A : File} (h : Parses F A) :
    Parse.header.run (blobRead F) = some A.header := by
  unfold Parses parse read at h
  obtain ⟨hd, e1, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  cases h
  exact e1

theorem readHeader_of_run {F : Blob} {hd : Header} (h : Parse.header.run (blobRead F) = some hd) :
    Silmaril.Formats.ELF.readHeader F.bytes = some hd := by
  unfold Parse.header at h
  simp only [u8, u16, u32, u64] at h
  obtain ⟨v0, e0, h⟩ := run_le_bind_some h
  obtain ⟨g0, h⟩ := run_guard_bind_some h
  obtain ⟨v4, e4, h⟩ := run_le_bind_some h
  obtain ⟨g4, h⟩ := run_guard_bind_some h
  obtain ⟨v5, e5, h⟩ := run_le_bind_some h
  obtain ⟨g5, h⟩ := run_guard_bind_some h
  obtain ⟨v6, e6, h⟩ := run_le_bind_some h
  obtain ⟨g6, h⟩ := run_guard_bind_some h
  obtain ⟨v7, e7, h⟩ := run_le_bind_some h
  obtain ⟨v8, e8, h⟩ := run_le_bind_some h
  obtain ⟨v16, e16, h⟩ := run_le_bind_some h
  obtain ⟨v18, e18, h⟩ := run_le_bind_some h
  obtain ⟨v20, e20, h⟩ := run_le_bind_some h
  obtain ⟨v24, e24, h⟩ := run_le_bind_some h
  obtain ⟨v32, e32, h⟩ := run_le_bind_some h
  obtain ⟨v40, e40, h⟩ := run_le_bind_some h
  obtain ⟨v48, e48, h⟩ := run_le_bind_some h
  obtain ⟨v52, e52, h⟩ := run_le_bind_some h
  obtain ⟨v54, e54, h⟩ := run_le_bind_some h
  obtain ⟨v56, e56, h⟩ := run_le_bind_some h
  obtain ⟨v58, e58, h⟩ := run_le_bind_some h
  obtain ⟨v60, e60, h⟩ := run_le_bind_some h
  obtain ⟨v62, e62, h⟩ := run_le_bind_some h
  cases h
  have h64 : 64 ≤ F.len := by
    unfold blobRead Blob.readLEN at e62
    split at e62
    · rename_i hc; omega
    · cases e62
  unfold blobRead at e0 e4 e5 e6 e7 e8 e16 e18 e20 e24 e32 e40 e48 e52 e54 e56 e58 e60 e62
  rw [show F.bytes = Blob.bytesOf F.n F.len from rfl, Blob.readHeader_bytesOf]
  simp [Blob.readHeaderN, h64, e0, e4, e5, e6, e7, e8, e16, e18, e20, e24, e32, e40, e48, e52, e54,
    e56, e58, e60, e62, g0, g4, g5, g6]

/-! ## Program and section header tables -/

theorem forall₂_of_mapM_some {α β : Type} {f : α → Option β} :
    ∀ (l : List α) (out : List β), l.mapM f = some out → List.Forall₂ (fun a b => f a = some b) l out
  | [], out, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact .nil
  | a :: l, out, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM_some l bs hbs)

theorem forall₂_of_run_loop {α β : Type} {r : Src} (f : α → Rd β) :
    ∀ (l : List α) (acc out : List β), (List.mapM.loop f l acc).run r = some out →
    ∃ out', out = acc.reverse ++ out' ∧ List.Forall₂ (fun a b => (f a).run r = some b) l out'
  | [], acc, out, h => by
    have : (Rd.pure acc.reverse).run r = some out := h
    simp only [Rd.run, Option.some.injEq] at this
    exact ⟨[], by simp [← this], .nil⟩
  | a :: l, acc, out, h => by
    have h' : (f a >>= fun x => List.mapM.loop f l (x :: acc)).run r = some out := h
    obtain ⟨b, hb, h⟩ := run_bind_some h'
    obtain ⟨out', e, hl⟩ := forall₂_of_run_loop f l (b :: acc) out h
    exact ⟨b :: out', by simp [e], .cons hb hl⟩

theorem forall₂_of_run_mapM {α β : Type} {r : Src} {f : α → Rd β} {l : List α} {out : List β}
    (h : (l.mapM f).run r = some out) : List.Forall₂ (fun a b => (f a).run r = some b) l out := by
  obtain ⟨out', e, hl⟩ := forall₂_of_run_loop f l [] out h
  simp at e
  subst e
  exact hl

theorem map_of_forall₂ {α β : Type} {g : β → α} :
    ∀ {l : List α} {out : List β}, List.Forall₂ (fun a b => g b = a) l out → out.map g = l
  | _, _, .nil => rfl
  | _, _, .cons h hl => by simp [h, map_of_forall₂ hl]

theorem sections_headers {r : Src} {hd : Header} {shs : List SectionHeader} {secs : List Section}
    (h : (Parse.sections hd shs).run r = some secs) : secs.map (·.header) = shs := by
  unfold Parse.sections at h
  by_cases he : shs.isEmpty
  · rw [ite_t he] at h
    have : secs = [] := by cases h; rfl
    subst this
    exact (List.isEmpty_iff.mp he).symm
  · rw [ite_f he] at h
    obtain ⟨names, _, h⟩ := run_bind_some h
    apply map_of_forall₂
    refine List.Forall₂.imp ?_ (forall₂_of_run_mapM h)
    intro sh s hs
    obtain ⟨_, _, hs⟩ := run_bind_some hs
    obtain ⟨_, _, hs⟩ := run_bind_some hs
    cases hs
    rfl

/-- The program and section headers of the parse are its second and third steps. -/
theorem tables_of_parses {F : Blob} {A : File} (h : Parses F A) :
    (Parse.phdrs A.header).run (blobRead F) = some A.phdrs ∧
      (Parse.shdrs A.header).run (blobRead F) = some (A.sections.map (·.header)) := by
  unfold Parses parse read at h
  obtain ⟨hd, _, h⟩ := run_bind_some h
  obtain ⟨phs, e2, h⟩ := run_bind_some h
  obtain ⟨shs, e3, h⟩ := run_bind_some h
  obtain ⟨secs, e4, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  obtain ⟨_, _, h⟩ := run_bind_some h
  cases h
  exact ⟨e2, by rw [sections_headers e4]; exact e3⟩

theorem phdr_of_silmaril {F : Blob} {o : Nat} {p : Silmaril.Formats.ELF.ProgramHeader}
    (h : Blob.readProgramHeaderN F.n F.len o = some p) : (Parse.phdr o).run (blobRead F) = some p := by
  simp only [Blob.readProgramHeaderN, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, e0, f, e4, off, e8, va, e16, pa, e24, fs, e32, ms, e40, al, e48, rfl⟩ := h
  unfold Parse.phdr
  simp only [u32, u64]
  rw [run_read_of (r := blobRead F) _ e0, run_read_of (r := blobRead F) _ e4,
    run_read_of (r := blobRead F) _ e8, run_read_of (r := blobRead F) _ e16,
    run_read_of (r := blobRead F) _ e24, run_read_of (r := blobRead F) _ e32,
    run_read_of (r := blobRead F) _ e40, run_read_of (r := blobRead F) _ e48]
  rfl

theorem shdr_of_silmaril {F : Blob} {o : Nat} {p : SectionHeader}
    (h : Blob.readSectionHeaderN F.n F.len o = some p) : (Parse.shdr o).run (blobRead F) = some p := by
  simp only [Blob.readSectionHeaderN, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨k, e0, f, e4, fl, e8, ad, e16, off, e24, sz, e32, li, e40, inf, e44, al, e48, es, e56,
    rfl⟩ := h
  unfold Parse.shdr
  simp only [u32, u64]
  rw [run_read_of (r := blobRead F) _ e0, run_read_of (r := blobRead F) _ e4,
    run_read_of (r := blobRead F) _ e8, run_read_of (r := blobRead F) _ e16,
    run_read_of (r := blobRead F) _ e24, run_read_of (r := blobRead F) _ e32,
    run_read_of (r := blobRead F) _ e40, run_read_of (r := blobRead F) _ e44,
    run_read_of (r := blobRead F) _ e48, run_read_of (r := blobRead F) _ e56]
  rfl

theorem oguard_bind_some {β : Type} {c : Prop} [Decidable c] {f : Unit → Option β} {b : β}
    (h : (guard c >>= f) = some b) : c ∧ f () = some b := by
  by_cases hc : c
  · simp only [guard, hc, ↓reduceIte] at h; exact ⟨hc, h⟩
  · simp [guard, hc] at h

theorem phdrs_of_silmaril {F : Blob} {hd : Header} {ps : List Silmaril.Formats.ELF.ProgramHeader}
    (h : Silmaril.Formats.ELF.readProgramHeaders F.bytes hd = some ps) :
    (Parse.phdrs hd).run (blobRead F) = some ps := by
  rw [show F.bytes = Blob.bytesOf F.n F.len from rfl, Blob.readProgramHeaders_bytesOf] at h
  unfold Blob.readProgramHeadersN Blob.readTableN at h
  obtain ⟨_, h⟩ := oguard_bind_some h
  unfold Parse.phdrs
  by_cases h0 : hd.programCount = 0
  · rw [ite_t h0] at h ⊢
    cases h
    rfl
  · rw [ite_f h0] at h ⊢
    obtain ⟨⟨hes, _⟩, h⟩ := oguard_bind_some h
    obtain ⟨_, hm⟩ := oguard_bind_some h
    rw [run_guard_of _ hes]
    apply run_mapM
    exact List.Forall₂.imp (fun _ _ e => phdr_of_silmaril e) (forall₂_of_mapM_some _ _ hm)

theorem shdrs_of_silmaril {F : Blob} {hd : Header} {ss : List SectionHeader}
    (h : Silmaril.Formats.ELF.readSectionHeaders F.bytes hd = some ss) :
    (Parse.shdrs hd).run (blobRead F) = some ss := by
  rw [show F.bytes = Blob.bytesOf F.n F.len from rfl, Blob.readSectionHeaders_bytesOf] at h
  unfold Blob.readSectionHeadersN Blob.readTableN at h
  obtain ⟨_, h⟩ := oguard_bind_some h
  unfold Parse.shdrs
  by_cases h0 : hd.sectionCount = 0
  · rw [ite_t h0] at h ⊢
    obtain ⟨_, h⟩ := oguard_bind_some h
    cases h
    rfl
  · rw [ite_f h0] at h ⊢
    obtain ⟨⟨hes, _⟩, h⟩ := oguard_bind_some h
    obtain ⟨_, h⟩ := oguard_bind_some h
    obtain ⟨_, hm⟩ := oguard_bind_some h
    rw [run_guard_of _ hes]
    apply run_mapM
    exact List.Forall₂.imp (fun _ _ e => shdr_of_silmaril e) (forall₂_of_mapM_some _ _ hm)

/-- **`Task.tables_silmaril`**: whenever silmaril's table readers succeed, they agree with the
parse. -/
theorem tables_silmaril : Bridge.Task.tables_silmaril := by
  intro F A h
  obtain ⟨hp, hs⟩ := tables_of_parses h
  refine ⟨fun ps e => ?_, fun ss e => ?_⟩
  · exact Option.some.inj ((phdrs_of_silmaril e).symm.trans hp)
  · exact Option.some.inj ((shdrs_of_silmaril e).symm.trans hs)

/-- **`Task.header_silmaril`.** -/
theorem header_silmaril : Bridge.Task.header_silmaril :=
  fun _ _ h => readHeader_of_run (header_of_parses h)

end Silmaril.Elf.Check
