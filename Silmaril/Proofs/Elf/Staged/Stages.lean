module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.Elf.Link.Dyn.Elf.Thms

/-! # The stages of a parse are the parse

Proofs for `Silmaril.Elf.Staged.Thms` (standard axioms only). `read_run_eq` rewrites a run of
the whole-file reader `Silmaril.Elf.read` into the runs of the stage readers (`readLayout`,
`Parse.body` per section, `readLoader`), on any byte source; `parses_iff` follows. The windows
(`EntriesAt`, `TilesAt`) are lemmas about `List.mapM` runs and single reads.
-/

@[expose] public section

namespace Silmaril.Proofs.Elf.Staged

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Formats.ELF (Header ProgramHeader SectionHeader NameBytes Rela)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.X86.Link (Blob)

/-! ## Runs of `List.mapM` -/

theorem run_mapM_loop {α β : Type} (r : Src) (f : α → Rd β) : ∀ (l : List α) (acc : List β),
    (List.mapM.loop f l acc).run r = List.mapM.loop (fun a => (f a).run r) l acc
  | [], acc => rfl
  | a :: l, acc => by
    show ((f a).bind fun b => List.mapM.loop f l (b :: acc)).run r = _
    rw [Rd.run_bind]
    show _ = ((f a).run r).bind fun b => List.mapM.loop (fun a => (f a).run r) l (b :: acc)
    congr 1
    funext b
    exact run_mapM_loop r f l (b :: acc)

/-- **A `List.mapM` run is the `Option` `mapM` of the element runs.** -/
theorem run_mapM {α β : Type} (r : Src) (f : α → Rd β) (l : List α) :
    (l.mapM f).run r = l.mapM fun a => (f a).run r :=
  run_mapM_loop r f l []

theorem mapM_some_iff {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (out : List β), l.mapM f = some out ↔ List.Forall₂ (fun a b => f a = some b) l out
  | [], out => by cases out <;> simp
  | a :: l, out => by
    rw [List.mapM_cons]
    cases h : f a with
    | none => cases out <;> simp [h]
    | some b =>
      cases out with
      | nil => cases l.mapM f <;> simp
      | cons b' out =>
        simp only [List.forall₂_cons, h]
        rw [← mapM_some_iff f l out]
        cases l.mapM f <;> simp [eq_comm]

/-! ## The whole-file reader, staged -/

theorem run_pure {α : Type} (r : Src) (a : α) : (pure a : Rd α).run r = some a := rfl

theorem run_bind' {α β : Type} (r : Src) (p : Rd α) (f : α → Rd β) :
    (p >>= f).run r = (p.run r).bind fun a => (f a).run r := Rd.run_bind r p f

theorem run_ofOption {α : Type} (r : Src) (o : Option α) : (Rd.ofOption o).run r = o := by
  cases o <;> rfl

/-- The sections reader, element by element: name then body. -/
theorem run_sections (r : Src) (h : Header) (shs : List SectionHeader) :
    (Parse.sections h shs).run r =
      if shs.isEmpty then some [] else
        shs[h.sectionNameIndex]?.bind fun names =>
          shs.mapM fun sh => ((Parse.strAt names sh.name).run r).bind fun n =>
            ((Parse.body shs sh).run r).map fun b => (⟨sh, n, b⟩ : Section) := by
  unfold Parse.sections
  split
  · rfl
  · rw [run_bind', run_ofOption]
    congr 1; funext names
    rw [run_mapM]
    congr 1; funext sh
    rw [run_bind']
    congr 1; funext n
    rw [run_bind']
    cases (Parse.body shs sh).run r <;> rfl

/-- The stage-1 sections reader, element by element. -/
theorem run_readSecs (r : Src) (h : Header) (shs : List SectionHeader) :
    (readSecs h shs).run r =
      if shs.isEmpty then some [] else
        shs[h.sectionNameIndex]?.bind fun names =>
          shs.mapM fun sh => ((Parse.strAt names sh.name).run r).map fun n => (⟨sh, n⟩ : Sec) := by
  unfold readSecs
  split
  · rfl
  · rw [run_bind', run_ofOption]
    congr 1; funext names
    rw [run_mapM]
    congr 1; funext sh
    rw [run_bind']
    cases (Parse.strAt names sh.name).run r <;> rfl

theorem elem_iff (r : Src) (names : SectionHeader) (all : List SectionHeader) (sh : SectionHeader)
    (s : Section) :
    (((Parse.strAt names sh.name).run r).bind fun n =>
        ((Parse.body all sh).run r).map fun b => (⟨sh, n, b⟩ : Section)) = some s ↔
      ((Parse.strAt names sh.name).run r).map (fun n => (⟨sh, n⟩ : Sec)) =
          some ⟨s.header, s.name⟩ ∧ (Parse.body all s.header).run r = some s.body := by
  cases hn : (Parse.strAt names sh.name).run r with
  | none => simp
  | some n =>
    cases hb : (Parse.body all sh).run r with
    | none =>
      simp only [Option.bind_some, Option.map_none, Option.map_some, reduceCtorEq, false_iff,
        not_and, Option.some.injEq, Sec.mk.injEq]
      rintro ⟨rfl, -⟩; simp [hb]
    | some b =>
      obtain ⟨sh', n', b'⟩ := s
      simp only [Option.bind_some, Option.map_some, Option.some.injEq, Section.mk.injEq,
        Sec.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, rfl⟩, hb⟩
      · rintro ⟨⟨rfl, rfl⟩, h⟩; rw [hb] at h; exact ⟨rfl, rfl, Option.some.inj h⟩

theorem list_iff (r : Src) (names : SectionHeader) (all : List SectionHeader) :
    ∀ (l : List SectionHeader) (secs : List Section),
    List.Forall₂ (fun sh s => (((Parse.strAt names sh.name).run r).bind fun n =>
        ((Parse.body all sh).run r).map fun b => (⟨sh, n, b⟩ : Section)) = some s) l secs ↔
      List.Forall₂ (fun sh s => ((Parse.strAt names sh.name).run r).map (fun n => (⟨sh, n⟩ : Sec)) =
          some s) l (secs.map fun s => ⟨s.header, s.name⟩) ∧
        ∀ s ∈ secs, (Parse.body all s.header).run r = some s.body
  | [], secs => by cases secs <;> simp
  | sh :: l, [] => by simp
  | sh :: l, s :: secs => by
    rw [List.forall₂_cons, elem_iff, list_iff r names all l secs]
    simp only [List.map_cons, List.forall₂_cons, List.mem_cons, forall_eq_or_imp]
    tauto

/-- Element-wise: the sections are the named sections with their bodies. -/
theorem sections_iff (r : Src) (h : Header) (shs : List SectionHeader) (secs : List Section) :
    (Parse.sections h shs).run r = some secs ↔
      (readSecs h shs).run r = some (secs.map fun s => ⟨s.header, s.name⟩) ∧
        ∀ s ∈ secs, (Parse.body shs s.header).run r = some s.body := by
  rw [run_sections, run_readSecs]
  split
  · simp only [Option.some.injEq]
    constructor
    · rintro rfl; simp
    · rintro ⟨h1, -⟩
      cases secs with
      | nil => rfl
      | cons _ _ => simp at h1
  · cases shs[h.sectionNameIndex]? with
    | none => simp
    | some names =>
      simp only [Option.bind_some]
      rw [mapM_some_iff, mapM_some_iff]
      exact list_iff r names shs shs secs

theorem forall₂_headers {r : Src} {names : SectionHeader} : ∀ {l : List SectionHeader}
    {secs : List Sec}, List.Forall₂ (fun sh s => ((Parse.strAt names sh.name).run r).map
      (fun n => (⟨sh, n⟩ : Sec)) = some s) l secs → secs.map (·.header) = l
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hx hl => by
    simp only [Option.map_eq_some_iff] at hx
    obtain ⟨n, -, rfl⟩ := hx
    simp [forall₂_headers hl]

/-- The named sections keep the headers they were read from. -/
theorem readSecs_headers {r : Src} {h : Header} {shs : List SectionHeader} {secs : List Sec}
    (hs : (readSecs h shs).run r = some secs) : secs.map (·.header) = shs := by
  rw [run_readSecs] at hs
  split at hs
  · rename_i he
    simp only [Option.some.injEq] at hs
    subst hs
    simp only [List.isEmpty_iff] at he
    simp [he]
  · cases hn : shs[h.sectionNameIndex]? with
    | none => simp [hn] at hs
    | some names =>
      simp only [hn, Option.bind_some] at hs
      rw [mapM_some_iff] at hs
      exact forall₂_headers hs

/-- The whole-file reader, with its loader-view tail as `readLoader`. -/
theorem read_run (r : Src) :
    Silmaril.Elf.read.run r =
      (Parse.header.run r).bind fun h => ((Parse.phdrs h).run r).bind fun phs =>
        ((Parse.shdrs h).run r).bind fun shs => ((Parse.sections h shs).run r).bind fun secs =>
          ((readLoader phs).run r).map fun ld =>
            ⟨h, phs, secs, ld.dynamic, ld.interp, ld.needed, ld.soname, ld.runpath⟩ := by
  simp only [Silmaril.Elf.read, readLoader, run_bind', run_pure, Option.map_bind, Option.map_some,
    Function.comp_def]

/-- **A run of the whole-file reader is a run of the stage readers.** -/
theorem read_iff (r : Src) (A : File) :
    Silmaril.Elf.read.run r = some A ↔
      readLayout.run r = some A.layout ∧
        (∀ s ∈ A.sections, (Parse.body A.layout.shs s.header).run r = some s.body) ∧
        (readLoader A.phdrs).run r = some A.loader := by
  rw [read_run]
  unfold readLayout
  simp only [run_bind', run_pure, Option.bind_eq_some_iff, Option.map_eq_some_iff,
    Option.some.injEq]
  constructor
  · rintro ⟨h, hh, phs, hp, shs, hsh, secs, hsec, ld, hld, rfl⟩
    obtain ⟨h1, h2⟩ := (sections_iff r h shs secs).mp hsec
    have hshs := readSecs_headers h1
    refine ⟨⟨h, hh, phs, hp, shs, hsh, _, h1, rfl⟩, ?_, hld⟩
    intro s hs
    have : (File.layout ⟨h, phs, secs, ld.dynamic, ld.interp, ld.needed, ld.soname,
        ld.runpath⟩).shs = shs := by
      rw [← hshs]; simp [File.layout, Layout.shs]
    rw [this]; exact h2 s hs
  · rintro ⟨⟨h, hh, phs, hp, shs, hsh, secs', h1, hL⟩, h2, hld⟩
    obtain ⟨A0, A1, A2, A3, A4, A5, A6, A7⟩ := A
    simp only [File.layout, Layout.mk.injEq] at hL
    obtain ⟨rfl, rfl, rfl⟩ := hL
    have hshs := readSecs_headers h1
    refine ⟨h, hh, phs, hp, shs, hsh, A2, (sections_iff r h shs A2).mpr ⟨h1, ?_⟩, _, hld, rfl⟩
    intro s hs
    have := h2 s hs
    have e : (File.layout ⟨h, phs, A2, A3, A4, A5, A6, A7⟩).shs = shs := by
      rw [← hshs]; simp [File.layout, Layout.shs]
    rwa [e] at this

theorem zip_names {P : Sec → Body → Prop} : ∀ {secs : List Sec} {bodies : List Body},
    List.Forall₂ P secs bodies →
      (secs.zipWith (fun s b => (⟨s.header, s.name, b⟩ : Section)) bodies).map
        (fun s => (⟨s.header, s.name⟩ : Sec)) = secs
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [zip_names h]

theorem zip_mem {P : SectionHeader → Body → Prop} : ∀ {secs : List Sec} {bodies : List Body},
    List.Forall₂ (fun s b => P s.header b) secs bodies →
      ∀ s ∈ secs.zipWith (fun s b => (⟨s.header, s.name, b⟩ : Section)) bodies, P s.header s.body
  | [], [], .nil => by simp
  | _ :: _, _ :: _, .cons hx h => by
    intro s hs
    simp only [List.zipWith_cons_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hx
    · exact zip_mem h s hs

/-- **Assembling a parse from its stages.** -/
theorem read_assemble {r : Src} {L : Layout} {bodies : List Body} {ld : Loader}
    (hL : readLayout.run r = some L)
    (hb : List.Forall₂ (fun s b => (Parse.body L.shs s.header).run r = some b) L.sections bodies)
    (hld : (readLoader L.phdrs).run r = some ld) :
    Silmaril.Elf.read.run r = some (L.assemble bodies ld) := by
  have hlay : (L.assemble bodies ld).layout = L := by
    obtain ⟨h, phs, secs⟩ := L
    simp only [Layout.assemble, File.layout, Layout.mk.injEq, true_and]
    exact zip_names hb
  refine (read_iff r _).mpr ⟨by rw [hlay]; exact hL, ?_, hld⟩
  rw [hlay]
  exact zip_mem (P := fun sh b => (Parse.body L.shs sh).run r = some b) hb

/-! ## Records and windows -/

theorem forall₂_range {α : Type} {P : Nat → α → Prop} :
    ∀ (k : Nat) (es : List α), List.Forall₂ P (List.range k) es ↔
      es.length = k ∧ ∀ j (hj : j < es.length), P j es[j]
  | k, es => by
    rw [List.forall₂_iff_get]
    simp only [List.length_range, List.get_eq_getElem, List.getElem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun j hj => h2 j (h1 ▸ hj) hj⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun j _ hj => h2 j hj⟩

/-- **A table run is its record runs.** -/
theorem records_iff {α : Type} (r : Src) (o w k : Nat) (p : Nat → Rd α) (es : List α) :
    (Parse.records o w k p).run r = some es ↔
      es.length = k ∧ ∀ j (hj : j < es.length), (p (o + w * j)).run r = some es[j] := by
  unfold Parse.records
  rw [run_mapM, mapM_some_iff, forall₂_range]

theorem entriesAt_append {α : Type} {F : Blob} {p : Nat → Rd α} {o w i : Nat}
    {es₁ es₂ : List α} :
    EntriesAt F p o w i (es₁ ++ es₂) ↔
      EntriesAt F p o w i es₁ ∧ EntriesAt F p o w (i + es₁.length) es₂ := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j (by simp; omega)
      rwa [List.getElem_append_left hj] at this
    · have := h (es₁.length + j) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simp only [Nat.add_sub_cancel_left] at this
      rwa [Nat.add_assoc]
  · rintro ⟨h1, h2⟩ j hj
    by_cases hj1 : j < es₁.length
    · rw [List.getElem_append_left hj1]; exact h1 j hj1
    · rw [List.getElem_append_right (by omega)]
      have := h2 (j - es₁.length) (by simp at hj; omega)
      rwa [Nat.add_assoc, Nat.add_sub_cancel' (by omega)] at this

theorem entriesAt_of_ok {α : Type} [BEq α] [LawfulBEq α] {r : Src} {F : Blob} (hs : Sub r F)
    {p : Nat → Rd α} {o w : Nat} : ∀ (i : Nat) (es : List α),
    entriesOk r p o w i es = true → EntriesAt F p o w i es
  | _, [], _ => fun j hj => absurd hj (by simp)
  | i, e :: es, h => by
    simp only [entriesOk, Bool.and_eq_true, beq_iff_eq] at h
    have h0 := Rd.run_mono hs _ _ h.1
    have ht := entriesAt_of_ok hs (i + 1) es h.2
    rw [show e :: es = [e] ++ es from rfl, entriesAt_append]
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · simp at hj; subst hj; simpa using h0
    · simpa [Nat.add_comm 1 i] using ht j hj

/-- **A `RELA` section's body from a window covering it.** -/
theorem body_relas_iff {r : Src} {all : List SectionHeader} {sh : SectionHeader} {es : List Rela}
    (hk : sh.kind = SHT_RELA) :
    (Parse.body all sh).run r = some (.relas es) ↔
      sh.entrySize = 24 ∧ es.length = sh.size / 24 ∧
        ∀ j (hj : j < es.length), (Parse.rela (sh.offset + 24 * j)).run r = some es[j] := by
  simp only [Parse.body, hk, SHT_RELA, SHT_NULL, SHT_NOBITS, SHT_PROGBITS, SHT_STRTAB, SHT_SYMTAB,
    SHT_DYNSYM, Nat.reduceEqDiff, ite_false, false_or, ite_true]
  by_cases he : sh.entrySize = 24
  · simp only [Rd.guard, he, ite_true, run_bind', run_pure]
    show ((Parse.records _ _ _ _).run r).bind _ = _ ↔ _
    cases hr : (Parse.records sh.offset 24 (sh.size / 24) Parse.rela).run r with
    | none =>
      simp only [Option.bind_none, reduceCtorEq, false_iff, true_and, not_and]
      intro hl hj
      have := (records_iff r _ _ _ _ es).mpr ⟨hl, hj⟩
      rw [hr] at this; cases this
    | some es' =>
      simp only [Option.bind_some, Option.some.injEq, Body.relas.injEq, true_and]
      rw [records_iff] at hr
      constructor
      · rintro rfl; exact hr
      · rintro ⟨hl, hj⟩
        apply List.ext_getElem (by omega)
        intro j h1 h2
        have := hr.2 j h1
        rw [hj j h2] at this
        exact (Option.some.inj this).symm
  · simp only [Rd.guard, he, ite_false, run_bind', false_and, iff_false]
    exact fun h => nomatch h

/-! ## Tiles -/

theorem tilesAt_of_ok {r : Src} {F : Blob} (hs : Sub r F) {ok : Nat → Nat → Bool} :
    ∀ (o : Nat) (lens : List Nat), tilesOk r ok o lens = true → TilesAt F ok o lens
  | _, [], _ => trivial
  | o, l :: ls, h => by
    simp only [tilesOk, Bool.and_eq_true] at h
    refine ⟨?_, tilesAt_of_ok hs (o + l) ls h.2⟩
    obtain ⟨h1, -⟩ := h
    cases e : r o l with
    | none => simp [e] at h1
    | some v => simp only [e] at h1; exact ⟨v, hs o l v e, h1⟩

end Silmaril.Proofs.Elf.Staged

namespace Silmaril.Proofs.Elf.Staged

open Silmaril.Elf
open Silmaril.Elf.Staged
open Silmaril.Formats.ELF (SectionHeader Rela)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

theorem parses_iff (F : Blob) (A : File) :
    Parses F A ↔ LayoutIs F A.layout ∧ (∀ s ∈ A.sections, BodyIs F A.layout s.header s.body) ∧
      LoaderIs F A.layout A.loader :=
  read_iff (blobRead F) A

theorem parses_assemble {F : Blob} {L : Layout} {bodies : List Body} {ld : Loader}
    (hL : LayoutIs F L) (hb : List.Forall₂ (fun s b => BodyIs F L s.header b) L.sections bodies)
    (hld : LoaderIs F L ld) : Parses F (L.assemble bodies ld) :=
  read_assemble hL hb hld

theorem bodyIs_relas_iff {F : Blob} {L : Layout} {sh : SectionHeader} {es : List Rela}
    (hk : sh.kind = SHT_RELA) :
    BodyIs F L sh (.relas es) ↔
      sh.entrySize = 24 ∧ es.length = sh.size / 24 ∧ EntriesAt F Parse.rela sh.offset 24 0 es := by
  unfold BodyIs EntriesAt
  rw [body_relas_iff hk]
  simp only [Nat.zero_add]

end Silmaril.Proofs.Elf.Staged
