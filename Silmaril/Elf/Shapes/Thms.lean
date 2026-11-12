module

public import Silmaril.Elf.Shapes.Defs
public import Silmaril.Elf.Facts.Thms
public import Silmaril.Elf.Link.Dyn.Pages.Thms
public import Silmaril.Project.Shapes.Elf.Thms

/-! # Proving rows: checking programs, pages, compounds

PROVED (no `sorry`, no new axiom). How a row of `Silmaril.Elf.Shapes` is closed.

**1. Checking programs.** A fact is checked by one reading program `check p := read >>= p`: the
parse specification, then a check `p A : Rd Bool` on the AST that may read payload bytes (the
code of `CodeAt`). `of_check` turns a successful run on **any byte source** that agrees with the
file (`blobRead`, `pageRead` on its pages, `sparseRead` on chunks) into the parse and the check
on the file. Each fact has its program and soundness lemma:

| fact | program | lemma | pages form |
|---|---|---|---|
| `KindIs` | `kindP k` | `kindIs_of_check` | `kindIs_of_pages` |
| `SymbolAt` | `symbolP t i s` | `symbolAt_of_check` | `symbolAt_of_pages` |
| `Lookup` | `lookupP sel d` | `lookup_of_check` | `lookup_of_pages` |
| `Needed` | `neededP ns` | `needed_of_check` | `needed_of_pages` |
| `Relocs` | `relocsP sel rs` | `relocs_of_check` | `relocs_of_pages` |
| `Placement` | `placementP base` | `placement_of_check` | `placement_of_pages` |
| `CodeAt` | `codeP v code` | `codeAt_of_check` | `codeAt_of_pages'` |
| `Binds` | `bindsP sel v code` | `binds_of_check` | `binds_of_pages` |
| `EntryIs` | `entryP v` | `entryIs_of_check` | `entryIs_of_pages` |

A pages form is closed by `decide +kernel` on `(check …).run (pageRead 4096 pg) = some true`:
one kernel run of the specification on 4 KiB literals, never a 2 MB number.

**2. From a given parse.** When `Parses F A` is already known (a checker's output, or the
hypothesis of an open `parses` row), facts follow from `A` alone: `kindIs_of_parses`,
`lookup_of_parses`, …, `codeAt_of_pages` (`CodeAt` from the parse and one page read), and
`binds_of_index` (`Binds` from the lookup index and `CodeAt`, given the index builder's
`Task`s).

**3. Compounds.** `binds_of` builds a `Binds` row from its two parts, `Shapes.binds_iff` states
the shape-level conjunction, and `binds_lookup_frame` is the frame form of a compound: a binding
row transfers to any file with the same parse and the same code.
-/

@[expose] public section

namespace Silmaril.Elf

open Silmaril.Elf.Link.DynElf (Rd blobRead Chunk ChunksOf pageRead)
open Silmaril.X86.Link (Blob)
open Silmaril.Formats.ELF (NameBytes ObjectSymbol)

namespace Rows

/-! ## Checking programs -/

/-- **The checking program of `p`**: the parse specification, then `p` on the AST. -/
def check (p : File → Rd Bool) : Rd Bool := read.bind p

/-- A byte source agrees with the file `F`: every read it answers is a read of `F`. -/
def Agrees (F : Blob) (rd : Nat → Nat → Option Nat) : Prop :=
  ∀ o w v, rd o w = some v → blobRead F o w = some v

theorem agrees_blob (F : Blob) : Agrees F (blobRead F) := fun _ _ _ h => h

theorem agrees_pages {F : Blob} {c : Nat} {pg : List Chunk} (hc : ChunksOf F pg) :
    Agrees F (pageRead c pg) := fun _ _ _ h => Silmaril.Elf.Link.DynElf.pageRead_of hc h

theorem agrees_sparse {F : Blob} {cs : List Chunk} (hc : ChunksOf F cs) :
    Agrees F (Silmaril.Elf.Link.DynElf.sparseRead cs) :=
  fun _ _ _ h => Silmaril.Elf.Link.DynElf.sparseRead_of hc h

/-- **Soundness of a checking program**: a successful run on an agreeing source is the parse of
`F`, and the check passes on `F` itself. -/
theorem of_check {F : Blob} {rd : Nat → Nat → Option Nat} (hrd : Agrees F rd)
    {p : File → Rd Bool} (h : (check p).run rd = some true) :
    ∃ A, Parses F A ∧ (p A).run (blobRead F) = some true := by
  have h' := Rd.run_mono hrd _ _ h
  unfold check at h'
  rw [Silmaril.Elf.Link.DynElf.Rd.run_bind] at h'
  cases hA : read.run (blobRead F) with
  | none => rw [hA] at h'; cases h'
  | some A => rw [hA] at h'; exact ⟨A, hA, h'⟩

/-- A check of the AST alone (no payload read). -/
def pureP (q : File → Prop) [DecidablePred q] : File → Rd Bool := fun A => pure (decide (q A))

theorem of_pure {F : Blob} {rd : Nat → Nat → Option Nat} (hrd : Agrees F rd)
    {q : File → Prop} [DecidablePred q] (h : (check (pureP q)).run rd = some true) :
    ∃ A, Parses F A ∧ q A := by
  obtain ⟨A, hA, h⟩ := of_check hrd h
  refine ⟨A, hA, ?_⟩
  have : decide (q A) = true := Option.some.inj h
  exact of_decide_eq_true this

/-! ## The programs of the facts -/

def kindP (k : Kind) : File → Rd Bool := pureP fun A => A.kind = k

def symbolP (t : Table) (i : Nat) (s : ObjectSymbol) : File → Rd Bool :=
  pureP fun A => (A.symbols t)[i]? = some s

def lookupP (sel : Sel) (d : Option Def) : File → Rd Bool := pureP fun A => A.select sel = some d

def neededP (ns : List NameBytes) : File → Rd Bool := pureP fun A => A.needed = ns

def relocsP (sel : File.RelocSel) (rs : List File.Reloc) : File → Rd Bool :=
  pureP fun A => A.relocs sel = rs

/-- The placement condition of `Placement`, on an AST. -/
def PlacementOk (base : Nat) (A : File) : Prop :=
  (A.header.fileType = ET_EXEC ∧ base = 0 ∨ A.header.fileType = ET_DYN ∧ base % 4096 = 0) ∧
    ∀ ph ∈ A.loads, ph.fileSize ≤ ph.memorySize ∧ base + ph.virtualAddress + ph.memorySize ≤ 2 ^ 47

instance (base : Nat) : DecidablePred (PlacementOk base) := fun A => by
  unfold PlacementOk; infer_instance

def placementP (base : Nat) : File → Rd Bool := pureP (PlacementOk base)

def entryP (v : Nat) : File → Rd Bool := pureP fun A => A.header.entry = v

/-- The code check of `CodeAt` on `A`: the first read-only executable `PT_LOAD` mapping
`[v, v + |code|)`, and one wide read of the file there. -/
def codeP (v : Nat) (code : List (BitVec 8)) (A : File) : Rd Bool :=
  match A.phdrs.find? (codeSeg v code.length) with
  | none => pure false
  | some ph => .read (ph.offset + (v - ph.virtualAddress)) code.length fun x =>
      pure (x == Blob.valueLE code)

/-- The lookup part of `Binds`, on an AST. -/
def BindsDef (sel : Sel) (v : Nat) (A : File) : Prop :=
  ∃ d, A.select sel = some (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false

/-- `BindsDef` as a check. -/
def bindsDefB (sel : Sel) (v : Nat) (A : File) : Bool :=
  match A.select sel with
  | some (some d) => d.value == v && !d.ifunc && !d.abs
  | _ => false

theorem bindsDef_of_b {sel : Sel} {v : Nat} {A : File} (h : bindsDefB sel v A = true) :
    BindsDef sel v A := by
  unfold bindsDefB at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    exact ⟨d, hd, h.1.1, h.1.2, h.2⟩
  · cases h

/-- The check of `Binds` on `A`: the lookup, then the code. -/
def bindsP (sel : Sel) (v : Nat) (code : List (BitVec 8)) (A : File) : Rd Bool :=
  if bindsDefB sel v A then codeP v code A else pure false

/-! ## Soundness of each program -/

variable {F : Blob} {rd : Nat → Nat → Option Nat}

theorem kindIs_of_check (hrd : Agrees F rd) {k : Kind} (h : (check (kindP k)).run rd = some true) :
    KindIs F k := of_pure hrd h

theorem symbolAt_of_check (hrd : Agrees F rd) {t : Table} {i : Nat} {s : ObjectSymbol}
    (h : (check (symbolP t i s)).run rd = some true) : SymbolAt F t i s := of_pure hrd h

theorem lookup_of_check (hrd : Agrees F rd) {sel : Sel} {d : Option Def}
    (h : (check (lookupP sel d)).run rd = some true) : Lookup F sel d := of_pure hrd h

theorem needed_of_check (hrd : Agrees F rd) {ns : List NameBytes}
    (h : (check (neededP ns)).run rd = some true) : Needed F ns := of_pure hrd h

theorem relocs_of_check (hrd : Agrees F rd) {sel : File.RelocSel} {rs : List File.Reloc}
    (h : (check (relocsP sel rs)).run rd = some true) : Relocs F sel rs := of_pure hrd h

theorem placement_of_check (hrd : Agrees F rd) {base : Nat}
    (h : (check (placementP base)).run rd = some true) : Placement F base := of_pure hrd h

/-- The code check passes on the file: `F` holds `code` at `v` (given its parse). -/
theorem codeAt_of_codeP {A : File} (hA : Parses F A) {v : Nat} {code : List (BitVec 8)}
    (h : (codeP v code A).run (blobRead F) = some true) : CodeAt F v code := by
  refine ⟨A, hA, ?_⟩
  unfold codeP at h
  split at h
  · cases h
  · rename_i ph hph
    refine ⟨ph, hph, ?_⟩
    cases e : blobRead F (ph.offset + (v - ph.virtualAddress)) code.length with
    | none => rw [Rd.run_read_none _ e] at h; cases h
    | some x =>
      rw [Rd.run_read_some _ e] at h
      have : (x == Blob.valueLE code) = true := Option.some.inj h
      rw [beq_iff_eq.mp this]

theorem codeAt_of_check (hrd : Agrees F rd) {v : Nat} {code : List (BitVec 8)}
    (h : (check (codeP v code)).run rd = some true) : CodeAt F v code := by
  obtain ⟨A, hA, h⟩ := of_check hrd h
  exact codeAt_of_codeP hA h

theorem entryIs_of_check (hrd : Agrees F rd) {v : Nat}
    (h : (check (entryP v)).run rd = some true) : EntryIs F v := of_pure hrd h

/-! ## Several facts from one run -/

/-- **All the checks `ps`** on one AST (one parse for many rows: the parse is the expensive part
of a check, so a file's rows share one run). -/
def allP : List (File → Rd Bool) → File → Rd Bool
  | [], _ => pure true
  | p :: ps, A => (p A).bind fun b => if b then allP ps A else pure false

theorem allP_run {r : Nat → Nat → Option Nat} {A : File} :
    ∀ {ps : List (File → Rd Bool)}, (allP ps A).run r = some true →
      ∀ p ∈ ps, (p A).run r = some true
  | [], _, _, h => nomatch h
  | p :: ps, h, q, hq => by
    unfold allP at h
    rw [Silmaril.Elf.Link.DynElf.Rd.run_bind] at h
    cases e : (p A).run r with
    | none => rw [e] at h; cases h
    | some b =>
      rw [e] at h
      cases b with
      | false => cases h
      | true =>
        cases hq with
        | head => exact e
        | tail _ hq => exact allP_run h q hq

/-- **Soundness of a shared run**: the parse, and every check on the file. -/
theorem of_checkAll {F : Blob} {rd : Nat → Nat → Option Nat} (hrd : Agrees F rd)
    {ps : List (File → Rd Bool)} (h : (check (allP ps)).run rd = some true) :
    ∃ A, Parses F A ∧ ∀ p ∈ ps, (p A).run (blobRead F) = some true := by
  obtain ⟨A, hA, h⟩ := of_check hrd h
  exact ⟨A, hA, fun p hp => allP_run h p hp⟩

/-- A passing AST check is its proposition. -/
theorem pure_of_run {q : File → Prop} [DecidablePred q] {A : File} {r : Nat → Nat → Option Nat}
    (h : (pureP q A).run r = some true) : q A :=
  of_decide_eq_true (Option.some.inj h)

/-- A fact of the form `∃ A, Parses F A ∧ q A` from a passing check on the parse. -/
theorem holds {F : Blob} {A : File} (hA : Parses F A) {q : File → Prop} [DecidablePred q]
    {r : Nat → Nat → Option Nat} (h : (pureP q A).run r = some true) : ∃ A, Parses F A ∧ q A :=
  ⟨A, hA, pure_of_run h⟩

/-- `Binds` from a passing `bindsP` on the parse. -/
theorem binds_of_run {F : Blob} {A : File} (hA : Parses F A) {sel : Sel} {v : Nat}
    {code : List (BitVec 8)} (h : (bindsP sel v code A).run (blobRead F) = some true) :
    Binds F sel v code := by
  unfold bindsP at h
  split at h
  · rename_i hb
    obtain ⟨d, hd, hv, hi, ha⟩ := bindsDef_of_b hb
    exact ⟨⟨d, ⟨A, hA, hd⟩, hv, hi, ha⟩, codeAt_of_codeP hA h⟩
  · cases h

theorem binds_of_check (hrd : Agrees F rd) {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : (check (bindsP sel v code)).run rd = some true) : Binds F sel v code := by
  obtain ⟨A, hA, h⟩ := of_check hrd h
  exact binds_of_run hA h

/-! ## Pages forms -/

variable {c : Nat} {pg : List Chunk}

theorem kindIs_of_pages (hc : ChunksOf F pg) {k : Kind}
    (h : (check (kindP k)).run (pageRead c pg) = some true) : KindIs F k :=
  kindIs_of_check (agrees_pages hc) h

theorem symbolAt_of_pages (hc : ChunksOf F pg) {t : Table} {i : Nat} {s : ObjectSymbol}
    (h : (check (symbolP t i s)).run (pageRead c pg) = some true) : SymbolAt F t i s :=
  symbolAt_of_check (agrees_pages hc) h

theorem lookup_of_pages (hc : ChunksOf F pg) {sel : Sel} {d : Option Def}
    (h : (check (lookupP sel d)).run (pageRead c pg) = some true) : Lookup F sel d :=
  lookup_of_check (agrees_pages hc) h

theorem needed_of_pages (hc : ChunksOf F pg) {ns : List NameBytes}
    (h : (check (neededP ns)).run (pageRead c pg) = some true) : Needed F ns :=
  needed_of_check (agrees_pages hc) h

theorem relocs_of_pages (hc : ChunksOf F pg) {sel : File.RelocSel} {rs : List File.Reloc}
    (h : (check (relocsP sel rs)).run (pageRead c pg) = some true) : Relocs F sel rs :=
  relocs_of_check (agrees_pages hc) h

theorem placement_of_pages (hc : ChunksOf F pg) {base : Nat}
    (h : (check (placementP base)).run (pageRead c pg) = some true) : Placement F base :=
  placement_of_check (agrees_pages hc) h

theorem codeAt_of_pages' (hc : ChunksOf F pg) {v : Nat} {code : List (BitVec 8)}
    (h : (check (codeP v code)).run (pageRead c pg) = some true) : CodeAt F v code :=
  codeAt_of_check (agrees_pages hc) h

theorem binds_of_pages (hc : ChunksOf F pg) {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : (check (bindsP sel v code)).run (pageRead c pg) = some true) : Binds F sel v code :=
  binds_of_check (agrees_pages hc) h

theorem entryIs_of_pages (hc : ChunksOf F pg) {v : Nat}
    (h : (check (entryP v)).run (pageRead c pg) = some true) : EntryIs F v :=
  entryIs_of_check (agrees_pages hc) h

/-- **The pages of an included file are chunks of it**: `b` is `⟨include_bytes …⟩`, 4 KiB
chunk literals `cs` (as `Silmaril.Proofs.Spec.Lib.pages_of_decode`, for `blobOf`). -/
theorem pages_of_bytes {b : Silmaril.Formats.Bytes} {len : Nat} {cs : List Nat}
    (hb : b = ⟨Silmaril.IncludeBytes.decode 4096 len cs⟩) :
    ChunksOf (blobOf b) (Silmaril.Elf.Link.DynElf.pagesFrom 4096 0 len cs) := by
  unfold blobOf
  rw [Silmaril.Project.Shapes.blob_of_decode hb rfl]
  exact Silmaril.Elf.Link.DynElf.pagesFrom_zero_of 4096 len cs

/-- The parse itself, from a run on the pages (`silmaril.shapes.elf.parses` with a literal AST). -/
theorem parses_of_pages (hc : ChunksOf F pg) {A : File} (h : read.run (pageRead c pg) = some A) :
    Parses F A :=
  Rd.run_mono (agrees_pages hc) _ _ h

end Rows

/-! ## From a given parse -/

open Rows

variable {F : Blob} {A : File}

theorem kindIs_of_parses (hA : Parses F A) {k : Kind} (h : A.kind = k) : KindIs F k := ⟨A, hA, h⟩

theorem symbolAt_of_parses (hA : Parses F A) {t : Table} {i : Nat} {s : ObjectSymbol}
    (h : (A.symbols t)[i]? = some s) : SymbolAt F t i s := ⟨A, hA, h⟩

theorem lookup_of_parses (hA : Parses F A) {sel : Sel} {d : Option Def}
    (h : A.select sel = some d) : Lookup F sel d := ⟨A, hA, h⟩

theorem needed_of_parses (hA : Parses F A) {ns : List NameBytes} (h : A.needed = ns) :
    Needed F ns := ⟨A, hA, h⟩

theorem relocs_of_parses (hA : Parses F A) {sel : File.RelocSel} {rs : List File.Reloc}
    (h : A.relocs sel = rs) : Relocs F sel rs := ⟨A, hA, h⟩

theorem placement_of_parses (hA : Parses F A) {base : Nat} (h : PlacementOk base A) :
    Placement F base := ⟨A, hA, h⟩

theorem entryIs_of_parses (hA : Parses F A) {v : Nat} (h : A.header.entry = v) : EntryIs F v :=
  ⟨A, hA, h⟩

/-- **`CodeAt` from the parse and one page read** (`pageRead` on the file's pages; the read
may cross into the next page). -/
theorem codeAt_of_pages {c : Nat} {pg : List Chunk} (hc : ChunksOf F pg) (hA : Parses F A)
    {v : Nat} {code : List (BitVec 8)} {ph : Silmaril.Formats.ELF.ProgramHeader}
    (hph : A.phdrs.find? (codeSeg v code.length) = some ph)
    (hr : pageRead c pg (ph.offset + (v - ph.virtualAddress)) code.length = some (Blob.valueLE code)) :
    CodeAt F v code :=
  ⟨A, hA, ph, hph, Silmaril.Elf.Link.DynElf.pageRead_of hc hr⟩

/-! ## Compounds -/

/-- **`Binds` from its parts**: a lookup fact for a plain definition at `v`, and `CodeAt`. -/
theorem binds_of {sel : Sel} {v : Nat} {code : List (BitVec 8)} {d : Def}
    (hl : Lookup F sel (some d)) (hv : d.value = v) (hi : d.ifunc = false) (ha : d.abs = false)
    (hc : CodeAt F v code) : Binds F sel v code := ⟨⟨d, hl, hv, hi, ha⟩, hc⟩

/-- **`Binds` from the lookup index and `CodeAt`** (given the index builder's `Task`s). -/
theorem binds_of_index (hix : Task.index_lookup_sound) (hgs : Task.gnu_eq_scan)
    (hA : Parses F A) (hok : A.GnuHashOk) {ix : Index} (hb : Index.build A = some ix)
    {r : Ref} {d : Def} (hl : ix.lookup r false = some (some d)) (habs : d.abs = false)
    {v : Nat} (hv : d.value = v) (hi : d.ifunc = false) {code : List (BitVec 8)}
    (hc : CodeAt F v code) : Binds F (.dyn r) v code :=
  binds_of (lookup_of_index hix hgs hA hok hb hl habs) hv hi habs hc

/-- A binding's definition is unique: two binding rows of one selector agree on the address. -/
theorem Binds.value_unique {sel : Sel} {v v' : Nat} {code code' : List (BitVec 8)}
    (h : Binds F sel v code) (h' : Binds F sel v' code') : v = v' := by
  obtain ⟨⟨d, hd, hv, -⟩, -⟩ := h
  obtain ⟨⟨d', hd', hv', -⟩, -⟩ := h'
  cases Option.some.inj (Lookup.unique hd hd')
  exact hv.symm.trans hv'

/-- **Compound frame**: a binding row holds of every file with the same parse and the same code
bytes at the binding (the lookup half by `lookup_frame`, the code half by the one read). -/
theorem binds_frame {G : Blob} (hF : Parses F A) (hG : Parses G A) {sel : Sel} {v : Nat}
    {code : List (BitVec 8)} (h : Binds F sel v code)
    (hcode : ∀ ph, A.phdrs.find? (codeSeg v code.length) = some ph →
      blobRead G (ph.offset + (v - ph.virtualAddress)) code.length =
        blobRead F (ph.offset + (v - ph.virtualAddress)) code.length) :
    Binds G sel v code := by
  obtain ⟨⟨d, hd, hrest⟩, B, hB, ph, hph, hr⟩ := h
  cases parses_unique hF hB
  exact ⟨⟨d, (lookup_frame hF hG).1 hd, hrest⟩, A, hG, ph, hph, (hcode ph hph).trans hr⟩

namespace Shapes

open Silmaril.Project (Value)

variable {V : Type}

/-- **The `binds` shape is the conjunction** of a `lookup` row (a plain definition at `v`) and
a `code_at` row. -/
theorem binds_iff (X : Value V) (sel : Sel) (v : Nat) (code : List (BitVec 8)) :
    Binds X sel v code ↔
      (∃ d, Lookup X sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false) ∧
        CodeAt X v code := Iff.rfl

theorem Binds.lookup {X : Value V} {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : Binds X sel v code) :
    ∃ d, Lookup X sel (some d) ∧ d.value = v ∧ d.ifunc = false ∧ d.abs = false := h.1

theorem Binds.code {X : Value V} {sel : Sel} {v : Nat} {code : List (BitVec 8)}
    (h : Binds X sel v code) : CodeAt X v code := h.2

/-- A `kind` row (or any fact row) proves the value's `parses` obligation under `elf.ast`. -/
theorem parses_of_kind {X : Value V} {k : Kind} (h : KindIs X k) : ∃ A, Parses X A :=
  let ⟨A, hA, _⟩ := h; ⟨A, hA⟩

end Shapes

end Silmaril.Elf
