module

public import Silmaril.Process.CLI.X86Linux
public import Silmaril.Process.CLI.StaticElf

/-! # Static launches: the auxiliary vector names the image's own program headers

`X86Linux.Loaded` leaves the auxiliary vector free beyond `AT_NULL` and `AT_RANDOM`,
and allows any further mappings. A statically linked libc reads its program headers
through `AT_PHDR`/`AT_PHENT`/`AT_PHNUM` before `main` (musl: `__init_libc`, then
`static_init_tls`, which copies the `PT_TLS` initializer it finds there). So a launch
could point startup at a forged table and run code of its choice before `main`
(erebor-lean #70). `LoadedStatic` is `Loaded` plus `Static`:

* **The table** (`StaticTable`): the image's program-header table, derived from its
  file bytes and checked (`Image.StaticTable`, in `StaticElf`).
* **The vectors as libc parses them** (`StackVectors`): `envp` has no NULL entry
  and no auxiliary entry has tag `AT_NULL`, so the auxiliary vector musl's
  `__init_libc` scans (from after `envp`'s NULL to the first `AT_NULL` tag) is exactly
  the listed one. `StackVectors.auxv_unique`: any two such readings of one stack agree.
* **The pinned entries** (`AuxvPinned`): `AT_PHDR`, `AT_PHENT`, `AT_PHNUM` and
  `AT_PAGESZ` each occur exactly once, with the table's address, `56`, the table's
  count and `4096`; `AT_SYSINFO_EHDR` is absent (the vDSO is not modelled, and musl
  would otherwise call into an ELF image the launch chose).
* **Mappings** (`ExecFromImage`, `NoAlias`): every executable mapping is one of the
  image's segments (there is no vDSO in this model), and no mapping overlaps a
  segment except that segment's own region.

`LoadedStatic.loaded`: every static launch is a launch, so every universal statement
(`Agrees`, `Covered`, `Halts`, `Bounded`) over `Loaded` holds over `LoadedStatic`
(`staticModel_le`). Existential statements (nonvacuity witnesses) over `Loaded` do
not transfer and must be re-proved with a static launch.

`LoadedStatic.headers`: in a static launch, the table libc reads at `AT_PHDR`, of
`AT_PHNUM` entries of `AT_PHENT` bytes, is readable and holds exactly the file's
program-header bytes, for every reading of the stack.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.Process
open Silmaril.X86 (Word)
open Silmaril.Machine.LittleEndian (encodeWords wordByte)

/-! ## Definitions -/

def atPhdr : Word := 3
def atPhent : Word := 4
def atPhnum : Word := 5
def atSysinfoEhdr : Word := 33

/-- The values of the auxiliary entries with tag `tag`, in order. -/
def auxvValues (auxv : List (Word × Word)) (tag : Word) : List Word :=
  (auxv.filter fun entry => entry.1 == tag).map Prod.snd

/-- The auxiliary vector names `table`, unambiguously, with the x86-64 page size and
without a vDSO. -/
def AuxvPinned (table : HeaderTable) (auxv : List (Word × Word)) : Prop :=
  auxvValues auxv atPhdr = [BitVec.ofNat 64 table.address] ∧
  auxvValues auxv atPhent = [BitVec.ofNat 64 Elf.phentSize] ∧
  auxvValues auxv atPhnum = [BitVec.ofNat 64 table.count] ∧
  auxvValues auxv atPagesz = [BitVec.ofNat 64 Elf.pageSize] ∧
  auxvValues auxv atSysinfoEhdr = []

instance (table : HeaderTable) (auxv : List (Word × Word)) : Decidable (AuxvPinned table auxv) := by
  unfold AuxvPinned; infer_instance

/-- The vectors at `sp`, read as libc's startup reads them: `argc` words of `argv`, then
`envp` up to its first NULL, then auxiliary pairs up to the first `AT_NULL` tag. -/
def StackVectors (input : ProcInput) (memory : Memory) (sp : Nat)
    (argv envp : List Word) (auxv : List (Word × Word)) : Prop :=
  argv.length = input.argv.length ∧ envp.length = input.envp.length ∧
  BytesAt memory sp (encodeWords (vectorWords argv envp auxv)) ∧
  (0 : Word) ∉ envp ∧ ∀ entry ∈ auxv, entry.1 ≠ atNull

/-- The stack names the image's table. -/
def StaticStack (table : HeaderTable) (input : ProcInput) (memory : Memory) (sp : Nat) : Prop :=
  ∃ argv envp auxv, StackVectors input memory sp argv envp auxv ∧ AuxvPinned table auxv

/-- Every executable mapping is an image segment. -/
def ExecFromImage (image : Image) (memory : Memory) : Prop :=
  ∀ region ∈ memory.regions, region.permissions.execute = true →
    region ∈ image.segments.map Segment.region

/-- No mapping overlaps a segment except that segment's own region. -/
def NoAlias (image : Image) (memory : Memory) : Prop :=
  ∀ region ∈ memory.regions, ∀ segment ∈ image.segments,
    region = segment.region ∨ region.Disjoint segment.region

/-- The conditions a static launch adds to `Loaded`. -/
structure Static (image : Image) (input : ProcInput) (core : Core) (memory : Memory) : Prop where
  table : ∃ table, image.StaticTable table ∧ StaticStack table input memory (core.read .rsp).toNat
  exec : ExecFromImage image memory
  noAlias : NoAlias image memory

/-- **The static loader**: `Loaded`, and the launch names the image's own program headers. -/
def LoadedStatic (image : Image) (input : ProcInput) (core : Core) (memory : Memory) : Prop :=
  Loaded image input core memory ∧ Static image input core memory

theorem LoadedStatic.loaded {image : Image} {input : ProcInput} {core : Core} {memory : Memory}
    (h : LoadedStatic image input core memory) : Loaded image input core memory := h.1

/-- The static loader is a lower point on the loader axis. -/
theorem staticModel_le (env : Env) (envInit : ProcInput → Memory → env.State → Prop) :
    ({ model env envInit with load := LoadedStatic } : Model).Le (model env envInit) :=
  ⟨{ isa := Isa.Sim.id isa
     env := Env.Sim.id env
     envInit := fun {_ _ s} init => ⟨s, init, rfl⟩
     load := fun {_ _ c _} load => ⟨c, load.1, rfl⟩ }⟩

/-! ## The stack is read unambiguously -/

/-- Two reads at one address agree where both are defined. -/
theorem BytesAt.agree {memory : Memory} {address : Nat} {xs ys : List Byte}
    (hx : BytesAt memory address xs) (hy : BytesAt memory address ys) {i : Nat}
    (hi : i < xs.length) (hj : i < ys.length) : xs[i]? = ys[i]? := by
  have a := Memory.readWith_get (access := .read) hx i hi
  have b := Memory.readWith_get (access := .read) hy i hj
  rw [a] at b
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, b]

/-- A word is determined by its eight little-endian bytes. -/
theorem wordByte_inj {v w : Word} (h : ∀ b < 8, wordByte v b = wordByte w b) : v = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun x : BitVec 8 => x.getLsbD (i % 8)) (h (i / 8) (by omega))
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : 8 * (i / 8) + i % 8 = i := Nat.div_add_mod i 8
  simpa [wordByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hm, he] using hb

/-- Two word lists read at one address agree where both are defined. -/
theorem BytesAt.words_agree {memory : Memory} {address : Nat} {ws vs : List Word}
    (hx : BytesAt memory address (encodeWords ws)) (hy : BytesAt memory address (encodeWords vs))
    {k : Nat} (hk : k < ws.length) (hk' : k < vs.length) : ws[k]? = vs[k]? := by
  rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
  congr 1
  apply wordByte_inj
  intro b hb
  have agree := hx.agree hy (i := 8 * k + b) (by simp; omega) (by simp; omega)
  rw [Silmaril.Machine.LittleEndian.encodeWords_byte ws ⟨k, hk⟩ ⟨b, hb⟩,
    Silmaril.Machine.LittleEndian.encodeWords_byte vs ⟨k, hk'⟩ ⟨b, hb⟩] at agree
  exact Option.some.inj agree

/-- The auxiliary words: the pairs, then `(AT_NULL, 0)`. -/
def auxWords (auxv : List (Word × Word)) : List Word :=
  auxv.flatMap (fun entry => [entry.1, entry.2]) ++ [atNull, 0]

theorem vectorWords_eq (argv envp : List Word) (auxv : List (Word × Word)) :
    vectorWords argv envp auxv =
      ([BitVec.ofNat 64 argv.length] ++ argv ++ [0] ++ envp ++ [0]) ++ auxWords auxv := by
  simp [vectorWords, auxWords, List.append_assoc]

/-- Auxiliary vectors without `AT_NULL` tags whose words agree are equal. -/
theorem auxv_eq_of_agree : ∀ (first second : List (Word × Word)),
    (∀ entry ∈ first, entry.1 ≠ atNull) → (∀ entry ∈ second, entry.1 ≠ atNull) →
    (∀ j, j < (auxWords first).length → j < (auxWords second).length →
      (auxWords first)[j]? = (auxWords second)[j]?) → first = second
  | [], [], _, _, _ => rfl
  | [], entry :: _, _, h₂, agree => by
    have := agree 0 (by simp [auxWords]) (by simp [auxWords])
    simp [auxWords] at this
    exact absurd this.symm (h₂ entry (by simp))
  | entry :: _, [], h₁, _, agree => by
    have := agree 0 (by simp [auxWords]) (by simp [auxWords])
    simp [auxWords] at this
    exact absurd this (h₁ entry (by simp))
  | e :: first, f :: second, h₁, h₂, agree => by
    have tag := agree 0 (by simp [auxWords]) (by simp [auxWords])
    have value := agree 1 (by simp [auxWords]) (by simp [auxWords])
    simp only [auxWords, List.flatMap_cons, List.cons_append, List.nil_append,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at tag value
    have rest := auxv_eq_of_agree first second (fun x hx => h₁ x (by simp [hx]))
      (fun x hx => h₂ x (by simp [hx])) (fun j hj hj' => by
        have := agree (j + 2) (by simp [auxWords] at hj ⊢; omega) (by simp [auxWords] at hj' ⊢; omega)
        simpa [auxWords] using this)
    rw [Prod.ext tag value, rest]

/-- **The auxiliary vector libc reads is unique**: any two readings of one stack, for
one input, have the same auxiliary vector. -/
theorem StackVectors.auxv_unique {input : ProcInput} {memory : Memory} {sp : Nat}
    {argv envp argv' envp' : List Word} {auxv auxv' : List (Word × Word)}
    (h : StackVectors input memory sp argv envp auxv)
    (h' : StackVectors input memory sp argv' envp' auxv') : auxv = auxv' := by
  obtain ⟨la, le, bytes, -, tags⟩ := h
  obtain ⟨la', le', bytes', -, tags'⟩ := h'
  apply auxv_eq_of_agree auxv auxv' tags tags'
  intro j hj hj'
  have agree := bytes.words_agree bytes'
    (k := argv.length + envp.length + 3 + j)
    (by rw [vectorWords_eq]; simp; omega) (by rw [vectorWords_eq]; simp; omega)
  rw [vectorWords_eq, vectorWords_eq] at agree
  have n₁ : ([BitVec.ofNat 64 argv.length] ++ argv ++ [0] ++ envp ++ [(0 : Word)]).length =
      argv.length + envp.length + 3 := by simp; omega
  have n₂ : ([BitVec.ofNat 64 argv'.length] ++ argv' ++ [0] ++ envp' ++ [(0 : Word)]).length =
      argv.length + envp.length + 3 := by simp; omega
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), n₁, n₂] at agree
  simpa using agree

/-! ## Startup reads the file's program headers -/

/-- **Startup's header reads use the mapped file bytes.** In a static launch there is
one table: it is the image's (`StaticTable`); its address fits a word; the
`table.size = AT_PHNUM * AT_PHENT` bytes at `AT_PHDR` are readable and are the
file's program-header bytes; and every reading of the stack libc can make has the
auxiliary vector pinned to it. -/
theorem LoadedStatic.headers {image : Image} {input : ProcInput} {core : Core} {memory : Memory}
    (h : LoadedStatic image input core memory) :
    ∃ table, image.StaticTable table ∧
      (BitVec.ofNat 64 table.address).toNat = table.address ∧
      memory.readBytes table.address table.size = some table.bytes ∧
      ∀ argv envp auxv, StackVectors input memory (core.read .rsp).toNat argv envp auxv →
        AuxvPinned table auxv := by
  obtain ⟨⟨mapped, -⟩, ⟨table, static, argv, envp, auxv, vectors, pinned⟩, -, -⟩ := h
  obtain ⟨count, fits, headOk, limit, -⟩ := static.2
  refine ⟨table, static, ?_, ?_, fun argv' envp' auxv' vectors' => ?_⟩
  · have : table.address < 2 ^ 64 := by
      have : 1 ≤ table.size := by simp only [HeaderTable.size, Elf.phentSize]; omega
      simp only [addressLimit] at limit; omega
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt this
  · obtain ⟨segment, head, base, file⟩ := Image.headerTable?_segment static.1
    have member : segment ∈ image.segments := List.mem_of_mem_head? head
    rw [head] at headOk
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at headOk
    obtain ⟨readable, filesFit⟩ := headOk
    obtain ⟨inMemory, contents⟩ := mapped segment member
    have length := HeaderTable.bytes_length fits
    have hsize : 1 ≤ table.size := by simp only [HeaderTable.size, Elf.phentSize]; omega
    have permitted : memory.Permitted .read table.address table.bytes.length := by
      rw [length]
      refine Memory.permitted_of_region memory .read _ _ segment.region inMemory readable
        (by simp only [addressLimit] at limit ⊢; omega) limit ?_ ?_
      · simp only [Segment.region, HeaderTable.address]; omega
      · simp only [Segment.region, HeaderTable.address]
        rw [file] at filesFit; omega
    have read := Memory.readWith_eq memory .read table.address table.bytes permitted (by
      intro index bound
      rw [length] at bound
      have inFile : table.offset + index < segment.fileBytes.length := by rw [file]; omega
      have inContents : table.offset + index < segment.contents.length := by
        simp only [Segment.contents, List.length_append]; omega
      have := contents (table.offset + index) inContents
      rw [show segment.vaddr + (table.offset + index) = table.address + index by
        simp only [HeaderTable.address]; omega] at this
      rw [this]
      congr 1
      simp only [Segment.contents, HeaderTable.bytes]
      rw [List.getElem_append_left inFile, List.getElem_take, List.getElem_drop]
      simp only [file])
    rw [length] at read
    exact read
  · rw [← vectors.auxv_unique vectors']
    exact pinned

end Silmaril.Process.CLI.X86Linux
