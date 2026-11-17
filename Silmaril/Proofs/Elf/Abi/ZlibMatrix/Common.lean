module

public import Silmaril.Elf.Abi.ZlibMatrix.Defs
public import Silmaril.Elf.Staged.Reader.Thms

/-! # The zlib library matrix: file-fact lemmas for any parsed file

Each lemma takes the file `F` and its parse `A0` (`Parses F A0`, as a pinned module's `parses`
gives it) and turns a decidable check on `A0` into the fact a row states. The per-binary modules
apply them with kernel computations on their own parse. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.ZlibMatrix

open Silmaril.Elf Silmaril.Elf.Abi
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)

variable {F : Blob} {A0 : File}

/-- Entry `i` of `.dynsym` is an `STT_FUNC` named `f`. -/
def funcSymB (A0 : File) (i : Nat) (f : String) : Bool :=
  match (A0.symbols .dynsym)[i]? with
  | some s => s.name == nameOf f && s.kind == 2
  | none => false

theorem funcSym (hp : Parses F A0) {i : Nat} {f : String} (h : funcSymB A0 i f = true) :
    ∃ s, SymbolAt F .dynsym i s ∧ s.name = nameOf f ∧ s.kind = 2 := by
  unfold funcSymB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, ⟨_, hp, hs⟩, h.1, h.2⟩
  · exact absurd h (by simp)

theorem codeOf (hp : Parses F A0) (b : Binding) (f : String) (c : Code) (i : Nat)
    (hb : b.table = .dynsym)
    (hl : A0.select (b.sel f) = some (some ⟨i, c.base.toNat + c.off, c.len, false, false⟩))
    (hs : funcSymB A0 i f = true) (hc : CodeAt F c.base.toNat c.bytes)
    (hd : ∀ d ∈ c.data, MappedAt F d.1.toNat d.2)
    (hi : c.image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)) :
    CodeOf F b f c :=
  ⟨⟨_, ⟨_, hp, hl⟩, rfl, rfl, rfl, rfl, hb ▸ funcSym hp hs⟩, hc, hd, ⟨_, hp, hi⟩⟩

/-- **An IFUNC is refused**: if the lookup finds an `STT_GNU_IFUNC` definition, no code is the
function of that binding. -/
theorem not_codeOf_ifunc (hp : Parses F A0) {b : Binding} {f : String} {d : Def}
    (hl : A0.select (b.sel f) = some (some d)) (hi : d.ifunc = true) (c : Code) :
    ¬ CodeOf F b f c := by
  rintro ⟨⟨d', ⟨A, hA, hs⟩, -, -, hf, -⟩, -⟩
  cases (Option.some.inj (hA.symm.trans hp) : A = A0)
  rw [hl] at hs
  cases hs
  rw [hi] at hf
  cases hf

/-- No dynamic relocation, `w` bytes each, writes `[v, v + n)` (the core's `Image.Misses`). -/
def missesAllB (A0 : File) (w v n : Nat) : Bool :=
  (A0.relocs .dynamic).all fun r => Silmaril.Elf.Image.Misses r.offset w v n

/-- Every dynamic relocation is `w` bytes wide (`File.relocWidth`) and neither `COPY` nor
`IRELATIVE`. -/
def widthsB (A0 : File) (w : Nat) : Bool :=
  (A0.relocs .dynamic).all fun r => A0.relocWidth r == some w && r.kind != R_X86_64_COPY &&
    r.kind != R_X86_64_IRELATIVE

/-- `Untouched` from the relocations' widths and kinds and the misses. -/
theorem untouched_of (hp : Parses F A0) {c : Code} {w : Nat} (hw : widthsB A0 w = true)
    (hc : missesAllB A0 w c.base.toNat c.bytes.length = true)
    (hd : ∀ d ∈ c.data, missesAllB A0 w d.1.toNat d.2.length = true) : Untouched F c := by
  have hw' := fun r hr => List.all_eq_true.mp hw r hr
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hw'
  refine ⟨_, hp, fun r hr => ⟨w, (hw' r hr).1.1, List.all_eq_true.mp hc r hr⟩,
    fun d hdm r hr => ⟨w, (hw' r hr).1.1, List.all_eq_true.mp (hd d hdm) r hr⟩,
    fun r hr => ⟨(hw' r hr).1.2, (hw' r hr).2⟩⟩

/-- Some table defines a function named `f` (the core's `File.definesFn`). -/
def presentB (A0 : File) (f : String) : Bool := A0.definesFn (nameOf f)

theorem present_of (hp : Parses F A0) {f : String} (h : presentB A0 f = true) : Present F f := ⟨_, hp, h⟩

/-- No table defines a symbol named `f` (the core's `File.definesName`). -/
def absentB (A0 : File) (f : String) : Bool := !A0.definesName (nameOf f)

theorem absent_of (hp : Parses F A0) {f : String} (h : absentB A0 f = true) : Absent F f :=
  ⟨_, hp, by simpa [absentB] using h⟩

/-- `Declares` from the decidable comparison of lowered signatures (as
`Proofs.Elf.Abi.ZlibRows.declares_of_sig`, which is another topic's proof module; follow-up: one
copy in `Machine.Abi.Conformance.Thms`). -/
theorem declares_of_sig {hdr : HeaderSrc} {f : String} {p : Silmaril.Machine.Abi.SystemV.Proto}
    (h : (hdr.proto? f).bind (fun cp => (sysvInt.lower cp).toOption.map (·.signature)) =
      some p.signature) :
    Declares sysvInt hdr f p := by
  cases hp : hdr.proto? f with
  | none => rw [hp] at h; cases h
  | some cp =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    cases hl : sysvInt.lower cp with
    | error e => rw [hl] at h; cases h
    | ok q =>
      rw [hl] at h
      have hs : q.signature = p.signature := Option.some.inj h
      have : q = p := by cases q; cases p; simp only at hs; subst hs; rfl
      exact ⟨cp, hp, this ▸ hl⟩

/-- A row from its file facts, a load base, and its open conformance at every admitted base. -/
theorem row {M : Mach} {hdr : HeaderSrc} {f : String} {p : Silmaril.Machine.Abi.SystemV.Proto}
    {b : Binding} {c : Code} {frame : Nat} {S : CallSpec sysvInt.V p} (hc : CodeOf F b f c)
    (hu : Untouched F c) (h0 : Placement F 0)
    (h : ∀ base, Placement F base → Conforms sysvInt M .total hdr f p (c.rebase base) frame S) :
    AbiConforms sysvInt M .total hdr f p F b c frame S :=
  ⟨hc, hu, ⟨0, h0⟩, h⟩

end Silmaril.Proofs.Elf.Abi.ZlibMatrix

end
