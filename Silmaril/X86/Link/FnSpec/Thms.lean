module

public import Silmaril.X86.Link.FnSpec.Defs
public import Silmaril.X86.Link.Contract.Thms
public import Silmaril.X86.Link.Validate.Thms
public import Silmaril.X86.Sep.SysV.Thms
public import Silmaril.X86.Safe.Thms
import Silmaril.Proofs.X86.Link.FnSpec.Data
import Silmaril.Proofs.X86.Link.FnSpec.CallSite

/-! # The `FnSpec` logic for `link_compose`: theorems (header)

Proved with the standard axioms; the proofs are in `Silmaril.Proofs.X86.Link.FnSpec.*`. Every
statement holds on any machine `I : SegVC.Isa σ`; the bridges from total triples need
`E : Open.isa.Extends I` (`Isa.Extends.refl _`, `Open9.extendsOpen`, `Str9.extendsOpen`).

**The logic** (`Logic`):
* `logicOn I : Contract.Logic FnSpec` on any machine `I`, and `logic := logicOn Open.isa`,
  with `Safe := SafeOn I`, the laws `safe_zero`, `safe_mono`, `safe_frame` and `safe_sub`
  (`Sub := FnSpec.Sub`).
* `SafeN`, `STriple` and `Progress` are those of `Silmaril.X86.Safe`, with its lemmas.
* Code regions: `code_congr`, `code_split_byte`, `code_split`.

**Unit contracts** (`Unit`):
* `tu_sat_of_code`: a relocation-free unit whose exports are `unverified` or have
  position-independent `FnSpec.Sat` proofs (`ExportCode`) satisfies `TU.Sat logic` for every
  relocator. `safe_of_sat`, `safe_unverified`, `image_mem`, `exportCode_contains`.

**Call sites** (`Step`, `CallSite`):
* `aluI8_step`: the `op $imm8,%r64` triple. `code_triple`: instruction triples inside a code
  region. `scall_rule`: the step-indexed call rule (a call to a `Safe n` import is one
  instruction at index `n + 1`).

**Loaded executables** (`Load`):
* `validated_compose`: from `Validated objs exe W` (`validate_sound`), prepared objects equal
  to the units' objects, `TU.Sat`, `AbiCompatible` and `ImportsClosed`, every export at its
  linked address is `(logicOn I).Safe n` in the linked image and `SafeN I n` from every live
  state of `I` that holds the executable's loader image. `Code` covers the executable
  sections only (`ContainsX`, `Dom`); the data sections are in the frame.
* `linkSection_meta`, `link_meta`, `containsF_loaded`, `contains_loaded`, `ContainsX.contains`,
  `code_onBytes`, `sep_onBytes`.

**Data sections** (`Data`):
* `data_section_ro`, `data_section_rw`: in a validated link, every non-executable section
  `s` is `bytesPtRO s.address (expected s) ∗ ⊤` (its data then its zero fill, so `.bss` is
  covered; `bytesPt …` if writable) in the frame
  `offBytes (Dom out) (toFrag m)` of every machine that holds the loader image with its
  permissions (`ImageLoaded`, `ImagePerms`); this is the frame `validated_compose` hands to an
  export's precondition. `data_loaded` (the whole `DataPt out`), `containsM_loaded`,
  `expected_length`, `not_dom_of_data`,
  `region_split_byte`, `region_split`, `pairwise_ne`.

Assumed / modelled (not proved): the open x86 machine (`Silmaril.X86.Ext`/`Ext8` semantics),
`ImageLoaded` as the meaning of "the executable is loaded", and the readers and linker that
`Validated` mentions (see `Silmaril.X86.Link.Validate.Thms`). `Safe` is partial correctness:
it does not claim termination. `Code` asks for execute permission on the bytes of executable
sections only; read-only and writable sections are owned through the frame (`DataPt`,
`bytesPtRO`, `bytesPt`); see `Silmaril.X86.Link.FnSpec.Defs`.
-/

@[expose] public section

namespace Silmaril.X86.Link.FnSpec

open Silmaril.X86 (MState Word Byte Reg)
open Silmaril.Process (addressLimit)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le)
open Silmaril.X86.Safe
variable {n : Nat}
variable {D D' : Nat → Prop} {bs : Nat → Byte}

theorem code_congr (h : ∀ x, D x ↔ D' x) : Code D bs = Code D' bs :=
  Proofs.X86.Link.FnSpec.code_congr h

/-- **Splitting one byte off a code region.** -/
theorem code_split_byte {a : Nat} (hD : D a) :
    Code D bs = (codeByte a (bs a) ∗ Code (fun x => D x ∧ x ≠ a) bs) :=
  Proofs.X86.Link.FnSpec.code_split_byte hD

/-- **Splitting a function's bytes off a code region.** -/
theorem code_split : ∀ (code : List Byte) {D : Nat → Prop} (a : Nat),
    (∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i]) →
    Code D bs = (codePt a code ∗ Code (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs) :=
  Proofs.X86.Link.FnSpec.code_split

open Silmaril.X86.Link.Contract (Extends Image)
variable {σ : Type} {I : Silmaril.X86.SegVC.Isa σ}

theorem safe_zero (a : Nat) (S : FnSpec) (ctx : Image) : SafeOn I 0 a S ctx :=
  Proofs.X86.Link.FnSpec.safe_zero a S ctx

theorem safe_mono {a : Nat} {S : FnSpec} {ctx : Image} (h : SafeOn I (n + 1) a S ctx) :
    SafeOn I n a S ctx :=
  Proofs.X86.Link.FnSpec.safe_mono h

theorem safe_frame {a : Nat} {S : FnSpec} {img big : Image} (hext : Extends img big)
    (h : SafeOn I n a S img) : SafeOn I n a S big :=
  Proofs.X86.Link.FnSpec.safe_frame hext h

/-- **Refinement**: a function safe for `S` is safe for every `T` with `S ⊑ T`. -/
theorem safe_sub {a : Nat} {S T : FnSpec} {ctx : Image} (hsub : S.Sub T)
    (h : SafeOn I n a S ctx) : SafeOn I n a T ctx :=
  Proofs.X86.Link.FnSpec.safe_sub hsub h

end Silmaril.X86.Link.FnSpec

namespace Silmaril.X86.Link.FnSpec

open Silmaril.X86.Sep

/-- **The `FnSpec` logic on the machine `step`** (`Spec := FnSpec`, `Sub := FnSpec.Sub`). -/
def logicOn {σ : Type} (I : Silmaril.X86.SegVC.Isa σ) :
    Silmaril.X86.Link.Contract.Logic FnSpec where
  Safe := SafeOn I
  zero := safe_zero
  mono := safe_mono
  frame := safe_frame
  Sub := FnSpec.Sub
  sub := safe_sub

/-- **The `FnSpec` logic** on the open machine. -/
abbrev logic : Silmaril.X86.Link.Contract.Logic FnSpec := logicOn Silmaril.X86.Open.isa

end Silmaril.X86.Link.FnSpec

namespace Silmaril.X86.Link.FnSpec

open Silmaril.Formats.ELF.Link (mapM_some_mem)
open Silmaril.X86 (MState Word Byte)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection ResolvedRelocation Relocator Patch applyPatch)
open Silmaril.X86.Sep
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Safe

/-- **A placed section of a relocation-free unit holds the object's bytes.** -/
theorem image_mem {object : ObjectFile} {slot : Nat} {p : Placement} {σ : Valuation}
    {relocate : Relocator} {img : List LinkedSection} (hrel : object.relocations = [])
    (himg : image object slot p σ relocate = some img) {k base : Nat} {part : ObjectSection}
    (hp : p.addr k = some base) (hpart : object.sections[k]? = some part) :
    ∃ s ∈ img, s.address = base ∧ s.data = part.data ∧ s.flags = part.header.flags :=
  Proofs.X86.Link.FnSpec.image_mem hrel himg hp hpart

/-- The address and the bytes of an export in a relocation-free unit image. -/
theorem exportCode_contains {Tag : Type} {u : TU Tag FnSpec} {slot : Nat} {p : Placement}
    {σ : Valuation} {relocate : Relocator} {img : List LinkedSection}
    (hrel : u.object.relocations = []) (himg : u.image slot p σ relocate = some img)
    {name : NameBytes} {code : List Byte} (hc : ExportCode u.object name code) {a : Nat}
    (ha : u.exportAddr p name = some a) :
    a < 2 ^ 64 ∧ ∀ i (hi : i < code.length), ContainsX img (a + i) code[i] :=
  Proofs.X86.Link.FnSpec.exportCode_contains hrel himg hc ha

variable {σ : Type} {I : Silmaril.X86.SegVC.Isa σ}

/-- **A position-independent proof gives safety in every context**, on every machine that
extends the open machine. -/
theorem safe_of_sat (E : Silmaril.X86.Open.isa.Extends I) {a : Nat} {S : FnSpec} {code : List Byte} {ctx : Silmaril.X86.Link.Contract.Image} (ha : a < 2 ^ 64)
    (hcode : ∀ i (hi : i < code.length), ContainsX ctx (a + i) code[i])
    (hS : ∀ entry : Word, S.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry) (n : Nat) :
    SafeOn I n a S ctx :=
  Proofs.X86.Link.FnSpec.safe_of_sat E ha hcode hS n

/-- The `unverified` spec cannot be called. -/
theorem safe_unverified (n a : Nat) (ctx : Silmaril.X86.Link.Contract.Image) :
    SafeOn I n a unverified ctx :=
  Proofs.X86.Link.FnSpec.safe_unverified n a ctx

/-- **Unit contracts of relocation-free, position-independent units.** -/
theorem tu_sat_of_code (E : Silmaril.X86.Open.isa.Extends I) {Tag : Type} {relocate : Relocator} (u : TU Tag FnSpec)
    (hrel : u.object.relocations = [])
    (hex : ∀ e ∈ u.exports, e.spec = unverified ∨ ∃ code, ExportCode u.object e.name code ∧
      ∀ entry : Word, e.spec.Sat Silmaril.X86.Open.isa (codePt entry.toNat code) entry) :
    u.Sat (logicOn I) relocate :=
  Proofs.X86.Link.FnSpec.tu_sat_of_code E u hrel hex

end Silmaril.X86.Link.FnSpec

namespace Silmaril.X86.Link.FnSpec

open Silmaril.X86 (MState Word Byte)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection ResolvedRelocation Relocator Layout
  AbsoluteSymbols allocated linkSection sectionAt)
open Silmaril.X86.Linking (Relocation.link Relocation.relocate)
open Silmaril.Process.LPS.ELFImage (x86Policy)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint)
open Silmaril.X86.Link.Unit
open Silmaril.X86.Link.Contract
open Silmaril.X86.Link.Validate
open Silmaril.X86.Safe

/-- What a linked section is made of. -/
theorem linkSection_meta {objects : List ObjectFile} {rels : List ResolvedRelocation}
    {relocate : Relocator} {pl : Silmaril.Formats.ELF.Link.Placement} {s : LinkedSection}
    (h : linkSection objects rels relocate pl = some s) :
    ∃ part, sectionAt objects pl.key = some part ∧ allocated part = true ∧
      s.key = pl.key ∧ s.flags = part.header.flags ∧ s.data.size ≤ s.memorySize ∧
      s.address + s.memorySize ≤ 2 ^ 64 :=
  Proofs.X86.Link.FnSpec.linkSection_meta h

theorem link_meta {objects : List ObjectFile} {layout : Layout} {absolute : AbsoluteSymbols}
    {out : List LinkedSection} (h : Relocation.link objects layout absolute = some out)
    {s : LinkedSection} (hs : s ∈ out) :
    ∃ part, sectionAt objects s.key = some part ∧ allocated part = true ∧
      s.flags = part.header.flags ∧ s.data.size ≤ s.memorySize ∧
      s.address + s.memorySize ≤ 2 ^ 64 :=
  Proofs.X86.Link.FnSpec.link_meta h hs

/-- A code byte is a byte of the image. -/
theorem ContainsX.contains {ctx : Silmaril.X86.Link.Contract.Image} {a : Nat}
    {b : Byte} (h : ContainsX ctx a b) : Contains ctx a b :=
  Proofs.X86.Link.FnSpec.ContainsX.contains h

/-- **Every linked byte is in a machine that holds the loader image**, with the permissions
of its segment. -/
theorem containsF_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte} {f : Nat}
    (hc : ContainsF out a b f) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧
      ∃ seg ∈ image.segments, ∃ i < seg.size, seg.base + i = a ∧ PermsOk seg f ∧
        seg.bytes[i]? = some b :=
  Proofs.X86.Link.FnSpec.containsF_loaded hin hb hl hc

/-- **Every code byte is in a machine that holds the loader image**, executable. -/
theorem contains_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte}
    (hc : ContainsX out a b) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧ m.memory.permits .execute a = true :=
  Proofs.X86.Link.FnSpec.contains_loaded hin hb hl hc

/-- The machine's bytes on `D` form a code region. -/
theorem code_onBytes {D : Nat → Prop} {bs : Nat → Byte} {m : MState}
    (hD : ∀ a, D a → a < 2 ^ 64 ∧ m.memory.bytes.get? a = some (bs a) ∧
      m.memory.permits .execute a = true) :
    Code D bs (onBytes D (toFrag m)) :=
  Proofs.X86.Link.FnSpec.code_onBytes hD

/-- A fragment splits into its part on `D` and its part off `D`. -/
theorem sep_onBytes {P R : SProp} {D : Nat → Prop} {h : Frag} (hP : P (onBytes D h))
    (hR : R (offBytes D h)) : (P ∗ R) h :=
  Proofs.X86.Link.FnSpec.sep_onBytes hP hR

/-- **S-validate-compose**, on any machine `step` (the logic laws hold for every machine). -/
theorem validated_compose {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} {Tag : Type} [DecidableEq Tag] {policy : Silmaril.X86.Link.Abi.Policy Tag}
    {objs : List Bytes} {exe : Bytes} {W : Witness} {units : List (TU Tag FnSpec)}
    (hv : Validated objs exe W)
    (hprep : ∀ parsed, objs.mapM readObject = some parsed →
      prepare parsed W.dropped = units.map TU.object)
    (habi : AbiCompatible policy units)
    (hsat : ∀ u ∈ units, u.Sat (logicOn I) Relocation.relocate)
    (hclosed : ImportsClosed (logicOn I) units []) :
    ∃ records out, Silmaril.Process.LPS.ELFImage.parse x86Policy exe = some records ∧
      Relocation.link (units.map TU.object) W.layout W.absolute = some out ∧
      ∀ (n slot : Nat) (u : TU Tag FnSpec), units[slot]? = some u → ∀ e ∈ u.exports, ∀ a,
        globalValuation (units.map TU.object) W.layout W.absolute e.name = some a →
        (logicOn I).Safe n a e.spec out ∧
        ∀ s, I.live s → ImageLoaded (records.image exe) ⟨I.core s, I.mem s⟩ →
          ∀ (x : e.spec.Arg) (sp ret : Word), FnSpec.EntryAligned sp → e.spec.stack ≤ sp.toNat →
          ∀ F : SProp, (e.spec.SysVPre x (BitVec.ofNat 64 a) sp ret ∗ F)
              (offBytes (Dom out) (frag I s)) →
            Silmaril.X86.Safe.SafeN I (fun t => ((Code (Dom out) (byteOf ⟨I.core s, I.mem s⟩) ∗
              e.spec.SysVPost x sp ret) ∗ F) (frag I t)) n s :=
  Proofs.X86.Link.FnSpec.validated_compose hv hprep habi hsat hclosed

end Silmaril.X86.Link.FnSpec

open Silmaril.X86 (MState Word Byte)
open Silmaril.Process (addressLimit Permissions)
open Silmaril.Formats.ELF
open Silmaril.Formats.ELF.Link (LinkedSection)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint)
open Silmaril.X86.Link.Contract (ContainsF)
open Silmaril.X86.Link.FnSpec
open Silmaril.X86.Safe
open Silmaril.X86.Link.Validate (SectionIn PermsOk expected)

namespace Silmaril.X86.Link.FnSpec

variable {need : Nat → Permissions → Prop} {D : Nat → Prop} {bs : Nat → Byte}

/-- **Splitting one byte off a region**, weakening its permission to `N`. -/
theorem region_split_byte {N : Permissions → Prop} {a : Nat} (hD : D a)
    (hN : ∀ p, need a p → N p) :
    Region need D bs ⊢ₛ (byteAt N a (bs a) ∗ Region need (fun x => D x ∧ x ≠ a) bs) :=
  Proofs.X86.Link.FnSpec.region_split_byte hD hN

/-- **Splitting consecutive bytes off a region**, weakening their permissions to `N`. -/
theorem region_split {N : Permissions → Prop} : ∀ (code : List Byte) {D : Nat → Prop} (a : Nat),
    (∀ i (hi : i < code.length), D (a + i) ∧ bs (a + i) = code[i] ∧ ∀ p, need (a + i) p → N p) →
    Region need D bs ⊢ₛ
      (bytesAt N a code ∗ Region need (fun x => D x ∧ ¬ (a ≤ x ∧ x < a + code.length)) bs) :=
  Proofs.X86.Link.FnSpec.region_split

open Silmaril.X86.Link.Unit (Contains x86_link_some)
open Silmaril.X86.Linking (Relocation.link)

theorem expected_length {s : LinkedSection} (h : s.data.size ≤ s.memorySize) :
    (expected s).length = s.memorySize :=
  Proofs.X86.Link.FnSpec.expected_length h

/-- **Every in-memory byte of a linked section (data or zero fill) is in a machine that holds
the loader image**, with the permissions of its segment. -/
theorem containsM_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) {a : Nat} {b : Byte} {f : Nat}
    (hc : ContainsM out a b f) :
    a < 2 ^ 64 ∧ m.memory.bytes.get? a = some b ∧
      ∃ seg ∈ image.segments, ∃ i < seg.size, seg.base + i = a ∧ PermsOk seg f ∧
        seg.bytes[i]? = some b :=
  Proofs.X86.Link.FnSpec.containsM_loaded hin hb hl hc

/-- **The data sections are in the frame of a loaded machine**: on a machine that holds the
loader image with its permissions, the fragment off the code bytes owns every data byte of
the linked image (`DataPt`), with the machine's bytes, which are the linked bytes. -/
theorem data_loaded {image : Silmaril.Process.LPS.Image} {out : List LinkedSection}
    {m : MState} (hin : ∀ s ∈ out, SectionIn image s)
    (hb : ∀ s ∈ out, s.data.size ≤ s.memorySize ∧ s.address + s.memorySize ≤ 2 ^ 64)
    (hl : ImageLoaded image m) (hp : ImagePerms image m) :
    (DataPt out (byteOf m) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) ∧
      ∀ a b f, ContainsM out a b f → byteOf m a = b :=
  Proofs.X86.Link.FnSpec.data_loaded hin hb hl hp

theorem pairwise_ne {α : Type} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) :
    ∀ {l : List α}, l.Pairwise R → ∀ x ∈ l, ∀ y ∈ l, x ≠ y → R x y :=
  Proofs.X86.Link.FnSpec.pairwise_ne hR

/-- In a successful link, a byte of a non-executable section is not a code byte. -/
theorem not_dom_of_data {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    (h : Relocation.link objects layout absolute = some out) {s : LinkedSection} (hs : s ∈ out)
    (hx : s.flags &&& 4 = 0) {i : Nat} (hi : i < s.memorySize) : ¬ Dom out (s.address + i) :=
  Proofs.X86.Link.FnSpec.not_dom_of_data h hs hx hi

/-- **A loaded data section, as a precondition can use it**: in a validated link, every
non-executable section's linked bytes are owned, readable, by the frame of a loaded machine
(`bytesPtRO`); writable ones are also owned writable (`data_section_rw`). -/
theorem data_section_ro {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    {image : Silmaril.Process.LPS.Image} {m : MState}
    (h : Relocation.link objects layout absolute = some out)
    (hin : ∀ s ∈ out, SectionIn image s) (hl : ImageLoaded image m) (hp : ImagePerms image m)
    {s : LinkedSection} (hs : s ∈ out) (hx : s.flags &&& 4 = 0) :
    (bytesPtRO s.address (expected s) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) :=
  Proofs.X86.Link.FnSpec.data_section_ro h hin hl hp hs hx

/-- **A loaded writable data section** (`.data`, `.bss`): owned readable and writable
(`bytesPt`) by the frame of a loaded machine. -/
theorem data_section_rw {objects : List ObjectFile} {layout : Silmaril.Formats.ELF.Link.Layout}
    {absolute : Silmaril.Formats.ELF.Link.AbsoluteSymbols} {out : List LinkedSection}
    {image : Silmaril.Process.LPS.Image} {m : MState}
    (h : Relocation.link objects layout absolute = some out)
    (hin : ∀ s ∈ out, SectionIn image s) (hl : ImageLoaded image m) (hp : ImagePerms image m)
    {s : LinkedSection} (hs : s ∈ out) (hx : s.flags &&& 4 = 0) (hw : s.flags &&& 1 ≠ 0) :
    (bytesPt s.address (expected s) ∗ fun _ => True) (offBytes (Dom out) (toFrag m)) :=
  Proofs.X86.Link.FnSpec.data_section_rw h hin hl hp hs hx hw

end Silmaril.X86.Link.FnSpec

namespace Silmaril.X86.Link.FnSpec

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.X86.Sep
open Silmaril.X86.Sep.Frag (union Disjoint Le reval)

/-- **`op $imm8, %r64`** (`op ≠ cmp`), four bytes. -/
theorem aluI8_step {pc pc' v : Word} {r : Reg} {op : Silmaril.X86.AluOp} {imm : BitVec 8}
    {bytes : List Byte}
    (hdec : Silmaril.X86.Ext.decode bytes = some (.aluI8 .q op (.reg r) imm, 4))
    (hlen : bytes.length = 4) (hop : op ≠ .cmp) (hnext : pc + 4#64 = pc') :
    Triple Silmaril.X86.Open.isa (codePt pc.toNat bytes ∗ ripPt pc ∗ regPt r v ∗ flagsAny)
      (codePt pc.toNat bytes ∗ ripPt pc' ∗
        regPt r (Silmaril.X86.Ext.AluOp.resultN op v (imm.signExtend 64)) ∗ flagsAny) :=
  Proofs.X86.Link.FnSpec.aluI8_step hdec hlen hop hnext

end Silmaril.X86.Link.FnSpec

namespace Silmaril.X86.Link.FnSpec

open Silmaril.X86 (MState Word Byte Reg Insn)
open Silmaril.X86.Sep
open Silmaril.X86.Safe
variable {D : Nat → Prop} {bs : Nat → Byte}

/-- An instruction triple inside a code region. -/
theorem code_triple {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} {pc : Nat} {bytes : List Byte}
    (hD : ∀ i (hi : i < bytes.length), D (pc + i) ∧ bs (pc + i) = bytes[i]) {P Q : SProp}
    (h : Triple I (codePt pc bytes ∗ P) (codePt pc bytes ∗ Q)) :
    Triple I (Code D bs ∗ P) (Code D bs ∗ Q) :=
  Proofs.X86.Link.FnSpec.code_triple hD h

/-- **The step-indexed call rule**, on every machine that extends the open machine. -/
theorem scall_rule {σ : Type} {I : Silmaril.X86.SegVC.Isa σ} (E : Silmaril.X86.Open.isa.Extends I)
    {S : FnSpec} {ctx : Silmaril.X86.Link.Contract.Image} {n f : Nat}
    {pc s : Word} {rel : BitVec 32} (hc : Covers ctx D bs) (hf : SafeOn I n f S ctx)
    (hD : ∀ i (hi : i < (Insn.encode (.call rel)).length),
      D (pc.toNat + i) ∧ bs (pc.toNat + i) = (Insn.encode (.call rel))[i])
    (htarget : pc + 5#64 + rel.signExtend 64 = BitVec.ofNat 64 f)
    (hA : FnSpec.EntryAligned (s - 8#64)) (hlow : S.stack + 8 ≤ s.toNat) (x : S.Arg) :
    Silmaril.X86.Safe.STriple I (n + 1)
      (Code D bs ∗ ripPt pc ∗ regPt .rsp s ∗ SysVRegs (S.args x) ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.pre x)
      (Code D bs ∗ sexists fun v => ripPt (pc + 5#64) ∗ regPt .rsp s ∗ SysVRet v ∗ flagsAny ∗
        blockAny (s.toNat - 8 - S.stack) (S.stack + 8) ∗ S.post x v) :=
  Proofs.X86.Link.FnSpec.scall_rule E hc hf hD htarget hA hlow x

end Silmaril.X86.Link.FnSpec
