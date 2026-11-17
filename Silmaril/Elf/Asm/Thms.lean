module

public import Silmaril.Elf.Asm.Defs
public import Silmaril.Elf.Staged.Reader.Defs
import Silmaril.Proofs.Elf.Asm

/-! # Assembly functions: what each kind of evidence gives, and what display cannot change

* **Display invariance** (`archOf_withLines`, `bytesAt_withLines`, `symbolOf_withLines`,
  `decodesAs_withLines`, and `_abiRef` versions): the listing lines and the ABI identifier are not
  read by any evidence proposition, so replacing them changes no fact. (Definitional: these are
  `Iff.rfl`, which is the point.)
* **Decoding is determined by the bytes**: `decodes_unique`/`DecodesAs.unique` (a decoder is a
  function, so a function's bytes have at most one decoding under one model) and `decodes_sum`
  (the decoded lengths add up to the byte count). `tiles_sum`: the same for listing boundaries,
  which are *not* determined by anything (`LinesTile` only checks they tile).
* **Bytes are determined by the extent**: `bytesAt_unique` (two grounded functions with the same
  extent in the same file have the same bytes), `bytesAt_origins` (every byte is file-backed by
  the stated segment at consecutive offsets).
* **Relation to `CodeAt`**: `bytesAt_codeAt` (grounded bytes in the first read-only executable
  segment are `CodeAt`), `codeAt_bytesAt` (every `CodeAt` fact grounds a function's bytes).

Proofs: `Silmaril.Proofs.Elf.Asm` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Asm

open Silmaril.X86.Link (Blob)

/-! ## Display invariance -/

theorem archOf_withLines (F : Blob) (f : AsmFunction) (ls : List Line) :
    ArchOf F (f.withLines ls) ↔ ArchOf F f := Iff.rfl

theorem bytesAt_withLines (F : Blob) (f : AsmFunction) (ls : List Line) :
    BytesAt F (f.withLines ls) ↔ BytesAt F f := Iff.rfl

theorem symbolOf_withLines (F : Blob) (f : AsmFunction) (ls : List Line) :
    SymbolOf F (f.withLines ls) ↔ SymbolOf F f := Iff.rfl

theorem decodesAs_withLines (isa : Isa) (f : AsmFunction) (ls : List Line)
    (d : List (Nat × isa.Instr)) : DecodesAs isa (f.withLines ls) d ↔ DecodesAs isa f d := Iff.rfl

theorem sectionBytesAt_withLines (F : Blob) (f : AsmFunction) (ls : List Line) :
    SectionBytesAt F (f.withLines ls) ↔ SectionBytesAt F f := Iff.rfl

theorem bytesAt_abiRef (F : Blob) (f : AsmFunction) (a : Option String) :
    BytesAt F { f with abiRef := a } ↔ BytesAt F f := Iff.rfl

theorem decodesAs_abiRef (isa : Isa) (f : AsmFunction) (a : Option String)
    (d : List (Nat × isa.Instr)) : DecodesAs isa { f with abiRef := a } d ↔ DecodesAs isa f d :=
  Iff.rfl

/-- A display reference is never grounded. -/
theorem not_refGrounded_display {F : Blob} {f : AsmFunction} {isa : Isa}
    {d : List (Nat × isa.Instr)} {r : CodeRef} (h : r.origin = .display) : ¬ RefGrounded F f isa d r := by
  unfold RefGrounded; rw [h]; exact id

/-! ## Decoding -/

theorem decodes_unique (isa : Isa) {bs : List Byte} {d₁ d₂ : List (Nat × isa.Instr)}
    (h₁ : decodes isa bs d₁ = true) (h₂ : decodes isa bs d₂ = true) : d₁ = d₂ :=
  Proofs.Elf.Asm.decodes_unique isa h₁ h₂

/-- **The decodings of `bs` are exactly the greedy one**, when every instruction decodes. -/
theorem decodes_iff_decodeAll (isa : Isa) (bs : List Byte) (d : List (Nat × isa.Instr)) :
    decodes isa bs d = true ↔ decodeAll isa bs = some d :=
  Proofs.Elf.Asm.decodes_iff_decodeAll isa bs d

/-- **No decoding at all** when the greedy one stops on an instruction the model does not decode. -/
theorem not_decodesAs_of_decodeAll {isa : Isa} {f : AsmFunction} (h : decodeAll isa f.bytes = none)
    (d : List (Nat × isa.Instr)) : ¬ DecodesAs isa f d := fun hd => by
  rw [(decodes_iff_decodeAll isa f.bytes d).mp hd.2] at h; cases h

/-- `DecodesAs` from a computed decoding. -/
theorem decodesAs_of_decodeAll {isa : Isa} {f : AsmFunction} {d : List (Nat × isa.Instr)}
    (hm : isa.machine = f.arch.machine) (h : decodeAll isa f.bytes = some d) : DecodesAs isa f d :=
  ⟨hm, (decodes_iff_decodeAll isa f.bytes d).mpr h⟩

theorem DecodesAs.unique {isa : Isa} {f : AsmFunction} {d₁ d₂ : List (Nat × isa.Instr)}
    (h₁ : DecodesAs isa f d₁) (h₂ : DecodesAs isa f d₂) : d₁ = d₂ :=
  decodes_unique isa h₁.2 h₂.2

theorem decodes_sum (isa : Isa) {bs : List Byte} {d : List (Nat × isa.Instr)}
    (h : decodes isa bs d = true) : (d.map (·.1)).sum = bs.length :=
  Proofs.Elf.Asm.decodes_sum isa h

theorem tiles_sum {o : Nat} {ls : List Line} {n : Nat} (h : tiles o ls n = true) :
    o + (ls.map (·.len)).sum = n :=
  Proofs.Elf.Asm.tiles_sum h

/-! ## Bytes -/

theorem bytesAt_unique {F : Blob} {f g : AsmFunction} (hf : BytesAt F f) (hg : BytesAt F g)
    (he : f.extent = g.extent) : f.bytes = g.bytes :=
  Proofs.Elf.Asm.bytesAt_unique hf hg he

theorem bytesAt_origins {F : Blob} {f : AsmFunction} (h : BytesAt F f) {k : Nat}
    (hk : k < f.extent.size) : ∃ A i o, Parses F A ∧ f.extent.segment = some i ∧
      f.extent.fileOff = some o ∧ (i, Image.Origin.file (o + k)) ∈ A.origins (f.extent.vaddr + k) :=
  Proofs.Elf.Asm.bytesAt_origins h hk

/-- **Grounded bytes in the first read-only executable segment are `CodeAt`.** -/
theorem bytesAt_codeAt {F : Blob} {f : AsmFunction} (h : BytesAt F f)
    (hf : ∃ A i, Parses F A ∧ f.extent.segment = some i ∧
      A.phdrs.find? (codeSeg f.extent.vaddr f.bytes.length) = A.phdrs[i]?) :
    CodeAt F f.extent.vaddr f.bytes :=
  Proofs.Elf.Asm.bytesAt_codeAt h hf

/-- **Every `CodeAt` fact grounds a function's bytes** (with the segment and offset it names). -/
theorem codeAt_bytesAt {F : Blob} {f : AsmFunction} (h : CodeAt F f.extent.vaddr f.bytes)
    (hz : f.extent.size = f.bytes.length) :
    ∃ i o, BytesAt F { f with extent := { f.extent with segment := some i, fileOff := some o } } :=
  Proofs.Elf.Asm.codeAt_bytesAt h hz

/-! ## From checks -/

theorem archOf_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : archOk A f = true) : ArchOf F f :=
  Proofs.Elf.Asm.archOf_of_check hp h

theorem symbolOf_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : symbolOk A f = true) : SymbolOf F f :=
  Proofs.Elf.Asm.symbolOf_of_check hp h

theorem bytesAt_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : extentOk A f = true)
    (hr : ∀ o, f.extent.fileOff = some o → Image.FileBytes F o f.bytes) : BytesAt F f :=
  Proofs.Elf.Asm.bytesAt_of_check hp h hr

/-- A decoded reference from its check against the decoding. -/
theorem refGrounded_of_check {F : Blob} {f : AsmFunction} {isa : Isa}
    {d : List (Nat × isa.Instr)} {r : CodeRef} (ho : r.origin = .decoded) (hd : DecodesAs isa f d)
    (h : decodedRefOk f isa d r = true) : RefGrounded F f isa d r :=
  Proofs.Elf.Asm.refGrounded_of_check ho hd h

theorem sectionBytesAt_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    (h : secOk A f = true)
    (hr : ∀ o, f.extent.fileOff = some o → Image.FileBytes F o f.bytes) : SectionBytesAt F f :=
  Proofs.Elf.Asm.sectionBytesAt_of_check hp h hr

/-- A relocation reference from its check against the parse. -/
theorem refGrounded_reloc_of_check {F : Blob} {A : File} (hp : Parses F A) {f : AsmFunction}
    {isa : Isa} {d : List (Nat × isa.Instr)} {r : CodeRef} (h : relocRefOk A f r = true) :
    RefGrounded F f isa d r :=
  Proofs.Elf.Asm.refGrounded_reloc_of_check hp h

/-- **File bytes from one kernel read** of the kernel bytes of an `include_bytes` file. -/
theorem fileBytes_of_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {o : Nat} {bytes : List (BitVec 8)}
    (hc : Staged.Reader.kread x o bytes.length = some (Blob.valueLE bytes)) :
    Image.FileBytes (blobOf ⟨raw⟩) o bytes :=
  Proofs.Elf.Asm.fileBytes_of_kbytes hx h hc

/-- **`BytesAt` of an `include_bytes` file**: the extent checked on its parse, the bytes by one
kernel read. -/
theorem bytesAt_of_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {A : File} (hp : Parses (blobOf ⟨raw⟩) A) {f : AsmFunction} {o : Nat}
    (ho : f.extent.fileOff = some o) (he : extentOk A f = true)
    (hc : Staged.Reader.kread x o f.bytes.length = some (Blob.valueLE f.bytes)) :
    BytesAt (blobOf ⟨raw⟩) f :=
  bytesAt_of_check hp he fun o' ho' => by
    rw [ho] at ho'; cases ho'; exact fileBytes_of_kbytes hx h hc

end Silmaril.Elf.Asm
