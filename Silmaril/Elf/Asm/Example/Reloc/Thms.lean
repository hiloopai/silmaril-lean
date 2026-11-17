module

public import Silmaril.Elf.Asm.Example.Reloc.Defs
public import Silmaril.Elf.Asm.Thms
public import Silmaril.Elf.Staged.Reader.Thms
public import Silmaril.Elf.Link.Dyn.Elf.Thms
public import Silmaril.Elf.Facts.Thms

/-! # The relocatable object, dimension by dimension

| evidence | theorem |
|---|---|
| the parse | `parses : Parses F ast` (the specification run on the kernel bytes, `Rd.run_mono`) |
| `ET_REL`, for `EM_X86_64` | `kind`, `arch` |
| no program headers, so no `BytesAt` | `no_segments`, `not_bytesAt` |
| section bytes | `sectionBytes : SectionBytesAt F scaledPlusBias` |
| symbol | `symbol` (`.symtab` entry 2) |
| decoding, listing | `decodes` (`x86Ext`, 5 instructions), `tiles` |
| references | `refs`: both relocations of `.rela.text`, with types, addends and symbol names |
| the decoded call is not the reference | `call_unrelocated`: the decoded `call` targets offset 9, its own successor |
-/

@[expose] public section

namespace Silmaril.Elf.Asm.Example.Reloc

/-- **The parse**, from one run of the specification on the kernel bytes. -/
theorem parses : Parses F ast :=
  Silmaril.Elf.Link.DynElf.Rd.run_mono (Staged.Reader.sub_kbytes K.wf_true K.toByteArray_eq) read ast
    (Option.some_get _).symm

theorem kind : KindIs F .relocatable := ⟨ast, parses, by decide +kernel⟩

theorem arch : ArchOf F scaledPlusBias := archOf_of_check parses (by decide +kernel)

theorem no_segments : ast.phdrs = [] := by decide +kernel

/-- A relocatable object has no segment, so no `BytesAt`, whatever segment an extent claims. -/
theorem not_bytesAt (f : AsmFunction) : ¬ BytesAt F f := by
  rintro ⟨-, A, i, o, hA, hi, -, ⟨ph, hph, -⟩, -⟩
  cases parses_unique hA parses; rw [no_segments] at hph; cases hph

theorem sectionBytes : SectionBytesAt F scaledPlusBias :=
  sectionBytesAt_of_check parses (by decide +kernel) fun o ho => by
    cases ho; exact fileBytes_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)

theorem symbol : SymbolOf F scaledPlusBias := symbolOf_of_check parses (by decide +kernel)

theorem tiles : LinesTile scaledPlusBias := by decide +kernel

theorem decodes : DecodesAs x86Ext scaledPlusBias scaledDecoding :=
  decodesAs_of_decodeAll rfl (by decide +kernel)

/-- **Both references are the object's relocations** (offset, type, addend, symbol name). -/
theorem refs : RefsGrounded F scaledPlusBias x86Ext scaledDecoding := by
  intro r hr _
  simp only [scaledPlusBias, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact refGrounded_reloc_of_check parses (by decide +kernel)

/-- The decoded `call` (offset 4, 5 bytes) targets offset 9: the unrelocated displacement, not
`scale`. Only the relocation says where the call goes. -/
theorem call_unrelocated : (insnAt scaledDecoding 0 4).bind (fun (n, i) => x86Ext.target i 4 n) = some 9 := by
  decide +kernel

end Silmaril.Elf.Asm.Example.Reloc
