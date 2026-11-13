module

public import Init.Data.ByteArray

/-! # Writing ELF64 relocatable objects

`writeRelocatable` produces the bytes of a little-endian ELF64 `ET_REL` object with
allocated `PROGBITS` sections, one symbol table of global symbols (section-relative or
absolute), the string tables and an empty `.note.GNU-stack` (no executable stack). It
writes no relocation sections: the C compiler's code addresses its data through a base
register (`docs/projects/cerberus.md`), so its objects need none.

The layout is: the ELF header, the section contents (each aligned), the symbol
table, the string tables, then the section header table. The reader
`Silmaril.Formats.ELF.Object` parses this format; the intended theorem of this writer
is the round trip `readObject (writeRelocatable o) = some o'` with `o'` the same
sections and symbols.
-/

@[expose] public section

namespace Silmaril.Formats.ELF.Write

/-- An allocated section. -/
structure Section where
  name : String
  /-- `SHF_*` flags: 2 = alloc, 4 = exec, 1 = write. -/
  flags : Nat
  align : Nat
  data : ByteArray

/-- A global symbol: in section `sec` (index into the section list, from 0) at
`value`, or absolute when `sec = none`. `kind` is `STT_*`: 0 none, 1 object, 2 func. -/
structure Sym where
  name : String
  sec : Option Nat
  value : Nat
  size : Nat
  kind : Nat

def le (n v : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    b := b.push ((v >>> (8 * i)) % 256).toUInt8
  return b

def pad (b : ByteArray) (align : Nat) : ByteArray := Id.run do
  let mut b := b
  if align > 1 then
    while b.size % align != 0 do
      b := b.push 0
  return b

/-- A string table and the offset of each name in it. -/
def strtab (names : List String) : ByteArray × List Nat := Id.run do
  let mut b := ByteArray.mk #[0]
  let mut offs := #[]
  for n in names do
    offs := offs.push b.size
    b := b ++ n.toUTF8 ++ ByteArray.mk #[0]
  return (b, offs.toList)

/-- One section header. -/
def shdr (name type flags addr offset size link info align entsize : Nat) : ByteArray :=
  le 4 name ++ le 4 type ++ le 8 flags ++ le 8 addr ++ le 8 offset ++ le 8 size ++ le 4 link ++
    le 4 info ++ le 8 align ++ le 8 entsize

/-- The object file. `machine` is `e_machine` (62 x86-64, 243 RISC-V), `flags` is
`e_flags`. -/
def writeRelocatable (machine flags : Nat) (sections : List Section) (syms : List Sym) :
    ByteArray := Id.run do
  let nsec := sections.length
  -- section indices: 0 null, 1..nsec user, then .note.GNU-stack, .symtab, .strtab, .shstrtab
  let noteIdx := nsec + 1
  let symtabIdx := nsec + 2
  let strtabIdx := nsec + 3
  let shstrIdx := nsec + 4
  let (shstr, shoffs) := strtab (sections.map (·.name) ++
    [".note.GNU-stack", ".symtab", ".strtab", ".shstrtab"])
  let (str, soffs) := strtab (syms.map (·.name))
  -- contents
  let mut out := ByteArray.mk (Array.replicate 64 0)
  let mut secOffs : Array Nat := #[]
  for s in sections do
    out := pad out (max s.align 1)
    secOffs := secOffs.push out.size
    out := out ++ s.data
  let noteOff := out.size
  out := pad out 8
  let symOff := out.size
  out := out ++ ByteArray.mk (Array.replicate 24 0)
  for (s, nameOff) in syms.zip soffs do
    let shndx := match s.sec with | some i => i + 1 | none => 0xfff1
    out := out ++ le 4 nameOff ++ le 1 (16 + s.kind) ++ le 1 0 ++ le 2 shndx ++ le 8 s.value ++
      le 8 s.size
  let symSize := 24 * (syms.length + 1)
  let strOff := out.size
  out := out ++ str
  let shstrOff := out.size
  out := out ++ shstr
  out := pad out 8
  let shoff := out.size
  -- section headers
  out := out ++ ByteArray.mk (Array.replicate 64 0)
  for ((s, off), i) in (sections.zip secOffs.toList).zipIdx do
    out := out ++ shdr shoffs[i]! 1 s.flags 0 off s.data.size 0 0 (max s.align 1) 0
  out := out ++ shdr shoffs[nsec]! 1 0 0 noteOff 0 0 0 1 0
  out := out ++ shdr shoffs[nsec + 1]! 2 0 0 symOff symSize strtabIdx 1 8 24
  out := out ++ shdr shoffs[nsec + 2]! 3 0 0 strOff str.size 0 0 1 0
  out := out ++ shdr shoffs[nsec + 3]! 3 0 0 shstrOff shstr.size 0 0 1 0
  let _ := noteIdx; let _ := symtabIdx
  -- ELF header
  let header := ByteArray.mk #[0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    le 2 1 ++ le 2 machine ++ le 4 1 ++ le 8 0 ++ le 8 0 ++ le 8 shoff ++ le 4 flags ++
    le 2 64 ++ le 2 0 ++ le 2 0 ++ le 2 64 ++ le 2 (nsec + 5) ++ le 2 shstrIdx
  return header ++ out.extract 64 out.size

end Silmaril.Formats.ELF.Write
