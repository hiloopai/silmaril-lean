module

public import Silmaril.Process.LPS.MemImage

/-!
# LPS in Lean: the initial stack (argc, argv, envp, auxv, AT_RANDOM)

Translation of LPS `StackLayout.v` (upstream commit `f1006fe8`): the block the kernel writes
at the initial stack pointer, in the order of `create_elf_tables` (`fs/binfmt_elf.c`):
`argc`, the `argv` pointers and NULL, the `envp` pointers and NULL, the auxiliary vector, the
argument and environment strings, padding to eight bytes and the sixteen `AT_RANDOM` bytes.

The auxiliary vector has the ten entries LPS publishes (`StackLayout.v:211`): `AT_PHDR`,
`AT_PHENT`, `AT_PHNUM`, `AT_HWCAP`, `AT_PAGESZ`, `AT_UID`, `AT_EUID`, `AT_SECURE`,
`AT_RANDOM`, `AT_NULL`. No vDSO is published, so a C library falls back to real system calls.
The `AT_RANDOM` bytes and the bytes above the block are a free draw (`EntryDraw`).
-/

@[expose] public section

namespace Silmaril.Process.LPS

/-- LPS `StackLayout.v:17` `string_addrs`: the address of each string, and the end. -/
def stringAddrs (base : Word) : List (List Byte) → List Word × Word
  | [] => ([], base)
  | s :: rest =>
    let next := base + lenWord s + 1
    let r := stringAddrs next rest
    (base :: r.1, r.2)

/-- LPS `StackLayout.v:27` `flatten_strings`: NUL-terminated and concatenated. -/
def flattenStrings (strs : List (List Byte)) : List Byte := strs.flatMap (· ++ [0])

/-- LPS `StackLayout.v:30` `AT_NULL`. -/
def AT_NULL : Word := 0
/-- LPS `StackLayout.v:31` `AT_PHDR`. -/
def AT_PHDR : Word := 3
/-- LPS `StackLayout.v:32` `AT_PHENT`. -/
def AT_PHENT : Word := 4
/-- LPS `StackLayout.v:33` `AT_PHNUM`. -/
def AT_PHNUM : Word := 5
/-- LPS `StackLayout.v:34` `AT_PAGESZ`. -/
def AT_PAGESZ : Word := 6
/-- LPS `StackLayout.v:36` `AT_UID`. -/
def AT_UID : Word := 11
/-- LPS `StackLayout.v:37` `AT_EUID`. -/
def AT_EUID : Word := 12
/-- LPS `StackLayout.v:35` `AT_HWCAP`. -/
def AT_HWCAP : Word := 16
/-- LPS `StackLayout.v:38` `AT_SECURE`. -/
def AT_SECURE : Word := 23
/-- LPS `StackLayout.v:39` `AT_RANDOM`. -/
def AT_RANDOM : Word := 25

/-- LPS `StackLayout.v:51` `hwcap_rv64gc`. -/
def hwcapRv64gc : Word := 0x112D
/-- LPS `StackLayout.v:52` `hwcap_rv64gcv`. -/
def hwcapRv64gcv : Word := 0x20112D

/-- LPS `StackLayout.v:211` `auxv_entries`. -/
def auxvEntries (ph : PhdrInfo) (atRandom uid hwcap : Word) : List (Word × Word) :=
  [ (AT_PHDR, zw ph.addr), (AT_PHENT, zw ph.ent), (AT_PHNUM, zw ph.num), (AT_HWCAP, hwcap),
    (AT_PAGESZ, 4096), (AT_UID, uid), (AT_EUID, uid), (AT_SECURE, 0), (AT_RANDOM, atRandom),
    (AT_NULL, 0) ]

/-- LPS `StackLayout.v:225` `build_auxv`. -/
def buildAuxv (entries : List (Word × Word)) : List Byte :=
  entries.flatMap fun e => wordLe8 e.1 ++ wordLe8 e.2

/-- LPS `StackLayout.v:228` `auxv_bytes`. -/
def auxvBytes (ph : PhdrInfo) (atRandom uid hwcap : Word) : List Byte :=
  buildAuxv (auxvEntries ph atRandom uid hwcap)

/-- LPS `StackLayout.v:243` `auxv_size`: ten entries of sixteen bytes. -/
def auxvSize : Nat := 160

/-- LPS `StackLayout.v:318` `EntryDraw`: the kernel's entropy and the unspecified bytes above
the entry block. -/
structure EntryDraw where
  random : BitVec 128
  slack : Word → Byte

/-- LPS `StackLayout.v:347` `at_random_bytes`. -/
def atRandomBytes (rnd : BitVec 128) : List Byte :=
  (List.range 16).map fun k => rnd.extractLsb' (8 * k) 8

/-- LPS `StackLayout.v:360` `at_random_ptr`. -/
def atRandomPtr (sp : Word) (argv envp : List (List Byte)) : Word :=
  let structSize := 8 + (argv.length + 1) * 8 + (envp.length + 1) * 8 + auxvSize
  let len := structSize + (flattenStrings argv).length + (flattenStrings envp).length
  let pad := ((8 - (len : Int) % 8) % 8).toNat
  sp + natToWord (len + pad)

/-- LPS `StackLayout.v:374` `build_stack_bytes`. -/
def buildStackBytes (ph : PhdrInfo) (sp : Word) (argv envp : List (List Byte))
    (uid hwcap : Word) (draw : EntryDraw) : List Byte :=
  let argc := lenWord argv
  let auxv := auxvBytes ph (atRandomPtr sp argv envp) uid hwcap
  let structSize := 8 + (argv.length + 1) * 8 + (envp.length + 1) * 8 + auxv.length
  let stringBase := sp + natToWord structSize
  let a := stringAddrs stringBase argv
  let e := stringAddrs a.2 envp
  let raw := wordLe8 argc ++ a.1.flatMap wordLe8 ++ wordLe8 0 ++ e.1.flatMap wordLe8 ++
    wordLe8 0 ++ auxv ++ flattenStrings argv ++ flattenStrings envp
  let pad := ((8 - (raw.length : Int) % 8) % 8).toNat
  raw ++ List.replicate pad 0 ++ atRandomBytes draw.random

/-- LPS `StackLayout.v:433` `stack_to_mem`. -/
def stackToMem (base : Word) (bytes : List Byte) : Word → Option Byte := fun addr =>
  if uns base ≤ uns addr then
    let off := uns addr - uns base
    if off < bytes.length then bytes[off.toNat]? else none
  else none

end Silmaril.Process.LPS
