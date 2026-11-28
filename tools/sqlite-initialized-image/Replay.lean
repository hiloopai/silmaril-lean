module

import Silmaril.Data.IncludeBytes.Kernel
import Silmaril.Elf.Link.Dyn.Image.Thms
import Silmaril.Elf.Staged.Reader.Thms

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace SqliteCampaign

open Silmaril (KBytes)
open Silmaril.Elf (blobOf)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Staged.Reader (kread sub_kbytes)
open Silmaril.X86 (Byte Word)
open Silmaril.X86.Link (Blob)
open Silmaril.Process (Memory)

noncomputable def clientRaw : ByteArray := include_bytes "client"
noncomputable def sqliteRaw : ByteArray := include_bytes "libsqlite3.so.0"
noncomputable def libcRaw : ByteArray := include_bytes "libc.so.6"
noncomputable def loaderRaw : ByteArray := include_bytes "ld-linux-x86-64.so.2"

kbytes_def clientK of_include clientRaw
kbytes_def sqliteK of_include sqliteRaw
kbytes_def libcK of_include libcRaw
kbytes_def loaderK of_include loaderRaw

noncomputable def client : Blob := blobOf ⟨clientRaw⟩
noncomputable def sqlite : Blob := blobOf ⟨sqliteRaw⟩
noncomputable def libc : Blob := blobOf ⟨libcRaw⟩
noncomputable def loader : Blob := blobOf ⟨loaderRaw⟩

/-- Search order supplied for this receipt, as observed on the clean-env client launch. -/
noncomputable def scope : List Blob := [client, sqlite, libc, loader]

/-- Chosen page-aligned bases for the witness. -/
def bases : List Word := [0x400000, 0x70000000, 0x71000000, 0x72000000]

private theorem read_checked {raw : ByteArray} {K : KBytes} (wf : K.wf = true)
    (same : K.toByteArray = raw) {α : Type} {reader : Rd α} {value : α}
    (check : reader.run (kread K) = some value) :
    frun (blobOf ⟨raw⟩) reader = some value :=
  Rd.run_mono (sub_kbytes wf same) _ _ check

private def infoAt (K : KBytes) : Elf.DynInfo :=
  (Elf.dynInfo.run (kread K)).getD ⟨[], []⟩

noncomputable def clientInfo := infoAt clientK
noncomputable def sqliteInfo := infoAt sqliteK
noncomputable def libcInfo := infoAt libcK
noncomputable def loaderInfo := infoAt loaderK

theorem client_info : finfo client = some clientInfo :=
  read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel)

theorem sqlite_info : finfo sqlite = some sqliteInfo :=
  read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel)

private def soname (info : Elf.DynInfo) : Rd Name := do
  info.str (← Rd.ofOption (info.tag Elf.DT_SONAME))

/-- The checked names connect the four supplied ELF files. Search and selection are premises. -/
theorem dependency_names :
    frun client (Elf.interp clientInfo) = some (nm "/lib64/ld-linux-x86-64.so.2") ∧
    frun client (Elf.needed clientInfo) = some [nm "libsqlite3.so.0", nm "libc.so.6"] ∧
    frun sqlite (soname sqliteInfo) = some (nm "libsqlite3.so.0") ∧
    frun sqlite (Elf.needed sqliteInfo) = some [nm "libc.so.6"] ∧
    finfo libc = some libcInfo ∧
    frun libc (soname libcInfo) = some (nm "libc.so.6") ∧
    frun libc (Elf.needed libcInfo) = some [nm "ld-linux-x86-64.so.2"] ∧
    finfo loader = some loaderInfo ∧
    frun loader (soname loaderInfo) = some (nm "ld-linux-x86-64.so.2") ∧
    frun loader (Elf.needed loaderInfo) = some [] := by
  exact ⟨read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel),
    read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel),
    read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel),
    read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel),
    read_checked libcK.wf_true libcK.toByteArray_eq (by decide +kernel),
    read_checked libcK.wf_true libcK.toByteArray_eq (by decide +kernel),
    read_checked libcK.wf_true libcK.toByteArray_eq (by decide +kernel),
    read_checked loaderK.wf_true loaderK.toByteArray_eq (by decide +kernel),
    read_checked loaderK.wf_true loaderK.toByteArray_eq (by decide +kernel),
    read_checked loaderK.wf_true loaderK.toByteArray_eq (by decide +kernel)⟩

def slot : Elf.Rela := ⟨0x4078, 7, 19, 0⟩
def target : Val := .addr 1 0xa4ca0

private def openRef : Elf.Ref := ⟨nm "sqlite3_open_v2", false, none⟩

private theorem selected_ref : frun client (Elf.refOf clientInfo 19) = some openRef :=
  read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel)

private theorem client_miss : frun client (Elf.lookupDef clientInfo openRef true) = some none :=
  read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel)

private theorem sqlite_hit :
    frun sqlite (Elf.lookupDef sqliteInfo openRef true) =
      some (some ⟨0xa4ca0, false, false⟩) :=
  read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel)

private theorem scope_hit :
    resolve scope openRef true = some (some (1, ⟨0xa4ca0, false, false⟩)) := by
  rw [resolve, scope, resolveFrom, client_info, Option.bind_eq_bind, Option.bind_some,
    client_miss, Option.bind_eq_bind, Option.bind_some]
  rw [resolveFrom, sqlite_info, Option.bind_eq_bind, Option.bind_some,
    sqlite_hit, Option.bind_eq_bind, Option.bind_some]
  rfl

private theorem jump_value {R : Resolver} {f : Blob} {i : Elf.DynInfo} {off sym : Nat}
    {ref : Elf.Ref} {value : Nat × Elf.Def}
    (reference : frun f (Elf.refOf i sym) = some ref)
    (binding : R ref true = some (some value)) :
    relocVal R f i ⟨off, 7, sym, 0⟩ = some (defVal value) := by
  change ((frun f (Elf.refOf i sym)).bind fun r => bindVal R r true) = _
  rw [reference, Option.bind_some]
  unfold bindVal
  rw [Option.bind_eq_bind, binding, Option.bind_some]
  rfl

/-- The eager JUMP_SLOT resolves in the client scope to the SQLite definition. -/
theorem resolved_slot : relocVal (resolve scope) client clientInfo slot = some target :=
  jump_value selected_ref scope_hit

private def tablesAt (K : KBytes) (info : Elf.DynInfo) : List Elf.Rela × List Elf.Rela :=
  ((Elf.relas info).run (kread K)).getD ([], [])

noncomputable def clientRows := tablesAt clientK clientInfo
noncomputable def sqliteRows := tablesAt sqliteK sqliteInfo

theorem client_rows : frun client (Elf.relas clientInfo) = some clientRows :=
  read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel)

theorem sqlite_rows : frun sqlite (Elf.relas sqliteInfo) = some sqliteRows :=
  read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel)

def callCode : List Byte := [0xe8, 0x60, 0xff, 0xff, 0xff]
def pltCode : List Byte := [0xff, 0x25, 0x52, 0x2f, 0x00, 0x00]
def entryCode : List Byte := [0xe9, 0x4b, 0xf8, 0xff, 0xff]

private def clientRX : Elf.Phdr := ⟨1, 5, 0x1000, 0x1000, 0x465, 0x465⟩
private def clientRW : Elf.Phdr := ⟨1, 6, 0x2db0, 0x3db0, 0x2e0, 0x320⟩
private def sqliteRX : Elf.Phdr := ⟨1, 5, 0xd000, 0xd000, 0xd39c9, 0xd39c9⟩

private def covers (start addr : Nat) : Bool :=
  decide (start ≤ addr ∧ addr < start + 8)

private def rowAt (rows : List Elf.Rela × List Elf.Rela) (addr : Nat) : Option Elf.Rela :=
  (rows.1 ++ rows.2).find? (fun r => covers r.off addr)

/-- A map of the selected ranges only, with their relocated word and permissions. -/
def cutMemory : Memory :=
  ⟨[⟨0x4011bb, 5, ⟨true, false, true⟩⟩, ⟨0x401120, 6, ⟨true, false, true⟩⟩,
    ⟨0x404078, 8, ⟨true, true, false⟩⟩, ⟨0x700a4ca0, 5, ⟨true, false, true⟩⟩],
    Memory.install (Memory.install (Memory.install (Memory.install ∅ 0x4011bb callCode)
      0x401120 pltCode) 0x404078 ((List.range 8).map (wordByte 0x700a4ca0)))
      0x700a4ca0 entryCode⟩

/-- The read-only branch's call instruction and its PLT indirection in a loaded memory. -/
def ClientRoute (memory : Memory) : Prop :=
  memory.fetchBytes 0x4011bb callCode.length = some callCode ∧
  memory.fetchBytes 0x401120 pltCode.length = some pltCode ∧
  Silmaril.X86.Ext.loadN memory 0x404078 8 = some 0x700a4ca0

/-- The route together with executable backing for the selected SQLite entry. -/
def ClientCut (memory : Memory) : Prop :=
  ClientRoute memory ∧ memory.fetchBytes 0x700a4ca0 entryCode.length = some entryCode

private theorem read_checked_span {memory : Memory} {acc : Silmaril.Process.Access}
    {addr : Nat} {bytes : List Byte} (span : memory.checkSpan acc addr bytes.length = true)
    (backed : ∀ k (bound : k < bytes.length),
      memory.bytes.get? (addr + k) = some bytes[k]) :
    memory.readWith acc addr bytes.length = some bytes := by
  obtain ⟨start, finish, permitted⟩ := (Memory.checkSpan_iff ..).mp span
  exact readWith_of_points finish start (fun k bound => ⟨permitted k bound, backed k bound⟩)

private theorem cut_call : cutMemory.fetchBytes 0x4011bb callCode.length = some callCode := by
  apply read_checked_span (by decide +kernel)
  intro k bound
  have hk : k < 5 := bound
  simp only [cutMemory]
  rw [Memory.install_outside _ _ _ _ (Or.inl (by omega)),
    Memory.install_outside _ _ _ _ (Or.inl (by omega)),
    Memory.install_outside _ _ _ _ (Or.inr (show 0x401120 + 6 ≤ 0x4011bb + k by omega))]
  exact Memory.install_get _ _ _ k bound

private theorem cut_plt : cutMemory.fetchBytes 0x401120 pltCode.length = some pltCode := by
  apply read_checked_span (by decide +kernel)
  intro k bound
  have hk : k < 6 := bound
  simp only [cutMemory]
  rw [Memory.install_outside _ _ _ _ (Or.inl (by omega)),
    Memory.install_outside _ _ _ _ (Or.inl (by omega))]
  exact Memory.install_get _ _ _ k bound

private theorem cut_slot : Silmaril.X86.Ext.loadN cutMemory 0x404078 8 = some 0x700a4ca0 := by
  let bytes := (List.range 8).map (wordByte 0x700a4ca0)
  have read : cutMemory.readWith .read 0x404078 bytes.length = some bytes := by
    apply read_checked_span (by decide +kernel)
    intro k bound
    have hk : k < 8 := bound
    simp only [cutMemory]
    rw [Memory.install_outside _ _ _ _ (Or.inl (by omega))]
    exact Memory.install_get _ _ _ k bound
  change (cutMemory.readWith .read 0x404078 bytes.length).map _ = _
  rw [read, Option.map_some, leValue_wordBytes]
  rfl

private theorem cut_entry :
    cutMemory.fetchBytes 0x700a4ca0 entryCode.length = some entryCode := by
  apply read_checked_span (by decide +kernel)
  intro k bound
  exact Memory.install_get _ _ _ k bound

/-- The cut is inhabited at page-aligned bases, with the value of the checked relocation. -/
theorem cut_inhabited :
    PageBase bases ∧ relocVal (resolve scope) client clientInfo slot = some target ∧
    target.word bases (fun _ => none) 0 = some (some 0x700a4ca0) ∧
    ∃ memory, ClientCut memory := by
  refine ⟨?_, resolved_slot, rfl, cutMemory, ⟨cut_call, cut_plt, cut_slot⟩, cut_entry⟩
  intro b hb
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Checked file-side data for the four ranges, including all dynamic relocation
footprints that could otherwise overwrite the code or compete for the slot. -/
theorem file_cut :
    clientRX ∈ clientInfo.phs ∧ clientRW ∈ clientInfo.phs ∧ sqliteRX ∈ sqliteInfo.phs ∧
    slot ∈ clientRows.2 ∧
    (List.range 5).all (fun k => (rowAt clientRows (0x11bb + k)).isNone) = true ∧
    (List.range 6).all (fun k => (rowAt clientRows (0x1120 + k)).isNone) = true ∧
    (List.range 8).all (fun k =>
      ((clientRows.1 ++ clientRows.2).filter (fun r => covers r.off (0x4078 + k))) == [slot]) =
      true ∧
    (List.range 5).all (fun k => (rowAt sqliteRows (0xa4ca0 + k)).isNone) = true ∧
    frun client (Rd.le 0x11bb 5) =
      some (Silmaril.X86.Link.Blob.valueLE callCode) ∧
    frun client (Rd.le 0x1120 6) =
      some (Silmaril.X86.Link.Blob.valueLE pltCode) ∧
    frun sqlite (Rd.le 0xa4ca0 5) =
      some (Silmaril.X86.Link.Blob.valueLE entryCode) := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel),
    read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel),
    read_checked sqliteK.wf_true sqliteK.toByteArray_eq (by decide +kernel)⟩

/-- The contribution of the one checked relocation to the client byte image. -/
noncomputable def selectedTable : Option (List (Nat × Option Word)) := do
  let value ← relocVal (resolve scope) client clientInfo slot
  let word ← value.word bases (fun _ => none) 0
  pure [(slot.off, word)]

theorem selected_table : selectedTable = some [(0x4078, some 0x700a4ca0)] := by
  unfold selectedTable
  rw [Option.bind_eq_bind, resolved_slot, Option.bind_some]
  rfl

/-- Every byte of the selected relocation has the same value in the loader's
projected image and in the inhabited memory. -/
theorem placed_slot_byte (k : Nat) (small : k < 8) :
    ∃ table, selectedTable = some table ∧
      expectedByte client table clientRW (0x4078 + k) = some (some (wordByte 0x700a4ca0 k)) ∧
      cutMemory.bytes.get? (0x404078 + k) = some (wordByte 0x700a4ca0 k) := by
  refine ⟨_, selected_table, ?_, ?_⟩
  · have covered : 0x4078 ≤ 0x4078 + k ∧ 0x4078 + k < 0x4078 + 8 := by omega
    simp [expectedByte, covered]
  · let bytes := (List.range 8).map (wordByte 0x700a4ca0)
    have bound : k < bytes.length := by simpa [bytes] using small
    simp only [cutMemory]
    rw [Memory.install_outside _ _ _ _ (Or.inl (by omega))]
    rw [Memory.install_get _ _ _ k bound]
    simp [bytes]

#print axioms dependency_names
#print axioms file_cut
#print axioms resolved_slot
#print axioms cut_inhabited
#print axioms placed_slot_byte

end SqliteCampaign
