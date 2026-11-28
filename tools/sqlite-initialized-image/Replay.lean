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

/-- Numeric relocation inventory of the pinned client, in ELF table order. -/
private def clientDyn : List Elf.Rela :=
  [⟨0x3db0, 8, 0, 0x1450⟩, ⟨0x3db8, 8, 0, 0x1410⟩, ⟨0x4088, 8, 0, 0x4088⟩,
    ⟨0x3fc0, 6, 2, 0⟩, ⟨0x3fc8, 6, 3, 0⟩, ⟨0x3fd0, 6, 14, 0⟩,
    ⟨0x3fd8, 6, 20, 0⟩, ⟨0x3fe0, 6, 22, 0⟩, ⟨0x40a0, 5, 21, 0⟩, ⟨0x40c0, 5, 23, 0⟩]

private def clientPlt : List Elf.Rela :=
  ([1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19] : List Nat).zipIdx.map
    fun (index, position) => ⟨0x4000 + 8 * position, 7, index, 0⟩

/-- All 26 client RELA rows, using the loader reader for both tables. -/
theorem client_inventory : frun client (Elf.relas clientInfo) = some (clientDyn, clientPlt) :=
  read_checked clientK.wf_true clientK.toByteArray_eq (by decide +kernel)

/-- A SQLite API slot and the direct client call sites covered by this receipt. -/
structure ApiSlot where
  name : String
  off : Nat
  index : Nat
  plt : Nat
  entry : Nat
  size : Nat
  sites : List Nat

def pointApi : List ApiSlot :=
  [⟨"sqlite3_bind_int",     0x4010,  5, 0x1050, 0x49810,    8, [0x11f6]⟩,
   ⟨"sqlite3_column_int",  0x4028,  8, 0x1080, 0x26ee0,   82, [0x1353]⟩,
   ⟨"sqlite3_errmsg",      0x4030,  9, 0x1090, 0x4d5d0,  298, [0x1299]⟩,
   ⟨"sqlite3_column_type", 0x4040, 11, 0x10b0, 0x27010,   82, [0x133e]⟩,
   ⟨"sqlite3_step",        0x4048, 12, 0x10c0, 0xb6600, 3969, [0x12fd, 0x135f]⟩,
   ⟨"sqlite3_close",       0x4058, 15, 0x10e0, 0x810f0,    7, [0x121e, 0x12bc]⟩,
   ⟨"sqlite3_finalize",    0x4068, 17, 0x1100, 0x81280,  223, [0x128b, 0x1317]⟩,
   ⟨"sqlite3_prepare_v2",  0x4070, 18, 0x1110, 0xce420,   27, [0x11dc]⟩,
   ⟨"sqlite3_open_v2",     0x4078, 19, 0x1120, 0xa4ca0,    5, [0x11bb]⟩]

def ApiSlot.row (a : ApiSlot) : Elf.Rela := ⟨a.off, 7, a.index, 0⟩
def ApiSlot.ref (a : ApiSlot) : Elf.Ref := ⟨nm a.name, false, none⟩
def ApiSlot.destination (a : ApiSlot) : Word := 0x70000000 + BitVec.ofNat 64 a.entry

private def inFileSpan (ph : Elf.Phdr) (va length : Nat) : Prop :=
  ph.vaddr ≤ va ∧ va + length ≤ ph.vaddr + ph.filesz ∧
    va + length ≤ ph.vaddr + ph.memsz

private instance (ph : Elf.Phdr) (va length : Nat) : Decidable (inFileSpan ph va length) :=
  inferInstanceAs (Decidable (_ ∧ _))

private def callEncoding (pc plt : Nat) : Nat :=
  0xe8 + 0x100 * (BitVec.ofInt 32 ((plt : Int) - (pc + 5 : Nat))).toNat

private def pltEncoding (a : ApiSlot) : Nat :=
  0x25ff + 0x10000 * (BitVec.ofInt 32 ((a.off : Int) - (a.plt + 6 : Nat))).toNat

private theorem point_check {p : ApiSlot → Bool} (checked : pointApi.all p = true)
    {a : ApiSlot} (member : a ∈ pointApi) : p a = true :=
  List.all_eq_true.mp checked a member

private theorem point_prop (p : ApiSlot → Prop) [∀ a, Decidable (p a)]
    (checked : pointApi.all (fun a => decide (p a)) = true)
    {a : ApiSlot} (member : a ∈ pointApi) : p a :=
  of_decide_eq_true (point_check checked member)

private theorem ref_checked {a : ApiSlot} (member : a ∈ pointApi) :
    frun client (Elf.refOf clientInfo a.index) = some a.ref :=
  read_checked clientK.wf_true clientK.toByteArray_eq
    (point_prop (fun a => (Elf.refOf clientInfo a.index).run (kread clientK) = some a.ref)
      (by decide +kernel) member)

private theorem miss_checked {a : ApiSlot} (member : a ∈ pointApi) :
    frun client (Elf.lookupDef clientInfo a.ref true) = some none :=
  read_checked clientK.wf_true clientK.toByteArray_eq
    (point_prop (fun a => (Elf.lookupDef clientInfo a.ref true).run (kread clientK) = some none)
      (by decide +kernel) member)

private theorem hit_checked {a : ApiSlot} (member : a ∈ pointApi) :
    frun sqlite (Elf.lookupDef sqliteInfo a.ref true) = some (some ⟨a.entry, false, false⟩) :=
  read_checked sqliteK.wf_true sqliteK.toByteArray_eq
    (point_prop (fun a => (Elf.lookupDef sqliteInfo a.ref true).run (kread sqliteK) =
        some (some ⟨a.entry, false, false⟩))
      (by decide +kernel) member)

private theorem api_lookup {a : ApiSlot} (member : a ∈ pointApi) :
    resolve scope a.ref true = some (some (1, ⟨a.entry, false, false⟩)) := by
  rw [resolve, scope, resolveFrom, client_info, Option.bind_eq_bind, Option.bind_some,
    miss_checked member, Option.bind_eq_bind, Option.bind_some]
  rw [resolveFrom, sqlite_info, Option.bind_eq_bind, Option.bind_some,
    hit_checked member, Option.bind_eq_bind, Option.bind_some]
  rfl

theorem api_relocation {a : ApiSlot} (member : a ∈ pointApi) :
    relocVal (resolve scope) client clientInfo a.row = some (.addr 1 a.entry) :=
  jump_value (ref_checked member) (api_lookup member)

/-- Real relocations, dedicated slots, and file-backed executable destinations. -/
theorem api_ranges {a : ApiSlot} (member : a ∈ pointApi) :
    a.row ∈ clientPlt ∧ inFileSpan clientRW a.off 8 ∧
    inFileSpan clientRX a.plt 6 ∧ inFileSpan sqliteRX a.entry a.size ∧
    (∀ pc ∈ a.sites, inFileSpan clientRX pc 5) ∧
    (∀ k : Fin 8, (clientDyn ++ clientPlt).filter (fun r => covers r.off (a.off + k.val)) =
      [a.row]) ∧ 0x4000 ≤ a.off ∧ a.off + 8 ≤ 0x4080 := by
  have checked : pointApi.all (fun p => decide (p.row ∈ clientPlt ∧
      inFileSpan clientRW p.off 8 ∧ inFileSpan clientRX p.plt 6 ∧
      inFileSpan sqliteRX p.entry p.size ∧
      (∀ pc ∈ p.sites, inFileSpan clientRX pc 5) ∧
      (∀ k : Fin 8, (clientDyn ++ clientPlt).filter (fun r => covers r.off (p.off + k.val)) =
        [p.row]) ∧ 0x4000 ≤ p.off ∧ p.off + 8 ≤ 0x4080)) = true := by decide +kernel
  exact of_decide_eq_true (point_check checked member)

private def rel32Fits (displacement : Int) : Prop :=
  -(2 ^ 31) ≤ displacement ∧ displacement < 2 ^ 31

private instance (displacement : Int) : Decidable (rel32Fits displacement) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The selected writes remain writable after RELRO, and both instruction
displacements and the loaded symbol extent fit their address widths. -/
theorem api_address_bounds {a : ApiSlot} (member : a ∈ pointApi) :
    a.off % 8 = 0 ∧ (∀ k : Fin 8, inRelro clientInfo (a.off + k.val) = false) ∧
    0x70000000 + a.entry + a.size < 2 ^ 64 ∧ rel32Fits ((a.off : Int) - (a.plt + 6 : Nat)) ∧
    ∀ pc ∈ a.sites, rel32Fits ((a.plt : Int) - (pc + 5 : Nat)) :=
  point_prop (fun a =>
    a.off % 8 = 0 ∧ (∀ k : Fin 8, inRelro clientInfo (a.off + k.val) = false) ∧
    0x70000000 + a.entry + a.size < 2 ^ 64 ∧ rel32Fits ((a.off : Int) - (a.plt + 6 : Nat)) ∧
    ∀ pc ∈ a.sites, rel32Fits ((a.plt : Int) - (pc + 5 : Nat))) (by decide +kernel) member

/-- The definition found by GNU hash must be a default-visible global function. -/
private noncomputable def providerExtent (a : ApiSlot) : Rd (Nat × Nat) := do
  let found ← Elf.lookupIn sqliteInfo a.ref true
  let index ← Rd.ofOption found
  let symbol ← Elf.sym sqliteInfo index
  Rd.guard (symbol.type = 2 ∧ symbol.bind = 1 ∧ symbol.other % 4 = 0 ∧ symbol.shndx ≠ 0)
  let size ← symSize sqliteInfo index
  pure (symbol.value, size)

theorem api_entry_extent {a : ApiSlot} (member : a ∈ pointApi) :
    frun sqlite (providerExtent a) = some (a.entry, a.size) :=
  read_checked sqliteK.wf_true sqliteK.toByteArray_eq
    (point_prop (fun a => (providerExtent a).run (kread sqliteK) = some (a.entry, a.size))
      (by decide +kernel) member)

/-- Direct CALL rel32 bytes in the client and its six-byte RIP-relative PLT jump. -/
theorem api_route_bytes {a : ApiSlot} (member : a ∈ pointApi) :
    frun client (Rd.le a.plt 6) = some (pltEncoding a) ∧
    ∀ pc ∈ a.sites, frun client (Rd.le pc 5) = some (callEncoding pc a.plt) := by
  constructor
  · exact read_checked clientK.wf_true clientK.toByteArray_eq
      (point_prop (fun a => (Rd.le a.plt 6).run (kread clientK) = some (pltEncoding a))
        (by decide +kernel) member)
  · intro pc site
    have checked : pointApi.all (fun p => p.sites.all fun loc =>
        decide ((Rd.le loc 5).run (kread clientK) = some (callEncoding loc p.plt))) =
        true := by decide +kernel
    exact read_checked clientK.wf_true clientK.toByteArray_eq
      (of_decide_eq_true (List.all_eq_true.mp (point_check checked member) pc site))

def apiTable : List (Nat × Option Word) :=
  pointApi.map fun a => (a.off, some a.destination)

private def apiFind (va : Nat) : Option (Nat × Option Word) :=
  apiTable.find? (fun item => covers item.1 va)

private def apiByte (va : Nat) : Byte :=
  match apiFind va with
  | some (off, some word) => wordByte word (va - off)
  | _ => 0

/-- Only the selected slot spans are mapped. Padding in the finite backing has no access. -/
def apiMemory : Memory :=
  ⟨pointApi.map (fun a => ⟨0x400000 + a.off, 8, ⟨true, true, false⟩⟩),
    Memory.install ∅ 0x404000 ((List.range 0x80).map fun k => apiByte (0x4000 + k))⟩

private theorem api_find {a : ApiSlot} (member : a ∈ pointApi) (k : Fin 8) :
    apiFind (a.off + k.val) = some (a.off, some a.destination) :=
  point_prop (fun a => ∀ j : Fin 8, apiFind (a.off + j.val) = some (a.off, some a.destination))
    (by decide +kernel) member k

private theorem api_backed {a : ApiSlot} (member : a ∈ pointApi) {k : Nat} (small : k < 8) :
    apiMemory.bytes.get? (0x400000 + a.off + k) = some (wordByte a.destination k) := by
  obtain ⟨_, _, _, _, _, _, lo, hi⟩ := api_ranges member
  let j := a.off - 0x4000 + k
  have hj : j < 0x80 := by dsimp [j]; omega
  have addr : 0x404000 + j = 0x400000 + a.off + k := by dsimp [j]; omega
  have va : 0x4000 + j = a.off + k := by dsimp [j]; omega
  rw [← addr]
  change (Memory.install ∅ 0x404000 ((List.range 0x80).map fun n => apiByte (0x4000 + n))).get?
    (0x404000 + j) = _
  rw [Memory.install_get _ _ _ j (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range, va, apiByte, api_find member ⟨k, small⟩,
    Nat.add_sub_cancel_left]

private theorem api_read_word {a : ApiSlot} (member : a ∈ pointApi) :
    Silmaril.X86.Ext.loadN apiMemory (0x400000 + BitVec.ofNat 64 a.off) 8 =
      some a.destination := by
  obtain ⟨_, _, _, _, _, _, _, hi⟩ := api_ranges member
  have permitted : apiMemory.checkSpan .read (0x400000 + a.off) 8 = true :=
    point_check (p := fun a => apiMemory.checkSpan .read (0x400000 + a.off) 8)
      (by decide +kernel) member
  let bytes := (List.range 8).map (wordByte a.destination)
  have read : apiMemory.readWith .read (0x400000 + a.off) bytes.length = some bytes := by
    apply read_checked_span (by simpa [bytes] using permitted)
    intro k bound
    have small : k < 8 := by simpa [bytes] using bound
    simpa [bytes] using api_backed member small
  have addr : ((0x400000 : Word) + BitVec.ofNat 64 a.off).toNat = 0x400000 + a.off :=
    addr_toNat (by change 0x400000 + a.off < 2 ^ 64; omega)
  unfold Silmaril.X86.Ext.loadN Memory.readBytes
  rw [addr]
  change (apiMemory.readWith .read (0x400000 + a.off) bytes.length).map _ = _
  rw [read, Option.map_some, leValue_wordBytes, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- All selected bindings share one inhabited, bounded projection of the eager byte image. -/
theorem point_api_closure : ∃ memory : Memory, ∀ a ∈ pointApi,
    a.row ∈ clientPlt ∧ inFileSpan clientRW a.off 8 ∧ inFileSpan sqliteRX a.entry a.size ∧
    relocVal (resolve scope) client clientInfo a.row = some (.addr 1 a.entry) ∧
    (Val.addr 1 a.entry).word bases (fun _ => none) 0 = some (some a.destination) ∧
    Silmaril.X86.Ext.loadN memory (0x400000 + BitVec.ofNat 64 a.off) 8 = some a.destination ∧
    ∀ k < 8, expectedByte client apiTable clientRW (a.off + k) =
        some (some (wordByte a.destination k)) ∧
      memory.bytes.get? (0x400000 + a.off + k) = some (wordByte a.destination k) := by
  refine ⟨apiMemory, ?_⟩
  intro a member
  obtain ⟨row, fits, _, extent, _, _, _, _⟩ := api_ranges member
  refine ⟨row, fits, extent, api_relocation member, rfl, api_read_word member, ?_⟩
  intro k small
  refine ⟨?_, api_backed member small⟩
  unfold expectedByte
  change (match apiFind (a.off + k) with
    | some (off, some word) => some (some (wordByte word (a.off + k - off)))
    | some (_, none) => some none
    | none => (imageByte client clientRW (a.off + k)).map some) = _
  rw [api_find member ⟨k, small⟩]
  simp only [Nat.add_sub_cancel_left]

#print axioms client_inventory
#print axioms api_ranges
#print axioms api_address_bounds
#print axioms api_entry_extent
#print axioms api_route_bytes
#print axioms point_api_closure

end SqliteCampaign
