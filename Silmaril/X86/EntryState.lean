module

public import Silmaril.X86.Machine

/-!
# A reusable entry-state builder

A compiled-function contract states its precondition as "there is a machine
state whose memory maps these regions, backs these of them with these bytes,
and whose registers hold these values". Proving such a precondition *non-vacuous*
means exhibiting one. This module builds that state once, generically, so each
contract only has to supply its own region list and check the geometry.

The input is a list of `Placement`s: a `Silmaril.Process.Region` — base, size and
permissions — together with an optional blob of backing bytes covering it
exactly. `some bs` makes the region readable back as `bs`; `none` leaves it
mapped but unbacked, which is what a fresh stack frame is: a caller cannot be
asked to pre-fill the callee's frame, so requiring backing there would make the
precondition unsatisfiable.

The side conditions are only about geometry: each backing has its region's
length, no region runs past `Silmaril.Process.addressLimit`, and the regions are
pairwise disjoint. Everything else — permission checks, reading a blob back,
fetching code, the register reads — is proved here once.

Nothing is duplicated: `Memory`, `Region`, `Permitted`, `install`, `readWith`
and the System V record are main's.
-/

@[expose] public section

namespace Silmaril.X86.EntryState

open Silmaril.Process (Memory Region Access Permissions Byte ByteMemory addressLimit)

/-! ## Installing several disjoint blobs -/

/-- A run of backing bytes at an address. -/
abbrev Blob := Nat × List Byte

/-- Two blobs occupy disjoint spans. -/
def Blob.Disjoint (first second : Blob) : Prop :=
  first.1 + first.2.length ≤ second.1 ∨ second.1 + second.2.length ≤ first.1

/-- Install every blob, in list order. -/
def installAll (bytes : ByteMemory) : List Blob → ByteMemory
  | [] => bytes
  | blob :: rest => installAll (Memory.install bytes blob.1 blob.2) rest

/-- An address outside every blob keeps whatever backing it already had. -/
theorem installAll_outside {bytes : ByteMemory} {blobs : List Blob} {address : Nat}
    (outside : ∀ blob ∈ blobs, address < blob.1 ∨ blob.1 + blob.2.length ≤ address) :
    (installAll bytes blobs).get? address = bytes.get? address := by
  induction blobs generalizing bytes with
  | nil => rfl
  | cons blob rest ih =>
    rw [installAll, ih fun other member => outside other (List.mem_cons_of_mem _ member)]
    exact Memory.install_outside _ _ _ _ (outside blob List.mem_cons_self)

/-- Pairwise-disjoint blobs do not disturb each other: every one of them reads
back exactly as installed, whatever its position in the list. -/
theorem installAll_get {bytes : ByteMemory} {blobs : List Blob} {blob : Blob} {index : Nat}
    (pairwise : blobs.Pairwise Blob.Disjoint) (member : blob ∈ blobs)
    (bound : index < blob.2.length) :
    (installAll bytes blobs).get? (blob.1 + index) = some blob.2[index] := by
  induction blobs generalizing bytes with
  | nil => cases member
  | cons head rest ih =>
    rw [List.pairwise_cons] at pairwise
    rcases List.mem_cons.mp member with rfl | tail
    · rw [installAll, installAll_outside ?_]
      · exact Memory.install_get _ _ _ _ bound
      · intro other member
        rcases pairwise.1 other member with apart | apart
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    · exact ih pairwise.2 tail

/-! ## Placements -/

/-- One mapping of the entry state: a region, and optionally the bytes backing
it. `backing = none` leaves the region mapped but unbacked. -/
structure Placement where
  /-- Base, size and permissions, as `Silmaril.Process` records them. -/
  region : Region
  /-- `some bs` installs `bs` over the whole region; `bs.length = region.size`
  is part of `WF`. -/
  backing : Option (List Byte)

/-- The blob a placement contributes, if it is backed. -/
def Placement.blob? (placement : Placement) : Option Blob :=
  placement.backing.map (placement.region.base, ·)

/-- Every backed placement's blob, in order. -/
def blobs (placements : List Placement) : List Blob :=
  placements.filterMap Placement.blob?

/-- The memory of the entry state: the placements' regions, backed by their
blobs over empty memory. -/
def memory (placements : List Placement) : Memory :=
  { regions := placements.map Placement.region, bytes := installAll ∅ (blobs placements) }

@[simp] theorem memory_regions (placements : List Placement) :
    (memory placements).regions = placements.map Placement.region := rfl

/-- The geometric side conditions, and only those. -/
structure WF (placements : List Placement) : Prop where
  /-- A backing covers its region exactly. -/
  backing_length : ∀ placement ∈ placements, ∀ bytes,
    placement.backing = some bytes → bytes.length = placement.region.size
  /-- No region runs past the address space. -/
  noWrap : ∀ placement ∈ placements,
    placement.region.base + placement.region.size ≤ addressLimit
  /-- The regions are pairwise disjoint. -/
  disjoint : (placements.map Placement.region).Pairwise Region.Disjoint

theorem region_mem {placements : List Placement} {placement : Placement}
    (member : placement ∈ placements) : placement.region ∈ (memory placements).regions :=
  List.mem_map_of_mem member

theorem blob_mem {placements : List Placement} {placement : Placement} {bytes : List Byte}
    (member : placement ∈ placements) (backed : placement.backing = some bytes) :
    (placement.region.base, bytes) ∈ blobs placements :=
  List.mem_filterMap.mpr ⟨placement, member, by simp [Placement.blob?, backed]⟩

theorem blobs_pairwise {placements : List Placement} (wf : WF placements) :
    (blobs placements).Pairwise Blob.Disjoint := by
  refine List.pairwise_filterMap.mpr ?_
  have regions : placements.Pairwise fun first second =>
      Region.Disjoint first.region second.region := List.pairwise_map.mp wf.disjoint
  refine regions.imp_of_mem ?_
  rintro first second firstMem secondMem apart ⟨_, xs⟩ firstBlob ⟨_, ys⟩ secondBlob
  simp only [Placement.blob?, Option.map_eq_some_iff] at firstBlob secondBlob
  obtain ⟨bs, firstBacked, firstEq⟩ := firstBlob
  obtain ⟨cs, secondBacked, secondEq⟩ := secondBlob
  have firstLen := wf.backing_length first firstMem bs firstBacked
  have secondLen := wf.backing_length second secondMem cs secondBacked
  cases firstEq; cases secondEq
  simpa [Blob.Disjoint, Region.Disjoint, firstLen, secondLen] using apart

/-! ## What the builder proves -/

/-- Any span inside a placement's region carries that region's permissions. -/
theorem permitted {placements : List Placement} (wf : WF placements) {placement : Placement}
    (member : placement ∈ placements) {access : Access}
    (allowed : placement.region.permissions.allows access = true) {address length : Nat}
    (lower : placement.region.base ≤ address)
    (start : address < placement.region.base + placement.region.size)
    (upper : address + length ≤ placement.region.base + placement.region.size) :
    (memory placements).Permitted access address length := by
  have bound := wf.noWrap placement member
  exact Memory.permitted_of_region _ _ _ _ placement.region (region_mem member) allowed
    (by omega) (by omega) lower upper

/-- A whole nonempty region carries its own permissions. -/
theorem permitted_region {placements : List Placement} (wf : WF placements)
    {placement : Placement} (member : placement ∈ placements) {access : Access}
    (allowed : placement.region.permissions.allows access = true)
    (nonempty : 0 < placement.region.size) :
    (memory placements).Permitted access placement.region.base placement.region.size :=
  permitted wf member allowed (Nat.le_refl _) (by omega) (Nat.le_refl _)

/-- A backed placement reads back exactly as installed, under any access its
permissions allow. -/
theorem readWith_blob {placements : List Placement} (wf : WF placements) {placement : Placement}
    (member : placement ∈ placements) {bytes : List Byte}
    (backed : placement.backing = some bytes) {access : Access}
    (allowed : placement.region.permissions.allows access = true)
    (nonempty : 0 < placement.region.size) :
    (memory placements).readWith access placement.region.base placement.region.size = some bytes := by
  have length := wf.backing_length placement member bytes backed
  rw [← length]
  refine Memory.readWith_eq _ _ _ _ ?_ fun index bound => ?_
  · rw [length]; exact permitted_region wf member allowed nonempty
  · exact installAll_get (blobs_pairwise wf) (blob_mem member backed) bound

/-- The readable case of `readWith_blob`. -/
theorem readBytes_blob {placements : List Placement} (wf : WF placements) {placement : Placement}
    (member : placement ∈ placements) {bytes : List Byte}
    (backed : placement.backing = some bytes)
    (readable : placement.region.permissions.read = true)
    (nonempty : 0 < placement.region.size) :
    (memory placements).readBytes placement.region.base placement.region.size = some bytes :=
  readWith_blob wf member backed readable nonempty

/-- The executable case of `readWith_blob`: code fetches back as the image. -/
theorem fetchBytes_blob {placements : List Placement} (wf : WF placements) {placement : Placement}
    (member : placement ∈ placements) {bytes : List Byte}
    (backed : placement.backing = some bytes)
    (executable : placement.region.permissions.execute = true)
    (nonempty : 0 < placement.region.size) :
    (memory placements).fetchBytes placement.region.base placement.region.size = some bytes :=
  readWith_blob wf member backed executable nonempty

/-! ## Registers

The memory is the hard part; the registers are a few `State.write`s. `sysvCore`
is the shape a System V entry has: RIP at the entry point, the first two integer
arguments in RDI and RSI, and RSP at the entry stack pointer. Everything else —
the callee-saved registers and the flags — is inherited, so a caller may supply
any state at all. -/

/-- Flags with every status bit undefined: the weakest flags there are. -/
def unknownFlags : Flags := ⟨none, none, none, none, none, none⟩

/-- A state with every register zero, every flag undefined, and RIP at `rip`. -/
def blankCore (rip : Word) : State :=
  { regs := fun _ => 0, rip := rip, flags := unknownFlags, fsBase := 0 }

/-- The register file at a System V entry. -/
def sysvCore (core : State) (entry arg0 arg1 sp : Word) : State :=
  { ((core.write .rdi arg0).write .rsi arg1).write .rsp sp with rip := entry }

@[simp] theorem sysvCore_rip (core : State) (entry arg0 arg1 sp : Word) :
    (sysvCore core entry arg0 arg1 sp).rip = entry := rfl

@[simp] theorem sysvCore_rdi (core : State) (entry arg0 arg1 sp : Word) :
    (sysvCore core entry arg0 arg1 sp).read .rdi = arg0 := by
  simp [sysvCore, State.read, State.write, Machine.RegisterFile.write]

@[simp] theorem sysvCore_rsi (core : State) (entry arg0 arg1 sp : Word) :
    (sysvCore core entry arg0 arg1 sp).read .rsi = arg1 := by
  simp [sysvCore, State.read, State.write, Machine.RegisterFile.write]

@[simp] theorem sysvCore_rsp (core : State) (entry arg0 arg1 sp : Word) :
    (sysvCore core entry arg0 arg1 sp).read .rsp = sp := by
  simp [sysvCore, State.read, State.write, Machine.RegisterFile.write]

/-- The entry state itself. -/
def build (core : State) (placements : List Placement) : MState := ⟨core, memory placements⟩

@[simp] theorem build_core (core : State) (placements : List Placement) :
    (build core placements).core = core := rfl

@[simp] theorem build_memory (core : State) (placements : List Placement) :
    (build core placements).memory = memory placements := rfl

end Silmaril.X86.EntryState
