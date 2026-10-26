module

public import Silmaril.Apps.Sha256sum.Binary

/-! # Entering the linked compression routine after driver writes

The executable's entire `Image.Mapped` predicate need not hold at a later call:
the driver may already have changed mutable data. `constants_of_loaded_writesWithin`
retains only the fetched compression code and readable K table across writes
outside those two regions. `CallSite.entry_of_loaded` supplies exactly these
loader facts and the checked relocation to the existing, unchanged `SysVEntry`.

The call site still owes its argument, backing, stack and separation clauses.
The final lemmas turn the compression contract's footprint into unchanged reads
of any driver buffer disjoint from the output state and callee frame.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Binary

open Silmaril.Process (Access Memory Region)
open Silmaril.X86 (MState Word sysv64)
open Silmaril.Crypto.X86.Sha256O2

/-- The caller-owned part of `SysVEntry` for this linked routine. The omitted
clauses are precisely `code`, `kTable` and `relocFits`; every ABI and memory
geometry clause remains explicit. -/
structure CallSite (exit state block rspEntry : Word) (initial : MState) : Prop where
  rip : initial.core.rip = (layout exit).textBase
  argState : initial.core.read .rdi = state
  argBlock : initial.core.read .rsi = block
  rsp : initial.core.read .rsp = rspEntry
  aligned : sysv64.EntryAligned rspEntry.toNat
  returnAddress : initial.memory.readBytes rspEntry.toNat 8 =
    some (Silmaril.X86.Ext.leBytes exit 8)
  stateReads : StateReads initial.memory state
  stateWritable : initial.memory.Permitted .write state.toNat 32
  blockReads : BlockReads initial.memory block
  frameMapped :
    initial.memory.Permitted .read (sysv64.frameFloor rspEntry.toNat frameSize)
        (sysv64.frameExtent frameSize) ∧
      initial.memory.Permitted .write (sysv64.frameFloor rspEntry.toNat frameSize)
        (sysv64.frameExtent frameSize)
  frameFits : sysv64.frameExtent frameSize ≤ rspEntry.toNat
  noWrap : ∀ r ∈ regions (layout exit) state block rspEntry frameSize,
    r.base + r.size ≤ Silmaril.Process.addressLimit
  disjoint : (regions (layout exit) state block rspEntry frameSize).Pairwise Region.Disjoint
  stateAligned : state.toNat % 4 = 0

/-- Forgetting loader-owned clauses does not change any call-site requirement. -/
theorem CallSite.of_entry {exit state block rspEntry : Word} {initial : MState}
    (h : SysVEntry (layout exit) state block rspEntry frameSize initial) :
    CallSite exit state block rspEntry initial :=
  { rip := h.rip
    argState := h.argState
    argBlock := h.argBlock
    rsp := h.rsp
    aligned := h.aligned
    returnAddress := h.returnAddress
    stateReads := h.stateReads
    stateWritable := h.stateWritable
    blockReads := h.blockReads
    frameMapped := h.frameMapped
    frameFits := h.frameFits
    noWrap := h.noWrap
    disjoint := h.disjoint
    stateAligned := h.stateAligned }

/-- Supply the linked constants to recover the full, unweakened precondition. -/
theorem CallSite.entry {exit state block rspEntry : Word} {initial : MState}
    (h : CallSite exit state block rspEntry initial)
    (code : initial.memory.fetchBytes textBase.toNat size = some (image textBase rodataBase))
    (kTable : initial.memory.readBytes rodataBase.toNat kSize = some kBytes) :
    SysVEntry (layout exit) state block rspEntry frameSize initial :=
  { rip := h.rip
    code := code
    relocFits := layout_relocFits exit
    kTable := kTable
    argState := h.argState
    argBlock := h.argBlock
    rsp := h.rsp
    aligned := h.aligned
    returnAddress := h.returnAddress
    stateReads := h.stateReads
    stateWritable := h.stateWritable
    blockReads := h.blockReads
    frameMapped := h.frameMapped
    frameFits := h.frameFits
    noWrap := h.noWrap
    disjoint := h.disjoint
    stateAligned := h.stateAligned }

/-- A loaded image supplies the required constants even after mutable driver
data have changed. The footprint is arbitrary; it must exclude the code and K
table, and `WritesWithin` also retains their permissions. -/
theorem constants_of_loaded_writesWithin {loaded current : Memory} {inside : Nat → Prop}
    (mapped : Image.image.Mapped loaded)
    (writes : Memory.WritesWithin loaded current inside)
    (codeOutside : ∀ address, (codeRegion (layout 0)).Contains address → ¬ inside address)
    (kTableOutside : ∀ address, (kTableRegion (layout 0)).Contains address → ¬ inside address) :
    current.fetchBytes textBase.toNat size = some (image textBase rodataBase) ∧
      current.readBytes rodataBase.toNat kSize = some kBytes := by
  constructor
  · rw [writes.fetchBytes ?_]
    · exact loaded_code mapped
    · intro offset hoffset
      exact codeOutside _ (by simp only [codeRegion, layout, Region.Contains]; omega)
  · rw [writes.readBytes ?_]
    · exact loaded_kTable mapped
    · intro offset hoffset
      exact kTableOutside _ (by simp only [kTableRegion, layout, Region.Contains]; omega)

/-- Complete the call-site precondition using constants preserved since load.
No mapping claim is made about the executable's mutable data at call time. -/
theorem CallSite.entry_of_loaded {exit state block rspEntry : Word} {initial : MState}
    (h : CallSite exit state block rspEntry initial) {loaded : Memory} {inside : Nat → Prop}
    (mapped : Image.image.Mapped loaded)
    (writes : Memory.WritesWithin loaded initial.memory inside)
    (codeOutside : ∀ address, (codeRegion (layout 0)).Contains address → ¬ inside address)
    (kTableOutside : ∀ address, (kTableRegion (layout 0)).Contains address → ¬ inside address) :
    SysVEntry (layout exit) state block rspEntry frameSize initial := by
  obtain ⟨code, kTable⟩ := constants_of_loaded_writesWithin mapped writes codeOutside kTableOutside
  exact h.entry code kTable

/-- A buffer disjoint from both halves of the compression footprint contains
no address that the contract permits the callee to modify. -/
theorem region_outside_footprint {buffer : Region} {state rspEntry : Word} {frame : Nat}
    (stateDisjoint : Region.Disjoint buffer (stateRegion state))
    (frameDisjoint : Region.Disjoint buffer (frameRegion rspEntry frame))
    {address : Nat} (inside : buffer.Contains address) :
    ¬ Footprint state rspEntry frame address := by
  rintro (hs | hf)
  · simp only [Region.Disjoint, Region.Contains] at stateDisjoint inside hs
    omega
  · simp only [Region.Disjoint, Region.Contains] at frameDisjoint inside hf
    omega

/-- A driver-buffer read with any access kind is unchanged by compression. -/
theorem post_readWith_region {L : Layout} {state block rspEntry : Word} {frame : Nat}
    {initial final : MState} (post : Post L state block rspEntry frame initial final)
    (buffer : Region)
    (stateDisjoint : Region.Disjoint buffer (stateRegion state))
    (frameDisjoint : Region.Disjoint buffer (frameRegion rspEntry frame)) (access : Access) :
    final.memory.readWith access buffer.base buffer.size =
      initial.memory.readWith access buffer.base buffer.size := by
  apply post.untouched.readWith
  intro offset hoffset
  exact region_outside_footprint stateDisjoint frameDisjoint
    (by simp only [Region.Contains]; omega)

theorem post_readBytes_region {L : Layout} {state block rspEntry : Word} {frame : Nat}
    {initial final : MState} (post : Post L state block rspEntry frame initial final)
    (buffer : Region)
    (stateDisjoint : Region.Disjoint buffer (stateRegion state))
    (frameDisjoint : Region.Disjoint buffer (frameRegion rspEntry frame)) :
    final.memory.readBytes buffer.base buffer.size = initial.memory.readBytes buffer.base buffer.size :=
  post_readWith_region post buffer stateDisjoint frameDisjoint .read

theorem post_fetchBytes_region {L : Layout} {state block rspEntry : Word} {frame : Nat}
    {initial final : MState} (post : Post L state block rspEntry frame initial final)
    (buffer : Region)
    (stateDisjoint : Region.Disjoint buffer (stateRegion state))
    (frameDisjoint : Region.Disjoint buffer (frameRegion rspEntry frame)) :
    final.memory.fetchBytes buffer.base buffer.size = initial.memory.fetchBytes buffer.base buffer.size :=
  post_readWith_region post buffer stateDisjoint frameDisjoint .execute

/-- In particular the fetched linked compression code survives its own call. -/
theorem post_code {exit state block rspEntry : Word} {initial final : MState}
    (entry : SysVEntry (layout exit) state block rspEntry frameSize initial)
    (post : Post (layout exit) state block rspEntry frameSize initial final) :
    final.memory.fetchBytes textBase.toNat size = some (image textBase rodataBase) := by
  have stateDisjoint : Region.Disjoint (codeRegion (layout exit)) (stateRegion state) := by
    simpa only [Region.Disjoint, or_comm] using entry.state_disjoint_code
  exact (post_fetchBytes_region post (codeRegion (layout exit)) stateDisjoint
    entry.code_disjoint_frame).trans entry.code

/-- The linked K table likewise survives a call, for reuse by a later call. -/
theorem post_kTable {exit state block rspEntry : Word} {initial final : MState}
    (entry : SysVEntry (layout exit) state block rspEntry frameSize initial)
    (post : Post (layout exit) state block rspEntry frameSize initial final) :
    final.memory.readBytes rodataBase.toNat kSize = some kBytes := by
  have stateDisjoint : Region.Disjoint (kTableRegion (layout exit)) (stateRegion state) := by
    simpa only [Region.Disjoint, or_comm] using entry.state_disjoint_kTable
  exact (post_readBytes_region post (kTableRegion (layout exit)) stateDisjoint
    entry.kTable_disjoint_frame).trans entry.kTable

/-- The retained call-site clauses are satisfiable at the linked layout, for
every continuation address. This uses the existing backed-entry builder. -/
theorem callSite_realisable (exit : Word) :
    ∃ initial, CallSite exit 0x500000 0x501000 0x7ffff008 initial := by
  refine ⟨_, CallSite.of_entry (entryState_sysVEntry (L := layout exit)
    (state := 0x500000) (block := 0x501000) (rspEntry := 0x7ffff008)
    (frame := frameSize) (layout_relocFits exit) ?_ ?_ ?_ ?_ ?_)⟩
  · rw [Silmaril.X86.sysv64_entryAligned_iff]; decide
  · decide
  · decide
  · change ∀ r ∈ regions (layout 0) 0x500000 0x501000 0x7ffff008 frameSize,
      r.base + r.size ≤ Silmaril.Process.addressLimit
    decide
  · change (regions (layout 0) 0x500000 0x501000 0x7ffff008 frameSize).Pairwise Region.Disjoint
    decide

end Silmaril.Apps.Sha256sum.Binary
