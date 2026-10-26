module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.Compress

/-! # Explicit dynamic compressor stack geometry and permissions

With launch stack `top`, the driver calls at `top - 32`, the callee enters at
`top - 40`, and its frame plus red zone starts at `top - 384`. The 352-byte
span includes the return slot. Geometry establishes separation, not mappings.
`Loaded` supplies write permission only; the read permission remains explicit.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.CompressionStack

open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word sysv64)
open Silmaril.Crypto.X86.Sha256O2

def entryStack (top : Nat) : Word := BitVec.ofNat 64 (top - 40)

/-- A sufficient, satisfiable geometry placing the entire callee stack above
the loaded driver's globals. It implies neither read nor write permission. -/
structure Geometry (top : Nat) : Prop where
  aboveGlobals : 0x401680 + 384 ≤ top
  bounded : top < addressLimit
  aligned : top % 16 = 0

/-- Loaded already supplies alignment and the machine-word bound. Only the
additional stack/global separation condition is required here. -/
theorem Geometry.of_loaded {input : ProcInput} {initial : Core} {memory : Memory}
    (loaded : Loaded image input initial memory)
    (apart : 0x401680 + 384 ≤ (initial.read .rsp).toNat) :
    Geometry (initial.read .rsp).toNat :=
  ⟨apart, BitVec.isLt _, loaded.2.2.1.aligned⟩

theorem Geometry.entry_toNat {top : Nat} (geometry : Geometry top) :
    (entryStack top).toNat = top - 40 := by
  simp only [entryStack, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := geometry.bounded; dsimp [addressLimit] at *; omega)

theorem Geometry.call_sub {top : Nat} (geometry : Geometry top) :
    BitVec.ofNat 64 (top - 32) - (8 : Word) = entryStack top := by
  have lower := geometry.aboveGlobals
  erw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (top - 32) 8 (by decide) (by omega)]
  congr 1

theorem Geometry.frame_floor {top : Nat} (geometry : Geometry top) :
    sysv64.frameFloor (entryStack top).toNat frameSize = top - 384 := by
  rw [frameFloor_frameSize, geometry.entry_toNat]
  omega

theorem Geometry.entry_aligned {top : Nat} (geometry : Geometry top) :
    sysv64.EntryAligned (entryStack top).toNat := by
  rw [Silmaril.X86.sysv64_entryAligned_iff, geometry.entry_toNat]
  have := geometry.aboveGlobals
  have := geometry.aligned
  omega

theorem Geometry.frame_fits {top : Nat} (geometry : Geometry top) :
    sysv64.frameExtent frameSize ≤ (entryStack top).toNat := by
  rw [geometry.entry_toNat]
  change 344 ≤ top - 40
  have := geometry.aboveGlobals
  omega

theorem Geometry.noWrap {top : Nat} (geometry : Geometry top) (exit : Word) :
    ∀ region ∈ regions (Compress.layout exit) 0x401660 0x401620 (entryStack top) frameSize,
      region.base + region.size ≤ addressLimit := by
  intro region member
  simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [stateRegion, blockRegion, codeRegion, kTableRegion, frameRegion,
      returnSlot, Compress.layout, Compress.textBase, Compress.rodataBase,
      geometry.entry_toNat]
  all_goals have := geometry.aboveGlobals; have := geometry.bounded
  all_goals change _ ≤ addressLimit
  all_goals dsimp [size, kSize, Silmaril.Machine.CallingConvention.frameFloor,
    Silmaril.Machine.CallingConvention.frameExtent,
    sysv64, frameSize, addressLimit] at *
  all_goals omega

theorem Geometry.disjoint {top : Nat} (geometry : Geometry top) (exit : Word) :
    (regions (Compress.layout exit) 0x401660 0x401620 (entryStack top) frameSize).Pairwise
      Region.Disjoint := by
  simp only [regions, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq,
    stateRegion, blockRegion, codeRegion, kTableRegion, frameRegion, returnSlot,
    Compress.layout, Compress.textBase, Compress.rodataBase, Region.Disjoint,
    geometry.entry_toNat]
  have := geometry.aboveGlobals
  simp
  dsimp [size, kSize, Silmaril.Machine.CallingConvention.frameFloor,
    Silmaril.Machine.CallingConvention.frameExtent, sysv64, frameSize]
  omega

/-- Only permissions, no preinstalled frame bytes or return address. -/
structure Mapping (memory : Memory) (top : Nat) : Prop where
  readable : memory.Permitted .read (top - 384) 352
  writable : memory.Permitted .write (top - 384) 352

theorem Mapping.transport {initial current : Memory} {top : Nat}
    (mapping : Mapping initial top) {inside : Nat → Prop}
    (writes : Memory.WritesWithin initial current inside) : Mapping current top :=
  ⟨(writes.permitted_iff _ _ _).mpr mapping.readable,
    (writes.permitted_iff _ _ _).mpr mapping.writable⟩

/-- The loader's writable room discharges the whole required write span.
Its missing read permission is retained as the sole new mapping premise. -/
theorem Mapping.of_loaded {input : ProcInput} {initial : Core} {memory : Memory}
    (loaded : Loaded image input initial memory)
    (readable : memory.Permitted .read ((initial.read .rsp).toNat - 384) 352) :
    Mapping memory (initial.read .rsp).toNat := by
  have room := loaded.2.2.2.1
  have writable := loaded.2.2.2.2.1
  refine ⟨readable, X86.Ext.Memory.Permitted.sub writable ?_ ?_ ?_⟩
  all_goals dsimp [stackRoom] at *; omega

theorem Mapping.frame {memory : Memory} {top : Nat}
    (mapping : Mapping memory top) (geometry : Geometry top) :
    memory.Permitted .read (sysv64.frameFloor (entryStack top).toNat frameSize)
        (sysv64.frameExtent frameSize) ∧
      memory.Permitted .write (sysv64.frameFloor (entryStack top).toNat frameSize)
        (sysv64.frameExtent frameSize) := by
  rw [geometry.frame_floor]
  exact ⟨X86.Ext.Memory.Permitted.sub mapping.readable (by decide) (by omega) (by
      change top - 384 + 344 ≤ top - 384 + 352; omega),
    X86.Ext.Memory.Permitted.sub mapping.writable (by decide) (by omega) (by
      change top - 384 + 344 ≤ top - 384 + 352; omega)⟩

theorem Mapping.return_slot {memory : Memory} {top : Nat}
    (mapping : Mapping memory top) (geometry : Geometry top) :
    memory.Permitted .read (entryStack top).toNat 8 ∧
      memory.Permitted .write (entryStack top).toNat 8 := by
  rw [geometry.entry_toNat]
  have := geometry.aboveGlobals
  exact ⟨X86.Ext.Memory.Permitted.sub mapping.readable (by decide) (by omega) (by omega),
    X86.Ext.Memory.Permitted.sub mapping.writable (by decide) (by omega) (by omega)⟩

end Silmaril.Process.CLI.Sha256Cli.CompressionStack
