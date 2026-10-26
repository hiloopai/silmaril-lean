module

public import Silmaril.Process.CLI.Sha256Cli.CompressionEntry

/-! # The caller's immutable bytes survive the actual compression call -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.CompressionEntry

open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (MState)
open Silmaril.Crypto.X86.Sha256O2

theorem footprint_above_code (address : Nat) (below : address < 0x4005c0) :
    ¬ Footprint (0x401660 : Silmaril.X86.Word) entryStack frameSize address := by
  simp only [Footprint, stateRegion, frameRegion, Region.Contains, entryStack,
    Machine.CallingConvention.frameFloor, Machine.CallingConvention.frameExtent,
    X86.sysv64, frameSize, sp]
  norm_num [BitVec.toNat_ofNat] at *
  omega

theorem post_intact {initial final : MState}
    (post : Post (EmptySupport.layout returnAddress) 0x401660 0x401620 entryStack frameSize initial final)
    (intact : Output.Intact initial.memory) : Output.Intact final.memory := by
  intro entry member
  have upper := Output.code_end entry member
  rw [post.untouched.fetchBytes (by
    intro offset bound
    exact footprint_above_code _ (by omega))]
  exact intact entry member

theorem post_hexTable {initial final : MState}
    (post : Post (EmptySupport.layout returnAddress) 0x401660 0x401620 entryStack frameSize initial final) :
    final.memory.readBytes 0x4004b0 16 = initial.memory.readBytes 0x4004b0 16 :=
  post.untouched.readBytes (by
    intro offset bound
    exact footprint_above_code _ (by omega))

end Silmaril.Process.CLI.Sha256Cli.CompressionEntry
