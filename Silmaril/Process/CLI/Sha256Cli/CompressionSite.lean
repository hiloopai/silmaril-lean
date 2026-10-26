module

public import Silmaril.Process.CLI.Sha256Cli.CompressionStack
public import Silmaril.Process.CLI.X86Linux.Call

/-! # The three actual driver compression CALL sites

A full input block, an extra padding block and the final length-bearing block
call the same checked compressor with different real return addresses. These
finite descriptors bind each site to the transcript's executable bytes.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli

open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

inductive CompressionSite where
  | fullBlock
  | extraPadding
  | finalBlock
  deriving DecidableEq, Repr

namespace CompressionSite

def address : CompressionSite → Word
  | .fullBlock => 0x4001a8
  | .extraPadding => 0x4001f3
  | .finalBlock => 0x400229

def displacement : CompressionSite → BitVec 32
  | .fullBlock => 0x133
  | .extraPadding => 0xe8
  | .finalBlock => 0xb2

def returnAddress (site : CompressionSite) : Word := site.address + 5

def entryCore (site : CompressionSite) (c : Core) : Core :=
  directCallCore c site.displacement

/-- Each actual rel32 displacement lands at the same compressor entry. -/
theorem target (site : CompressionSite) :
    site.address + 5 + site.displacement.signExtend 64 = 0x4002e0 := by
  cases site <;> decide

set_option maxRecDepth 10000 in
/-- Fetch facts come from the checked transcript, not a source-level call. -/
theorem fetch (site : CompressionSite) {memory : Memory} {c : Core}
    (intact : Output.Intact memory) (pc : c.rip = site.address) :
    memory.fetchBytes c.rip.toNat 5 = some (X86.Ext.encode (.call site.displacement)) := by
  rw [pc]
  cases site with
  | fullBlock => exact intact Binary.i_4001a8 (by simp [Binary.transcript])
  | extraPadding => exact intact Binary.i_4001f3 (by simp [Binary.transcript])
  | finalBlock => exact intact Binary.i_400229 (by simp [Binary.transcript])

end CompressionSite

end Silmaril.Process.CLI.Sha256Cli
