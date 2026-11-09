module

public import Silmaril.Formats.Compression.Zlib.Defs
public import Silmaril.Formats.Compression.Gzip.Defs
public import Silmaril.Formats.Compression.Inflate.Common
public import Silmaril.Formats.Compression.Inflate.Manual.Dynamic
public import Silmaril.Formats.Compression.Inflate.Manual.Stored
public import Silmaril.Formats.Compression.Inflate.Manual.Symbols
public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedData
public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedDecode
public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedReservoir
public import Silmaril.Formats.Compression.Inflate.Packed.PackedFixedToken
public import Silmaril.Formats.Compression.Inflate.Packed.PackedLookupSound
public import Silmaril.Formats.Compression.Inflate.Packed.PackedTableEntry
public import Silmaril.Formats.Compression.Inflate.Packed.PackedTables
public import Silmaril.Formats.Compression.Inflate.Stream.Bits
public import Silmaril.Formats.Compression.Inflate.Stream.Blocks
public import Silmaril.Formats.Compression.Inflate.Stream.CheckedRaw
public import Silmaril.Formats.Compression.Inflate.Stream.Checksums
public import Silmaril.Formats.Compression.Inflate.Stream.ContainerFields
public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeader
public import Silmaril.Formats.Compression.Inflate.Stream.GzipHeaderSpec
public import Silmaril.Formats.Compression.Inflate.Stream.History
public import Silmaril.Formats.Compression.Inflate.Stream.MemberExamples
public import Silmaril.Formats.Compression.Inflate.Stream.MemberMachine
public import Silmaril.Formats.Compression.Inflate.Stream.MemberSemantics
public import Silmaril.Formats.Compression.Inflate.Stream.MemberSpec
public import Silmaril.Formats.Compression.Inflate.Stream.ParserBridge
public import Silmaril.Formats.Compression.Inflate.Stream.Parser
public import Silmaril.Formats.Compression.Inflate.Stream.ParserPhases
public import Silmaril.Formats.Compression.Inflate.Stream.Progress
public import Silmaril.Formats.Compression.Inflate.Stream.Protocol
public import Silmaril.Formats.Compression.Inflate.Stream.RawContainers
public import Silmaril.Formats.Compression.Inflate.Stream.RawEmission
public import Silmaril.Formats.Compression.Inflate.Stream.RawMachine
public import Silmaril.Formats.Compression.Inflate.Stream.RawRuns
public import Silmaril.Formats.Compression.Inflate.Stream.RawSemantics
public import Silmaril.Formats.Compression.Inflate.Stream.ReaderOffset
public import Silmaril.Formats.Compression.Inflate.Stream.TokenContinuation
public import Silmaril.Formats.Compression.Inflate.Stream.TokenMachine
public import Silmaril.Formats.Compression.Inflate.Stream.TokenOutput

/-!
# Streaming inflate: zlib 1.3.1's resumable inflater, as a mathematical machine

A model of the streaming decoder of zlib 1.3.1 (`inflate.c`) with arbitrary
call chunking: each call (`RawMachine.Call`) offers more input bytes, a
scheduler budget and an output capacity, and the machine suspends with its
exact continuation when it runs out of any of them. It is a mathematical
inflater, **not** a C or machine-code refinement of zlib; such a refinement
would be stated against it.

* `RawMachine`: the raw DEFLATE controller (block header, stored copy, dynamic
  table construction, token loop with a 32 KiB window);
* `MemberMachine`: a zlib or gzip member around it (header, body with running
  checksum, trailer, then `done` or `bad`);
* `member version kind`, `raw version`: these machines as framework
  `Incremental` decoders, whose soundness is proved against `Zlib.decoder`,
  `Gzip.decoder` and `Deflate.decoder` (`Inflate.Thms`);
* `Stream.Version`: `.v131` is zlib 1.3.1; `.develop` is a later development
  revision whose block dispatcher is defined separately. Results quantify over
  both or use `.v131`;
* `Manual.PackedTables`: zlib's packed Huffman table entries (`Entry`, after
  `inftrees.h`), the slow-path table `lookup` and `decode`, and the fixed tables
  `lenfix` and `distfix` of `inffixed.h`.

`Task.member_complete` and `Task.raw_complete` (frozen, open) are the
completeness directions.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.Inflate

open Silmaril.Formats.Compression.Inflate.Stream

/-- What a member machine reports. -/
def memberStatus : MemberMachine → Compression.Status
  | .done state => .done state.output
  | .bad _ _ => .failed
  | _ => .running

/-- What a raw DEFLATE machine reports. -/
def rawStatus : RawMachine → Compression.Status
  | .done state => .done state.output
  | .bad _ _ => .failed
  | _ => .running

/-- The member machine of a zlib (`.zlib`) or gzip (`.gzip`) container. -/
def member (version : Stream.Version) (kind : MemberSemantics.Kind) : Incremental where
  Machine := MemberMachine
  Call := RawMachine.Call
  start := MemberMachine.start kind
  step := MemberMachine.applyCall version
  offered := RawMachine.Call.input
  status := memberStatus

/-- The raw DEFLATE machine. -/
def raw (version : Stream.Version) : Incremental where
  Machine := RawMachine
  Call := RawMachine.Call
  start := RawMachine.start
  step := RawMachine.applyCall version
  offered := RawMachine.Call.input
  status := rawStatus

/-- The member specification the machine is checked against: `Zlib.take` for
zlib and `Gzip.member` for gzip. -/
abbrev shared : MemberSemantics.Kind → Decoder := MemberMachine.shared

/-- **Open (frozen): member completeness.** Every zlib member is finished by the
zlib 1.3.1 member machine with a schedule that offers no further input. -/
def Task.member_complete : Prop := (member .v131 .zlib).Complete Zlib.decoder

/-- **Open (frozen): raw completeness.** The same for the raw DEFLATE machine. -/
def Task.raw_complete : Prop := (raw .v131).Complete Deflate.decoder

/-- `Zlib.sampleHello` offered as `78 | 9c cb 48 | cd c9 c9 07 00 06 | 2c 02 15 07`,
with one- or two-byte output capacity per call; the final `07` is a caller byte
after the member. -/
def helloChunked : List RawMachine.Call :=
  [⟨[0x9c, 0xcb, 0x48], 8, 1⟩, ⟨[0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x06], 8, 2⟩,
    ⟨[0x2c, 0x02, 0x15, 0x07], 64, 1⟩] ++ List.replicate 24 ⟨[], 64, 1⟩

end Silmaril.Formats.Compression.Inflate
