module

public import Silmaril.Formats.Compression.Deflate.Defs

/-!
# Raw DEFLATE with sync-flush boundaries (RFC 1951 §3.2.4, RFC 7692 §7.2)

`Deflate.decoder` reads a raw DEFLATE stream up to and including its `BFINAL` block. A
*sync flush* (zlib's `Z_SYNC_FLUSH`) instead ends a run of blocks with an empty, non-final
stored block (`00 00 ff ff` once the 3 header bits and the padding are written), so that
everything sent so far can be decoded while the stream continues. The WebSocket extension
permessage-deflate (RFC 7692) uses this: each message is a run of blocks whose trailing
`00 00 ff ff` is removed by the sender, and the receiver "Append[s] 4 octets of 0x00 0x00
0xff 0xff to the tail end of the payload of the message" and decompresses (§7.2.2).

* `decompressBlocksFlush fuel r out`: decode blocks onto `out` until a `BFINAL` block (the
  rest of the input is ignored, as RFC 7692 §7.2.3.4 relies on) or until the input is used up
  right after a block (only padding bits left, `bitsLeft < 8`). It reports whether `BFINAL`
  was seen. It reuses the block decoder of `Deflate` (`decompressBlockBody`) unchanged.
* `inflateFlushed history bytes`: decode with an installed LZ77 window `history`; the
  returned data excludes the history (as `Deflate.deflateTakeWithHistory`).
* `inflateMessage window history payload`: RFC 7692 §7.2.2 for one message: append
  `00 00 ff ff`, decode with the sliding window, and return the message and the next window
  (the last `2^windowBits` bytes of history and message: context takeover, §7.1.1). Without
  context takeover the caller passes `[]` as history. Back-references beyond the window fail,
  because the block decoder rejects distances larger than its output so far.

This is the decoding side only, and a specification (list-based, fuel-bounded). The
WebSocket framing and extension negotiation belong to `Silmaril.Net.WebSocket` (TLS and
WebSockets track); this module is the interface they can call.
-/

@[expose] public section

namespace Silmaril.Formats.Compression.SyncFlush

open Silmaril.Formats.Compression.Deflate

/-- Decode blocks until `BFINAL` (`true`) or the end of the input at a block boundary
(`false`). Every block consumes its three header bits, which bounds `fuel`. -/
def decompressBlocksFlush : Nat → LSBReader → List UInt8 →
    Except DecompressError (List UInt8 × Bool)
  | 0, _, _ => .error .decodeOverrun
  | fuel + 1, r, out =>
    match r.readBit with
    | none => .error .decodeOverrun
    | some (bfinal, r1) =>
      match r1.readBits 2 with
      | none => .error .decodeOverrun
      | some (btype, r2) =>
        match decompressBlockBody btype r2 out with
        | .error e => .error e
        | .ok (out', r3) =>
          if bfinal then .ok (out', true)
          else if r3.bitsLeft < 8 then .ok (out', false)
          else decompressBlocksFlush fuel r3 out'

/-- Decode a sync-flushed run of blocks with an installed history; the history is not part
of the result. -/
def inflateFlushed (history bytes : List UInt8) : Except DecompressError (List UInt8 × Bool) :=
  let r : LSBReader := ⟨0, 0, bytes, 0⟩
  (decompressBlocksFlush (r.bitsLeft + 1) r history).map fun (out, fin) =>
    (out.drop history.length, fin)

/-- The four octets a sync flush ends with, which permessage-deflate senders strip. -/
def syncTail : List UInt8 := [0x00, 0x00, 0xff, 0xff]

/-- The LZ77 window kept between messages: the last `2^windowBits` bytes. RFC 7692 allows
`windowBits` from 8 to 15 (`server_max_window_bits`, `client_max_window_bits`, §7.1.2);
the default is 15 (32 768 bytes). -/
def keepWindow (windowBits : Nat) (bytes : List UInt8) : List UInt8 :=
  bytes.drop (bytes.length - 2 ^ windowBits)

/-- Decompress one permessage-deflate message (RFC 7692 §7.2.2) with the window `history`;
returns the message and the window for the next message (context takeover). -/
def inflateMessage (windowBits : Nat) (history payload : List UInt8) :
    Except DecompressError (List UInt8 × List UInt8) :=
  (inflateFlushed history (payload ++ syncTail)).map fun (msg, _) =>
    (msg, keepWindow windowBits (history ++ msg))

/-- Decompress a sequence of messages, carrying the window (context takeover) or resetting it
(`noContextTakeover`, §7.1.1). -/
def inflateMessages (windowBits : Nat) (noContextTakeover : Bool) :
    List UInt8 → List (List UInt8) → Except DecompressError (List (List UInt8))
  | _, [] => .ok []
  | history, p :: ps =>
    match inflateMessage windowBits history p with
    | .error e => .error e
    | .ok (msg, window) =>
      match inflateMessages windowBits noContextTakeover (if noContextTakeover then [] else window) ps with
      | .error e => .error e
      | .ok msgs => .ok (msg :: msgs)

end Silmaril.Formats.Compression.SyncFlush
