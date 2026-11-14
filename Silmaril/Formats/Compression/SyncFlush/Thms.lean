module

public import Silmaril.Formats.Compression.SyncFlush.Defs

/-!
# Raw DEFLATE with sync-flush boundaries: facts

PROVED (standard axioms):

* `inflateMessages_nil`, `keepWindow_length`: the window kept between messages is at most
  `2^windowBits` bytes, so memory carried by context takeover is bounded by the negotiated
  window (RFC 7692 §7.1.2).

CHECKED (`decide +kernel`): every example of RFC 7692 §7.2.3:
§7.2.3.1 (one compressed block), §7.2.3.2 (the second message reuses the first one's window,
and fails without it), §7.2.3.3 (a stored block), §7.2.3.4 (a `BFINAL` block followed by an
empty header octet), §7.2.3.5 (two blocks around an empty stored block), §7.2.3.6 (an empty
message), and the rejection of a back-reference when context takeover is off.

Not proved yet: a round trip against a sync-flushing encoder, and agreement with
`Deflate.decoder` on `BFINAL`-terminated streams (both are planned in
`docs/projects/content-coding.md`).
-/

@[expose] public section

namespace Silmaril.Formats.Compression.SyncFlush

theorem keepWindow_length (w : Nat) (bytes : List UInt8) :
    (keepWindow w bytes).length ≤ 2 ^ w := by
  simp only [keepWindow, List.length_drop]; generalize 2 ^ w = n; omega

theorem inflateMessages_nil (w : Nat) (b : Bool) (h : List UInt8) :
    inflateMessages w b h [] = .ok [] := rfl

/-- `"Hello"`. -/
def hello : List UInt8 := [0x48, 0x65, 0x6c, 0x6c, 0x6f]

/-- §7.2.3.1: one compressed DEFLATE block. -/
theorem rfc7692_one_block :
    (inflateMessage 15 [] [0xf2, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00]).toOption = some (hello, hello) := by
  decide +kernel

/-- §7.2.3.2: the second "Hello" is a back-reference into the first message's window. -/
theorem rfc7692_shared_window :
    (inflateMessages 15 false [] [[0xf2, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00],
      [0xf2, 0x00, 0x11, 0x00, 0x00]]).toOption = some [hello, hello] := by decide +kernel

/-- Without context takeover the second message's back-reference has nothing to point at. -/
theorem rfc7692_no_takeover_rejects :
    (inflateMessages 15 true [] [[0xf2, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00],
      [0xf2, 0x00, 0x11, 0x00, 0x00]]).toOption = none := by decide +kernel

/-- §7.2.3.3: a DEFLATE block with no compression. -/
theorem rfc7692_stored :
    (inflateMessage 15 [] [0x00, 0x05, 0x00, 0xfa, 0xff, 0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x00]).toOption =
      some (hello, hello) := by decide +kernel

/-- §7.2.3.4: a `BFINAL` block; the bytes after it are ignored. -/
theorem rfc7692_bfinal :
    (inflateFlushed [] ([0xf3, 0x48, 0xcd, 0xc9, 0xc9, 0x07, 0x00, 0x00] ++ syncTail)).toOption =
      some (hello, true) := by decide +kernel

/-- §7.2.3.5: two DEFLATE blocks around an empty stored block. -/
theorem rfc7692_two_blocks :
    (inflateMessage 15 [] [0xf2, 0x48, 0x05, 0x00, 0x00, 0x00, 0xff, 0xff, 0xca, 0xc9, 0xc9,
      0x07, 0x00]).toOption = some (hello, hello) := by decide +kernel

/-- §7.2.3.6: an empty fragment. -/
theorem rfc7692_empty : (inflateMessage 15 [] [0x00]).toOption = some ([], []) := by decide +kernel

end Silmaril.Formats.Compression.SyncFlush
