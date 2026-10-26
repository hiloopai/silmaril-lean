module

public import Silmaril.Process.LPS.Problems.GnuSha256sum.Startup
public import Silmaril.Apps.Sha256sum.Binary.Startup.Cmain

/-! # `cmain`'s segment as a `GStep` segment: `OptParseCut` to `DigestEntryCutW`

`DigestEntryCutW` is `DigestEntryCut` strengthened with `cmain`'s frame at the call
(`Startup.AtDigestEntryW`); `DigestEntryCutW.toCut` forgets the strengthening.

Status: everything in this file is VERIFIED (no `sorry`, no new axiom; the segment rests on
`Startup.Cmain.cmain_runs`, VERIFIED).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.GnuSha256sum

open Silmaril.Apps.Sha256sum.Binary.Startup (AtDigestEntryW)

/-- **`digest_file`'s entry from the stdin-path call, with `cmain`'s frame.** -/
def DigestEntryCutW : Cut := StartCut AtDigestEntryW

theorem DigestEntryCutW.toCut {w : Silmaril.Apps.Sha256sum.World} {message : List Byte} {g : GS}
    {h : List Ev} (hc : DigestEntryCutW w message g h) : DigestEntryCut w message g h := by
  obtain ⟨hh, hk, hex, c, hf, hp⟩ := hc
  exact ⟨hh, hk, hex, c, hf, hp.toEntry⟩

/-- `Leads` to the strengthened cut gives `Leads` to the plain one. -/
theorem Seg.toDigestEntryCut {domain : List Byte → Prop} {A : Cut}
    (h : Seg domain A DigestEntryCutW) : Seg domain A DigestEntryCut :=
  fun prog posix fs message g hist member start =>
    (h prog posix fs message g hist member start).trans fun _ _ p => .done (DigestEntryCutW.toCut p)

/-- **VERIFIED. `cmain` from `AtOptParse` to `digest_file`'s entry** (argv = [prog], any
environment, no system call). -/
theorem optParse_digestEntryW (domain : List Byte → Prop) :
    Seg domain OptParseCut DigestEntryCutW := by
  intro prog posix fs message g h _ start
  obtain ⟨hh, hk, hex, c, hc, hs⟩ := start
  obtain ⟨t, hr, ht⟩ := Silmaril.Apps.Sha256sum.Binary.Startup.Cmain.cmain_runs hc hs
  subst hh
  refine leads_of_reaches (t := t) hr hex ⟨hex, fun e he => by simp at he, by simp [stdinRead],
    by simp [out], Or.inl (by simp [out]), hs.faulted⟩ ⟨rfl, hk, hex, c, hc, ht⟩

/-- **The plain form.** -/
theorem optParse_digestEntry (domain : List Byte → Prop) :
    Seg domain OptParseCut DigestEntryCut :=
  Seg.toDigestEntryCut (optParse_digestEntryW domain)

end Silmaril.Process.LPS.Problems.GnuSha256sum
