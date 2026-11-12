module

public import Silmaril.Raw.X86.Str9FsX

/-!
# `Str9FsX`: both conservative extensions, the listing laws, the machine

* `step_of_str9fs`: every `Str9Fs` step of `x.m` is a step that keeps the XMM file, so
  `extendsStr9Fs : Str9Fs.isa.Extends isa` (along the lens `x ↦ x.m`) and, by composition,
  `extendsStr9`, `extendsOpen9`, `extendsOpen`.
* `step_of_sse9`: **every `Sse9` step is a step**, so `extendsSse9 : Sse9.isa.Extends isa`
  (the same states). It rests on `sse_not_lower`: bytes `Sse9` reads as an SSE form are
  never a string form (`decodeStr_none_of_pSse`), an atomic form (`atomic_bad_of_pSse`) or an
  FS form (`fs_bad_of_pSse`).
* Listing laws: `step_of_listed` (`isa`: `Str9Fs`'s instructions and `rep stosd`), and
  `step_of_listed_sse` for the SSE forms (as in `Sse9`).
-/

/-! The proofs are in `Silmaril.Raw.X86.Str9FsX` (valid, not yet in Isar style), re-exported here. -/
