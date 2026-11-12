module

public import Silmaril.Raw.X86.Str9Fs

/-!
# `Str9Fs`: conservative extension of `Str9`, the listing law, the machine

* `step_of_str9`: **every `Str9` step is a step** (the new forms are tried only where
  `Ext8`, `Ext9` and the string forms all reject the fetch window), hence `extendsStr9 :
  Str9.isa.Extends isa` (identity lens), and `extendsOpen9`, `extendsOpen` by composition. So
  every generic transfer along `Isa.Extends` applies (`FnContract.lift`, `Spec.Strict.lift`,
  `Sep.Triple.lift`, ...): **every `Str9`/`Open9`/`Open` proof lifts unchanged.**
* `good_pNewAtomic` (`Atomic9.pNew`, which silmaril defines without its decoder laws) and
  `good_pFs`: the parsers have the prefix laws, so `decodeNew_append`: a decoded new form keeps
  its reading whatever bytes follow.
* `step_of_fetch_new`, `step_of_listed_new`, `step_of_listed`: the listing law; `isa`: the
  machine as a `SegVC.Isa MState`.
* Vectors: `decode_errno_store`, `decode_lock_cmpxchg`, `decode_canary` (the base-less canary
  stays `Str9`'s), `decode_fs_rip_none`, and `exec_errno_store` (the `errno` write lands at
  `fsBase + rdx`).

Proved with the standard axioms only. What is **not** claimed: that the handwritten FS and
atomic semantics match hardware (`Atomic9`'s were differentially tested by silmaril; the FS
forms reuse `Ext9`'s semantics at a shifted base and are not tested).
-/

/-! The proofs are in `Silmaril.Raw.X86.Str9Fs` (valid, not yet in Isar style), re-exported here. -/
