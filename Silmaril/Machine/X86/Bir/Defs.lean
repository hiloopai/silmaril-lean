module

public import Silmaril.Raw.Machine.X86.Lift.BirListing

/-!
# Bir: the x86 basic-block IR (pinned interface)

Pinned interface for the imported `Silmaril.X86.Lift.Bir*` chain (copied unchanged from
`an earlier development`). Declarations keep the
`Silmaril.X86.Lift.Bir` namespace. The Raw modules form one linear import chain, so this
header exposes all of it; the stable names are:

* machine side: `XState`, `XResult`, `LInstr` (`ext`/`x`/`sse`), `execBlock`
  (run a straight-line listing on `Ext.exec` plus the `XInstr`/`SInstr` extensions);
* IR side: `E`, `F`, `Stmt`, `Block`, `runStmts`, `Block.run`;
* lifting: `symExec` (symbolic execution) and `liftBlock` (`symExec` then the
  verified simplifier `Block.simp`);
* listings: `LInstr.decodeOk`, `listingOk`, `extCount`.

Trust: `LInstr.ext` instructions are checked against `Ext.decode` by `listingOk`;
`LInstr.x`/`LInstr.sse` are only length-checked and their semantics
(`XInstr.exec`, `SInstr.exec`) are hand-written, so new work on main should
restrict to `Ext` forms or count `extCount` in its trust summary.
-/
