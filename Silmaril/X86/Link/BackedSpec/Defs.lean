module

public import Silmaril.X86.Link.FnSpec.Defs

/-! # A backed-stack variant of the System V `FnSpec` template

The System V template `FnSpec.SysVPre`/`SysVPost` (`Silmaril.X86.Sep.SysV`) has two gaps
when a function
passes pointers into its own stack frame to a callee:

1. The stack budget is `blockAny (sp - stack) stack`: readable, writable addresses whose
   bytes may be **unbacked**. Callee specs such as `fillSpec`/`copySpec` ask for `bytesPt`
   (backed) buffers, so no stack-buffer-passing caller can meet them from `blockAny`.
2. `copySpec` returns its source as `bytesPtRO` (read-only), so a caller that hands a stack
   buffer to `memcpy` as the source cannot give its budget back as `blockAny` (read-write).

This module adds, **without changing** `FnSpec`, `SysVPre`, `SysVPost` or `Safe` (so every
existing proof and spec is untouched), a second template and safety predicate:

* `blockB a n`: `n` **backed**, readable and writable bytes from `a`, contents unknown
  (`∃ zs, |zs| = n ∧ bytesPt a zs`).
* `blockRd a n`: `n` **readable** byte addresses from `a`, contents unknown and possibly
  unbacked. `blockAny`, `bytesPt` and `bytesPtRO` all weaken to it.
* `FnSpec.SysVPreB`: `SysVPre` with the budget as `blockB` (the caller guarantees a backed
  stack, as Linux's initial stack is: zero-filled pages).
* `FnSpec.SysVPostB`: `SysVPost` with the budget and return slot given back as `blockRd`.
* `SafeB n a S ctx`: `Safe` with this template.

The backed template has a stronger precondition and a weaker postcondition than the plain
one, so `Safe n a S ctx` should give `SafeB n a S ctx`; that lemma and a call rule for
`SafeB` callees are not part of this module.

**Limitation (stated).** The postcondition gives the budget back read-only (`blockRd`). A
caller that calls a backed-stack callee *twice* with the same stack area cannot re-establish
`blockB` for the second call from the template alone. A sharper post (budget back with
`RW` permission, which holds because nothing in the open machine changes mappings) needs the
caller to frame the `regions` location; that refinement is a next step.
-/

@[expose] public section

namespace Silmaril.X86.Link.BackedSpec

open Silmaril.X86 (MState Word Byte)
open Silmaril.Process (addressLimit)
open Silmaril.X86.Sep
open Silmaril.X86.Link.FnSpec

/-- `n` backed, readable and writable bytes from `a`, contents unknown. -/
def blockB (a n : Nat) : SProp :=
  sexists fun zs : List Byte => ⌜zs.length = n⌝ ∗ bytesPt a zs

/-- A readable byte address (below `2 ^ 64`), contents unknown and possibly unbacked. -/
def byteRd (a : Nat) : SProp := fun h =>
  a < addressLimit ∧ ∃ c : Cell, RO c.perms ∧ h = Frag.single (.mem a) (.cell c)

/-- `n` readable byte addresses from `a`, contents unknown. -/
def blockRd : Nat → Nat → SProp
  | _, 0 => emp
  | a, n + 1 => byteRd a ∗ blockRd (a + 1) n

namespace FnSpecB

/-- **The backed-stack precondition template**: `SysVPre` with a backed budget. -/
def SysVPreB (S : FnSpec) (x : S.Arg) (entry sp ret : Word) : SProp :=
  ripPt entry ∗ regPt .rsp sp ∗ SysVRegs (S.args x) ∗ flagsAny ∗ wordPt sp.toNat ret ∗
    blockB (sp.toNat - S.stack) S.stack ∗ S.pre x

/-- **The backed-stack postcondition template**: `SysVPost` with the budget and the return
slot given back readable. -/
def SysVPostB (S : FnSpec) (x : S.Arg) (sp ret : Word) : SProp :=
  sexists fun v => ripPt ret ∗ regPt .rsp (sp + 8#64) ∗ SysVRet v ∗ flagsAny ∗
    blockRd (sp.toNat - S.stack) (S.stack + 8) ∗ S.post x v

end FnSpecB

/-- **Safety with the backed-stack template** (cf. `Silmaril.X86.Link.FnSpec.Safe`). -/
def SafeB (n a : Nat) (S : FnSpec) (ctx : Silmaril.X86.Link.Contract.Image) : Prop :=
  ∀ (D : Nat → Prop) (bs : Nat → Byte), Silmaril.X86.Link.FnSpec.Covers ctx D bs →
    ∀ (x : S.Arg) (sp ret : Word), FnSpec.EntryAligned sp → S.stack ≤ sp.toNat →
      STriple n (Code D bs ∗ FnSpecB.SysVPreB S x (BitVec.ofNat 64 a) sp ret)
        (Code D bs ∗ FnSpecB.SysVPostB S x sp ret)

/-! ## Total variants

`Safe` is step-indexed and therefore partial: it cannot express that a function returns.
For acyclic call graphs (no recursion through imports) the total triple `Triple` of `Silmaril.X86.Sep`
composes directly. `SafeT`/`SafeTB` are `Safe`/`SafeB` with `Triple` in place of
`STriple n`: from every state splitting as the precondition and a frame, the open machine
**reaches** a state splitting as the postcondition and the same frame. -/

/-- **Total safety** with the System V template. -/
def SafeT (a : Nat) (S : FnSpec) (ctx : Silmaril.X86.Link.Contract.Image) : Prop :=
  ∀ (D : Nat → Prop) (bs : Nat → Byte), Silmaril.X86.Link.FnSpec.Covers ctx D bs →
    ∀ (x : S.Arg) (sp ret : Word), FnSpec.EntryAligned sp → S.stack ≤ sp.toNat →
      Triple Silmaril.X86.Open.isa (Code D bs ∗ S.SysVPre x (BitVec.ofNat 64 a) sp ret) (Code D bs ∗ S.SysVPost x sp ret)

/-- **Total safety** with the backed-stack template. -/
def SafeTB (a : Nat) (S : FnSpec) (ctx : Silmaril.X86.Link.Contract.Image) : Prop :=
  ∀ (D : Nat → Prop) (bs : Nat → Byte), Silmaril.X86.Link.FnSpec.Covers ctx D bs →
    ∀ (x : S.Arg) (sp ret : Word), FnSpec.EntryAligned sp → S.stack ≤ sp.toNat →
      Triple Silmaril.X86.Open.isa (Code D bs ∗ FnSpecB.SysVPreB S x (BitVec.ofNat 64 a) sp ret)
        (Code D bs ∗ FnSpecB.SysVPostB S x sp ret)

end Silmaril.X86.Link.BackedSpec
