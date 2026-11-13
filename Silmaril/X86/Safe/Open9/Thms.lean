module

public import Silmaril.X86.Safe.Thms
public import Silmaril.X86.Open9.Thms
/-!
# Safety on the open machine is safety on `Open9` (and so on `JumpTable`)

`safeN_open9`: step-indexed safety on `Open.isa` is safety on `Open9.isa`, by
`SafeN.lift` along `Open9.extendsOpen` (whose lens is the identity). The source stated this
through an `ExtendsOpen Open9.step` instance; the public `Safe` relates machines by
`SegVC.Isa.Extends` instead, so the instance is `Open9.extendsOpen` and every generic lemma of
`Safe.Thms` (`SafeN.lift`, `STriple.lift`, `Progress.lift`) applies along it.
-/

@[expose] public section

namespace Silmaril.X86.Safe

/-- Safety on the `Ext8` open machine is safety on the `Ext9` one. -/
theorem safeN_open9 {Q : Silmaril.X86.MState → Prop} {n : Nat} {m : Silmaril.X86.MState}
    (h : SafeN Silmaril.X86.Open.isa Q n m) : SafeN Silmaril.X86.Open9.isa Q n m :=
  SafeN.lift Silmaril.X86.Open9.extendsOpen h

end Silmaril.X86.Safe
