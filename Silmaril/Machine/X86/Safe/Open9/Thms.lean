module

public import Silmaril.Machine.X86.Safe.Thms
public import Silmaril.Machine.X86.Open9.Thms

/-!
# `Open9` (and so `JumpTable`) extends the open machine

PROVED (standard axioms): `instExtendsOpenOpen9 : ExtendsOpen Open9.step`, from
`Open9.step_of_open`. `JumpTable.step` is `Open9.step`, so this
instance also serves the jump machine. With it, every generic lemma of `Safe.Thms` and every
generic consumer (the `FnSpec` logic `logicOn`, `validated_compose`, the call rule) applies to
the open machine over `Ext9`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Safe

/-- **The open machine over `Ext9` extends the open machine.** -/
instance instExtendsOpenOpen9 : ExtendsOpen Silmaril.Machine.X86.Open9.step :=
  ⟨fun h => Silmaril.Machine.X86.Open9.step_of_open h⟩

/-- Safety on the `Ext8` open machine is safety on the `Ext9` one. -/
theorem safeN_open9 {Q : Silmaril.X86.MState → Prop} {n : Nat} {m : Silmaril.X86.MState}
    (h : SafeN Silmaril.Machine.X86.Open.step Q n m) : SafeN Silmaril.Machine.X86.Open9.step Q n m :=
  safeN_of_refines ExtendsOpen.ext h

end Silmaril.Machine.X86.Safe
