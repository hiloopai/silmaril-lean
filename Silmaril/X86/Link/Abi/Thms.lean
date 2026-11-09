module

public import Silmaril.X86.Link.Abi.Defs
public import Silmaril.X86.Linking.Thms
import Silmaril.Proofs.X86.Link.Abi

/-! # ABI-tagged static linking: theorems (header)

PROVED (`Silmaril.Proofs.X86.Link.Abi`, standard axioms): `checkAbi_sound`
(`checkAbi = true → AbiSound`), `linkAbi_sound` (a successful `linkAbi` gives
`AbiSound` and a tag in `policy.externals` for every absolute symbol),
`linkAbi_some`, `linkAbi_eq`, `linkAbi_rejects`, `linkAbi_rejects_untagged`.

Closed checks on the imported `Checks` ASTs (caller imports `f`, callee defines
`f`), linked by the x86-64 profile: matching `sysv64` tags link to the same
sections as the untagged `Checks.succeeds`; a `sysv64` import of an `ms64`
export is rejected; declaring a thunk admits it; a missing annotation is
rejected; an import bound to an untagged absolute symbol is rejected, and to
an absolute symbol with an incompatible external tag too.
-/

@[expose] public section

namespace Silmaril.X86.Link.Abi

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link
variable {Tag : Type} [DecidableEq Tag]

/-- **`checkAbi` is sound**: every cross-object binding the static linker can
make (an undefined global to a strong definition of the same name in any
object, or to an absolute symbol) is between tags the policy accepts. -/
theorem checkAbi_sound {policy : Policy Tag} {objects : List ObjectFile}
    {ifaces : List (Interface Tag)} (h : checkAbi policy objects ifaces = true) :
    AbiSound policy objects ifaces :=
  Proofs.X86.Link.Abi.checkAbi_sound h

theorem linkAbi_some {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : linkAbi accepts relocate policy objects ifaces layout absolute = some out) :
    checkAbi policy objects ifaces = true ∧ externalsTag policy absolute = true ∧
      link accepts relocate objects layout absolute = some out :=
  Proofs.X86.Link.Abi.linkAbi_some h

/-- **ABI soundness of a successful tagged link**: `AbiSound` holds, and every
absolute symbol the linker may bind has a tag in `policy.externals` (which
`AbiSound` checks against every import of that name). -/
theorem linkAbi_sound {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} {out : List LinkedSection}
    (h : linkAbi accepts relocate policy objects ifaces layout absolute = some out) :
    AbiSound policy objects ifaces ∧ ∀ entry ∈ absolute, ∃ tag, (entry.1, tag) ∈ policy.externals :=
  Proofs.X86.Link.Abi.linkAbi_sound h

/-- ABI-tagged links are exactly the imported links that pass the ABI checks. -/
theorem linkAbi_eq {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} (h : checkAbi policy objects ifaces = true)
    (he : externalsTag policy absolute = true) :
    linkAbi accepts relocate policy objects ifaces layout absolute =
      link accepts relocate objects layout absolute :=
  Proofs.X86.Link.Abi.linkAbi_eq h he

/-- A failed ABI check rejects the link whatever the layout. -/
theorem linkAbi_rejects {accepts : Header → Bool} {relocate : Relocator} {policy : Policy Tag}
    {objects : List ObjectFile} {ifaces : List (Interface Tag)} {layout : Layout}
    {absolute : AbsoluteSymbols} (h : checkAbi policy objects ifaces = false) :
    linkAbi accepts relocate policy objects ifaces layout absolute = none :=
  Proofs.X86.Link.Abi.linkAbi_rejects h

/-- An absolute symbol without an external tag rejects the link. -/
theorem linkAbi_rejects_untagged {accepts : Header → Bool} {relocate : Relocator}
    {policy : Policy Tag} {objects : List ObjectFile} {ifaces : List (Interface Tag)}
    {layout : Layout} {absolute : AbsoluteSymbols} (h : externalsTag policy absolute = false) :
    linkAbi accepts relocate policy objects ifaces layout absolute = none :=
  Proofs.X86.Link.Abi.linkAbi_rejects_untagged h

end Silmaril.X86.Link.Abi

namespace Silmaril.X86.Link.Abi

open Silmaril.Formats.ELF Silmaril.Formats.ELF.Link

open Silmaril.X86.Linking.Relocation (accepts relocate)

/-- `f` as a byte string. -/
def nameF : NameBytes := [102]

def callerIface (tag : Conv) : Interface Conv := { imports := [(nameF, tag)] }
def calleeIface (tag : Conv) : Interface Conv := { exports := [(nameF, tag)] }

theorem sysv64_links :
    linkAbi accepts relocate Policy.exact [Silmaril.X86.Linking.Checks.caller, Silmaril.X86.Linking.Checks.callee]
      [callerIface .sysv64, calleeIface .sysv64] Silmaril.X86.Linking.Checks.layout =
    some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩, ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by
  rfl

theorem cross_abi_rejected :
    linkAbi accepts relocate Policy.exact [Silmaril.X86.Linking.Checks.caller, Silmaril.X86.Linking.Checks.callee]
      [callerIface .sysv64, calleeIface .ms64] Silmaril.X86.Linking.Checks.layout = none :=
  linkAbi_rejects (by decide)

/-- A declared `sysv64 → ms64` thunk for `f` admits the cross-ABI binding. -/
def thunkPolicy : Policy Conv :=
  { compatible := fun a b => decide (a = b), thunks := [⟨nameF, .sysv64, .ms64⟩] }

theorem cross_abi_with_thunk :
    linkAbi accepts relocate thunkPolicy [Silmaril.X86.Linking.Checks.caller, Silmaril.X86.Linking.Checks.callee]
      [callerIface .sysv64, calleeIface .ms64] Silmaril.X86.Linking.Checks.layout =
    some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x20, 0, 0, 0]⟩, ⟨⟨1, 1⟩, 0x1020, 6, 1, #[0x90]⟩] := by
  rfl

/-- An untagged import is rejected even though the untagged link succeeds. -/
theorem missing_tag_rejected :
    linkAbi accepts relocate Policy.exact [Silmaril.X86.Linking.Checks.caller, Silmaril.X86.Linking.Checks.callee]
      [{}, calleeIface .sysv64] Silmaril.X86.Linking.Checks.layout = none :=
  linkAbi_rejects (by decide)

/-- An `ms64` import of `f` resolved to an absolute symbol with no external tag
is rejected (the untagged link itself succeeds). -/
theorem untagged_absolute_rejected :
    linkAbi accepts relocate Policy.exact [Silmaril.X86.Linking.Checks.caller]
      [callerIface .ms64] [⟨⟨0, 1⟩, 0x1000⟩] [(nameF, 0x2000)] = none :=
  linkAbi_rejects_untagged (by decide)

theorem untagged_absolute_links :
    Silmaril.X86.Linking.Relocation.link [Silmaril.X86.Linking.Checks.caller]
      [⟨⟨0, 1⟩, 0x1000⟩] [(nameF, 0x2000)] =
    some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x00, 0x10, 0, 0]⟩] := by
  rfl

/-- Tagging the absolute symbol `sysv64` rejects the `ms64` import of it ... -/
theorem absolute_cross_abi_rejected :
    linkAbi accepts relocate { (Policy.exact : Policy Conv) with externals := [(nameF, .sysv64)] }
      [Silmaril.X86.Linking.Checks.caller] [callerIface .ms64] [⟨⟨0, 1⟩, 0x1000⟩]
      [(nameF, 0x2000)] = none :=
  linkAbi_rejects (by decide)

/-- ... and admits a `sysv64` import of it. -/
theorem absolute_sysv64_links :
    linkAbi accepts relocate { (Policy.exact : Policy Conv) with externals := [(nameF, .sysv64)] }
      [Silmaril.X86.Linking.Checks.caller] [callerIface .sysv64] [⟨⟨0, 1⟩, 0x1000⟩]
      [(nameF, 0x2000)] = some [⟨⟨0, 1⟩, 0x1000, 6, 4, #[0x00, 0x10, 0, 0]⟩] := by
  rfl

end Silmaril.X86.Link.Abi
