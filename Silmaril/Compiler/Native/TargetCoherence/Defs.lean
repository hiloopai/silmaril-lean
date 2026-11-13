module

public import Silmaril.Cerberus.Target.Defs
public import Silmaril.Cerberus.Elaboration.Constants.Defs
public import Silmaril.Cerberus.Elaboration.Arithmetic.Defs
public import Silmaril.Compiler.Native.Types.Defs
public import Silmaril.Compiler.Native.Layout.Defs
public import Silmaril.Compiler.Native.Abi.Defs

/-! A deliberately partial Linux AMD64 LP64 primitive target profile, and exact
function-level coherence with the actual native layout/type adapters. This does
not replace pinnedApple or claim Cerberus operational/ISO C/FFI adequacy. -/
@[expose] public section
namespace Silmaril.Compiler.Native.TargetCoherence
open Silmaril.Cerberus
open Silmaril.Cerberus.Target
open Silmaril.Machine.SystemV.Abi

/-- Exact-width ordinary aliases plus the native 128-bit extension. -/
def exactWidthAlias : Nat → Option IntegerBaseType
  | 128 => some (.intN 128)
  | width => pinnedWidthAlias width

def baseLayout : IntegerBaseType → Option Silmaril.Cerberus.Target.Layout
  | .intN 128 => some ⟨16, 16⟩
  | base => pinnedBaseLayout base

/-- Primitive layout profile, rather than a complete selected Linux Cerberus
implementation. Least/fast typedef aliases remain explicitly unresolved.
The upstream signedness helper still fixes raw wint as signed independently of
this record's unsigned alias; the theorems expose that limit. -/
def linuxLP64 : Config where
  name := "linux-amd64-lp64-primitive-layout"
  binaryMode := .twosComplement
  plainCharSigned := true
  charLayout := ⟨1, 1⟩
  boolLayout := ⟨1, 1⟩
  baseLayout := baseLayout
  floatLayout := fun
    | .realFloating .float => some ⟨4, 4⟩
    | .realFloating .double => some ⟨8, 8⟩
    | .realFloating .longDouble => some ⟨16, 16⟩
  pointerLayout := some ⟨8, 8⟩
  maximumAlignment := 16
  aliases := {
    intN := exactWidthAlias, intLeastN := fun _ => none, intFastN := fun _ => none
    intmax := .long, intptr := .long
    wchar := .signed .int, wint := .unsigned .int
    size := .unsigned .long, ptrdiff := .signed .long }

structure Ordinary where
  type : IntegerType
  bytes : Nat
  signed : Bool
  deriving DecidableEq, Repr

/-- Supported names retain their exact type identity. In particular no raw
least/fast alias, enum, extended128 or wint case is silently normalized here. -/
def ordinary : List Ordinary := [
  ⟨.char, 1, true⟩,
  ⟨.bool, 1, false⟩,
  ⟨(.signed .ichar), 1, true⟩,
  ⟨(.unsigned .ichar), 1, false⟩,
  ⟨(.signed .short), 2, true⟩,
  ⟨(.unsigned .short), 2, false⟩,
  ⟨(.signed .int), 4, true⟩,
  ⟨(.unsigned .int), 4, false⟩,
  ⟨(.signed .long), 8, true⟩,
  ⟨(.unsigned .long), 8, false⟩,
  ⟨(.signed .longLong), 8, true⟩,
  ⟨(.unsigned .longLong), 8, false⟩,
  ⟨(.signed (.intN 8)), 1, true⟩,
  ⟨(.unsigned (.intN 8)), 1, false⟩,
  ⟨(.signed (.intN 16)), 2, true⟩,
  ⟨(.unsigned (.intN 16)), 2, false⟩,
  ⟨(.signed (.intN 32)), 4, true⟩,
  ⟨(.unsigned (.intN 32)), 4, false⟩,
  ⟨(.signed (.intN 64)), 8, true⟩,
  ⟨(.unsigned (.intN 64)), 8, false⟩,
  ⟨(.signed .intmax), 8, true⟩,
  ⟨(.unsigned .intmax), 8, false⟩,
  ⟨(.signed .intptr), 8, true⟩,
  ⟨(.unsigned .intptr), 8, false⟩,
  ⟨.wchar, 4, true⟩,
  ⟨.size, 8, false⟩,
  ⟨.ptrdiff, 8, true⟩,
  ⟨.ptraddr, 8, false⟩]

def integerCtype (type : IntegerType) : Ctype := .mk [] (.basic (.integer type))

/-- Storage layout and scalar code view, independent of source evaluation.
For Bool the signed flag is false and storage is one byte; its semantic values
remain 0/1, separately from the upstream generic range helper. -/
def Agrees (entry : Ordinary) : Prop :=
  integerLayout linuxLP64 emptyEnvironment entry.type = .ok ⟨entry.bytes, entry.bytes⟩ ∧
  signedness linuxLP64 emptyEnvironment entry.type = .ok entry.signed ∧
  Types.ordinaryIntegerLayout entry.type = .ok (entry.bytes, entry.signed) ∧
  Layout.sizeAlign ∅ (integerCtype entry.type) = .ok (entry.bytes, entry.bytes) ∧
  Abi.objectOfCodeType ∅ (Types.ofCtype (integerCtype entry.type)) =
    .ok (.integer entry.bytes entry.bytes)


/-- Equality only for the generic range helper; this does not identify it with
the complete Cerberus integer value semantics. Bool is excluded explicitly. -/
def HelperBoundsAgree (entry : Ordinary) : Prop :=
  ((integerRange linuxLP64 emptyEnvironment entry.type).mapError reprStr).map (fun r => (r.lower, r.upper)) =
      Types.integerBounds entry.type


/-- Concrete max/min translation is a different source API: Bool and wchar
have genuine upstream special cases and are excluded from this equality. -/
def ConstantBoundsAgree (entry : Ordinary) : Prop :=
  Silmaril.Cerberus.Elaboration.Constants.concreteMaximum linuxLP64 emptyEnvironment entry.type =
      Types.integerConstantValue (.max entry.type) ∧
    Silmaril.Cerberus.Elaboration.Constants.concreteMinimum linuxLP64 emptyEnvironment entry.type =
      Types.integerConstantValue (.min entry.type)


end Silmaril.Compiler.Native.TargetCoherence
