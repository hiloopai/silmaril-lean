module

public import Silmaril.Project.Shapes.CTV.Defs
public import Silmaril.Cerberus.TV.Validate.Thms

/-!
# Standard problem shapes: whole-program C translation validation (theorems)

* `CRefines.of_validate`, `CRefinesUBFree.of_validate`, `CNotRefines.of_validate`,
  `CEquivalent.of_validate`: a verdict of the
  validator (`Silmaril.Cerberus.TV.Validate`) gives a row of the corresponding shape. Computing the
  verdict in the kernel (`by cbv` or `by decide`) makes the row a kernel fact.
* The coherence table of the profiles of `Defs`: `linuxX86_64` agrees with the Core semantics at
  every integer type of the table except `wchar_t`, at pointers and at `double`; it disagrees at
  `wchar_t` (the port's `Mem.Concrete.integerBounds` gives `wchar_t` an unsigned range while its
  layout and the psABI make it a signed 32-bit integer), at `float` and at `long double` (the
  port's 8-byte binary64 floating values). `legacyPinnedApple` disagrees at the floating types for
  the elaborator configuration as well.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.CTV

open Silmaril.Cerberus
open Silmaril.Cerberus.TV

theorem CRefines.of_validate {impl : Spec.Impl} {src tgt : Closed} (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .validated) : CRefines impl src tgt :=
  validate_sound impl src tgt bounds h

theorem CRefinesUBFree.of_validate {impl : Spec.Impl} {src tgt : Closed} (bounds : Bounds)
    (h : validateUBFree impl src tgt bounds = true) : CRefinesUBFree impl src tgt :=
  validateUBFree_sound impl src tgt bounds h

theorem CNotRefines.of_validate {impl : Spec.Impl} {src tgt : Closed} (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .refuted) : CNotRefines impl src tgt :=
  validate_refuted impl src tgt bounds h

theorem CEquivalent.of_validate {impl : Spec.Impl} {P Q : Closed} (bounds : Bounds)
    (h : validateEquivalent impl P Q bounds = true) : CEquivalent impl P Q :=
  validateEquivalent_sound impl P Q bounds h

theorem not_coherentAt_of {p : Profile} {s : Scalar} (h : (p.issues s).isEmpty = false) :
    ¬ ProfileCoherentAt p s := by
  intro hc
  unfold ProfileCoherentAt Profile.CoherentAt at hc
  rw [hc] at h
  cases h

/-- The scalar types at which `linuxX86_64` is coherent with the Core semantics. -/
theorem linuxX86_64_coherentScalars :
    linuxX86_64.coherentScalars = [.bool, .char, .schar, .uchar, .short, .ushort, .int, .uint,
      .long, .ulong, .longLong, .ulongLong, .size, .ptrdiff, .intptr, .uintptr, .pointer,
      .double] := by
  cbv

theorem linuxX86_64_coherent_int : ProfileCoherentAt linuxX86_64 .int := by
  unfold ProfileCoherentAt Profile.CoherentAt; cbv

theorem linuxX86_64_coherent_double : ProfileCoherentAt linuxX86_64 .double := by
  unfold ProfileCoherentAt Profile.CoherentAt; cbv

theorem linuxX86_64_incoherent_float : ¬ ProfileCoherentAt linuxX86_64 .float := by
  exact not_coherentAt_of (by cbv)

theorem linuxX86_64_incoherent_longDouble : ¬ ProfileCoherentAt linuxX86_64 .longDouble := by
  exact not_coherentAt_of (by cbv)

theorem linuxX86_64_incoherent_wchar : ¬ ProfileCoherentAt linuxX86_64 .wchar := by
  exact not_coherentAt_of (by cbv)

theorem legacyPinnedApple_incoherent_float : ¬ ProfileCoherentAt legacyPinnedApple .float := by
  exact not_coherentAt_of (by cbv)

end Silmaril.Project.Shapes.CTV
