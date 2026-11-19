module

public import Silmaril.Cerberus.TV.Validate.Defs
import Silmaril.Proofs.Cerberus.TV.Validate

/-!
# Soundness of the whole-program refinement validator

Kernel-checked; the axioms are the standard three (`propext`, `Classical.choice`, `Quot.sound`).
How a verdict is *computed* is a separate matter: a theorem instance obtained with `decide`
evaluates the validator in the kernel, while an executable run of `validate` (as in `tools/`)
evaluates it with the compiled code and is evidence of that weaker kind.
-/

@[expose] public section

namespace Silmaril.Cerberus.TV

open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Spec

/-- The observations of a closed program are exactly those its endings admit. -/
theorem Closed.allows_iff (P : Closed) (impl : Impl) (x : Obs) :
    P.Allows impl x ↔ ∃ o out, P.Ends o out ∧ admits impl o out x :=
  Proofs.Cerberus.TV.Closed.allows_iff P impl x

/-- Coverage is sound: a covering ending admits every observation the covered one admits. -/
theorem covers_sound (impl : Impl) (s e : Outcome × String) (h : covers impl s e = true)
    (x : Obs) (hx : admits impl e.1 e.2 x) : admits impl s.1 s.2 x :=
  Proofs.Cerberus.TV.covers_sound impl s e h x hx

/-- A witness is an observation of its ending. -/
theorem witness_admits (impl : Impl) (e : Outcome × String) (x : Obs)
    (h : witness impl e = some x) : admits impl e.1 e.2 x :=
  Proofs.Cerberus.TV.witness_admits impl e x h

/-- **`validated` is sound**: the target refines the source. -/
theorem validate_sound (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .validated) : Refines impl src tgt :=
  Proofs.Cerberus.TV.validate_sound impl src tgt bounds h

/-- **`refuted` is sound**: the target does not refine the source. -/
theorem validate_refuted (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : (validate impl src tgt bounds).verdict = .refuted) : ¬ Refines impl src tgt :=
  Proofs.Cerberus.TV.validate_refuted impl src tgt bounds h

/-- An exhaustive exploration without undefined behaviour proves the program UB-free. -/
theorem Closed.ubFree_of_explore (P : Closed) (bounds : Bounds)
    (hl : (P.explore bounds).limited = false) (hu : (P.explore bounds).ub = false) : P.UBFree :=
  Proofs.Cerberus.TV.Closed.ubFree_of_explore P bounds hl hu

/-- **`validateUBFree` is sound**: refinement of a UB-free source. -/
theorem validateUBFree_sound (impl : Impl) (src tgt : Closed) (bounds : Bounds)
    (h : validateUBFree impl src tgt bounds = true) : RefinesUBFree impl src tgt :=
  Proofs.Cerberus.TV.validateUBFree_sound impl src tgt bounds h

/-- **The equivalence validator is sound.** -/
theorem validateEquivalent_sound (impl : Impl) (P Q : Closed) (bounds : Bounds)
    (h : validateEquivalent impl P Q bounds = true) : Equivalent impl P Q :=
  Proofs.Cerberus.TV.validateEquivalent_sound impl P Q bounds h

end Silmaril.Cerberus.TV
