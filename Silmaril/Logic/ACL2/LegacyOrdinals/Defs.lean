module

public import Silmaril.Logic.ACL2.OrdinalAdmission.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.LegacyOrdinals

open Ordinals Recursive

/-- Three-way comparison for ACL2 E0-ORD-< on E0-ORDINALP encodings. Each cons
has an exponent in its car and contributes one copy of that power of omega. -/
def cmp : Encoding → Encoding → Ordering
  | .natural m, .natural n => compare m n
  | .natural _, .cons .. => .lt
  | .cons .., .natural _ => .gt
  | .cons e r, .cons f s => (cmp e f).then (cmp r s)
  | _, _ => .eq

def lt (x y : Encoding) : Prop := cmp x y = .lt

instance (x y : Encoding) : Decidable (lt x y) :=
  inferInstanceAs (Decidable (cmp x y = .lt))

/-- ACL2 E0-ORDINALP allows repeated exponents, with consecutive exponents
nonincreasing. The last cdr is a natural, including zero. -/
def valid : Encoding → Bool
  | .natural _ => true
  | .otherAtom => false
  | .cons e r =>
    valid e && (e != .natural 0) && valid r &&
      match r with
      | .cons f _ => cmp e f != .lt
      | _ => true

/-- ACL2 ATOC adds one omega power at every cons. Mathlib addition combines
repeated exponents so that the resulting notation has canonical coefficients.
The conversion theorems apply when E0-ORDINALP holds. -/
def toNote : Encoding → ONote
  | .natural n => ONote.ofNat n
  | .otherAtom => .zero
  | .cons e r => ONote.oadd (toNote e) 1 .zero + toNote r

def ordinalMeasure (x : Encoding) : Encoding := Encoding.ofNote (toNote x)

variable {S : Signature}

/-- Require E0-ORDINALP at every state and require E0-ORD-< at each selected call. -/
structure Terminates (B : Block S) (M : Model S) (rank : OrdinalAdmission.Measure B M) : Prop where
  valid : ∀ state, LegacyOrdinals.valid (rank state) = true
  decreases : B.TerminatesBy M (fun next current => lt (rank next) (rank current))

end Silmaril.Logic.ACL2.LegacyOrdinals
