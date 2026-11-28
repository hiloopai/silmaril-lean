-- Generated from corpus/acl2/prefixes-projections by tests/logic/acl2/check_prefixes.py.
module

public import Silmaril.Logic.ACL2.Standard.FixedWidth.Defs
public import Silmaril.Logic.ACL2.Standard.BitSelection.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedWidth.Source

def prefixesFix (x : Object) : Object :=
  BitSelection.Source.loghead (Object.integer (52)) (x)

def prefixesAdr (x : Object) : Object :=
  let fixed := prefixesFix (x)
  BitSelection.Source.partSelectWidthLow (fixed) (Object.integer (8)) (Object.integer (36))

def prefixesNum (x : Object) : Object :=
  let fixed := prefixesFix (x)
  BitSelection.Source.partSelectWidthLow (fixed) (Object.integer (4)) (Object.integer (0))

def prefixesNxt (x : Object) : Object :=
  let fixed := prefixesFix (x)
  BitSelection.Source.partSelectWidthLow (fixed) (Object.integer (8)) (Object.integer (44))

def observations : List (Object × Object × Object × Object × Object) := [
  (Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.integer (15), Object.integer (15), Object.integer (0), Object.integer (15), Object.integer (0)),
  (Object.integer (16), Object.integer (16), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.integer (68719476735), Object.integer (68719476735), Object.integer (0), Object.integer (15), Object.integer (0)),
  (Object.integer (68719476736), Object.integer (68719476736), Object.integer (1), Object.integer (0), Object.integer (0)),
  (Object.integer (17592186044415), Object.integer (17592186044415), Object.integer (255), Object.integer (15), Object.integer (0)),
  (Object.integer (17592186044416), Object.integer (17592186044416), Object.integer (0), Object.integer (0), Object.integer (1)),
  (Object.integer (4503599627370495), Object.integer (4503599627370495), Object.integer (255), Object.integer (15), Object.integer (255)),
  (Object.integer (4503599627370496), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.integer (1208925823162547039109127), Object.integer (3547917864402951), Object.integer (173), Object.integer (7), Object.integer (201)),
  (Object.integer (-1), Object.integer (4503599627370495), Object.integer (255), Object.integer (15), Object.integer (255)),
  (Object.integer (-4503599627370496), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.integer (-4503599627370497), Object.integer (4503599627370495), Object.integer (255), Object.integer (15), Object.integer (255)),
  (Object.integer (-17), Object.integer (4503599627370479), Object.integer (255), Object.integer (15), Object.integer (255)),
  (Object.rational (Rat.divInt (-3) 2), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (-2)), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.string [49, 50, 51], Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide)), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.nil, Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0)),
  (Object.cons (Object.integer (1)) (Object.integer (2)), Object.integer (0), Object.integer (0), Object.integer (0), Object.integer (0))]

end Silmaril.Logic.ACL2.Standard.FixedWidth.Source
