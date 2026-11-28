-- Generated from corpus/acl2/bit-selection by tests/logic/acl2/check_bit_selection.py.
module

public import Silmaril.Logic.ACL2.Standard.BitSelection.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.BitSelection.Source

def expt2 (n : Object) : Object :=
  Object.integer (Int.ofNat (2 ^ (Object.nfix (n)).integerFix.toNat))

def ifloor (i j : Object) : Object :=
  floorIntegers (Object.ifix (i)).integerFix (Object.ifix (j)).integerFix

def imod (i j : Object) : Object :=
  modIntegers (Object.ifix (i)).integerFix (Object.ifix (j)).integerFix

def loghead (size i : Object) : Object :=
  imod (i) (expt2 (size))

def logtail (pos i : Object) : Object :=
  ifloor (i) (expt2 (pos))

def partSelectWidthLow (x width low : Object) : Object :=
  loghead (width) (logtail (low) (x))

def partSelectLowHigh (x low high : Object) : Object :=
  partSelectWidthLow (x) (Object.binaryAdd (Object.integer (1)) (Object.binaryAdd (high) (Object.unaryMinus (low)))) (low)

def observations : List (Object × Object) := [
  (Object.loghead (Object.integer (0)) (Object.integer (-13)), Object.integer (0)),
  (Object.loghead (Object.integer (4)) (Object.integer (-13)), Object.integer (3)),
  (Object.loghead (Object.integer (-2)) (Object.integer (-13)), Object.integer (0)),
  (Object.loghead (Object.rational (Rat.divInt (5) 2)) (Object.integer (-13)), Object.integer (0)),
  (Object.loghead (Object.integer (4)) (Object.ofParts (Rat.ofInt (3)) (Rat.ofInt (1))), Object.integer (0)),
  (Object.loghead (Object.integer (129)) (Object.integer (-1)), Object.integer (680564733841876926926749214863536422911)),
  (Object.logtail (Object.integer (2)) (Object.integer (-13)), Object.integer (-4)),
  (Object.logtail (Object.integer (2)) (Object.integer (13)), Object.integer (3)),
  (Object.logtail (Object.integer (-2)) (Object.integer (-13)), Object.integer (-13)),
  (Object.logtail (Object.rational (Rat.divInt (5) 2)) (Object.integer (-13)), Object.integer (-13)),
  (Object.logtail (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide))) (Object.integer (-13)), Object.integer (-13)),
  (Object.logtail (Object.integer (2)) (Object.rational (Rat.divInt (7) 2)), Object.integer (0)),
  (Object.logtail (Object.integer (129)) (Object.integer (-13)), Object.integer (-1)),
  (Object.partSelectWidthLow (Object.integer (-13)) (Object.integer (4)) (Object.integer (2)), Object.integer (12)),
  (Object.partSelectWidthLow (Object.integer (-13)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide))) (Object.integer (2)), Object.integer (0)),
  (Object.partSelectWidthLow (Object.integer (254)) (Object.integer (3)) (Object.integer (-2)), Object.integer (6)),
  (Object.partSelectLowHigh (Object.integer (214)) (Object.integer (1)) (Object.integer (4)), Object.integer (11)),
  (Object.partSelectLowHigh (Object.integer (-13)) (Object.integer (2)) (Object.integer (5)), Object.integer (12)),
  (Object.partSelectLowHigh (Object.integer (16)) (Object.integer (4)) (Object.integer (4)), Object.integer (1)),
  (Object.partSelectLowHigh (Object.integer (-1)) (Object.integer (4)) (Object.integer (3)), Object.integer (0)),
  (Object.partSelectLowHigh (Object.integer (-1)) (Object.integer (4)) (Object.integer (2)), Object.integer (0)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.integer (-2)) (Object.integer (0)), Object.integer (6)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.rational (Rat.divInt (1) 2)) (Object.rational (Rat.divInt (5) 2)), Object.integer (6)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.rational (Rat.divInt (1) 2)) (Object.integer (2)), Object.integer (0)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (2))) (Object.ofParts (Rat.ofInt (3)) (Rat.ofInt (2))), Object.integer (6)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (2))) (Object.ofParts (Rat.ofInt (3)) (Rat.ofInt (3))), Object.integer (0)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide))) (Object.integer (3)), Object.integer (14)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.integer (-2)) (Object.string [98, 97, 100]), Object.integer (6)),
  (Object.partSelectLowHigh (Object.integer (254)) (Object.integer (-2)) (Object.integer (-1)), Object.integer (2)),
  (Object.partSelectLowHigh (Object.cons (Object.integer (4)) (Object.integer (6))) (Object.integer (0)) (Object.integer (9)), Object.integer (0)),
  (Object.partSelectLowHigh (Object.integer (1461501638692032385887438686569781449383005388800)) (Object.integer (128)) (Object.integer (132)), Object.integer (4))]

end Silmaril.Logic.ACL2.Standard.BitSelection.Source
