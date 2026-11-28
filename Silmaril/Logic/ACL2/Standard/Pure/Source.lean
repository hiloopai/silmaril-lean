-- Generated from the certified world by tools/acl2-x86isa/check_pure_helpers.py.
module

public import Silmaril.Logic.ACL2.Standard.Pure.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.Pure

def eqlBody (x y : Object) : Object :=
  Object.equal (x) (y)

def notBody (x : Object) : Object :=
  if x = Object.nil then
    Object.truth
  else
    Object.nil

def atomBody (x : Object) : Object :=
  Object.logicalNot ((fun x => Object.ofBool (Object.consp x)) (x))

def mvNthBody (recur : Object → Object → Object) (index values : Object) : Object :=
  if atomBody (values) = Object.nil then
    if Object.zp (index) = Object.nil then
      recur (Object.binaryAdd (Object.integer (-1)) (index)) (Object.cdr (values))
    else
      Object.car (values)
  else
    Object.nil

def mvNthObservations : List (Object × Object × Object) := [
  (Object.integer (0), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.integer (1), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))),
  (Object.integer (2), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.nil),
  (Object.integer (1208925819614629174706176), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.nil),
  (Object.integer (-3), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.rational (Rat.divInt (1) 2), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (2)), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide)), Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.nil, Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.ofList [Object.integer (1)], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.integer (0), Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide))), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))),
  (Object.integer (1), Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide))), Object.nil),
  (Object.integer (1), Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))) (Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide)))), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))),
  (Object.integer (2), Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FIRST"⟩).get (by decide))) (Object.cons (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SECOND"⟩).get (by decide))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide)))), Object.nil),
  (Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide)), Object.nil),
  (Object.integer (3), Object.string [97, 98, 99], Object.nil),
  (Object.integer (0), Object.nil, Object.nil),
  (Object.integer (1), Object.ofList [Object.truth, Object.nil], Object.nil)]

def eqlObservations : List (Object × Object × Object) := [
  (Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide))), Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide))), Object.truth),
  (Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TAIL"⟩).get (by decide))), Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OTHER"⟩).get (by decide))), Object.nil),
  (Object.string [97, 99, 108, 50], Object.string [97, 99, 108, 50], Object.truth),
  (Object.string [97, 99, 108, 50], Object.string [65, 67, 76, 50], Object.nil),
  (Object.symbol ((Symbol.ofName? ⟨"ACL2", "C3-SAME"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "C3-SAME"⟩).get (by decide)), Object.nil),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SAME"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SAME"⟩).get (by decide)), Object.truth),
  (Object.rational (Rat.divInt (1) 2), Object.rational (Rat.divInt (1) 2), Object.truth),
  (Object.ofParts (Rat.ofInt (2)) (Rat.ofInt (-1)), Object.ofParts (Rat.ofInt (2)) (Rat.ofInt (-1)), Object.truth),
  (Object.character 65, Object.character 97, Object.nil),
  (Object.nil, Object.integer (0), Object.nil)]

def notObservations : List (Object × Object) := [
  (Object.nil, Object.truth),
  (Object.truth, Object.nil),
  (Object.integer (0), Object.nil),
  (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (2)), Object.nil),
  (Object.string [], Object.nil),
  (Object.character 97, Object.nil),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "NIL"⟩).get (by decide)), Object.nil),
  (Object.ofList [Object.nil], Object.nil)]

end Silmaril.Logic.ACL2.Standard.Pure
