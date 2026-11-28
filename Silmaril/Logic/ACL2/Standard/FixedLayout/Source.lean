-- Generated from corpus/acl2/toy-defstobj by tests/logic/acl2/check_toy_defstobj.py.
module

public import Silmaril.Logic.ACL2.Standard.FixedLayout.Defs
public import Silmaril.Logic.ACL2.Standard.Pure.Source

@[expose] public section

namespace Silmaril.Logic.ACL2.Standard.FixedLayout.Source

def lenBody (recur : Object → Object) (x : Object) : Object :=
  if Object.ofBool (Object.consp (x)) = Object.nil then
    Object.integer (0)
  else
    Object.binaryAdd (Object.integer (1)) (recur (Object.cdr (x)))

def length (x : Object) : Object :=
  if Object.ofBool (Object.stringp (x)) = Object.nil then
    Object.len (x)
  else
    Object.len (Object.coerce (x) (Object.symbol Symbol.list))

def numericEqual (x y : Object) : Object :=
  Object.equal (x) (y)

def endp (x : Object) : Object :=
  Pure.atomBody (x)

def nthBody (recur : Object → Object → Object) (n l : Object) : Object :=
  if endp (l) = Object.nil then
    if Object.zp (n) = Object.nil then
      recur (Object.binaryAdd (Object.integer (-1)) (n)) (Object.cdr (l))
    else
      Object.car (l)
  else
    Object.nil

def updateNthBody (recur : Object → Object → Object → Object) (key val l : Object) : Object :=
  if Object.zp (key) = Object.nil then
    Object.cons (Object.car (l)) (recur (Object.binaryAdd (Object.integer (-1)) (key)) (val) (Object.cdr (l)))
  else
    Object.cons (val) (Object.cdr (l))

def updateNthArray (j key val l : Object) : Object :=
  Object.updateNth (j) (Object.updateNth (key) (val) (Object.mvNth (j) (l))) (l)

def makeListAcBody (recur : Object → Object → Object → Object) (n val ac : Object) : Object :=
  if Object.zp (n) = Object.nil then
    recur (Object.binaryAdd (Object.integer (-1)) (n)) (val) (Object.cons (val) (ac))
  else
    ac

def scalarP (x : Object) : Object :=
  Object.ofBool (Object.integerp (x))

def cellsPBody (recur : Object → Object) (x : Object) : Object :=
  if Pure.atomBody (x) = Object.nil then
    if Object.ofBool (Object.integerp (Object.car (x))) = Object.nil then
      Object.nil
    else
      recur (Object.cdr (x))
  else
    Object.equal (x) (Object.nil)

def recognizer (sil_toy : Object) : Object :=
  if Object.ofBool (Object.trueListp (sil_toy)) = Object.nil then
    Object.nil
  else
    if numericEqual (length (sil_toy)) (Object.integer (2)) = Object.nil then
      Object.nil
    else
      if scalarP (Object.mvNth (Object.integer (0)) (sil_toy)) = Object.nil then
        Object.nil
      else
        if Toy.cellsP (Object.mvNth (Object.integer (1)) (sil_toy)) = Object.nil then
          Object.nil
        else
          if Object.equal (Object.len (Object.mvNth (Object.integer (1)) (sil_toy))) (Object.integer (3)) = Object.nil then
            Object.nil
          else
            Object.truth

def initial : Object :=
  Object.cons (Object.integer (-2)) (Object.cons (Object.makeListAc (Object.integer (3)) (Object.integer (7)) (Object.nil)) (Object.nil))

def readScalar (sil_toy : Object) : Object :=
  Object.mvNth (Object.integer (0)) (sil_toy)

def writeScalar (v sil_toy : Object) : Object :=
  Object.updateNth (Object.integer (0)) (v) (sil_toy)

def readCell (i sil_toy : Object) : Object :=
  Object.mvNth (i) (Object.mvNth (Object.integer (1)) (sil_toy))

def writeCell (i v sil_toy : Object) : Object :=
  updateNthArray (Object.integer (1)) (i) (v) (sil_toy)

def observations : List (Object × Object) := [
  (Toy.initial, Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (7), Object.integer (7)]]),
  (Toy.recognizer (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.truth),
  (Toy.recognizer (Object.ofList [Object.nil, Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.nil),
  (Toy.recognizer (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8)]]), Object.nil),
  (Toy.recognizer (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)], Object.symbol ((Symbol.ofName? ⟨"ACL2", "EXTRA"⟩).get (by decide))]), Object.nil),
  (Toy.recognizer (Object.ofList [Object.integer (-2), Object.cons (Object.integer (7)) (Object.cons (Object.integer (8)) (Object.cons (Object.integer (9)) (Object.integer (1))))]), Object.nil),
  (Toy.recognizer (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.nil, Object.integer (9)]]), Object.nil),
  (Toy.readScalar (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.integer (-2)),
  (Toy.writeScalar (Object.integer (13)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.ofList [Object.integer (13), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]),
  (Toy.readCell (Object.integer (1)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.integer (8)),
  (Toy.writeCell (Object.integer (1)) (Object.integer (13)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (13), Object.integer (9)]]),
  (Toy.readCell (Object.integer (-1)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.integer (7)),
  (Toy.writeCell (Object.rational (Rat.divInt (3) 2)) (Object.integer (5)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.ofList [Object.integer (-2), Object.ofList [Object.integer (5), Object.integer (8), Object.integer (9)]]),
  (Toy.readCell (Object.integer (4)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.nil),
  (Toy.writeCell (Object.integer (4)) (Object.integer (5)) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]]), Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9), Object.nil, Object.integer (5)]]),
  (Toy.writeCell (Object.string [98, 97, 100]) (Object.integer (5)) (Object.integer (82)), Object.ofList [Object.nil, Object.ofList [Object.integer (5)]]),
  (Toy.writeCell (Object.integer (0)) (Object.integer (5)) (Object.ofList [Object.integer (-2), Object.cons (Object.integer (7)) (Object.integer (8))]), Object.ofList [Object.integer (-2), Object.cons (Object.integer (5)) (Object.integer (8))]),
  (Toy.recognizer (Toy.writeCell (Object.integer (0)) (Object.nil) (Object.ofList [Object.integer (-2), Object.ofList [Object.integer (7), Object.integer (8), Object.integer (9)]])), Object.nil)]

end Silmaril.Logic.ACL2.Standard.FixedLayout.Source
