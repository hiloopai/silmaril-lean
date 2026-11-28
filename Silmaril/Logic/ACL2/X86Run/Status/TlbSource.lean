-- Generated from the certified world by tools/acl2-x86isa/check_tlb.py.
module

public import Silmaril.Logic.ACL2.X86Run.Status.TlbDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status.Tlb

open Standard

def layout : Layout where
  marker := Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))
  keyWidth := 46
  pageWidth := 40
  modeWidth := 2
  modeOffset := 6
  maxMode := 2

def tlbP : Object → Bool := recognizes layout

def arithmeticObservations : List (Int × Nat × Nat × Int × Int) := [
  (0, 64, 0, 0, 0),
  (17, 0, 0, 0, 17),
  (63, 64, 0, 0, 63),
  (64, 64, 1, 1, 0),
  (65, 64, 1, 1, 1),
  (192, 64, 3, 3, 0),
  (193, 64, 3, 3, 1),
  (7, 4, 1, 1, 3),
  (5, 1, 5, 5, 0),
  (-193, 64, 0, -4, 63),
  (-192, 64, 0, -3, 0),
  (-17, 0, 0, 0, -17)]

def keyObservations : List (Object × Bool × Bool × Object) := [
  (Object.integer (-1), false, false, Object.nil),
  (Object.rational (Rat.divInt (1) 2), false, false, Object.nil),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide)), false, false, Object.nil),
  (Object.ofList [Object.integer (0)], false, false, Object.nil),
  (Object.integer (0), true, true, Object.integer (0)),
  (Object.integer (63), true, true, Object.integer (0)),
  (Object.integer (64), true, true, Object.integer (1)),
  (Object.integer (128), true, true, Object.integer (2)),
  (Object.integer (191), true, true, Object.integer (2)),
  (Object.integer (192), true, false, Object.integer (3)),
  (Object.integer (255), true, false, Object.integer (3)),
  (Object.integer (256), true, true, Object.integer (0)),
  (Object.integer (70368744177599), true, true, Object.integer (2)),
  (Object.integer (70368744177663), true, false, Object.integer (3)),
  (Object.integer (70368744177664), false, false, Object.nil)]

def tlbObservations : List (Object × Bool × Object × Bool × Bool × Object × Object) := [
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)), true,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)))], false, false, Object.nil, Object.nil),
  (Object.symbol ((Symbol.ofName? ⟨"ACL2", "TLB"⟩).get (by decide)), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.symbol ((Symbol.ofName? ⟨"ACL2", "TLB"⟩).get (by decide)))], false, false, Object.nil, Object.nil),
  (Object.nil, false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]]], false, false, Object.nil, Object.nil),
  (Object.cons (Object.cons (Object.integer (0)) (Object.integer (0))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), true,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (0)) (Object.integer (0))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], true, true, Object.integer (40), Object.integer (42)),
  (Object.cons (Object.cons (Object.integer (128)) (Object.integer (1099511627775))) (Object.cons (Object.cons (Object.integer (0)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)))), true,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (128)) (Object.integer (1099511627775))) (Object.cons (Object.cons (Object.integer (0)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)))))], true, true, Object.integer (40), Object.integer (42)),
  (Object.cons (Object.cons (Object.integer (0)) (Object.integer (1099511627776))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (0)) (Object.integer (1099511627776))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil),
  (Object.cons (Object.cons (Object.integer (0)) (Object.integer (-1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (0)) (Object.integer (-1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil),
  (Object.cons (Object.cons (Object.integer (0)) (Object.rational (Rat.divInt (1) 2))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (0)) (Object.rational (Rat.divInt (1) 2))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil),
  (Object.cons (Object.cons (Object.integer (192)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.integer (192)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil),
  (Object.cons (Object.cons (Object.rational (Rat.divInt (1) 2)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.cons (Object.rational (Rat.divInt (1) 2)) (Object.integer (1))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil),
  (Object.ofList [Object.cons (Object.integer (0)) (Object.integer (1))], false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))], Object.cons (Object.integer (0)) (Object.integer (1))]], false, false, Object.nil, Object.nil),
  (Object.cons (Object.integer (17)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))), false,
    Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-DESCRIPTORS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FILE-CONTENTS"⟩).get (by decide))], Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ORACLE"⟩).get (by decide)), Object.ofList [Object.integer (0), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OK"⟩).get (by decide))]]], Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))]) (Object.cons (Object.integer (17)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide))))], false, false, Object.nil, Object.nil)]

end Silmaril.Logic.ACL2.X86Run.Status.Tlb
