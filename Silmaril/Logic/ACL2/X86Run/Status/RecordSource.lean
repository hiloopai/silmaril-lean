-- Generated from the certified export by tools/acl2-x86isa/check_object_order.py.
module

public import Silmaril.Logic.ACL2.X86Run.Status.RecordDefs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run.Status

open Standard

def fieldRules : List FieldRule := [
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide)), Object.nil, .any⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide)), Object.nil, .any⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENV"⟩).get (by decide)), Object.nil, .environment⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "UNDEF"⟩).get (by decide)), Object.integer (0), .any⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "APP-VIEW"⟩).get (by decide)), Object.truth, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MARKING-VIEW"⟩).get (by decide)), Object.truth, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ENABLE-PERIPHERALS"⟩).get (by decide)), Object.truth, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "HANDLE-EXCEPTIONS"⟩).get (by decide)), Object.truth, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OS-INFO"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "LINUX"⟩).get (by decide)), .keyword⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "RGF"⟩).get (by decide)), Object.integer (0), .signed 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "RIP"⟩).get (by decide)), Object.integer (0), .signed 48⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "RFLAGS"⟩).get (by decide)), Object.integer (2), .unsigned 32⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SEG-VISIBLE"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SEG-HIDDEN-BASE"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SEG-HIDDEN-LIMIT"⟩).get (by decide)), Object.integer (0), .unsigned 32⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SEG-HIDDEN-ATTR"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "STR"⟩).get (by decide)), Object.integer (0), .unsigned 80⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SSR-VISIBLE"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SSR-HIDDEN-BASE"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SSR-HIDDEN-LIMIT"⟩).get (by decide)), Object.integer (0), .unsigned 32⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "SSR-HIDDEN-ATTR"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "CTR"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "DBG"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-DATA"⟩).get (by decide)), Object.integer (0), .unsigned 80⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-CTRL"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-STATUS"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-TAG"⟩).get (by decide)), Object.integer (0), .unsigned 16⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-LAST-INST"⟩).get (by decide)), Object.integer (0), .unsigned 48⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-LAST-DATA"⟩).get (by decide)), Object.integer (0), .unsigned 48⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FP-OPCODE"⟩).get (by decide)), Object.integer (0), .unsigned 11⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MXCSR"⟩).get (by decide)), Object.integer (8064), .unsigned 32⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OPMSK"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ZMM"⟩).get (by decide)), Object.integer (0), .unsigned 512⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MSR"⟩).get (by decide)), Object.integer (0), .unsigned 64⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MEM"⟩).get (by decide)), Object.integer (0), .unsigned 8⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩).get (by decide)), Object.nil, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TIME-STAMP-COUNTER"⟩).get (by decide)), Object.integer (0), .natural⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "LAST-CLOCK-EVENT"⟩).get (by decide)), Object.integer (0), .natural⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "IMPLICIT-SUPERVISOR-ACCESS"⟩).get (by decide)), Object.nil, .boolean⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TLB"⟩).get (by decide)), .tlb⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-IN"⟩).get (by decide)), Object.nil, .tty⟩,
  ⟨Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-OUT"⟩).get (by decide)), Object.nil, .tty⟩]

def orderObservations : List (Object × Object × Bool × Bool × Bool × Bool) := [
  (Object.rational (Rat.divInt (-3) 2), Object.rational (Rat.divInt (-1) 2), true, false, true, false),
  (Object.integer (99), Object.ofParts (Rat.ofInt (-1)) (Rat.ofInt (-2)), true, false, true, false),
  (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (-2)), Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (2)), true, false, true, false),
  (Object.ofParts (Rat.ofInt (1)) (Rat.ofInt (3)), Object.ofParts (Rat.ofInt (2)) (Rat.ofInt (-3)), true, false, true, false),
  (Object.ofParts (Rat.ofInt (9)) (Rat.ofInt (-1)), Object.character 97, true, false, true, false),
  (Object.character 97, Object.character 255, true, false, true, false),
  (Object.character 122, Object.string [], true, false, true, false),
  (Object.string [], Object.string [], false, false, true, true),
  (Object.string [65], Object.string [65, 65], true, false, true, false),
  (Object.string [65, 65], Object.string [65, 90], true, false, true, false),
  (Object.string [200], Object.string [122], false, true, false, true),
  (Object.string [90], Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "A"⟩).get (by decide)), true, false, true, false),
  (Object.symbol ((Symbol.ofName? ⟨"ACL2", "C3-SAME"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "C3-SAME"⟩).get (by decide)), true, false, true, false),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "A"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"ACL2", "C3-SAME"⟩).get (by decide)), true, false, true, false),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "a"⟩).get (by decide)), Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "A"⟩).get (by decide)), false, true, false, true),
  (Object.nil, Object.ofList [Object.integer (0)], true, false, true, false),
  (Object.cons (Object.integer (2)) (Object.integer (-1)), Object.cons (Object.integer (2)) (Object.integer (1)), true, false, true, false),
  (Object.cons (Object.cons (Object.integer (1)) (Object.integer (9))) (Object.integer (20)), Object.cons (Object.cons (Object.integer (2)) (Object.integer (0))) (Object.integer (-20)), true, false, true, false),
  (Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "A"⟩).get (by decide))), Object.cons (Object.integer (1)) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "A"⟩).get (by decide))), false, false, true, true)]

def entryObservations : List (Object × Bool) := [
  (Object.nil, true),
  (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide)), false),
  (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "ONE"⟩).get (by decide))], false),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42))], true),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40))], true),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]) (Object.integer (42))], false),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "FAULT"⟩).get (by decide))]]], false),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40)), Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (42))], false),
  (Object.cons (Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "MS"⟩).get (by decide))]) (Object.integer (40))) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "BAD"⟩).get (by decide))), false),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "APP-VIEW"⟩).get (by decide))]) (Object.truth)], false),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "APP-VIEW"⟩).get (by decide))]) (Object.integer (1))], false),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "APP-VIEW"⟩).get (by decide))]]], true),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "OS-INFO"⟩).get (by decide))]) (Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "LINUX"⟩).get (by decide)))], false),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-IN"⟩).get (by decide))], Object.integer (0), Object.integer (255)]], true),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-IN"⟩).get (by decide))], Object.integer (256)]], false),
  (Object.ofList [Object.cons (Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-IN"⟩).get (by decide))]) (Object.cons (Object.integer (0)) (Object.integer (255)))], false),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-OUT"⟩).get (by decide))], Object.rational (Rat.divInt (1) 2)]], false),
  (Object.ofList [Object.ofList [Object.ofList [Object.symbol ((Symbol.ofName? ⟨"KEYWORD", "TTY-OUT"⟩).get (by decide))]]], false)]

end Silmaril.Logic.ACL2.X86Run.Status
