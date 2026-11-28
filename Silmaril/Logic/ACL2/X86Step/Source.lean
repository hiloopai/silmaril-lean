-- Generated from corpus/acl2/x86-dependencies by tools/acl2-x86isa/check_step.py.
module

public import Silmaril.Logic.ACL2.Translated.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Step

open Translated

def stepName : Name := ⟨"X86ISA", "X86-FETCH-DECODE-EXECUTE"⟩

def formals : List Name := [⟨"X86ISA", "X86"⟩]

def manifestCalls : List (Name × Nat) := [
  (⟨"ACL2", "BINARY-+"⟩, 2),
  (⟨"ACL2", "MV-NTH"⟩, 2),
  (⟨"BITOPS", "PART-SELECT-LOW-HIGH$INLINE"⟩, 3),
  (⟨"COMMON-LISP", "CONS"⟩, 2),
  (⟨"COMMON-LISP", "EQL"⟩, 2),
  (⟨"COMMON-LISP", "EQUAL"⟩, 2),
  (⟨"COMMON-LISP", "IF"⟩, 3),
  (⟨"COMMON-LISP", "NOT"⟩, 1),
  (⟨"X86ISA", "!EVEX-PREFIXES->BYTE0$INLINE"⟩, 2),
  (⟨"X86ISA", "!EVEX-PREFIXES->BYTE1$INLINE"⟩, 2),
  (⟨"X86ISA", "!INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩, 2),
  (⟨"X86ISA", "!MS"⟩, 2),
  (⟨"X86ISA", "!VEX-PREFIXES->BYTE0$INLINE"⟩, 2),
  (⟨"X86ISA", "!VEX-PREFIXES->BYTE1$INLINE"⟩, 2),
  (⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩, 4),
  (⟨"X86ISA", "APP-VIEW"⟩, 1),
  (⟨"X86ISA", "ENABLE-PERIPHERALS"⟩, 1),
  (⟨"X86ISA", "EVEX-DECODE-AND-EXECUTE"⟩, 7),
  (⟨"X86ISA", "FAULT"⟩, 1),
  (⟨"X86ISA", "GET-PREFIXES"⟩, 6),
  (⟨"X86ISA", "HANDLE-EXCEPTIONS"⟩, 1),
  (⟨"X86ISA", "HANDLE-FAULTS"⟩, 1),
  (⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩, 1),
  (⟨"X86ISA", "MS"⟩, 1),
  (⟨"X86ISA", "ONE-BYTE-OPCODE-EXECUTE"⟩, 9),
  (⟨"X86ISA", "ONE-BYTE-OPCODE-MODR/M-P$INLINE"⟩, 2),
  (⟨"X86ISA", "PREFIXES->ADR$INLINE"⟩, 1),
  (⟨"X86ISA", "PREFIXES->NUM$INLINE"⟩, 1),
  (⟨"X86ISA", "PREFIXES->NXT$INLINE"⟩, 1),
  (⟨"X86ISA", "READ-*IP$INLINE"⟩, 2),
  (⟨"X86ISA", "RIP"⟩, 1),
  (⟨"X86ISA", "RME08$INLINE"⟩, 5),
  (⟨"X86ISA", "SELECT-ADDRESS-SIZE$INLINE"⟩, 3),
  (⟨"X86ISA", "VEX-DECODE-AND-EXECUTE"⟩, 7),
  (⟨"X86ISA", "X86-DECODE-SIB-P"⟩, 2),
  (⟨"X86ISA", "X86-EXEC-PERIPHERALS"⟩, 1),
  (⟨"X86ISA", "X86-OPERATION-MODE"⟩, 1)]

def frontierEntries : List (Name × Nat) := [
  (⟨"ACL2", "MV-NTH"⟩, 2),
  (⟨"BITOPS", "PART-SELECT-LOW-HIGH$INLINE"⟩, 3),
  (⟨"COMMON-LISP", "EQL"⟩, 2),
  (⟨"COMMON-LISP", "NOT"⟩, 1),
  (⟨"X86ISA", "!EVEX-PREFIXES->BYTE0$INLINE"⟩, 2),
  (⟨"X86ISA", "!EVEX-PREFIXES->BYTE1$INLINE"⟩, 2),
  (⟨"X86ISA", "!INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩, 2),
  (⟨"X86ISA", "!MS"⟩, 2),
  (⟨"X86ISA", "!VEX-PREFIXES->BYTE0$INLINE"⟩, 2),
  (⟨"X86ISA", "!VEX-PREFIXES->BYTE1$INLINE"⟩, 2),
  (⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩, 4),
  (⟨"X86ISA", "APP-VIEW"⟩, 1),
  (⟨"X86ISA", "ENABLE-PERIPHERALS"⟩, 1),
  (⟨"X86ISA", "EVEX-DECODE-AND-EXECUTE"⟩, 7),
  (⟨"X86ISA", "FAULT"⟩, 1),
  (⟨"X86ISA", "GET-PREFIXES"⟩, 6),
  (⟨"X86ISA", "HANDLE-EXCEPTIONS"⟩, 1),
  (⟨"X86ISA", "HANDLE-FAULTS"⟩, 1),
  (⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩, 1),
  (⟨"X86ISA", "MS"⟩, 1),
  (⟨"X86ISA", "ONE-BYTE-OPCODE-EXECUTE"⟩, 9),
  (⟨"X86ISA", "ONE-BYTE-OPCODE-MODR/M-P$INLINE"⟩, 2),
  (⟨"X86ISA", "PREFIXES->ADR$INLINE"⟩, 1),
  (⟨"X86ISA", "PREFIXES->NUM$INLINE"⟩, 1),
  (⟨"X86ISA", "PREFIXES->NXT$INLINE"⟩, 1),
  (⟨"X86ISA", "READ-*IP$INLINE"⟩, 2),
  (⟨"X86ISA", "RIP"⟩, 1),
  (⟨"X86ISA", "RME08$INLINE"⟩, 5),
  (⟨"X86ISA", "SELECT-ADDRESS-SIZE$INLINE"⟩, 3),
  (⟨"X86ISA", "VEX-DECODE-AND-EXECUTE"⟩, 7),
  (⟨"X86ISA", "X86-DECODE-SIB-P"⟩, 2),
  (⟨"X86ISA", "X86-EXEC-PERIPHERALS"⟩, 1),
  (⟨"X86ISA", "X86-OPERATION-MODE"⟩, 1)]

def source : Raw :=
  .lambda [⟨"ACL2", "__FUNCTION__"⟩, ⟨"X86ISA", "X86"⟩]
    (.ite
      (.ite
        (.call ⟨"X86ISA", "MS"⟩
          (RawArgs.ofList [
            .var ⟨"X86ISA", "X86"⟩]))
        (.call ⟨"X86ISA", "MS"⟩
          (RawArgs.ofList [
            .var ⟨"X86ISA", "X86"⟩]))
        (.call ⟨"X86ISA", "FAULT"⟩
          (RawArgs.ofList [
            .var ⟨"X86ISA", "X86"⟩])))
      (.var ⟨"X86ISA", "X86"⟩)
      (.lambda [⟨"X86ISA", "APP-VIEW?"⟩, ⟨"X86ISA", "X86"⟩]
        (.lambda [⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩, ⟨"X86ISA", "APP-VIEW?"⟩, ⟨"X86ISA", "X86"⟩]
          (.lambda [⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩, ⟨"X86ISA", "APP-VIEW?"⟩]
            (.ite
              (.var ⟨"X86ISA", "APP-VIEW?"⟩)
              (.var ⟨"X86ISA", "X86"⟩)
              (.lambda [⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩]
                (.lambda [⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩]
                  (.ite
                    (.var ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩)
                    (.call ⟨"X86ISA", "!INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩
                      (RawArgs.ofList [
                        .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                        .var ⟨"X86ISA", "X86"⟩]))
                    (.var ⟨"X86ISA", "X86"⟩))
                  (RawArgs.ofList [
                    .ite
                      (.ite
                        (.call ⟨"X86ISA", "FAULT"⟩
                          (RawArgs.ofList [
                            .var ⟨"X86ISA", "X86"⟩]))
                        (.call ⟨"X86ISA", "HANDLE-EXCEPTIONS"⟩
                          (RawArgs.ofList [
                            .var ⟨"X86ISA", "X86"⟩]))
                        (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)))
                      (.call ⟨"X86ISA", "HANDLE-FAULTS"⟩
                        (RawArgs.ofList [
                          .var ⟨"X86ISA", "X86"⟩]))
                      (.var ⟨"X86ISA", "X86"⟩),
                    .var ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩]))
                (RawArgs.ofList [
                  .ite
                    (.call ⟨"X86ISA", "ENABLE-PERIPHERALS"⟩
                      (RawArgs.ofList [
                        .var ⟨"X86ISA", "X86"⟩]))
                    (.call ⟨"X86ISA", "X86-EXEC-PERIPHERALS"⟩
                      (RawArgs.ofList [
                        .var ⟨"X86ISA", "X86"⟩]))
                    (.var ⟨"X86ISA", "X86"⟩),
                  .var ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩])))
            (RawArgs.ofList [
              .lambda [⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                (.lambda [⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                  (.lambda [⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                    (.lambda [⟨"X86ISA", "START-RIP"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                      (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"ACL2", "CTX"⟩]
                        (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"ACL2", "(THE (UNSIGNED-BYTE 52) PREFIXES)"⟩, ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) REX-BYTE)"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"ACL2", "CTX"⟩]
                          (.lambda [⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) REX-BYTE)"⟩]
                            (.lambda [⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "FLG"⟩]
                              (.ite
                                (.var ⟨"X86ISA", "FLG"⟩)
                                (.call ⟨"X86ISA", "!MS"⟩
                                  (RawArgs.ofList [
                                    .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                      (.call ⟨"COMMON-LISP", "CONS"⟩
                                        (RawArgs.ofList [
                                          .call ⟨"COMMON-LISP", "CONS"⟩
                                            (RawArgs.ofList [
                                              .var ⟨"ACL2", "CTX"⟩,
                                              .call ⟨"COMMON-LISP", "CONS"⟩
                                                (RawArgs.ofList [
                                                  .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                    (RawArgs.ofList [
                                                      .call ⟨"X86ISA", "RIP"⟩
                                                        (RawArgs.ofList [
                                                          .var ⟨"X86ISA", "X86"⟩]),
                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                        (RawArgs.ofList [
                                                          .quote (.symbol ⟨"KEYWORD", "ERROR-IN-READING-PREFIXES"⟩),
                                                          .call ⟨"COMMON-LISP", "CONS"⟩
                                                            (RawArgs.ofList [
                                                              .var ⟨"X86ISA", "FLG"⟩,
                                                              .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                          .var ⟨"X86ISA", "ERP"⟩]))
                                      (RawArgs.ofList [
                                        .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                        .var ⟨"X86ISA", "FLG"⟩,
                                        .var ⟨"X86ISA", "X86"⟩,
                                        .var ⟨"ACL2", "CTX"⟩]),
                                    .var ⟨"X86ISA", "X86"⟩]))
                                (.lambda [⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "PREFIXES"⟩]
                                  (.lambda [⟨"X86ISA", "PREFIX-LENGTH"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                    (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                      (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                        (.ite
                                          (.var ⟨"X86ISA", "FLG"⟩)
                                          (.call ⟨"X86ISA", "!MS"⟩
                                            (RawArgs.ofList [
                                              .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                (.call ⟨"COMMON-LISP", "CONS"⟩
                                                  (RawArgs.ofList [
                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                      (RawArgs.ofList [
                                                        .var ⟨"ACL2", "CTX"⟩,
                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                          (RawArgs.ofList [
                                                            .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                              (RawArgs.ofList [
                                                                .call ⟨"X86ISA", "RIP"⟩
                                                                  (RawArgs.ofList [
                                                                    .var ⟨"X86ISA", "X86"⟩]),
                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                  (RawArgs.ofList [
                                                                    .quote (.symbol ⟨"KEYWORD", "INCREMENT-ERROR"⟩),
                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                      (RawArgs.ofList [
                                                                        .var ⟨"X86ISA", "FLG"⟩,
                                                                        .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                    .var ⟨"X86ISA", "ERP"⟩]))
                                                (RawArgs.ofList [
                                                  .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                  .var ⟨"X86ISA", "FLG"⟩,
                                                  .var ⟨"X86ISA", "X86"⟩,
                                                  .var ⟨"ACL2", "CTX"⟩]),
                                              .var ⟨"X86ISA", "X86"⟩]))
                                          (.lambda [⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                            (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩]
                                              (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩]
                                                (.ite
                                                  (.var ⟨"X86ISA", "FLG"⟩)
                                                  (.call ⟨"X86ISA", "!MS"⟩
                                                    (RawArgs.ofList [
                                                      .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                        (.call ⟨"COMMON-LISP", "CONS"⟩
                                                          (RawArgs.ofList [
                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                              (RawArgs.ofList [
                                                                .var ⟨"ACL2", "CTX"⟩,
                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                  (RawArgs.ofList [
                                                                    .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                      (RawArgs.ofList [
                                                                        .call ⟨"X86ISA", "RIP"⟩
                                                                          (RawArgs.ofList [
                                                                            .var ⟨"X86ISA", "X86"⟩]),
                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                          (RawArgs.ofList [
                                                                            .quote (.symbol ⟨"KEYWORD", "LES/LDS-DISTINGUISHING-BYTE-READ-ERROR"⟩),
                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                              (RawArgs.ofList [
                                                                                .var ⟨"X86ISA", "FLG"⟩,
                                                                                .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                            .var ⟨"X86ISA", "ERP"⟩]))
                                                        (RawArgs.ofList [
                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                          .var ⟨"X86ISA", "FLG"⟩,
                                                          .var ⟨"X86ISA", "X86"⟩,
                                                          .var ⟨"ACL2", "CTX"⟩]),
                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                  (.ite
                                                    (.ite
                                                      (.var ⟨"X86ISA", "VEX-BYTE0?"⟩)
                                                      (.ite
                                                        (.var ⟨"X86ISA", "64-BIT-MODEP"⟩)
                                                        (.var ⟨"X86ISA", "64-BIT-MODEP"⟩)
                                                        (.ite
                                                          (.call ⟨"COMMON-LISP", "NOT"⟩
                                                            (RawArgs.ofList [
                                                              .var ⟨"X86ISA", "64-BIT-MODEP"⟩]))
                                                          (.call ⟨"COMMON-LISP", "EQUAL"⟩
                                                            (RawArgs.ofList [
                                                              .call ⟨"BITOPS", "PART-SELECT-LOW-HIGH$INLINE"⟩
                                                                (RawArgs.ofList [
                                                                  .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                                  .quote (.integer (6)),
                                                                  .quote (.integer (7))]),
                                                              .quote (.integer (3))]))
                                                          (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩))))
                                                      (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)))
                                                    (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                      (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                        (.ite
                                                          (.var ⟨"X86ISA", "FLG"⟩)
                                                          (.call ⟨"X86ISA", "!MS"⟩
                                                            (RawArgs.ofList [
                                                              .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                  (RawArgs.ofList [
                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                      (RawArgs.ofList [
                                                                        .var ⟨"ACL2", "CTX"⟩,
                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                          (RawArgs.ofList [
                                                                            .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                              (RawArgs.ofList [
                                                                                .call ⟨"X86ISA", "RIP"⟩
                                                                                  (RawArgs.ofList [
                                                                                    .var ⟨"X86ISA", "X86"⟩]),
                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                  (RawArgs.ofList [
                                                                                    .quote (.symbol ⟨"KEYWORD", "VEX-BYTE1-INCREMENT-ERROR"⟩),
                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                      (RawArgs.ofList [
                                                                                        .var ⟨"X86ISA", "FLG"⟩,
                                                                                        .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                    .var ⟨"X86ISA", "ERP"⟩]))
                                                                (RawArgs.ofList [
                                                                  .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                  .var ⟨"X86ISA", "FLG"⟩,
                                                                  .var ⟨"X86ISA", "X86"⟩,
                                                                  .var ⟨"ACL2", "CTX"⟩]),
                                                              .var ⟨"X86ISA", "X86"⟩]))
                                                          (.lambda [⟨"X86ISA", "VEX-PREFIXES"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩]
                                                            (.lambda [⟨"X86ISA", "VEX-PREFIXES"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                              (.call ⟨"X86ISA", "VEX-DECODE-AND-EXECUTE"⟩
                                                                (RawArgs.ofList [
                                                                  .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                  .var ⟨"X86ISA", "START-RIP"⟩,
                                                                  .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                  .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                  .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                  .var ⟨"X86ISA", "VEX-PREFIXES"⟩,
                                                                  .var ⟨"X86ISA", "X86"⟩]))
                                                              (RawArgs.ofList [
                                                                .call ⟨"X86ISA", "!VEX-PREFIXES->BYTE1$INLINE"⟩
                                                                  (RawArgs.ofList [
                                                                    .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "VEX-PREFIXES"⟩]),
                                                                .var ⟨"X86ISA", "X86"⟩,
                                                                .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                .var ⟨"X86ISA", "START-RIP"⟩,
                                                                .var ⟨"X86ISA", "PROC-MODE"⟩]))
                                                            (RawArgs.ofList [
                                                              .call ⟨"X86ISA", "!VEX-PREFIXES->BYTE0$INLINE"⟩
                                                                (RawArgs.ofList [
                                                                  .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                                  .quote (.integer (0))]),
                                                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                              .var ⟨"X86ISA", "START-RIP"⟩,
                                                              .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                              .var ⟨"X86ISA", "PREFIXES"⟩,
                                                              .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                              .var ⟨"X86ISA", "X86"⟩,
                                                              .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩])))
                                                        (RawArgs.ofList [
                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                            (RawArgs.ofList [
                                                              .quote (.integer (0)),
                                                              .var ⟨"ACL2", "MV"⟩]),
                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                            (RawArgs.ofList [
                                                              .quote (.integer (1)),
                                                              .var ⟨"ACL2", "MV"⟩]),
                                                          .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                          .var ⟨"X86ISA", "PREFIXES"⟩,
                                                          .var ⟨"X86ISA", "START-RIP"⟩,
                                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                          .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                          .var ⟨"ACL2", "CTX"⟩,
                                                          .var ⟨"X86ISA", "X86"⟩]))
                                                      (RawArgs.ofList [
                                                        .call ⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩
                                                          (RawArgs.ofList [
                                                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                            .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                            .quote (.integer (1)),
                                                            .var ⟨"X86ISA", "X86"⟩]),
                                                        .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                        .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                        .var ⟨"X86ISA", "PREFIXES"⟩,
                                                        .var ⟨"X86ISA", "START-RIP"⟩,
                                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                        .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                        .var ⟨"ACL2", "CTX"⟩,
                                                        .var ⟨"X86ISA", "X86"⟩]))
                                                    (.lambda [⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"ACL2", "CTX"⟩]
                                                      (.lambda [⟨"X86ISA", "EVEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                        (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "EVEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩]
                                                          (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "64-BIT-MODEP"⟩, ⟨"X86ISA", "EVEX-BYTE0?"⟩, ⟨"ACL2", "CTX"⟩]
                                                            (.ite
                                                              (.var ⟨"X86ISA", "FLG"⟩)
                                                              (.call ⟨"X86ISA", "!MS"⟩
                                                                (RawArgs.ofList [
                                                                  .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                    (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                      (RawArgs.ofList [
                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                          (RawArgs.ofList [
                                                                            .var ⟨"ACL2", "CTX"⟩,
                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                              (RawArgs.ofList [
                                                                                .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                  (RawArgs.ofList [
                                                                                    .call ⟨"X86ISA", "RIP"⟩
                                                                                      (RawArgs.ofList [
                                                                                        .var ⟨"X86ISA", "X86"⟩]),
                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                      (RawArgs.ofList [
                                                                                        .quote (.symbol ⟨"KEYWORD", "BOUND-DISTINGUISHING-BYTE-READ-ERROR"⟩),
                                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                          (RawArgs.ofList [
                                                                                            .var ⟨"X86ISA", "FLG"⟩,
                                                                                            .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                        .var ⟨"X86ISA", "ERP"⟩]))
                                                                    (RawArgs.ofList [
                                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                      .var ⟨"X86ISA", "FLG"⟩,
                                                                      .var ⟨"X86ISA", "X86"⟩,
                                                                      .var ⟨"ACL2", "CTX"⟩]),
                                                                  .var ⟨"X86ISA", "X86"⟩]))
                                                              (.ite
                                                                (.ite
                                                                  (.var ⟨"X86ISA", "EVEX-BYTE0?"⟩)
                                                                  (.ite
                                                                    (.var ⟨"X86ISA", "64-BIT-MODEP"⟩)
                                                                    (.var ⟨"X86ISA", "64-BIT-MODEP"⟩)
                                                                    (.ite
                                                                      (.call ⟨"COMMON-LISP", "NOT"⟩
                                                                        (RawArgs.ofList [
                                                                          .var ⟨"X86ISA", "64-BIT-MODEP"⟩]))
                                                                      (.call ⟨"COMMON-LISP", "EQUAL"⟩
                                                                        (RawArgs.ofList [
                                                                          .call ⟨"BITOPS", "PART-SELECT-LOW-HIGH$INLINE"⟩
                                                                            (RawArgs.ofList [
                                                                              .var ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩,
                                                                              .quote (.integer (6)),
                                                                              .quote (.integer (7))]),
                                                                          .quote (.integer (3))]))
                                                                      (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩))))
                                                                  (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)))
                                                                (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                  (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                    (.ite
                                                                      (.var ⟨"X86ISA", "FLG"⟩)
                                                                      (.call ⟨"X86ISA", "!MS"⟩
                                                                        (RawArgs.ofList [
                                                                          .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                            (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                              (RawArgs.ofList [
                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                  (RawArgs.ofList [
                                                                                    .var ⟨"ACL2", "CTX"⟩,
                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                      (RawArgs.ofList [
                                                                                        .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                          (RawArgs.ofList [
                                                                                            .call ⟨"X86ISA", "RIP"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .var ⟨"X86ISA", "X86"⟩]),
                                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .quote (.symbol ⟨"KEYWORD", "EVEX-BYTE1-INCREMENT-ERROR"⟩),
                                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                  (RawArgs.ofList [
                                                                                                    .var ⟨"X86ISA", "FLG"⟩,
                                                                                                    .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                                .var ⟨"X86ISA", "ERP"⟩]))
                                                                            (RawArgs.ofList [
                                                                              .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                              .var ⟨"X86ISA", "FLG"⟩,
                                                                              .var ⟨"X86ISA", "X86"⟩,
                                                                              .var ⟨"ACL2", "CTX"⟩]),
                                                                          .var ⟨"X86ISA", "X86"⟩]))
                                                                      (.lambda [⟨"X86ISA", "EVEX-PREFIXES"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩]
                                                                        (.lambda [⟨"X86ISA", "EVEX-PREFIXES"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                                          (.call ⟨"X86ISA", "EVEX-DECODE-AND-EXECUTE"⟩
                                                                            (RawArgs.ofList [
                                                                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                              .var ⟨"X86ISA", "START-RIP"⟩,
                                                                              .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                              .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                              .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                              .var ⟨"X86ISA", "EVEX-PREFIXES"⟩,
                                                                              .var ⟨"X86ISA", "X86"⟩]))
                                                                          (RawArgs.ofList [
                                                                            .call ⟨"X86ISA", "!EVEX-PREFIXES->BYTE1$INLINE"⟩
                                                                              (RawArgs.ofList [
                                                                                .var ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩,
                                                                                .var ⟨"X86ISA", "EVEX-PREFIXES"⟩]),
                                                                            .var ⟨"X86ISA", "X86"⟩,
                                                                            .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                            .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                            .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                            .var ⟨"X86ISA", "START-RIP"⟩,
                                                                            .var ⟨"X86ISA", "PROC-MODE"⟩]))
                                                                        (RawArgs.ofList [
                                                                          .call ⟨"X86ISA", "!EVEX-PREFIXES->BYTE0$INLINE"⟩
                                                                            (RawArgs.ofList [
                                                                              .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                                              .quote (.integer (0))]),
                                                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                          .var ⟨"X86ISA", "START-RIP"⟩,
                                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                          .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                          .var ⟨"X86ISA", "X86"⟩,
                                                                          .var ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩])))
                                                                    (RawArgs.ofList [
                                                                      .call ⟨"ACL2", "MV-NTH"⟩
                                                                        (RawArgs.ofList [
                                                                          .quote (.integer (0)),
                                                                          .var ⟨"ACL2", "MV"⟩]),
                                                                      .call ⟨"ACL2", "MV-NTH"⟩
                                                                        (RawArgs.ofList [
                                                                          .quote (.integer (1)),
                                                                          .var ⟨"ACL2", "MV"⟩]),
                                                                      .var ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩,
                                                                      .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                      .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                      .var ⟨"X86ISA", "START-RIP"⟩,
                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                      .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                                      .var ⟨"ACL2", "CTX"⟩,
                                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                                  (RawArgs.ofList [
                                                                    .call ⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩
                                                                      (RawArgs.ofList [
                                                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                        .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                        .quote (.integer (1)),
                                                                        .var ⟨"X86ISA", "X86"⟩]),
                                                                    .var ⟨"X86ISA", "BOUND-DISTINGUISHING-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                    .var ⟨"X86ISA", "START-RIP"⟩,
                                                                    .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                    .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                                    .var ⟨"ACL2", "CTX"⟩,
                                                                    .var ⟨"X86ISA", "X86"⟩]))
                                                                (.lambda [⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩, ⟨"X86ISA", "EVEX-BYTE0?"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                                  (.lambda [⟨"X86ISA", "MODR/M?"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩, ⟨"X86ISA", "EVEX-BYTE0?"⟩, ⟨"X86ISA", "VEX-BYTE0?"⟩]
                                                                    (.lambda [⟨"ACL2", "MV"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "MODR/M?"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩]
                                                                      (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) MODR/M)"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "MODR/M?"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩]
                                                                        (.lambda [⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "MODR/M?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "FLG"⟩]
                                                                          (.ite
                                                                            (.var ⟨"X86ISA", "FLG"⟩)
                                                                            (.call ⟨"X86ISA", "!MS"⟩
                                                                              (RawArgs.ofList [
                                                                                .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                                  (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                        (RawArgs.ofList [
                                                                                          .var ⟨"ACL2", "CTX"⟩,
                                                                                          .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                              .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                (RawArgs.ofList [
                                                                                                  .call ⟨"X86ISA", "RIP"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .var ⟨"X86ISA", "X86"⟩]),
                                                                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .quote (.symbol ⟨"KEYWORD", "MODR/M-BYTE-READ-ERROR"⟩),
                                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                        (RawArgs.ofList [
                                                                                                          .var ⟨"X86ISA", "FLG"⟩,
                                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                                      .var ⟨"X86ISA", "ERP"⟩]))
                                                                                  (RawArgs.ofList [
                                                                                    .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                    .var ⟨"X86ISA", "FLG"⟩,
                                                                                    .var ⟨"X86ISA", "X86"⟩,
                                                                                    .var ⟨"ACL2", "CTX"⟩]),
                                                                                .var ⟨"X86ISA", "X86"⟩]))
                                                                            (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "MODR/M?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                              (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "MODR/M?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                                (.ite
                                                                                  (.var ⟨"X86ISA", "FLG"⟩)
                                                                                  (.call ⟨"X86ISA", "!MS"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                                        (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                          (RawArgs.ofList [
                                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .var ⟨"ACL2", "CTX"⟩,
                                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                  (RawArgs.ofList [
                                                                                                    .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                      (RawArgs.ofList [
                                                                                                        .call ⟨"X86ISA", "RIP"⟩
                                                                                                          (RawArgs.ofList [
                                                                                                            .var ⟨"X86ISA", "X86"⟩]),
                                                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                          (RawArgs.ofList [
                                                                                                            .quote (.symbol ⟨"KEYWORD", "INCREMENT-ERROR"⟩),
                                                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                              (RawArgs.ofList [
                                                                                                                .var ⟨"X86ISA", "FLG"⟩,
                                                                                                                .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                                            .var ⟨"X86ISA", "ERP"⟩]))
                                                                                        (RawArgs.ofList [
                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                          .var ⟨"X86ISA", "FLG"⟩,
                                                                                          .var ⟨"X86ISA", "X86"⟩,
                                                                                          .var ⟨"ACL2", "CTX"⟩]),
                                                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                                                  (.lambda [⟨"X86ISA", "SIB?"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                                                    (.lambda [⟨"ACL2", "MV"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "SIB?"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩]
                                                                                      (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) SIB)"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "SIB?"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩]
                                                                                        (.lambda [⟨"X86ISA", "SIB"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"X86ISA", "SIB?"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "FLG"⟩]
                                                                                          (.ite
                                                                                            (.var ⟨"X86ISA", "FLG"⟩)
                                                                                            (.call ⟨"X86ISA", "!MS"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                                                  (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                        (RawArgs.ofList [
                                                                                                          .var ⟨"ACL2", "CTX"⟩,
                                                                                                          .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                            (RawArgs.ofList [
                                                                                                              .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                                              .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                (RawArgs.ofList [
                                                                                                                  .call ⟨"X86ISA", "RIP"⟩
                                                                                                                    (RawArgs.ofList [
                                                                                                                      .var ⟨"X86ISA", "X86"⟩]),
                                                                                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                    (RawArgs.ofList [
                                                                                                                      .quote (.symbol ⟨"KEYWORD", "SIB-BYTE-READ-ERROR"⟩),
                                                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                        (RawArgs.ofList [
                                                                                                                          .var ⟨"X86ISA", "FLG"⟩,
                                                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                                                      .var ⟨"X86ISA", "ERP"⟩]))
                                                                                                  (RawArgs.ofList [
                                                                                                    .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                                    .var ⟨"X86ISA", "FLG"⟩,
                                                                                                    .var ⟨"X86ISA", "X86"⟩,
                                                                                                    .var ⟨"ACL2", "CTX"⟩]),
                                                                                                .var ⟨"X86ISA", "X86"⟩]))
                                                                                            (.lambda [⟨"ACL2", "MV"⟩, ⟨"X86ISA", "SIB"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                                              (.lambda [⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "TEMP-RIP"⟩, ⟨"X86ISA", "SIB"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "OPCODE-BYTE"⟩, ⟨"X86ISA", "REX-BYTE"⟩, ⟨"X86ISA", "PREFIXES"⟩, ⟨"X86ISA", "START-RIP"⟩, ⟨"X86ISA", "PROC-MODE"⟩, ⟨"ACL2", "CTX"⟩, ⟨"X86ISA", "X86"⟩]
                                                                                                (.ite
                                                                                                  (.var ⟨"X86ISA", "FLG"⟩)
                                                                                                  (.call ⟨"X86ISA", "!MS"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .lambda [⟨"X86ISA", "ERP"⟩, ⟨"X86ISA", "FLG"⟩, ⟨"X86ISA", "X86"⟩, ⟨"ACL2", "CTX"⟩]
                                                                                                        (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                          (RawArgs.ofList [
                                                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                              (RawArgs.ofList [
                                                                                                                .var ⟨"ACL2", "CTX"⟩,
                                                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                  (RawArgs.ofList [
                                                                                                                    .quote (.symbol ⟨"KEYWORD", "RIP"⟩),
                                                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                      (RawArgs.ofList [
                                                                                                                        .call ⟨"X86ISA", "RIP"⟩
                                                                                                                          (RawArgs.ofList [
                                                                                                                            .var ⟨"X86ISA", "X86"⟩]),
                                                                                                                        .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                          (RawArgs.ofList [
                                                                                                                            .quote (.symbol ⟨"KEYWORD", "INCREMENT-ERROR"⟩),
                                                                                                                            .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                                              (RawArgs.ofList [
                                                                                                                                .var ⟨"X86ISA", "FLG"⟩,
                                                                                                                                .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])])]),
                                                                                                            .var ⟨"X86ISA", "ERP"⟩]))
                                                                                                        (RawArgs.ofList [
                                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                                          .var ⟨"X86ISA", "FLG"⟩,
                                                                                                          .var ⟨"X86ISA", "X86"⟩,
                                                                                                          .var ⟨"ACL2", "CTX"⟩]),
                                                                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                                                                  (.call ⟨"X86ISA", "ONE-BYTE-OPCODE-EXECUTE"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                                      .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                                      .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                                      .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                                      .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                                      .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                                      .var ⟨"X86ISA", "SIB"⟩,
                                                                                                      .var ⟨"X86ISA", "X86"⟩])))
                                                                                                (RawArgs.ofList [
                                                                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .quote (.integer (0)),
                                                                                                      .var ⟨"ACL2", "MV"⟩]),
                                                                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .quote (.integer (1)),
                                                                                                      .var ⟨"ACL2", "MV"⟩]),
                                                                                                  .var ⟨"X86ISA", "SIB"⟩,
                                                                                                  .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                                  .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                                  .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                                  .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                                  .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                                  .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                                  .var ⟨"ACL2", "CTX"⟩,
                                                                                                  .var ⟨"X86ISA", "X86"⟩]))
                                                                                              (RawArgs.ofList [
                                                                                                .ite
                                                                                                  (.var ⟨"X86ISA", "SIB?"⟩)
                                                                                                  (.call ⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                                      .quote (.integer (1)),
                                                                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                                                                  (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                        (RawArgs.ofList [
                                                                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])),
                                                                                                .var ⟨"X86ISA", "SIB"⟩,
                                                                                                .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                                .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                                .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                                .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                                .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                                .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                                .var ⟨"ACL2", "CTX"⟩,
                                                                                                .var ⟨"X86ISA", "X86"⟩])))
                                                                                          (RawArgs.ofList [
                                                                                            .var ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) SIB)"⟩,
                                                                                            .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                            .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                            .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                            .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                            .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                            .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                            .var ⟨"X86ISA", "SIB?"⟩,
                                                                                            .var ⟨"ACL2", "CTX"⟩,
                                                                                            .var ⟨"X86ISA", "X86"⟩,
                                                                                            .var ⟨"X86ISA", "FLG"⟩]))
                                                                                        (RawArgs.ofList [
                                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .quote (.integer (0)),
                                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .quote (.integer (1)),
                                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .quote (.integer (2)),
                                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                                          .var ⟨"ACL2", "CTX"⟩,
                                                                                          .var ⟨"X86ISA", "SIB?"⟩,
                                                                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                          .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                          .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                          .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                          .var ⟨"X86ISA", "START-RIP"⟩]))
                                                                                      (RawArgs.ofList [
                                                                                        .ite
                                                                                          (.var ⟨"X86ISA", "SIB?"⟩)
                                                                                          (.call ⟨"X86ISA", "RME08$INLINE"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                              .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                              .quote (.integer (1)),
                                                                                              .quote (.symbol ⟨"KEYWORD", "X"⟩),
                                                                                              .var ⟨"X86ISA", "X86"⟩]))
                                                                                          (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                            (RawArgs.ofList [
                                                                                              .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                              .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                (RawArgs.ofList [
                                                                                                  .quote (.integer (0)),
                                                                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .var ⟨"X86ISA", "X86"⟩,
                                                                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])),
                                                                                        .var ⟨"ACL2", "CTX"⟩,
                                                                                        .var ⟨"X86ISA", "SIB?"⟩,
                                                                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                        .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                        .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                        .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                        .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                        .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                        .var ⟨"X86ISA", "START-RIP"⟩]))
                                                                                    (RawArgs.ofList [
                                                                                      .ite
                                                                                        (.var ⟨"X86ISA", "MODR/M?"⟩)
                                                                                        (.lambda [⟨"X86ISA", "P4?"⟩, ⟨"X86ISA", "MODR/M"⟩, ⟨"X86ISA", "X86"⟩, ⟨"X86ISA", "PROC-MODE"⟩]
                                                                                          (.lambda [⟨"X86ISA", "16-BIT-ADDRESSP"⟩, ⟨"X86ISA", "MODR/M"⟩]
                                                                                            (.call ⟨"X86ISA", "X86-DECODE-SIB-P"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                                .var ⟨"X86ISA", "16-BIT-ADDRESSP"⟩]))
                                                                                            (RawArgs.ofList [
                                                                                              .call ⟨"COMMON-LISP", "EQL"⟩
                                                                                                (RawArgs.ofList [
                                                                                                  .quote (.integer (2)),
                                                                                                  .call ⟨"X86ISA", "SELECT-ADDRESS-SIZE$INLINE"⟩
                                                                                                    (RawArgs.ofList [
                                                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                                      .var ⟨"X86ISA", "P4?"⟩,
                                                                                                      .var ⟨"X86ISA", "X86"⟩])]),
                                                                                              .var ⟨"X86ISA", "MODR/M"⟩]))
                                                                                          (RawArgs.ofList [
                                                                                            .call ⟨"COMMON-LISP", "EQL"⟩
                                                                                              (RawArgs.ofList [
                                                                                                .quote (.integer (103)),
                                                                                                .call ⟨"X86ISA", "PREFIXES->ADR$INLINE"⟩
                                                                                                  (RawArgs.ofList [
                                                                                                    .var ⟨"X86ISA", "PREFIXES"⟩])]),
                                                                                            .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                            .var ⟨"X86ISA", "X86"⟩,
                                                                                            .var ⟨"X86ISA", "PROC-MODE"⟩]))
                                                                                        (.quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)),
                                                                                      .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                      .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                      .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                      .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                      .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                      .var ⟨"ACL2", "CTX"⟩,
                                                                                      .var ⟨"X86ISA", "X86"⟩,
                                                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩])))
                                                                                (RawArgs.ofList [
                                                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .quote (.integer (0)),
                                                                                      .var ⟨"ACL2", "MV"⟩]),
                                                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .quote (.integer (1)),
                                                                                      .var ⟨"ACL2", "MV"⟩]),
                                                                                  .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                  .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                  .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                  .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                  .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                  .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                  .var ⟨"X86ISA", "MODR/M?"⟩,
                                                                                  .var ⟨"ACL2", "CTX"⟩,
                                                                                  .var ⟨"X86ISA", "X86"⟩]))
                                                                              (RawArgs.ofList [
                                                                                .ite
                                                                                  (.var ⟨"X86ISA", "MODR/M?"⟩)
                                                                                  (.call ⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                      .quote (.integer (1)),
                                                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                                                  (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                        (RawArgs.ofList [
                                                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])),
                                                                                .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                                .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                                .var ⟨"X86ISA", "START-RIP"⟩,
                                                                                .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                .var ⟨"X86ISA", "MODR/M"⟩,
                                                                                .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                                .var ⟨"X86ISA", "MODR/M?"⟩,
                                                                                .var ⟨"ACL2", "CTX"⟩,
                                                                                .var ⟨"X86ISA", "X86"⟩])))
                                                                          (RawArgs.ofList [
                                                                            .var ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) MODR/M)"⟩,
                                                                            .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                            .var ⟨"X86ISA", "START-RIP"⟩,
                                                                            .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                            .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                            .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                            .var ⟨"X86ISA", "MODR/M?"⟩,
                                                                            .var ⟨"ACL2", "CTX"⟩,
                                                                            .var ⟨"X86ISA", "X86"⟩,
                                                                            .var ⟨"X86ISA", "FLG"⟩]))
                                                                        (RawArgs.ofList [
                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                            (RawArgs.ofList [
                                                                              .quote (.integer (0)),
                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                            (RawArgs.ofList [
                                                                              .quote (.integer (1)),
                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                          .call ⟨"ACL2", "MV-NTH"⟩
                                                                            (RawArgs.ofList [
                                                                              .quote (.integer (2)),
                                                                              .var ⟨"ACL2", "MV"⟩]),
                                                                          .var ⟨"ACL2", "CTX"⟩,
                                                                          .var ⟨"X86ISA", "MODR/M?"⟩,
                                                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                          .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                          .var ⟨"X86ISA", "START-RIP"⟩,
                                                                          .var ⟨"X86ISA", "PREFIXES"⟩]))
                                                                      (RawArgs.ofList [
                                                                        .ite
                                                                          (.var ⟨"X86ISA", "MODR/M?"⟩)
                                                                          (.ite
                                                                            (.ite
                                                                              (.var ⟨"X86ISA", "VEX-BYTE0?"⟩)
                                                                              (.var ⟨"X86ISA", "VEX-BYTE0?"⟩)
                                                                              (.var ⟨"X86ISA", "EVEX-BYTE0?"⟩))
                                                                            (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                              (RawArgs.ofList [
                                                                                .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                                .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                  (RawArgs.ofList [
                                                                                    .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                                                    .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                      (RawArgs.ofList [
                                                                                        .var ⟨"X86ISA", "X86"⟩,
                                                                                        .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])]))
                                                                            (.call ⟨"X86ISA", "RME08$INLINE"⟩
                                                                              (RawArgs.ofList [
                                                                                .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                                .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                                .quote (.integer (1)),
                                                                                .quote (.symbol ⟨"KEYWORD", "X"⟩),
                                                                                .var ⟨"X86ISA", "X86"⟩])))
                                                                          (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                            (RawArgs.ofList [
                                                                              .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                              .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                (RawArgs.ofList [
                                                                                  .quote (.integer (0)),
                                                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                                                    (RawArgs.ofList [
                                                                                      .var ⟨"X86ISA", "X86"⟩,
                                                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])),
                                                                        .var ⟨"ACL2", "CTX"⟩,
                                                                        .var ⟨"X86ISA", "MODR/M?"⟩,
                                                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                        .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                        .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                        .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                        .var ⟨"X86ISA", "START-RIP"⟩,
                                                                        .var ⟨"X86ISA", "PREFIXES"⟩]))
                                                                    (RawArgs.ofList [
                                                                      .call ⟨"X86ISA", "ONE-BYTE-OPCODE-MODR/M-P$INLINE"⟩
                                                                        (RawArgs.ofList [
                                                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                          .var ⟨"X86ISA", "OPCODE-BYTE"⟩]),
                                                                      .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                      .var ⟨"X86ISA", "START-RIP"⟩,
                                                                      .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                      .var ⟨"X86ISA", "OPCODE-BYTE"⟩,
                                                                      .var ⟨"ACL2", "CTX"⟩,
                                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                      .var ⟨"X86ISA", "X86"⟩,
                                                                      .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                                      .var ⟨"X86ISA", "EVEX-BYTE0?"⟩,
                                                                      .var ⟨"X86ISA", "VEX-BYTE0?"⟩]))
                                                                  (RawArgs.ofList [
                                                                    .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                                    .var ⟨"X86ISA", "EVEX-BYTE0?"⟩,
                                                                    .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "X86"⟩,
                                                                    .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                    .var ⟨"ACL2", "CTX"⟩,
                                                                    .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                                    .var ⟨"X86ISA", "START-RIP"⟩,
                                                                    .var ⟨"X86ISA", "PREFIXES"⟩,
                                                                    .var ⟨"X86ISA", "PROC-MODE"⟩]))))
                                                            (RawArgs.ofList [
                                                              .call ⟨"ACL2", "MV-NTH"⟩
                                                                (RawArgs.ofList [
                                                                  .quote (.integer (0)),
                                                                  .var ⟨"ACL2", "MV"⟩]),
                                                              .call ⟨"ACL2", "MV-NTH"⟩
                                                                (RawArgs.ofList [
                                                                  .quote (.integer (1)),
                                                                  .var ⟨"ACL2", "MV"⟩]),
                                                              .call ⟨"ACL2", "MV-NTH"⟩
                                                                (RawArgs.ofList [
                                                                  .quote (.integer (2)),
                                                                  .var ⟨"ACL2", "MV"⟩]),
                                                              .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                              .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                              .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                              .var ⟨"X86ISA", "START-RIP"⟩,
                                                              .var ⟨"X86ISA", "PREFIXES"⟩,
                                                              .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                              .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                              .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                              .var ⟨"X86ISA", "EVEX-BYTE0?"⟩,
                                                              .var ⟨"ACL2", "CTX"⟩]))
                                                          (RawArgs.ofList [
                                                            .ite
                                                              (.var ⟨"X86ISA", "EVEX-BYTE0?"⟩)
                                                              (.call ⟨"X86ISA", "RME08$INLINE"⟩
                                                                (RawArgs.ofList [
                                                                  .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                                  .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                                  .quote (.integer (1)),
                                                                  .quote (.symbol ⟨"KEYWORD", "X"⟩),
                                                                  .var ⟨"X86ISA", "X86"⟩]))
                                                              (.call ⟨"COMMON-LISP", "CONS"⟩
                                                                (RawArgs.ofList [
                                                                  .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                                  .call ⟨"COMMON-LISP", "CONS"⟩
                                                                    (RawArgs.ofList [
                                                                      .quote (.integer (0)),
                                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                                        (RawArgs.ofList [
                                                                          .var ⟨"X86ISA", "X86"⟩,
                                                                          .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])),
                                                            .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                            .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                            .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                            .var ⟨"X86ISA", "START-RIP"⟩,
                                                            .var ⟨"X86ISA", "PREFIXES"⟩,
                                                            .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                            .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                            .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                            .var ⟨"X86ISA", "EVEX-BYTE0?"⟩,
                                                            .var ⟨"ACL2", "CTX"⟩]))
                                                        (RawArgs.ofList [
                                                          .call ⟨"COMMON-LISP", "EQUAL"⟩
                                                            (RawArgs.ofList [
                                                              .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                              .quote (.integer (98))]),
                                                          .var ⟨"ACL2", "CTX"⟩,
                                                          .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                          .var ⟨"X86ISA", "PREFIXES"⟩,
                                                          .var ⟨"X86ISA", "START-RIP"⟩,
                                                          .var ⟨"X86ISA", "OPCODE/EVEX-BYTE"⟩,
                                                          .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                          .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                          .var ⟨"X86ISA", "X86"⟩,
                                                          .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                          .var ⟨"X86ISA", "PROC-MODE"⟩]))
                                                      (RawArgs.ofList [
                                                        .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                        .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                        .var ⟨"X86ISA", "X86"⟩,
                                                        .var ⟨"X86ISA", "LES/LDS-DISTINGUISHING-BYTE"⟩,
                                                        .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                        .var ⟨"X86ISA", "START-RIP"⟩,
                                                        .var ⟨"X86ISA", "PREFIXES"⟩,
                                                        .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                        .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                        .var ⟨"ACL2", "CTX"⟩]))))
                                                (RawArgs.ofList [
                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                    (RawArgs.ofList [
                                                      .quote (.integer (0)),
                                                      .var ⟨"ACL2", "MV"⟩]),
                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                    (RawArgs.ofList [
                                                      .quote (.integer (1)),
                                                      .var ⟨"ACL2", "MV"⟩]),
                                                  .call ⟨"ACL2", "MV-NTH"⟩
                                                    (RawArgs.ofList [
                                                      .quote (.integer (2)),
                                                      .var ⟨"ACL2", "MV"⟩]),
                                                  .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                  .var ⟨"X86ISA", "START-RIP"⟩,
                                                  .var ⟨"X86ISA", "PREFIXES"⟩,
                                                  .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                  .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                  .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                  .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                  .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                  .var ⟨"ACL2", "CTX"⟩]))
                                              (RawArgs.ofList [
                                                .ite
                                                  (.var ⟨"X86ISA", "VEX-BYTE0?"⟩)
                                                  (.call ⟨"X86ISA", "RME08$INLINE"⟩
                                                    (RawArgs.ofList [
                                                      .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                      .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                      .quote (.integer (1)),
                                                      .quote (.symbol ⟨"KEYWORD", "X"⟩),
                                                      .var ⟨"X86ISA", "X86"⟩]))
                                                  (.call ⟨"COMMON-LISP", "CONS"⟩
                                                    (RawArgs.ofList [
                                                      .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩),
                                                      .call ⟨"COMMON-LISP", "CONS"⟩
                                                        (RawArgs.ofList [
                                                          .quote (.integer (0)),
                                                          .call ⟨"COMMON-LISP", "CONS"⟩
                                                            (RawArgs.ofList [
                                                              .var ⟨"X86ISA", "X86"⟩,
                                                              .quote (.symbol ⟨"COMMON-LISP", "NIL"⟩)])])])),
                                                .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                .var ⟨"X86ISA", "START-RIP"⟩,
                                                .var ⟨"X86ISA", "PREFIXES"⟩,
                                                .var ⟨"X86ISA", "REX-BYTE"⟩,
                                                .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                                .var ⟨"X86ISA", "PROC-MODE"⟩,
                                                .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                                .var ⟨"X86ISA", "VEX-BYTE0?"⟩,
                                                .var ⟨"ACL2", "CTX"⟩]))
                                            (RawArgs.ofList [
                                              .ite
                                                (.call ⟨"COMMON-LISP", "EQUAL"⟩
                                                  (RawArgs.ofList [
                                                    .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                    .quote (.integer (197))]))
                                                (.call ⟨"COMMON-LISP", "EQUAL"⟩
                                                  (RawArgs.ofList [
                                                    .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                    .quote (.integer (197))]))
                                                (.call ⟨"COMMON-LISP", "EQUAL"⟩
                                                  (RawArgs.ofList [
                                                    .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                                    .quote (.integer (196))])),
                                              .var ⟨"ACL2", "CTX"⟩,
                                              .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                              .var ⟨"X86ISA", "REX-BYTE"⟩,
                                              .var ⟨"X86ISA", "PREFIXES"⟩,
                                              .var ⟨"X86ISA", "START-RIP"⟩,
                                              .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                              .var ⟨"X86ISA", "X86"⟩,
                                              .var ⟨"X86ISA", "TEMP-RIP"⟩,
                                              .var ⟨"X86ISA", "PROC-MODE"⟩])))
                                        (RawArgs.ofList [
                                          .call ⟨"ACL2", "MV-NTH"⟩
                                            (RawArgs.ofList [
                                              .quote (.integer (0)),
                                              .var ⟨"ACL2", "MV"⟩]),
                                          .call ⟨"ACL2", "MV-NTH"⟩
                                            (RawArgs.ofList [
                                              .quote (.integer (1)),
                                              .var ⟨"ACL2", "MV"⟩]),
                                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                                          .var ⟨"X86ISA", "START-RIP"⟩,
                                          .var ⟨"X86ISA", "PREFIXES"⟩,
                                          .var ⟨"X86ISA", "REX-BYTE"⟩,
                                          .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                          .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                          .var ⟨"ACL2", "CTX"⟩,
                                          .var ⟨"X86ISA", "X86"⟩]))
                                      (RawArgs.ofList [
                                        .call ⟨"X86ISA", "ADD-TO-*IP$INLINE"⟩
                                          (RawArgs.ofList [
                                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                                            .var ⟨"X86ISA", "START-RIP"⟩,
                                            .call ⟨"ACL2", "BINARY-+"⟩
                                              (RawArgs.ofList [
                                                .quote (.integer (1)),
                                                .var ⟨"X86ISA", "PREFIX-LENGTH"⟩]),
                                            .var ⟨"X86ISA", "X86"⟩]),
                                        .var ⟨"X86ISA", "PROC-MODE"⟩,
                                        .var ⟨"X86ISA", "START-RIP"⟩,
                                        .var ⟨"X86ISA", "PREFIXES"⟩,
                                        .var ⟨"X86ISA", "REX-BYTE"⟩,
                                        .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                        .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                        .var ⟨"ACL2", "CTX"⟩,
                                        .var ⟨"X86ISA", "X86"⟩]))
                                    (RawArgs.ofList [
                                      .call ⟨"X86ISA", "PREFIXES->NUM$INLINE"⟩
                                        (RawArgs.ofList [
                                          .var ⟨"X86ISA", "PREFIXES"⟩]),
                                      .var ⟨"ACL2", "CTX"⟩,
                                      .var ⟨"X86ISA", "OPCODE/VEX/EVEX-BYTE"⟩,
                                      .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                      .var ⟨"X86ISA", "REX-BYTE"⟩,
                                      .var ⟨"X86ISA", "PREFIXES"⟩,
                                      .var ⟨"X86ISA", "X86"⟩,
                                      .var ⟨"X86ISA", "START-RIP"⟩,
                                      .var ⟨"X86ISA", "PROC-MODE"⟩]))
                                  (RawArgs.ofList [
                                    .call ⟨"X86ISA", "PREFIXES->NXT$INLINE"⟩
                                      (RawArgs.ofList [
                                        .var ⟨"X86ISA", "PREFIXES"⟩]),
                                    .var ⟨"X86ISA", "PROC-MODE"⟩,
                                    .var ⟨"X86ISA", "START-RIP"⟩,
                                    .var ⟨"X86ISA", "X86"⟩,
                                    .var ⟨"X86ISA", "REX-BYTE"⟩,
                                    .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                    .var ⟨"ACL2", "CTX"⟩,
                                    .var ⟨"X86ISA", "PREFIXES"⟩])))
                              (RawArgs.ofList [
                                .var ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) REX-BYTE)"⟩,
                                .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                                .var ⟨"X86ISA", "START-RIP"⟩,
                                .var ⟨"X86ISA", "PROC-MODE"⟩,
                                .var ⟨"X86ISA", "PREFIXES"⟩,
                                .var ⟨"ACL2", "CTX"⟩,
                                .var ⟨"X86ISA", "X86"⟩,
                                .var ⟨"X86ISA", "FLG"⟩]))
                            (RawArgs.ofList [
                              .var ⟨"ACL2", "(THE (UNSIGNED-BYTE 52) PREFIXES)"⟩,
                              .var ⟨"X86ISA", "FLG"⟩,
                              .var ⟨"X86ISA", "X86"⟩,
                              .var ⟨"ACL2", "CTX"⟩,
                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                              .var ⟨"X86ISA", "START-RIP"⟩,
                              .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                              .var ⟨"ACL2", "(THE (UNSIGNED-BYTE 8) REX-BYTE)"⟩]))
                          (RawArgs.ofList [
                            .call ⟨"ACL2", "MV-NTH"⟩
                              (RawArgs.ofList [
                                .quote (.integer (0)),
                                .var ⟨"ACL2", "MV"⟩]),
                            .call ⟨"ACL2", "MV-NTH"⟩
                              (RawArgs.ofList [
                                .quote (.integer (1)),
                                .var ⟨"ACL2", "MV"⟩]),
                            .call ⟨"ACL2", "MV-NTH"⟩
                              (RawArgs.ofList [
                                .quote (.integer (2)),
                                .var ⟨"ACL2", "MV"⟩]),
                            .call ⟨"ACL2", "MV-NTH"⟩
                              (RawArgs.ofList [
                                .quote (.integer (3)),
                                .var ⟨"ACL2", "MV"⟩]),
                            .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                            .var ⟨"X86ISA", "START-RIP"⟩,
                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                            .var ⟨"ACL2", "CTX"⟩]))
                        (RawArgs.ofList [
                          .call ⟨"X86ISA", "GET-PREFIXES"⟩
                            (RawArgs.ofList [
                              .var ⟨"X86ISA", "PROC-MODE"⟩,
                              .var ⟨"X86ISA", "START-RIP"⟩,
                              .quote (.integer (0)),
                              .quote (.integer (0)),
                              .quote (.integer (15)),
                              .var ⟨"X86ISA", "X86"⟩]),
                          .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                          .var ⟨"X86ISA", "START-RIP"⟩,
                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                          .var ⟨"ACL2", "CTX"⟩]))
                      (RawArgs.ofList [
                        .call ⟨"X86ISA", "READ-*IP$INLINE"⟩
                          (RawArgs.ofList [
                            .var ⟨"X86ISA", "PROC-MODE"⟩,
                            .var ⟨"X86ISA", "X86"⟩]),
                        .var ⟨"ACL2", "CTX"⟩,
                        .var ⟨"X86ISA", "64-BIT-MODEP"⟩,
                        .var ⟨"X86ISA", "X86"⟩,
                        .var ⟨"X86ISA", "PROC-MODE"⟩]))
                    (RawArgs.ofList [
                      .call ⟨"COMMON-LISP", "EQUAL"⟩
                        (RawArgs.ofList [
                          .var ⟨"X86ISA", "PROC-MODE"⟩,
                          .quote (.integer (0))]),
                      .var ⟨"ACL2", "CTX"⟩,
                      .var ⟨"X86ISA", "X86"⟩,
                      .var ⟨"X86ISA", "PROC-MODE"⟩]))
                  (RawArgs.ofList [
                    .call ⟨"X86ISA", "X86-OPERATION-MODE"⟩
                      (RawArgs.ofList [
                        .var ⟨"X86ISA", "X86"⟩]),
                    .var ⟨"X86ISA", "X86"⟩,
                    .var ⟨"ACL2", "CTX"⟩]))
                (RawArgs.ofList [
                  .quote (.symbol ⟨"X86ISA", "X86-FETCH-DECODE-EXECUTE"⟩),
                  .var ⟨"X86ISA", "X86"⟩]),
              .var ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION?"⟩,
              .var ⟨"X86ISA", "APP-VIEW?"⟩]))
          (RawArgs.ofList [
            .call ⟨"X86ISA", "INHIBIT-INTERRUPTS-ONE-INSTRUCTION"⟩
              (RawArgs.ofList [
                .var ⟨"X86ISA", "X86"⟩]),
            .var ⟨"X86ISA", "APP-VIEW?"⟩,
            .var ⟨"X86ISA", "X86"⟩]))
        (RawArgs.ofList [
          .call ⟨"X86ISA", "APP-VIEW"⟩
            (RawArgs.ofList [
              .var ⟨"X86ISA", "X86"⟩]),
          .var ⟨"X86ISA", "X86"⟩])))
    (RawArgs.ofList [
      .quote (.symbol ⟨"X86ISA", "X86-FETCH-DECODE-EXECUTE"⟩),
      .var ⟨"X86ISA", "X86"⟩])

end Silmaril.Logic.ACL2.X86Step
