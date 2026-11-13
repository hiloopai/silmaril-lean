module

public import Silmaril.X86.Assembly.Defs
public import Silmaril.X86.Ext.Decode
/-! A restricted native integer instruction grammar and a range-checked local
layout/encoding relation. The relation reuses existing Ext instruction encoding;
it does not add an evaluator or claim coverage of all native GNU output. -/
@[expose] public section
namespace Silmaril.Compiler.Native.Assembly
open Silmaril Silmaril.X86

inductive Statement where
  | plain (instruction : Ext.Instr)
  | jump (label : String)
  | label (name : String)
  deriving DecidableEq

def frame (offset : Nat) : Ext.Mem :=
  Ext.Mem.ofReg .rbp none (BitVec.ofInt 32 (-(offset : Int)))

/-- Register and integer lexical forms reuse the existing explicit parsers. -/
def RegToken (token : String) (register : Reg) (width : Nat) : Prop :=
  Assembly.reg? token = some (register, width)
def NatToken (token : String) (number : Nat) : Prop :=
  Assembly.natural token = .ok number
def IntTokens (tokens : List String) (number : Int) : Prop :=
  Assembly.integer tokens = .ok number

def labelLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_' || c == '.'

/-- Check a nonempty `.L` local symbol in the supported ASCII spelling subset. -/
def validLabel (name : String) : Bool :=
  match name.toList with
  | '.' :: 'L' :: first :: rest => labelLetter first &&
      rest.all (fun c => labelLetter c || ('0' ≤ c && c ≤ '9'))
  | _ => false

/-- Accepted local-symbol spelling, with a transparent exported checker. -/
def ValidLabel (name : String) : Prop := validLabel name = true

instance (name : String) : Decidable (ValidLabel name) :=
  inferInstanceAs (Decidable (validLabel name = true))

/-- Restricted instruction grammar. It selects a typed instruction rather than
wrapping equality with an emitter result. Bounds precede bit-vector conversion. -/
inductive Spells : List String → Statement → Prop where
  | push {token : String} {register : Reg} (reg : RegToken token register 64) :
      Spells ["push", token] (.plain (.push register))
  | mov {destination source : String} {d s : Reg} (dst : RegToken destination d 64) (src : RegToken source s 64) :
      Spells ["mov", destination, ",", source] (.plain (.mov .q (.reg d) s))
  | movabs {destination immediate : String} {d : Reg} {n : Nat} (dst : RegToken destination d 64) (number : NatToken immediate n)
      (range : n < 2^64) :
      Spells ["movabs", destination, ",", immediate] (.plain (.movabs d (BitVec.ofNat 64 n)))
  | store {source offset : String} {s : Reg} {n : Nat} (src : RegToken source s 64) (number : NatToken offset n) (range : n ≤ 2^31) :
      Spells ["mov", "QWORD", "PTR", "[", "rbp", "-", offset, "]", ",", source]
        (.plain (.mov .q (.mem (frame n)) s))
  | load {destination offset : String} {d : Reg} {n : Nat} (dst : RegToken destination d 64) (number : NatToken offset n) (range : n ≤ 2^31) :
      Spells ["mov", destination, ",", "QWORD", "PTR", "[", "rbp", "-", offset, "]"]
        (.plain (.load .q d (frame n)))
  | movsxd {destination source : String} {d s : Reg} (dst : RegToken destination d 64) (src : RegToken source s 32) :
      Spells ["movsxd", destination, ",", source] (.plain (.movsxd d (.reg s)))
  | aluI8 {operation destination : String} {immediate : List String}
      {op : AluOp} {d : Reg} {n : Int} (mnemonic : Assembly.alu? operation = some op) (reg : RegToken destination d 64)
      (number : IntTokens immediate n) (low : -128 ≤ n) (high : n < 128) :
      Spells (operation :: destination :: "," :: immediate)
        (.plain (.aluI8 .q op (.reg d) (BitVec.ofInt 8 n)))
  | jump {name : String} (valid : ValidLabel name) : Spells ["jmp", name] (.jump name)
  | label {name : String} (valid : ValidLabel name) : Spells [name ++ ":"] (.label name)
  | leave : Spells ["leave"] (.plain .leave)
  | ret : Spells ["ret"] (.plain .ret)

inductive Lines : List (List String) → List Statement → Prop where
  | nil : Lines [] []
  | blank {lines : List (List String)} {statements : List Statement}
      (rest : Lines lines statements) : Lines ([] :: lines) statements
  | cons {line : List String} {statement : Statement}
      {lines : List (List String)} {statements : List Statement}
      (head : Spells line statement) (rest : Lines lines statements) :
      Lines (line :: lines) (statement :: statements)

def Parses (source : String) (statements : List Statement) : Prop :=
  Lines ((Assembly.split '\n' source.toList).map (fun chars => Assembly.tokenizeChars chars [] []))
    statements

/-- A finite symbol table, checked at each declaration and branch use. -/
abbrev Labels := String → Option Nat

def displacement (target next : Nat) : Int := (target : Int) - next

def Fits (width : Nat) (value : Int) : Prop :=
  -2^(width-1) ≤ value ∧ value < 2^(width-1)

/-- Each rule lays out one actual typed instruction, or checks a declaration.
Short and near branch choices are explicit and range checked; no branch
relaxation algorithm is assumed. -/
inductive Assembles (labels : Labels) : Nat → List Statement → List Byte → Nat → Prop where
  | nil {pc : Nat} : Assembles labels pc [] [] pc
  | label {pc : Nat} {name : String} {statements : List Statement} {bytes : List Byte} {endPc : Nat}
      (found : labels name = some pc) (rest : Assembles labels pc statements bytes endPc) :
      Assembles labels pc (.label name :: statements) bytes endPc
  | plain {pc : Nat} {instruction : Ext.Instr} {statements : List Statement} {bytes : List Byte} {endPc : Nat}
      (rest : Assembles labels (pc + (Ext.encode instruction).length) statements bytes endPc) :
      Assembles labels pc (.plain instruction :: statements) (Ext.encode instruction ++ bytes) endPc
  | jump8 {pc : Nat} {name : String} {target : Nat} {statements : List Statement} {bytes : List Byte} {endPc : Nat}
      (found : labels name = some target) (fits : Fits 8 (displacement target (pc + 2)))
      (rest : Assembles labels (pc + 2) statements bytes endPc) :
      Assembles labels pc (.jump name :: statements)
        (Ext.encode (.jmp8 (BitVec.ofInt 8 (displacement target (pc + 2)))) ++ bytes) endPc
  | jump32 {pc : Nat} {name : String} {target : Nat} {statements : List Statement} {bytes : List Byte} {endPc : Nat}
      (found : labels name = some target) (fits : Fits 32 (displacement target (pc + 5)))
      (rest : Assembles labels (pc + 5) statements bytes endPc) :
      Assembles labels pc (.jump name :: statements)
        (Ext.encode (.jmp (BitVec.ofInt 32 (displacement target (pc + 5)))) ++ bytes) endPc

/-- Every used label is declared in this unit; duplicate declarations are rejected. -/
def Local (statements : List Statement) : Prop :=
  (statements.filterMap fun | .label name => some name | _ => none).Nodup ∧
    ∀ name, .jump name ∈ statements → .label name ∈ statements

end Silmaril.Compiler.Native.Assembly
