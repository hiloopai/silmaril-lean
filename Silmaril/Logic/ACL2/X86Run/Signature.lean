module

public import Silmaril.Logic.ACL2.Recursive.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.X86Run

open Recursive

def runName : Name := ⟨"X86ISA", "X86-RUN"⟩
def faultName : Name := ⟨"X86ISA", "FAULT"⟩
def msName : Name := ⟨"X86ISA", "MS"⟩
def stepName : Name := ⟨"X86ISA", "X86-FETCH-DECODE-EXECUTE"⟩
def zpName : Name := ⟨"ACL2", "ZP"⟩
def addName : Name := ⟨"ACL2", "BINARY-+"⟩

/-- Internal nullary encoding of the quoted integer -1. The package string is reserved for
literal encodings and is disjoint from the exported function names. -/
def minusOneName : Name := ⟨"Lean ACL2 literal", "-1"⟩

def old : Signature :=
  Signature.empty |>.add faultName 1 |>.add msName 1 |>.add stepName 1
    |>.add zpName 1 |>.add addName 2 |>.add minusOneName 0

def faultSymbol : old.Symbol 1 := ⟨faultName, rfl⟩
def msSymbol : old.Symbol 1 := ⟨msName, rfl⟩
def stepSymbol : old.Symbol 1 := ⟨stepName, rfl⟩
def zpSymbol : old.Symbol 1 := ⟨zpName, rfl⟩
def addSymbol : old.Symbol 2 := ⟨addName, rfl⟩
def minusOneSymbol : old.Symbol 0 := ⟨minusOneName, rfl⟩

def members : Signature := Signature.empty.add runName 2

def runSymbol : members.Symbol 2 := ⟨runName, rfl⟩

theorem member_arity {k : Nat} (f : members.Symbol k) : k = 2 := by
  have declared := f.property
  by_cases hf : f.val = runName <;> simp_all [members, Signature.add, Signature.empty]

def block (body : Body old members 2) : Block old where
  members := members
  fresh := by
    intro name k declared
    by_cases hn : name = runName <;> simp_all [members, Signature.add, Signature.empty]
    rfl
  body f := member_arity f ▸ body

end Silmaril.Logic.ACL2.X86Run
