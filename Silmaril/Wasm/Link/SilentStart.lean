module

public import Silmaril.Wasm.Execution.Core.Instantiation

@[expose] public section

/-! A conservative, executable recognizer for effect-free defined start bodies.
The checker is independent of a numerical profile. It deliberately requires
each temporary constant/local value to be dropped, and permits a final return.
Semantic preservation is established separately in `SilentStartSound`.
-/

namespace Silmaril.Wasm.Link.SilentStart

open Execution.Core Validation

/-- A local type with an initial value. Nullable references need no heap lookup. -/
def localDefault? : ValType → Bool
  | .num _ | .vec _ => true
  | .ref r => r.nullable

/-- The finite, nonrecursive silent body language. The returned flag records
whether the body ends in an explicit return instead of falling through. -/
def bodyResult? (locals : List ValType) : List Instr → Option Bool
  | [] => some false
  | [.return_] => some true
  | .nop :: rest => bodyResult? locals rest
  | .intConst _ _ :: .drop :: rest => bodyResult? locals rest
  | .floatConst _ _ :: .drop :: rest => bodyResult? locals rest
  | .vecConst _ :: .drop :: rest => bodyResult? locals rest
  | .localGet x :: .drop :: rest => do
      let type ← locals[x.toNat]?
      if localDefault? type then bodyResult? locals rest else none
  | _ => none

def body? (locals : List ValType) (instructions : List Instr) : Bool :=
  (bodyResult? locals instructions).isSome

def importedFunctions (m : Module) : Nat :=
  (m.imports.filter fun entry => match entry.type with | .func _ => true | _ => false).length

/-- Erase only a defined, independently checked silent start. No-start modules
are retained exactly, and no body, export, import or definition is removed. -/
def erase? (m : Module) : Option Module :=
  match m.start with
  | none => some m
  | some start => do
      if start.toNat < importedFunctions m then none else do
        let code ← m.funcs[start.toNat - importedFunctions m]?
        let tag ← (allocTypes m.types)[code.type.toNat]?
        if Expand tag (.func .nil .nil) ∧ body? code.locals code.body = true then
          some {m with start := none}
        else none

/-- Evidence comes from the actual checker, including the defined-function
offset and its closed empty-argument/empty-result signature. -/
structure Checked (m : Module) where
  start : FuncIdx
  code : Func
  tag : DefType
  startEq : m.start = some start
  defined : importedFunctions m ≤ start.toNat
  codeLookup : m.funcs[start.toNat - importedFunctions m]? = some code
  typeLookup : (allocTypes m.types)[code.type.toNat]? = some tag
  signature : Expand tag (.func .nil .nil)
  silent : body? code.locals code.body = true

theorem erase?_sound {m result : Module} (accepted : erase? m = some result) :
    (m.start = none ∧ result = m) ∨
      (Nonempty (Checked m) ∧ result = {m with start := none}) := by
  unfold erase? at accepted
  split at accepted
  · next noStart =>
    cases accepted
    exact .inl ⟨noStart, rfl⟩
  · next start hasStart =>
    split at accepted
    · cases accepted
    · next defined =>
      obtain ⟨code, hcode, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨tag, htag, accepted⟩ := Option.bind_eq_some_iff.mp accepted
      split at accepted
      · next checked =>
        cases accepted
        exact .inr ⟨⟨⟨start, code, tag, hasStart, Nat.le_of_not_gt defined,
          hcode, htag, checked.1, checked.2⟩⟩, rfl⟩
      · cases accepted

theorem erase?_output {m result : Module} (accepted : erase? m = some result) :
    result = {m with start := none} := by
  rcases erase?_sound accepted with ⟨noStart, rfl⟩ | ⟨_, rfl⟩
  · cases result; simp_all
  · rfl

end Silmaril.Wasm.Link.SilentStart
