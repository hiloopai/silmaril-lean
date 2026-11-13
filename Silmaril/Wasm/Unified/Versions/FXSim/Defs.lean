module

public import Silmaril.Wasm.Models.FX.Defs

/-!
# FX code that reads as Core code

The repaired FX algebra `algFXs` (`Silmaril.Wasm.Unified.Versions.FXEq`) interprets the 3.0 opcodes
`block`, `loop` and `if` also by the FX structured forms (`InstrFX.block` etc.) with FX bodies.
On 3.0 code those bodies are again Core code or structured forms, so the FX meaning of 3.0 code
is Core code in which some structured instructions are FX ones. This module names that
relation, for source code and for administrative code, and the configurations of Core 3.0 that
the simulation of `Silmaril.Wasm.Unified.Versions.FXSim` must set aside:

* `LiftI x i`, `LiftIs`: the FX instruction `x` reads as the Core instruction `i`: `x = core i`,
  or `x` is an FX `block`, `loop` or `if` whose bodies read as the bodies of `i`;
* `LiftA a c`, `LiftAs`: the same for administrative code, with FX labels (whose continuation and
  body read as the Core label's) in place of Core labels; there are no FX frames, handlers,
  stack-switching instructions or continuation references;
* `Struct c`: the Core administrative instructions with an FX counterpart (`block`, `loop`, `if`
  and labels); `Hot c`: a label or a `return_call_ref`;
* `Doomed d cs`: Core code whose first non-value is a `return_call_ref`, or a label (nested `d`
  deep) whose body is doomed. Core pops labels around a `return_call_ref` (`return_call_ref-label`)
  and then has nowhere to go without a frame; CoreFX has no such rule for its FX labels, so the
  two semantics part there, both without a result. `Doomed` is that place.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX

mutual
/-- The FX instruction `x` reads as the Core instruction `i`. -/
inductive LiftI : InstrFX → Instr → Prop
  /-- A Core instruction. -/
  | core (i : Instr) : LiftI (.core i) i
  /-- An FX `block` with a body that reads as the Core body. -/
  | block {bt : BlockType} {b : List InstrFX} {is : List Instr} :
      LiftIs b is → LiftI (.block bt b) (.block bt is)
  /-- An FX `loop`. -/
  | loop {bt : BlockType} {b : List InstrFX} {is : List Instr} :
      LiftIs b is → LiftI (.loop bt b) (.loop bt is)
  /-- An FX `if`. -/
  | if_ {bt : BlockType} {b₁ b₂ : List InstrFX} {is₁ is₂ : List Instr} :
      LiftIs b₁ is₁ → LiftIs b₂ is₂ → LiftI (.if_ bt b₁ b₂) (.if_ bt is₁ is₂)

/-- FX code that reads as Core code, instruction by instruction. -/
inductive LiftIs : List InstrFX → List Instr → Prop
  | nil : LiftIs [] []
  | cons {x : InstrFX} {i : Instr} {l : List InstrFX} {is : List Instr} :
      LiftI x i → LiftIs l is → LiftIs (x :: l) (i :: is)
end

mutual
/-- The FX administrative instruction `a` reads as the Core administrative instruction `c`. -/
inductive LiftA : AdminFX → Admin → Prop
  /-- A Core administrative instruction. -/
  | core (c : Admin) : LiftA (.core c) c
  /-- An FX `block`. -/
  | block {bt : BlockType} {b : List InstrFX} {is : List Instr} :
      LiftIs b is → LiftA (.block bt b) (.plain (.block bt is))
  /-- An FX `loop`. -/
  | loop {bt : BlockType} {b : List InstrFX} {is : List Instr} :
      LiftIs b is → LiftA (.loop bt b) (.plain (.loop bt is))
  /-- An FX `if`. -/
  | if_ {bt : BlockType} {b₁ b₂ : List InstrFX} {is₁ is₂ : List Instr} :
      LiftIs b₁ is₁ → LiftIs b₂ is₂ → LiftA (.if_ bt b₁ b₂) (.plain (.if_ bt is₁ is₂))
  /-- An FX label whose continuation and body read as the Core label's. -/
  | label {n : Nat} {k : List InstrFX} {cont : List Instr} {es : List AdminFX}
      {cs : List Admin} : LiftIs k cont → LiftAs es cs → LiftA (.label n k es) (.label n cont cs)

/-- FX administrative code that reads as Core administrative code. -/
inductive LiftAs : List AdminFX → List Admin → Prop
  | nil : LiftAs [] []
  | cons {a : AdminFX} {c : Admin} {l : List AdminFX} {cs : List Admin} :
      LiftA a c → LiftAs l cs → LiftAs (a :: l) (c :: cs)
end

/-- Core administrative instructions with an FX counterpart: `block`, `loop`, `if`, labels. -/
def Struct : Admin → Prop
  | .plain (.block _ _) | .plain (.loop _ _) | .plain (.if_ _ _ _) | .label _ _ _ => True
  | _ => False

/-- Labels and `return_call_ref`: what a doomed configuration starts with. -/
def Hot (c : Admin) : Prop := (∃ n cont body, c = .label n cont body) ∨ c.IsReturnCallRef

/-- **Doomed Core code**: the first non-value is a `return_call_ref`, or a label `d` deep whose
body is doomed. -/
inductive Doomed : Nat → List Admin → Prop
  /-- A `return_call_ref` after values. -/
  | rcr {vs : List Val} {c : Admin} {rest : List Admin} :
      c.IsReturnCallRef → Doomed 0 (vals vs ++ c :: rest)
  /-- A label with a doomed body after values. -/
  | label {d : Nat} {vs : List Val} {n : Nat} {cont : List Instr} {body rest : List Admin} :
      Doomed d body → Doomed (d + 1) (vals vs ++ .label n cont body :: rest)

end Silmaril.Wasm.Unified.Versions
