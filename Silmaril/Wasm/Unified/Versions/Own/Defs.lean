module

public import Silmaril.Wasm.Unified.Versions.Run.Defs

/-!
# Own syntaxes as opcode algebras

The version models of `Silmaril.Wasm.Unified.Versions` (1.0, 2.0, Lime1) are reducts of the Core
3.0 model `model30`: they run Core 3.0 code. This file builds the other reading: an algebra over
the **own syntax** of a version, run with the version's **own** reduction.

* `Syn`: an own instruction type `J`, a (partial) translation `tr : J → Option Instr` into Core
  3.0 and the nested bodies `bod j` of an instruction (`block`, `loop`, `if` bodies).
* `Syn.Tr js is`: the own code `js` translates to `is`, instruction by instruction.
* `Syn.Coh`: the translation of an instruction translates its bodies to the bodies of the
  image (`Instr.bodies`), the coherence the algebra needs.
* `ownAlg L`: **the own opcode algebra** over the 3.0 opcodes: an opcode with immediates,
  block meanings `Ds` and handler table denotes the own instructions whose translation has that
  head, those immediates and handlers, and whose own bodies lie in `Ds`; sequences are sets of
  own instruction lists. `Thms` shows that the meaning of code is the preimage under `Tr` of its
  Core 3.0 meaning (`mem_evalCode`): an own instruction is read through its Core image only to
  name its opcode, never to run it.
* `ownModel L okJ beh`: the model of the 3.0 signature running own meanings with the own
  behaviours `beh` (on Core argument values, read back by the version), with own validation
  `okJ`. Its reduct to a version signature `nsig S` is the version's own model there.
* `ownBeh`: own behaviours from a configuration semantics: the arguments are own values whose
  Core reading is the input, the behaviours are read in Core values.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions.Own

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified Silmaril.Wasm.Unified.Core30

/-- An own syntax, translated into Core 3.0. -/
structure Syn where
  /-- Own instructions. -/
  J : Type
  /-- The translation into Core 3.0 (partial). -/
  tr : J → Option Instr
  /-- The nested bodies of an own instruction. -/
  bod : J → List (List J)

namespace Syn

variable (L : Syn)

/-- Own code `js` translates to Core code `is`, instruction by instruction. -/
def Tr (js : List L.J) (is : List Instr) : Prop := List.Forall₂ (fun j i => L.tr j = some i) js is

/-- **Coherence**: the bodies of an own instruction translate to the bodies of its image. -/
def Coh : Prop := ∀ j i, L.tr j = some i → List.Forall₂ L.Tr (L.bod j) i.bodies

end Syn

/-- **The own opcode algebra** of an own syntax, over the 3.0 opcodes. -/
def ownAlg (L : Syn) : Alg sig30.Op where
  I := Set L.J
  D := Set (List L.J)
  nil := {[]}
  cons A D := {l | ∃ j t, l = j :: t ∧ j ∈ A ∧ t ∈ D}
  op o imms Ds hs :=
    {j | ∃ i, L.tr j = some i ∧ head i = o.1 ∧ immsOf i = imms ∧ hdlOf i = hs ∧
      List.Forall₂ (· ∈ ·) (L.bod j) Ds}

/-- The meaning of code in the own algebra. -/
def evalOwn (L : Syn) (c : sig30.Code) : Set (List L.J) := (ownAlg L).evalCode c

/-- **The own model**: own meanings run with own behaviours `beh` and own validation `okJ`. -/
def ownModel (L : Syn) (okJ : List L.J → Prop) (beh : List L.J → UIn → Set UObs) :
    Model UIn UObs sig30 where
  alg := ownAlg L
  ok := fun (D : Set (List L.J)) => ∃ js ∈ D, okJ js
  run := fun (D : Set (List L.J)) vs => {b | ∃ js ∈ D, okJ js ∧ b ∈ beh js vs}

/-- Own behaviours from a configuration semantics `behOf` on own values `V`: the own arguments
read as the Core input `vs` (through `rd`), the behaviours read in Core values (through `rv`). -/
def ownBeh {V W : Type} (rd : V → Val) (rv : W → Val) (behOf : List V → Set (Behaviour W)) :
    UIn → Set UObs := fun vs =>
  {b | ∃ ws, ws.map rd = vs ∧ b ∈ Behaviour.mapSet rv (behOf ws)}

end Silmaril.Wasm.Unified.Versions.Own
