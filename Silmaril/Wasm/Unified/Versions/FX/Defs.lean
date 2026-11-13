module

public import Silmaril.Wasm.Unified.Versions.Run.Defs
public import Silmaril.Wasm.Models.FX.Defs

/-!
# WasmFX as a model of the unified institution

WasmFX (Core 3.0 with stack switching, `Silmaril.Wasm.Models.FX`) as a signature extending the
3.0 signature and a model of it.

* `headFX`, `immsFX`, `hdlFX`: the opcodes (`contNew`, `contBind`, `resume`, `resumeThrow`,
  `suspend`, `switch`, family numbers `1000`–`1005`), immediates and handler tables (`resume` clauses `(on $tag $label)` and
  `(on $tag switch)`) of the stack-switching instructions;
* `sigFX`: **the WasmFX signature**: the 3.0 opcodes and the stack-switching opcodes, typed by
  `arityFX` (`arity30` on the 3.0 opcodes);
* `algFX`: **the FX opcode algebra**: meanings are sets of FX instructions
  (`Silmaril.Wasm.Models.FX.InstrFX`). A 3.0 opcode denotes the Core instructions with that head,
  immediates and handlers whose bodies, embedded in FX, lie in the block meanings (`.core i`),
  and for `block`, `loop` and `if` also the FX structured forms with FX bodies in the block
  meanings; a stack-switching opcode denotes the FX instructions with that head, immediates and
  handlers;
* `fxModelN P host s fx f okc`: **the WasmFX model**: CoreFX reduction
  (`Silmaril.Wasm.Models.FX.behavioursFX`, with the FX function table `fx`) of the meanings that
  pass `okc`, run on arguments from store `s` and frame `f` with no continuations.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Unified.Core30 Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Numerics (Profile)

/-- The opcode of a stack-switching instruction. -/
def headFX : FXInstr → Opcode
  | .contNew _ => .named "contNew" [1000]
  | .contBind _ _ => .named "contBind" [1001]
  | .resume _ _ => .named "resume" [1002]
  | .resumeThrow _ _ _ => .named "resumeThrow" [1003]
  | .suspend _ => .named "suspend" [1004]
  | .switch _ _ => .named "switch" [1005]

/-- The immediates of a stack-switching instruction. -/
def immsFX : FXInstr → List Imm
  | .contNew ct => [e ct]
  | .contBind ct ct' => [e ct, e ct']
  | .resume ct _ => [e ct]
  | .resumeThrow ct x _ => [e ct, e x]
  | .suspend x => [e x]
  | .switch ct x => [e ct, e x]

/-- A `resume` clause as a handler-table entry. -/
def onH : OnClause → Handler
  | .onLabel x l => ⟨"on", [e x, e l]⟩
  | .onSwitch x => ⟨"on_switch", [e x]⟩

/-- The handler table of a stack-switching instruction. -/
def hdlFX : FXInstr → List Handler
  | .resume _ hs | .resumeThrow _ _ hs => hs.map onH
  | _ => []

/-- The typing of the WasmFX opcodes, by family number (the stack-switching families are
numbered from `1000`, after the 3.0 families): `arity30` on the others. -/
def arityFX (o : Opcode) : OpTy :=
  match o with
  | .named _ (k :: _) =>
    if k = 1000 ∨ k = 1004 then ⟨1, 0, false⟩
    else if k = 1001 ∨ k = 1005 then ⟨2, 0, false⟩
    else if k = 1002 then ⟨1, 0, true⟩
    else if k = 1003 then ⟨2, 0, true⟩
    else arity30 o
  | _ => arity30 o

/-- **The WasmFX signature**: the 3.0 opcodes and the stack-switching opcodes. -/
def sigFX : FSig := ⟨Set.range head ∪ Set.range headFX, arityFX⟩

/-- FX instruction lists with heads in `A` and tails in `D`. -/
def consSetFX (A : Set InstrFX) (D : Set (List InstrFX)) : Set (List InstrFX) :=
  {l | ∃ i t, l = i :: t ∧ i ∈ A ∧ t ∈ D}

/-- The FX structured forms of `block`, `loop` and `if` with their opcode, immediates and
bodies. -/
def shapeFX : InstrFX → Option (Opcode × List Imm × List (List InstrFX))
  | .block bt b => some (.named "block" [], [e bt], [b])
  | .loop bt b => some (.named "loop" [], [e bt], [b])
  | .if_ bt b₁ b₂ => some (.named "if" [], [e bt], [b₁, b₂])
  | _ => none

/-- **The FX opcode algebra.** -/
def algFX : Alg sigFX.Op where
  I := Set InstrFX
  D := Set (List InstrFX)
  nil := {[]}
  cons := consSetFX
  op o imms Ds hs :=
    {x | (∃ i, x = .core i ∧ head i = o.1 ∧ immsOf i = imms ∧ hdlOf i = hs ∧
          List.Forall₂ (fun b D => b.map InstrFX.core ∈ D) i.bodies Ds) ∨
      (∃ j, x = .fx j ∧ headFX j = o.1 ∧ immsFX j = imms ∧ hdlFX j = hs ∧ Ds = []) ∨
      (∃ bs, shapeFX x = some (o.1, imms, bs) ∧ hs = [] ∧ List.Forall₂ (· ∈ ·) bs Ds)}

variable {H : Type}

/-- The FX configuration running FX code `is` on arguments `vs`. -/
def cfgFX (s : Store H) (f : Frame) (is : List InstrFX) (vs : UIn) : ConfigFX H :=
  ⟨s, [], f, cvals vs ++ is.map InstrFX.toAdmin⟩

/-- **The WasmFX model** at profile `P`. -/
def fxModelN (P : Profile) (host : HostSemantics H) (s : Store H) (fx : H → Option FuncFX)
    (f : Frame) (okc : List InstrFX → Prop) : Model UIn UObs sigFX where
  alg := algFX
  ok := fun (D : Set (List InstrFX)) => ∃ is ∈ D, okc is
  run := fun (D : Set (List InstrFX)) vs =>
    {b | ∃ is ∈ D, okc is ∧ b ∈ behavioursFX P host fx (cfgFX s f is vs)}

end Silmaril.Wasm.Unified.Versions
