module

public import Silmaril.Wasm.SpecTec.Sim.Round7.RMRed.Defs

/-!
# Round 7, the `NoMemSimd → NoAtoms` bridge (definitions)

`RMRed.Easy` asks for `VInv.NoAtoms HStep.hAtoms (configV hn c)`: no memory SIMD atom and no
`CALL_REF` anywhere in the image. These predicates say the same of the Core configuration.

* `instrOk cr i`: no memory SIMD instruction in `i` at any depth, and no `call_ref` unless `cr`.
  `instrOk true` is `Round6.MemSimd.instrMS`.
* `AdminOk cr a`, `AdminsOk cr is`: `instrOk cr` at every instruction of the code, and a `CALL_REF`
  administrative instruction (`Admin.callRefType`) only when `cr`. `AdminsOk true` is
  `Round6.MemSimd.AdminsMS`.
* `StoreOk cr s`: `instrOk cr` at every Wasm function body of the store. `StoreOk true` is
  `Round6.MemSimd.StoreMS`.
* `NoCallRef c`: `StoreOk false` and `AdminsOk false`: no memory SIMD instruction and no
  `call_ref` anywhere in `c`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Round6.MemSimd (memSimd)

variable {H : Type}

mutual
/-- No memory SIMD instruction in `i` at any depth, and no `call_ref` unless `cr`. -/
def instrOk (cr : Bool) : Instr → Bool
  | .block _ body => instrsOk cr body
  | .loop _ body => instrsOk cr body
  | .if_ _ b₁ b₂ => instrsOk cr b₁ && instrsOk cr b₂
  | .tryTable _ _ body => instrsOk cr body
  | .callRef _ => cr
  | i => !memSimd i

/-- `instrOk` on a sequence. -/
def instrsOk (cr : Bool) : List Instr → Bool
  | [] => true
  | i :: is => instrOk cr i && instrsOk cr is
end

mutual
/-- `instrOk cr` at every instruction of an administrative instruction; a `CALL_REF`
administrative instruction only when `cr`. -/
def AdminOk (cr : Bool) : Admin → Prop
  | .plain i => instrOk cr i = true
  | .callRefType _ => cr = true
  | .label _ cont body => instrsOk cr cont = true ∧ AdminsOk cr body
  | .handler _ _ body => AdminsOk cr body
  | .frame _ _ body => AdminsOk cr body
  | _ => True

/-- `AdminOk` on a sequence. -/
def AdminsOk (cr : Bool) : List Admin → Prop
  | [] => True
  | a :: l => AdminOk cr a ∧ AdminsOk cr l
end

/-- `instrOk cr` at every Wasm function body of the store. -/
def StoreOk (cr : Bool) (s : Store H) : Prop :=
  ∀ fi ∈ s.funcs, ∀ fn, fi.code = .wasm fn → instrsOk cr fn.body = true

/-- **No memory SIMD instruction and no `call_ref` anywhere in `c`.** -/
def NoCallRef (c : Config H) : Prop := StoreOk false c.store ∧ AdminsOk false c.code

end Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms
