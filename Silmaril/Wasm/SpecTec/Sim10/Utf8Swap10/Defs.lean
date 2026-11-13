module

public import Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10.Defs
public import Silmaril.Wasm.SpecTec.Sim20.Utf8Swap.Defs

/-!
# The 1.0 `$utf8` erratum: an involutive re-encoding of export lists (definitions)

The 1.0 form of `Sim20.Utf8Swap`. `expConfig10 F c` replaces the export list of every module
instance of the V1 configuration `c` (the store's defined function instances, the frame, every
frame in the code) by `F m`. The re-encoding of one configuration is round 9's 2.0 one:
`bnd S + i` copies of the export `"" ↦ FUNC 0` (`encExp10 S`), exchanged with the original by the
involution `swapS10 S`. `Utf8Swap.swapV` is the value map.

**The leaf** (`Task.swapStep10`, frozen here, proved in `Sim20.XSwap`): in
`utf8Env10T (fwdB10 nd r)`, `swapV τ` maps steps to steps, for every involution `τ` that keeps
`exportinst*` typing up to a fixed amount of fuel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst ExportInst ExternVal)
open Silmaril.Wasm.SpecTec.Sim20.Utf8Swap (swapV exportsT vlen bnd)

/-! ## The leaf -/

open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **SpecTec's 1.0 `Step` is invariant under re-encoding export lists** (frozen leaf). -/
def Task.swapStep10 : Prop :=
  ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice) (τ : Value → Value),
    (∀ u, τ (τ u) = u) → ∀ K : Nat,
    (∀ n u, hasTyp n (utf8Env10T (Whole.fwdB10 nd r)) VarEnv.empty exportsT u = .ok true →
      hasTyp (n + K) (utf8Env10T (Whole.fwdB10 nd r)) VarEnv.empty exportsT (τ u) = .ok true) →
    ∀ v w, SStepB (utf8Env10T (Whole.fwdB10 nd r)) v w →
      SStepB (utf8Env10T (Whole.fwdB10 nd r)) (swapV τ v) (swapV τ w)

/-! ## Re-encoding the export lists of a V1 configuration -/

variable {H : Type}

/-- A module instance with export list `F m`. -/
def expModule10 (F : ModuleInst → List ExportInst) (m : ModuleInst) : ModuleInst :=
  { m with exports := F m }

/-- `expModule10` on a frame's module. -/
def expFrame10 (F : ModuleInst → List ExportInst) (f : Frame) : Frame :=
  { f with module := expModule10 F f.module }

/-- `expModule10` on a defined function instance's module. -/
def expFI10 (F : ModuleInst → List ExportInst) : FuncInst V1.Func H → FuncInst V1.Func H
  | .wasm t m fn => .wasm t (expModule10 F m) fn
  | .host t h => .host t h

/-- `expModule10` on the module of every function instance of a store. -/
def expStore10 (F : ModuleInst → List ExportInst) (s : Store H) : Store H :=
  { s with funcs := s.funcs.map (expFI10 F) }

mutual
/-- `expFrame10` on every frame inside an administrative instruction. -/
def expAdmin10 (F : ModuleInst → List ExportInst) : Admin → Admin
  | .label n cont body => .label n cont (expAdmins10 F body)
  | .frame n f body => .frame n (expFrame10 F f) (expAdmins10 F body)
  | a => a

/-- `expAdmin10` on a sequence. -/
def expAdmins10 (F : ModuleInst → List ExportInst) : List Admin → List Admin
  | [] => []
  | a :: l => expAdmin10 F a :: expAdmins10 F l
end

/-- **A V1 configuration with every export list re-encoded by `F`.** -/
def expConfig10 (F : ModuleInst → List ExportInst) (c : Config H) : Config H :=
  ⟨expStore10 F c.store, expFrame10 F c.frame, expAdmins10 F c.code⟩

/-! ## The encoding of one configuration -/

/-- The image of a 1.0 export list (the `EXPORTS` field of `Sim10.moduleInstV`). -/
def expV10 (l : List ExportInst) : Value :=
  .list (l.map fun e => .struct [("NAME", Sim20.nameV e.name), ("ADDR", Sim10.externAddrV e.value)])

mutual
/-- The module instances of the frames inside an administrative instruction. -/
def adminMods10 : Admin → List ModuleInst
  | .label _ _ body => adminsMods10 body
  | .frame _ f body => f.module :: adminsMods10 body
  | _ => []

/-- `adminMods10` on a sequence. -/
def adminsMods10 : List Admin → List ModuleInst
  | [] => []
  | a :: l => adminMods10 a ++ adminsMods10 l
end

/-- The module instance of a defined function instance. -/
def fiMods10 : FuncInst V1.Func H → List ModuleInst
  | .wasm _ m _ => [m]
  | .host _ _ => []

/-- **The module instances of a V1 configuration.** -/
def mods10 (c : Config H) : List ModuleInst :=
  c.store.funcs.flatMap fiMods10 ++ c.frame.module :: adminsMods10 c.code

/-- **The export images of a configuration's module instances.** -/
def expsV10 (c : Config H) : List Value := (mods10 c).map fun m => expV10 m.exports

/-- The export that the re-encoding repeats: the empty name, at function address `0`. -/
def exp010 : ExportInst := ⟨"", .func ⟨0⟩⟩

/-- **The re-encoding of a module's exports**: `bnd S + i` copies of `exp010`. -/
def encExp10 (S : List Value) (m : ModuleInst) : List ExportInst :=
  List.replicate (bnd S + S.idxOf (expV10 m.exports)) exp010

/-- The re-encoding of an export image `u`, at the value level. -/
def encV10 (S : List Value) (u : Value) : Value := expV10 (List.replicate (bnd S + S.idxOf u) exp010)

/-- **The involution of one configuration**: each `u ∈ S` is exchanged with `encV10 S u`. -/
def swapS10 (S : List Value) (v : Value) : Value :=
  if v ∈ S then encV10 S v else
    match S.find? (fun u => encV10 S u == v) with
    | some u => u
    | none => v

end Silmaril.Wasm.SpecTec.Sim10.Utf8Swap10
