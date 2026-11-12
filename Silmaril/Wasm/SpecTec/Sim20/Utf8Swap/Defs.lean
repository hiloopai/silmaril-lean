module

public import Silmaril.Wasm.SpecTec.Sim20.Utf8Strip.Defs

/-!
# The 2.0 `$utf8` erratum: an involutive re-encoding of export lists (definitions)

Round 7 reduced `Utf8Mono.Task.fwdU20` to leg 3, `Utf8Strip.Task.unstripStep20`, which moves a
`utf8Env20T` derivation from export-free images to images with non-empty export names. Stripping
is not injective, so a forward transfer along it says nothing backwards. Round 8 (utf8, an earlier step)
proposed an **involution** instead: a value map `φ` with `φ ∘ φ = id` that commutes with the
evaluator transfers derivations forward, and, applied to `φ v`, also backward. This header states
that route.

**The value map.** `swapV τ v` replaces the contents `u` of every record field named `EXPORTS`
by `τ u` (not recursively); everything else is kept, deeply. When `τ` is an involution so is
`swapV τ` (`Utf8Swap.swapV_swapV`).

**The V2 side.** `expConfig20 F c` replaces the export list of every module instance of `c` (the
store's function instances, the frame, every frame in the code) by `F m`. Stripping is
`expConfig20 (fun _ => [])`.

**The encoding of one configuration** (`encS`, `swapS`). Let `S` be the list of the export-list
images of the module instances of `c`, and `M` one more than the sum of their lengths. The module
`m` is re-encoded with `M + i` copies of the export `"" ↦ FUNC 0`, where `i` is the index of
`m`'s export image in `S` (`encExp20 S`). Every name of the re-encoding is empty, so it is typed
in `simEnv20`, where the round-6 forward theorem lives. `swapS S` exchanges each `u ∈ S` with
its re-encoding and fixes every other value; it is an involution (`Utf8Swap.swapS_swapS`), and
`swapV (swapS S)` takes the image of the re-encoded configuration back to the image of `c`.

**The leaf** (`Task.swapStep20`, frozen here, proved in `Sim20.XSwap`): in `utf8Env20T (storeB P)`,
`swapV τ` maps steps to steps, for every involution `τ` that keeps the `exportinst*` typing up to a
fixed amount of fuel. It is a statement about the evaluator and the declarative reading only;
`Utf8Swap.fwdU20_of_swapStep20` derives `Utf8Mono.Task.fwdU20` (and so
`Utf8Strip.Task.unstripStep20`) from it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution

/-! ## The value map -/

mutual
/-- **Re-encode the export lists**: the contents `u` of every record field named `EXPORTS`
become `τ u`; everything else is kept, deeply. -/
def swapV (τ : Value → Value) : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (swapVs τ vs)
  | .case op w => .case op (swapV τ w)
  | .struct gs => .struct (swapVf τ gs)
  | .list vs => .list (swapVs τ vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (swapV τ w))

/-- `swapV` on a list of values. -/
def swapVs (τ : Value → Value) : List Value → List Value
  | [] => []
  | v :: vs => swapV τ v :: swapVs τ vs

/-- `swapV` on the fields of a record: an `EXPORTS` field `u` becomes `τ u`. -/
def swapVf (τ : Value → Value) : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, if a = "EXPORTS" then τ v else swapV τ v) :: swapVf τ gs
end

/-- The IL type of an export list, `exportinst*`. -/
def exportsT : IL.Typ := .iterT (.varT "exportinst" []) .list

/-! ## The leaf -/

open Silmaril.Wasm.SpecTec.Sim20.Utf8Mono (utf8Env20T)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)

/-- **SpecTec's 2.0 `Step` is invariant under re-encoding export lists** (frozen leaf, proved as
`XSwap.swapStep20_holds`): in `utf8Env20T (storeB P)`, for every involution `τ` that keeps
`exportinst*` typing with a bounded loss of fuel `K` (in the empty scope, where a `moduleinst`
field is typed), `swapV τ` maps steps to steps. Since `swapV τ` is then an involution, this is an
equivalence. -/
def Task.swapStep20 : Prop :=
  ∀ (P : Silmaril.Wasm.Numerics.Profile) (τ : Value → Value), (∀ u, τ (τ u) = u) →
    ∀ K : Nat, (∀ n u, hasTyp n (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT u = .ok true →
      hasTyp (n + K) (utf8Env20T (Whole.storeB P)) VarEnv.empty exportsT (τ u) = .ok true) →
    ∀ v w, SStepB (utf8Env20T (Whole.storeB P)) v w →
      SStepB (utf8Env20T (Whole.storeB P)) (swapV τ v) (swapV τ w)

/-! ## Re-encoding the export lists of a V2 configuration -/

variable {H : Type}

/-- A module instance with export list `F m`. -/
def expModule20 (F : ModuleInst → List ExportInst) (m : ModuleInst) : ModuleInst :=
  { m with exports := F m }

/-- `expModule20` on a frame's module. -/
def expFrame20 (F : ModuleInst → List ExportInst) (f : Frame) : Frame :=
  { f with module := expModule20 F f.module }

/-- `expModule20` on a function instance's module. -/
def expFI20 (F : ModuleInst → List ExportInst) (fi : FuncInst H) : FuncInst H :=
  { fi with module := expModule20 F fi.module }

/-- `expModule20` on the module of every function instance of a store. -/
def expStore20 (F : ModuleInst → List ExportInst) (s : Store H) : Store H :=
  { s with funcs := s.funcs.map (expFI20 F) }

mutual
/-- `expFrame20` on every frame inside an administrative instruction. -/
def expAdmin20 (F : ModuleInst → List ExportInst) : Admin → Admin
  | .label n cont body => .label n cont (expAdmins20 F body)
  | .frame n f body => .frame n (expFrame20 F f) (expAdmins20 F body)
  | a => a

/-- `expAdmin20` on a sequence. -/
def expAdmins20 (F : ModuleInst → List ExportInst) : List Admin → List Admin
  | [] => []
  | a :: l => expAdmin20 F a :: expAdmins20 F l
end

/-- **A configuration with every export list re-encoded by `F`.** -/
def expConfig20 (F : ModuleInst → List ExportInst) (c : Config H) : Config H :=
  ⟨expStore20 F c.store, expFrame20 F c.frame, expAdmins20 F c.code⟩

/-! ## The encoding of one configuration -/

/-- The image of an export list (the `EXPORTS` field of `Sim20.moduleInstV`). -/
def expV (l : List ExportInst) : Value :=
  .list (l.map fun e => .struct [("NAME", Sim20.nameV e.name), ("ADDR", Sim20.externAddrV e.addr)])

mutual
/-- The module instances of the frames inside an administrative instruction. -/
def adminMods20 : Admin → List ModuleInst
  | .label _ _ body => adminsMods20 body
  | .frame _ f body => f.module :: adminsMods20 body
  | _ => []

/-- `adminMods20` on a sequence. -/
def adminsMods20 : List Admin → List ModuleInst
  | [] => []
  | a :: l => adminMods20 a ++ adminsMods20 l
end

/-- **The module instances of a configuration**: of the store's function instances, the frame
and every frame in the code. -/
def mods20 (c : Config H) : List ModuleInst :=
  c.store.funcs.map (·.module) ++ c.frame.module :: adminsMods20 c.code

/-- **The export images of a configuration's module instances.** -/
def expsV20 (c : Config H) : List Value := (mods20 c).map fun m => expV m.exports

/-- The length of a list value (`0` elsewhere). -/
def vlen : Value → Nat
  | .list l => l.length
  | _ => 0

/-- One more than the total length of the values of `S`: longer than each of them. -/
def bnd (S : List Value) : Nat := (S.map vlen).sum + 1

/-- The export that the re-encoding repeats: the empty name, at function address `0`. -/
def exp0 : ExportInst := ⟨"", .func 0⟩

/-- **The re-encoding of a module's exports**: `bnd S + i` copies of `exp0`, where `i` is the
index of the module's export image in `S`. -/
def encExp20 (S : List Value) (m : ModuleInst) : List ExportInst :=
  List.replicate (bnd S + S.idxOf (expV m.exports)) exp0

/-- The re-encoding of an export image `u`, at the value level. -/
def encV (S : List Value) (u : Value) : Value := expV (List.replicate (bnd S + S.idxOf u) exp0)

/-- **The involution of one configuration**: each `u ∈ S` is exchanged with `encV S u`; every
other value is fixed. -/
def swapS (S : List Value) (v : Value) : Value :=
  if v ∈ S then encV S v else
    match S.find? (fun u => encV S u == v) with
    | some u => u
    | none => v

end Silmaril.Wasm.SpecTec.Sim20.Utf8Swap
