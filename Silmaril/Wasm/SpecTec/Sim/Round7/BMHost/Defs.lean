module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round5.Pos.Thms

/-!
# Round 7, memory SIMD: a host call that returns memory SIMD code, at `BM` (definitions)

Round 7 reduced `Round7.MemSimd.Task.wholeStepValidRM` to `MemSimd.OpenRMRest` (and to
`MemSimd.OpenRM V`, `VInv.OpenRMRestMS`), whose `forward` field reads SpecTec's step at the
builtins `BM = withVBytes (Prims.builtins P hn host)`. The `$hostcall` of `BM` lists the outcomes
of a host call with their stores encoded by round 3's `storeV`, while the target encodes
configurations by `configVD`, whose store is `storeVD`. The two differ exactly at stores with
memory SIMD code in a function body (`Round7.MSPres.storeVD_ne_storeV`).

This topic builds a `HostFinite`, `HostOk` host whose calls add such code, and states the
`forward` field on its own.

* `mem0`: an empty memory (`i32`, no pages, no maximum).
* `msFnAt k`: a function of type `[] -> []` (`Round5.Pos.dt0`) whose module has the type `dt0`
  and the memory address `k`, and whose body is `unreachable; v128.store`. It is valid when `k`
  holds a memory, and it is memory SIMD code.
* `addMS s`: `s` with `mem0` appended to its memories and `msFnAt |s.mems|` to its functions.
* `msAddHost`: the host on `Unit` whose every call returns `addMS` of the calling store, and
  `trap`.
* `ForwardBM hn P host`: the `forward` field of `OpenRMRest`, `OpenRM` and `OpenRMRestMS`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.BMHost

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round5.Pos (dt0)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD)

/-- An empty memory: `i32`, no pages, no maximum. -/
def mem0 : MemInst := ⟨⟨.i32, ⟨0, none⟩⟩, ByteArray.empty⟩

/-- The module of `msFnAt k`: the type `dt0` and the memory address `k`. -/
def msModule (k : Nat) : ModuleInst := { types := [dt0], mems := [k] }

/-- The body of `msFnAt k`: `unreachable; v128.store` (memory 0, offset 0, alignment 0). -/
def msBody : List Instr := [.unreachable, .vecStore ⟨0⟩ ⟨0, 0⟩]

/-- A function of type `dt0` over `msModule k` with the memory SIMD body `msBody`. -/
def msFnAt (k : Nat) : FuncInst Unit :=
  { type := dt0, module := msModule k, code := .wasm ⟨⟨0⟩, [], msBody⟩ }

/-- `s` with `mem0` appended to its memories and `msFnAt |s.mems|` to its functions. -/
def addMS (s : Store Unit) : Store Unit :=
  { s with mems := s.mems ++ [mem0], funcs := s.funcs ++ [msFnAt s.mems.length] }

/-- **The host that adds memory SIMD code**: every call returns `addMS` of the calling store,
and `trap`. -/
def msAddHost : HostSemantics Unit := fun _ s _ o => o = .returned (addMS s) .trap

/-- **The `forward` field of round 7's reductions at `BM`** (`MemSimd.OpenRMRest.forward`,
`MemSimd.OpenRM.forward`, `VInv.OpenRMRestMS.forward`). -/
def ForwardBM {H : Type} (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.MemSimd.BM P hn host)) (configVD hn c) (configVD hn d')

end Silmaril.Wasm.SpecTec.Sim.Round7.BMHost
