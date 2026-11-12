module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.Instr30ZSub

/-!
# Instruction typing of the wasm-3.0 script, `Instrs_ok/sub` at a defined type

Non-vacuity of `FragOkZ.sub` beyond `Instr30Y`'s number and vector types: `dFn` is the closed
defined type `rec (sub final (func [] -> []))`.0, and `unreachable` at `[] -> [ref dFn]`, a
non-flat type, is subsumed to `[] -> [ref null func]` (`unreachableDefSub`). Core validity of
`dFn` and the subtyping `ref dFn <: ref null func` are checked by Silmaril's checkers, reduced by
the kernel (`decide`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Instr30Z

open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.Validation (instrtypeV)
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.SpecTec.Sim

/-- The closed defined type `rec (sub final (func [] -> [])).0`. -/
def dFn : DefType := .defn (.group (.cons (.sub true .nil (.func .nil .nil)) .nil)) 0

/-- `ref dFn`, a non-flat value type. -/
def refDFn : CValType := .refv (.ref false (Ty.defHeap dFn))

/-- `ref null func`. -/
def funcrefV : CValType := .refv (.ref true (.abs .func))

/-- `dFn` is valid in `{}`. -/
theorem tyOk_refDFn : TyOk ({} : TypeCtx) refDFn := TyOk.check_sound (by decide)

/-- `ref null func` is valid in `{}`. -/
theorem tyOk_funcrefV : TyOk ({} : TypeCtx) funcrefV := TyOk.check_sound (by decide)

/-- `ref dFn <: ref null func` in `{}`. -/
theorem sub_refDFn : Sub ({} : TypeCtx) refDFn funcrefV := Sub.check_sound (by decide)

/-- `unreachable` at `[] -> [ref dFn]`, subsumed to `[] -> [ref null func]`. -/
theorem fragOkZ_unreachableDefSub : FragOkZ [.unreachable] (.plain [] [funcrefV]) := by
  have hok : InstrTypeOk {} (.plain [] [refDFn]) :=
    ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ tyOk_refDFn,
      fun _ h => absurd h List.not_mem_nil⟩
  have hok' : InstrTypeOk {} (.plain [] [funcrefV]) :=
    ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ tyOk_funcrefV,
      fun _ h => absurd h List.not_mem_nil⟩
  have h₀ : FragOkZ [.unreachable] (.plain [] [refDFn]) :=
    .instr rfl ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ rfl⟩
      (.parametric (.unreachable hok))
  exact .sub h₀ ⟨fun _ h => absurd h List.not_mem_nil, fun t ht => (List.mem_singleton.1 ht) ▸ rfl⟩
    ⟨.nil, .cons sub_refDFn .nil, fun _ h => absurd h List.not_mem_nil⟩ hok hok' ⟨by decide, by decide⟩

/-- **Non-vacuity of `Instrs_ok/sub` at a non-flat type**: `unreachable` at
`[] -> [ref null func]`, derived from its typing at `[] -> [ref dFn]`, is an `Instrs_ok {}` fact of
`stepModel BI` and Core-valid. -/
theorem unreachableDefSub {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
    (host : Silmaril.Wasm.Execution.Core.HostSemantics H) :
    (Wasm30.stepModel (Round4Int.BI P hn host)).D "Instrs_ok" "%|-%:%" []
        (.tuple [Round6.RefOkV.ctxEmptyV, .list (instrsToV [.unreachable]),
          instrtypeV (.plain [] [funcrefV])]) ∧
      InstrsOk {} [.unreachable] (.plain [] [funcrefV]) :=
  ⟨fragOkZ_dd _ fragOkZ_unreachableDefSub, fragOkZ_sound fragOkZ_unreachableDefSub⟩

end Silmaril.Wasm.SpecTec.Institution.Instr30Z
