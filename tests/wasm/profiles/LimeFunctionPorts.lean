module

import Silmaril.Wasm.Component.Reference.Validation.FunctionPorts.Thms

open Silmaril.Wasm Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.Types
open Silmaril.Wasm.Component.Engine (CoreExternType)

private def sig : V1.FuncType := ⟨[.i32], [.i32, .i64]⟩

private def wires : Lime1.Module where
  types := [sig]
  imports := [⟨"env", "right", .func ⟨0⟩⟩, ⟨"env", "left", .func ⟨0⟩⟩]
  exports := [⟨"left-out", .func ⟨1⟩⟩, ⟨"right-out", .func ⟨0⟩⟩]

private theorem valid : Lime1.Validation.ModuleValid wires := by
  constructor
  · intro ft mem
    have exactSig : ft = sig := List.mem_singleton.mp mem
    subst ft
    trivial
  · intro entry mem
    change entry ∈ [⟨"env", "right", .func ⟨0⟩⟩, ⟨"env", "left", .func ⟨0⟩⟩] at mem
    simp at mem
    rcases mem with rfl | rfl <;> exact ⟨.func sig, rfl, trivial⟩
  · simp [wires]
  · simp [wires]
  · simp [wires]
  · simp [wires]
  · simp [wires]
  · simp [wires]
  · simp [Lime1.Validation.StartValid, wires]
  · intro entry mem
    change entry ∈ [⟨"left-out", .func ⟨1⟩⟩, ⟨"right-out", .func ⟨0⟩⟩] at mem
    simp at mem
    rcases mem with rfl | rfl <;> exact ⟨.func sig, rfl⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem funcPorts : LimeFunctionPorts wires := by
  constructor
  · intro entry mem
    change entry ∈ [⟨"env", "right", .func ⟨0⟩⟩, ⟨"env", "left", .func ⟨0⟩⟩] at mem
    simp at mem
    rcases mem with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro entry mem
    change entry ∈ [⟨"left-out", .func ⟨1⟩⟩, ⟨"right-out", .func ⟨0⟩⟩] at mem
    simp at mem
    rcases mem with rfl | rfl <;> exact ⟨_, rfl⟩

private def ordered : CoreModuleType V1.FuncType :=
  ⟨[(("env", "right"), sig), (("env", "left"), sig)], [("left-out", sig), ("right-out", sig)]⟩

example : lime1ModuleType wires = some (ordered.mapX CoreExternType.func) := rfl

example : core3ModuleType? wires.toCore = some (ordered.mapX core3OfFlat) := by
  obtain ⟨view, native, core⟩ := resolveLimeFunctionPorts valid funcPorts
  have namesAndTypes : view.mapX CoreExternType.func = ordered.mapX CoreExternType.func :=
    Option.some.inj (native.symm.trans rfl)
  have exactView : view = ordered := by
    cases view with
    | mk imports exports =>
      have liftImports := congrArg (fun ty => ty.imports.map (fun entry =>
        (entry.1, match entry.2 with | .func signature => signature | _ => sig))) namesAndTypes
      have liftExports := congrArg (fun ty => ty.exports.map (fun entry =>
        (entry.1, match entry.2 with | .func signature => signature | _ => sig))) namesAndTypes
      simp [CoreModuleType.mapX, List.map_map, Function.comp_def, ordered] at liftImports liftExports
      simp [ordered, liftImports, liftExports]
  exact core.trans (congrArg (fun ty => some (ty.mapX core3OfFlat)) exactView)

example : wires.toCore.exports.map Export.index = [.func ⟨1⟩, .func ⟨0⟩] := rfl

example : core3OfFlat sig ≠ core3OfFlat ⟨[.i32], [.i64, .i32]⟩ :=
  fun eq => (show sig ≠ ⟨[.i32], [.i64, .i32]⟩ by decide +kernel) (core3OfFlat_eq_iff.mp eq)

#print axioms resolveLimeFunctionPorts
#print axioms core3OfFlat_eq_iff
