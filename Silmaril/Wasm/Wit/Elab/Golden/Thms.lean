module

public import Silmaril.Wasm.Wit.Elab.Golden.Defs
public import Silmaril.Wasm.Wit.Elab.Thms

/-!
# Elaboration of the examples, as theorems

The kernel evaluates `elaborate` on the examples (`decide +kernel`); the
general theorems (`elaborate_decode`, `elaborate_world_projects`) then apply to
them:

* `wasiIo_world`: the world `imports` of `wasi:io@0.2.0` elaborates to the
  imports `error`, `poll`, `streams` (the dependencies of `streams` first) with
  the world's `@since(version = 0.2.0)`;
* `wasiIo_roundtrip`, `wasiIo_projects`: the bytes of the elaborated package
  decode to its canonical form, and its world projects back;
* `consumer_world`: the consumer's world imports `wasi:io/error`, `poll`
  implicitly before `streams`;
* `incl_elaborates`: the include test elaborates.
-/

@[expose] public section

namespace Silmaril.Wasm.Wit.Elab.Golden

open Silmaril.Wasm.Component.Binary
open Silmaril.Wasm.Wit.Project

theorem exists_of_toBool {ε α : Type} {x : Except ε α} (h : x.toBool = true) : ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

def ioB : Binary.PackageName := ⟨"wasi", "io", some "0.2.0"⟩

theorem wasiIo_world :
    (elaborate [Example.wasiIo] Example.io).toOption.map (·.1.worlds) = some [("imports",
      { imports := [.ifaceRef ⟨ioB, "error"⟩ none .unknown, .ifaceRef ⟨ioB, "poll"⟩ none .unknown,
          .ifaceRef ⟨ioB, "streams"⟩ none .unknown],
        stability := .stable "0.2.0" none })] := by
  decide +kernel

theorem wasiIo_elaborates : ∃ r, elaborate [Example.wasiIo] Example.io = .ok r :=
  exists_of_toBool (by decide +kernel)

/-- The bytes of the elaborated `wasi:io` fragment decode to its canonical form. -/
theorem wasiIo_roundtrip : ∃ P deps, elaborate [Example.wasiIo] Example.io = .ok (P, deps) ∧
    ∀ b, Binary.encodePackage deps P = .ok b → Binary.decodePackage b = .ok P.canon := by
  obtain ⟨⟨P, deps⟩, h⟩ := wasiIo_elaborates
  exact ⟨P, deps, h, fun _ hb => elaborate_decode h hb⟩

/-- The world of the elaborated `wasi:io` fragment projects back. -/
theorem wasiIo_projects : ∃ P deps, elaborate [Example.wasiIo] Example.io = .ok (P, deps) ∧
    ∀ b, Binary.encodePackage deps P = .ok b →
      ∃ c its, parse b = .ok c ∧ (project c).bind (packageItems 0) = some its ∧
        ∀ nw ∈ P.worlds, ∃ ds d, Binary.encodeWorld (P.env deps) nw.2 = .ok ds ∧ (nw.1, d) ∈ its ∧
          Bridge.wrappedWorld d = some ds ∧ Binary.decWorld ds = .ok nw.2.normalize := by
  obtain ⟨⟨P, deps⟩, h⟩ := wasiIo_elaborates
  exact ⟨P, deps, h, fun _ hb => elaborate_world_projects h hb⟩

theorem consumer_world :
    (elaborate [Example.consumer, Example.wasiIo] Example.consumer.name).toOption.map
        (fun r => r.1.worlds.map fun nw => nw.2.imports.map Binary.WorldItem.key) =
      some [["wasi:io/error@0.2.0", "wasi:io/poll@0.2.0", "wasi:io/streams@0.2.0"]] := by
  decide +kernel

theorem incl_elaborates : ∃ r, elaborate [incl] inclName = .ok r :=
  exists_of_toBool (by decide +kernel)

end Silmaril.Wasm.Wit.Elab.Golden
