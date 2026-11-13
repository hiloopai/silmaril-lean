module

public import Silmaril.Wasm.Component.Passes.Flatten.Defs
public import Silmaril.Wasm.Component.Contract.Defs
public import Silmaril.Wasm.Component.Laws.Defs
import Silmaril.Proofs.Wasm.Component.Laws.Env

/-!
# Flattening nested components: soundness

* `denU_flatten`: **flattening preserves the denotation** — for every core
  semantics, `(flatten c).denU C = c.denU C` — *assuming the five pairing
  laws* `PairLaws` (`Silmaril.Wasm.Component.Laws.Defs`); these are proved
  (`pairLaws`), and `denU_flatten'` is the unconditional statement. The proof (`Silmaril.Proofs.Wasm.Component.Laws.Env`) is a simulation:
  the environment of the nested IR is implemented over the flat environment
  by the substitution `σ` maintained by `flattenNodes`; a nested instance,
  whose nodes run inside the right component of a pairing, is moved out of
  the pairing by `PairLaws.gflat`, `PairLaws.hdist` and `PairLaws.psum`, and its exports
  become wiring by `PairLaws.cp`.
* `flattenT L C : nestedIR C ⟶ linkedIR C`: flattening as a verified
  translation between IRs (`Silmaril.Compile.PassAPI.Translation`);
  `flattenT' C := flattenT pairLaws C`.
* `toComponentT C : linkedIR C ⟶ nestedIR C`: the embedding of the flat IR
  (unconditional).
* `denU_specialise`: cross-component specialisation — an import served by a
  known handler (wiring programs `σ₀`, e.g. constants) is composed in
  statically: `(specialise J σ₀ c).denU C = ofHandler (implsH σ₀) ≫ c.denU C`
  (assuming `PairLaws`; unconditional: `denU_specialise'`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Compile.PassAPI

variable {M : Type} [CoreModule M]

/-- **Flattening preserves the denotation** (assuming `PairLaws`). -/
theorem denU_flatten (L : PairLaws) (C : CoreSem M) (c : Comp M) :
    (flatten c).denU C = c.denU C :=
  Silmaril.Proofs.Wasm.Component.Laws.denU_flatten L C c

theorem imports_flatten (c : Comp M) : (flatten c).imports = c.imports := by
  cases c; rfl

theorem exports_length_flatten (c : Comp M) :
    (flatten c).exports.length = c.exports.length := by
  cases c; simp [flatten]

/-- **Specialisation by a known handler** (assuming `PairLaws`): composing the
handler of `σ₀` below `c` is substituting it statically. -/
theorem denU_specialise (L : PairLaws) (C : CoreSem M) (J : Iface) {σ₀ : List Impl}
    (hσ : ScopedList J.length σ₀) (c : Comp M) (hlen : σ₀.length = c.imports.length) :
    (specialise J σ₀ c).denU C = (Strategy.ofHandler (implsH J.length σ₀)).comp (c.denU C) :=
  Silmaril.Proofs.Wasm.Component.Laws.denU_specialise L C J hσ c hlen

/-- Flattening as a verified translation (assuming `PairLaws`). -/
def flattenT (L : PairLaws) (C : CoreSem M) : nestedIR C ⟶ linkedIR C where
  run := flatten
  inv_run _ := trivial
  sound {c} _ := ⟨congrArg List.length (imports_flatten c), exports_length_flatten c,
    (denU_flatten L C c).le⟩

/-- **Flattening preserves the denotation** (unconditional). -/
theorem denU_flatten' (C : CoreSem M) (c : Comp M) : (flatten c).denU C = c.denU C :=
  denU_flatten pairLaws C c

/-- **Specialisation by a known handler** (unconditional). -/
theorem denU_specialise' (C : CoreSem M) (J : Iface) {σ₀ : List Impl}
    (hσ : ScopedList J.length σ₀) (c : Comp M) (hlen : σ₀.length = c.imports.length) :
    (specialise J σ₀ c).denU C = (Strategy.ofHandler (implsH J.length σ₀)).comp (c.denU C) :=
  denU_specialise pairLaws C J hσ c hlen

/-- Flattening as a verified translation (unconditional). -/
def flattenT' (C : CoreSem M) : nestedIR C ⟶ linkedIR C := flattenT pairLaws C

/-- The embedding of the flat IR into the nested IR, as a translation. -/
def toComponentT (C : CoreSem M) : linkedIR C ⟶ nestedIR C where
  run := Linked.toComponent
  inv_run _ := trivial
  sound {l} _ := ⟨rfl, rfl, (Linked.denU_toComponent C l).le⟩

end Silmaril.Wasm.Component
