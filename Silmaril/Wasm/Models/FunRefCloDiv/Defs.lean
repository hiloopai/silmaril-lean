module

public import Silmaril.Wasm.Models.FunRefClo.Defs

/-!
# FunRefClo with divergence: definitions

`Silmaril.Wasm.Models.FunRefClo` observes programs only where they return, and its model
`funRefCloModel` is restricted to programs that terminate on every argument. Here divergence is
observed too, as for FunClo in `Silmaril.Wasm.Models.FunCloDiv`, with the heap threaded:

* `Diverges σ ρ e`: no fuel suffices, `eval k σ ρ e = none` for every `k`, from the heap `σ`.
  For a well-typed term in a typed heap and environment this is genuine non-termination, not a
  stuck term (`Silmaril.Proofs.Wasm.Models.FunRefCloDiv.conv_or_div` and the inversion lemmas
  there). Recursion may go through the heap (a closure stored in a cell calling itself).
* `DivergesOn p n`: the program diverges on `n`, from the empty heap.
* `obsAll p n`: the observations of a call, `returns [w]` with the word of the value, or
  `diverges`.
* `funRefCloAllModel`: FunRefClo as a model of the Wasm model graph on **every** accepted
  program (`Prog.Ok`), observed with divergence.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunRefCloDiv

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Models.FunRefClo (Tm Val Heap eval Prog obsWord)

/-- **The term `e` diverges** from the heap `σ` in the environment `ρ`: no fuel suffices. -/
def Diverges (σ : Heap) (ρ : List Val) (e : Tm) : Prop := ∀ k, eval k σ ρ e = none

/-- The program diverges on `n`, from the empty heap. -/
def DivergesOn (p : Prog) (n : BitVec 31) : Prop := Diverges [] [.int n] p.body

/-- The observations of a call: the returned word, or divergence. -/
def obsAll (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | (∃ v, p.Eval n v ∧ b = .returns [obsWord v]) ∨ (DivergesOn p n ∧ b = .diverges)}

/-- **FunRefClo as a model, with divergence**: every accepted program is in the domain. -/
def funRefCloAllModel : WasmModel where
  feats := micro functionalMutGC
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := obsAll
  dom := Prog.Ok

end Silmaril.Wasm.Models.FunRefCloDiv
