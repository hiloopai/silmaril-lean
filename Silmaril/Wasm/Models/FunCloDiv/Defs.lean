module

public import Silmaril.Wasm.Models.FunClo.Defs

/-!
# FunClo with divergence: definitions

`Silmaril.Wasm.Models.FunClo` observes programs only where they return, and its model
`funCloModel` is restricted to programs that terminate on every argument. Here divergence is
observed too:

* `Diverges ρ e`: no fuel suffices, `eval k ρ e = none` for every `k`. For a well-typed term in
  a typed environment this is genuine non-termination, not a stuck term
  (`Silmaril.Proofs.Wasm.Models.FunCloDiv.conv_or_div` and the inversion lemmas there).
* `DivergesOn p n`: the program diverges on `n`.
* `obsAll p n`: the observations of a call, `returns [w]` with the word of the value, or
  `diverges`.
* `funCloAllModel`: FunClo as a model of the Wasm model graph on **every** accepted program
  (`Prog.Ok`), observed with divergence.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FunCloDiv

open Silmaril.Wasm (Behaviour)
open Silmaril.Wasm.Models.FunClo (Tm Val eval Prog obsWord)

/-- **The term `e` diverges** in the environment `ρ`: no fuel suffices. -/
def Diverges (ρ : List Val) (e : Tm) : Prop := ∀ k, eval k ρ e = none

/-- The program diverges on `n`. -/
def DivergesOn (p : Prog) (n : BitVec 31) : Prop := Diverges [.int n] p.body

/-- The observations of a call: the returned word, or divergence. -/
def obsAll (p : Prog) (n : BitVec 31) : Set (Behaviour (BitVec 31)) :=
  {b | (∃ v, p.Eval n v ∧ b = .returns [obsWord v]) ∨ (DivergesOn p n ∧ b = .diverges)}

/-- **FunClo as a model, with divergence**: every accepted program is in the domain. -/
def funCloAllModel : WasmModel where
  feats := micro functional
  Module := Prog
  Valid := Prog.Ok
  Pt := Prog
  Call := BitVec 31
  Obs := Behaviour (BitVec 31)
  obs := obsAll
  dom := Prog.Ok

end Silmaril.Wasm.Models.FunCloDiv
