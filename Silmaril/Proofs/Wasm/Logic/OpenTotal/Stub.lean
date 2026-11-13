module

public import Silmaril.Proofs.Wasm.Logic.OpenTotal.Productive

/-!
# Open modules with total correctness: the total stub rule

`TFSpecAt.stub`: under the most general terminating environment
`specHostT bind Γi`, an import stub meets its import specification **totally**,
provided the specification is live (every call meeting the precondition has
some result allowed by the postcondition; otherwise `specHostT` has no outcome
and the call is stuck). Import calls in a total module proof are then
discharged with `Hoare.TSafe.call`.

A Silmaril addition (the total version of `Open.FSpecAt.stub`).
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.OpenTotal

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (decompose?)
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Open
open Silmaril.Wasm.Logic.Strategy (resultOutcome)

variable {H : Type} {P : Profile}

/-- A call that returned `r` below `vs₀` is a totally correct exit of the call
postcondition. -/
theorem tresult_exit {host : HostSemantics H} {vs₀ : List Val} {s' : Store H} {f : Frame}
    {R : Store H → Outcome → Prop} (r : Result) (hR : R s' (resultOutcome r)) :
    TSafe P host (callPost f vs₀ R) ⟨s', f, vals vs₀ ++ r.toAdmin⟩ := by
  rcases r with res | a | _
  · exact .exit (.normal (vs₀ ++ res)) (by simp [Exits, Result.toAdmin, vals])
      ⟨rfl, .inl ⟨res, rfl, hR⟩⟩
  · exact .exit (.throw a) ⟨vs₀, [], by simp [Result.toAdmin, throwing]⟩
      ⟨rfl, .inr (.inr ⟨a, rfl, hR⟩)⟩
  · exact .exit .trap ⟨vs₀, [], by simp [Result.toAdmin]⟩ ⟨rfl, .inr (.inl ⟨rfl, hR⟩)⟩

/-- **The total stub rule.** -/
theorem TFSpecAt.stub {bind : H → Nat} {Γi : Ctx H} {a : Nat} {h : H} {S : FSpec H}
    (hS : Γi (bind h) = some S)
    (hlive : ∀ s args, S.pre s args → ∃ s' r, S.post s args s' (resultOutcome r)) :
    TFSpecAt P (specHostT bind Γi) a (stubSpec a h S) := by
  rintro s args ⟨⟨fi, ps, rs, hf, hcode, he, hn⟩, hpre⟩ f vs₀ c hc
  have hd : decompose? s (vals vs₀ ++ vals args ++ [.ref (.func a), c]) =
      some ((SingleThreaded.Ctx.top [] []).wrap vs₀ [], a, h, args) :=
    decompose?_stub hc hf he hn hcode
  obtain ⟨s₀, r₀, hpost₀⟩ := hlive s args hpre
  refine .step (redex_progress (c := ⟨s, f, _⟩) hd (o := .returned s₀ r₀) ⟨S, hS, hpre, hpost₀⟩)
    fun c' hst => ?_
  rcases redex_step_inv hd hst with ⟨s', r, ⟨S', hS', -, hpost⟩, rfl⟩ | ⟨⟨-, -, -, ⟨⟩⟩, -⟩
  obtain rfl : S' = S := Option.some.inj (hS'.symm.trans hS)
  rw [stub_fill]
  exact tresult_exit r hpost

end Silmaril.Wasm.Logic.OpenTotal
