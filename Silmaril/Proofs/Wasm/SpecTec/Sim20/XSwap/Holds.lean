module

public import Silmaril.Raw.Wasm.SpecTec.Sim20.XSwap.Step

/-!
# the 2.0 `$utf8` forward theorem

* `tauOf`: an involution as an injective replacement (`XTau`); `swapX_eq_swapV`: the evaluator
  copy's `swapX` is `Utf8Swap.swapV τ`.
* **`swapStep20_holds`**: the leaf `Utf8Swap.Task.swapStep20`, from `Typ.sstepB_swap` at
  `EraseAll.hyps20`.
* **`fwdU20_holds`**: `Utf8Mono.Task.fwdU20`, by `Utf8Swap.fwdU20_of_swapStep20`.
* **`unstripStep20_holds`**: `Utf8Strip.Task.unstripStep20`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap

open Silmaril.SpecTec.Sem

/-- **An involution, as an injective replacement of `EXPORTS` contents.** -/
@[instance_reducible] def tauOf (τ : Value → Value) (hinv : ∀ u, τ (τ u) = u) : XTau :=
  ⟨τ, fun {u v} h => by rw [← hinv u, h, hinv]⟩

section
variable (τ : Value → Value) (hinv : ∀ u, τ (τ u) = u)

mutual
/-- **The evaluator copy's re-encoding is `Utf8Swap.swapV`.** -/
theorem swapX_eq_swapV : ∀ v : Value, @Swap.swapX (tauOf τ hinv) v = Utf8Swap.swapV τ v
  | .bool _ | .num _ | .text _ | .opt none => rfl
  | .tuple vs => by
    simp only [Swap.swapX, Utf8Swap.swapV]
    rw [swapXs_eq_swapVs vs]
  | .case _ w => by
    simp only [Swap.swapX, Utf8Swap.swapV]
    rw [swapX_eq_swapV w]
  | .struct gs => by
    simp only [Swap.swapX, Utf8Swap.swapV]
    rw [swapXf_eq_swapVf gs]
  | .list vs => by
    simp only [Swap.swapX, Utf8Swap.swapV]
    rw [swapXs_eq_swapVs vs]
  | .opt (some w) => by
    simp only [Swap.swapX, Utf8Swap.swapV]
    rw [swapX_eq_swapV w]

/-- `swapX_eq_swapV` on a list. -/
theorem swapXs_eq_swapVs : ∀ vs : List Value,
    @Swap.swapXs (tauOf τ hinv) vs = Utf8Swap.swapVs τ vs
  | [] => rfl
  | v :: vs => by
    simp only [Swap.swapXs, Utf8Swap.swapVs]
    rw [swapX_eq_swapV v, swapXs_eq_swapVs vs]

/-- `swapX_eq_swapV` on the fields of a record. -/
theorem swapXf_eq_swapVf : ∀ gs : List (Silmaril.SpecTec.IL.AtomS × Value),
    @Swap.swapXf (tauOf τ hinv) gs = Utf8Swap.swapVf τ gs
  | [] => rfl
  | (a, v) :: gs => by
    simp only [Swap.swapXf, Utf8Swap.swapVf]
    rw [swapX_eq_swapV v, swapXf_eq_swapVf gs]
    rfl
end

end

/-- **The leaf `Utf8Swap.Task.swapStep20` holds.** -/
theorem swapStep20_holds : Utf8Swap.Task.swapStep20 := by
  intro P τ hinv K hK v w h
  let _ : XTau := tauOf τ hinv
  have hS := Typ.sstepB_swap (EraseAll.hyps20 P) (K := K) hK hinv h
  rwa [swapX_eq_swapV τ hinv, swapX_eq_swapV τ hinv] at hS

/-- **The 2.0 forward theorem under both errata, at non-empty export names.** -/
theorem fwdU20_holds : Utf8Mono.Task.fwdU20 :=
  Utf8Swap.fwdU20_of_swapStep20 swapStep20_holds

/-- **Leg 3 of the 2.0 `$utf8` forward theorem holds.** -/
theorem unstripStep20_holds : Utf8Strip.Task.unstripStep20 :=
  Utf8Swap.unstripStep20_of_swapStep20 swapStep20_holds

end Silmaril.Wasm.SpecTec.Sim20.XSwap
