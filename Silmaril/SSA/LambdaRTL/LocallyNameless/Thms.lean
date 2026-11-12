module

public import Silmaril.SSA.LambdaRTL.LocallyNameless.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Thms
import Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless

/-!
# Locally nameless presentation of acyclic λSSA: checked results

* `Region.close_toLN` — **triangle**: `(r.toLN B).close Γ B.length = r.toDB (B ++ Γ)`, so the
  fully nameless translation factors through the locally nameless one
  (`toDB Γ = close Γ 0 ∘ toLN []`, `Region.toDB_eq_close_toLN`).
* `Region.ws_toLN`, `Region.fv_toLN` — `toLN` is locally closed at the binder depth and keeps
  exactly the free names outside `B`.
* `Region.eval_toLN` — **adequacy**: `(r.toLN []).eval m ρ η = r.evalSSA m ρ`.
* `LN.Region.toLN_ofLN` — **round trip** `toLN B (ofLN S A B e) = e` for `e` locally closed at
  depth `|B|` with free names in `A`, `B` duplicate-free and disjoint from `A`.
  `LN.Region.evalSSA_ofLN` — adequacy of opening.
* `Region.alphaEq_of_toLN_eq` — equal locally nameless forms are α-equivalent in every context;
  `Region.toLN_eq_of_alphaEq`, `Region.alphaEq_iff_toLN_eq` — conversely, α-equivalence in a
  context containing the free names gives equal locally nameless forms (closing is injective).

Infinitude enters only through the fresh-name supply `S : Supply V` used by `ofLN`.
-/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

universe v w

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [DecidableEq V]

open Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless in
theorem Region.close_toLN (Γ : List V) (r : Region V L F) (B : List V) :
    (r.toLN B).close Γ B.length = r.toDB (B ++ Γ) :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.close_toLN Γ r B

theorem Region.toDB_eq_close_toLN (Γ : List V) (r : Region V L F) :
    r.toDB Γ = (r.toLN []).close Γ 0 := by
  simpa using (Region.close_toLN Γ r []).symm

theorem Region.ws_toLN (r : Region V L F) (B : List V) : (r.toLN B).WS B.length :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.ws_toLN r B

theorem Region.fv_toLN (r : Region V L F) (B : List V) (z : V) (h : z ∈ (r.toLN B).fv) :
    z ∈ r.fv ∧ z ∉ B :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.fv_toLN r B z h

theorem Region.eval_toLN [Monad M] [DecidableEq L] (m : Model F M α) (r : Region V L F)
    (ρ : V → α) (η : ℕ → α) : (r.toLN []).eval m ρ η = r.evalSSA m ρ :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.eval_toLN m r ρ η

theorem LN.Region.toLN_ofLN (S : Supply V) {A : Finset V} (e : LN.Region V L F) (B : List V)
    (hB : B.Nodup) (hAB : ∀ x ∈ B, x ∉ A) (hw : e.WS B.length) (hA : e.fv ⊆ A) :
    (e.ofLN S A B).toLN B = e :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.toLN_ofLN S e B hB hAB hw hA

/-- **Adequacy of opening** a locally closed term. -/
theorem LN.Region.evalSSA_ofLN [Monad M] [DecidableEq L] (m : Model F M α) (S : Supply V)
    {A : Finset V} (e : LN.Region V L F) (hw : e.WS 0) (hA : e.fv ⊆ A) (ρ : V → α)
    (η : ℕ → α) : (e.ofLN S A []).evalSSA m ρ = e.eval m ρ η := by
  rw [← Region.eval_toLN m _ ρ η,
    LN.Region.toLN_ofLN S e [] List.nodup_nil (by simp) (by simpa using hw) hA]

/-- Equal locally nameless forms give α-equivalent regions in every context. -/
theorem Region.alphaEq_of_toLN_eq {r r' : Region V L F} (h : r.toLN [] = r'.toLN [])
    (Γ : List V) : r.AlphaEq Γ r' := by
  change r.toDB Γ = r'.toDB Γ
  rw [Region.toDB_eq_close_toLN, Region.toDB_eq_close_toLN, h]

/-- **α-converse**: α-equivalence in a context containing the free names gives equal locally
nameless forms. -/
theorem Region.toLN_eq_of_alphaEq {Γ : List V} {r r' : Region V L F} (hr : r.fv ⊆ Γ.toFinset)
    (hr' : r'.fv ⊆ Γ.toFinset) (h : r.AlphaEq Γ r') : r.toLN [] = r'.toLN [] :=
  Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless.Region.toLN_eq_of_alphaEq hr hr' h

/-- α-equivalence (in a context containing the free names) is equality of locally nameless
forms. -/
theorem Region.alphaEq_iff_toLN_eq {Γ : List V} {r r' : Region V L F}
    (hr : r.fv ⊆ Γ.toFinset) (hr' : r'.fv ⊆ Γ.toFinset) :
    r.AlphaEq Γ r' ↔ r.toLN [] = r'.toLN [] :=
  ⟨Region.toLN_eq_of_alphaEq hr hr', fun h => Region.alphaEq_of_toLN_eq h Γ⟩

end Silmaril.SSA.LambdaRTL
