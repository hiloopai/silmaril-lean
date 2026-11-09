module

public import Silmaril.X86.Institution.Defs

/-!
# The institution of loose x86 machine models: what is proved

The institution `inst V : Sig Φ ⥤ Room` and `classic V : ClassicInstitution (Sig Φ)` are
defined in `Institution/Defs.lean`, with their functor laws and `Sig.top_le` (a tighter
signature has a smaller top). Here:

* `satisfaction`, `classic_sat_iff`: the satisfaction condition (sentences are translated by
  the identity, so it is `Iff.rfl`);
* `sat_of_top`: a sentence of the top holds in every model; `Sig.topModel`: the top is a
  model when it has `Progress`; `sat_of_le`: satisfaction moves down along refinement;
* the room view: `thm_iff_top` (validity over the models is satisfaction on the top),
  `csa_iff_top` (a countermodel exists iff the top fails), `thm_mono` (validity moves to
  tighter signatures).
-/

@[expose] public section

namespace Silmaril.X86.Institution

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.X86.RelIsa (Views)

variable {Φ σ : Type} {V : Views σ} {G G' : Sig Φ} {φ : Sen σ}

/-- **The satisfaction condition** of the institution: a model of `G'` satisfies a sentence
of `G` iff its reduct does. -/
theorem satisfaction (h : G ≤ G') (M : Model V G') (φ : Sen σ) :
    Sat M.1 φ ↔ Sat (M.reduct h).1 φ :=
  Iff.rfl

/-- The satisfaction condition of `classic V` is that of `inst V`. -/
theorem classic_sat_iff (h : G ≤ G') (M : (room V G').Mod) (φ : Sen σ) :
    (room V G').Sat M ((corridor V h).sen φ) ↔ (room V G).Sat ((corridor V h).mod.obj M) φ :=
  (corridor V h).sat M φ

/-- Satisfaction moves down along refinement. -/
theorem sat_of_le' {C A : RelIsa σ} (hle : RelIsa.Le C A) (h : Sat A φ) : Sat C φ :=
  fun entry => FnContract.Spec.MustTotalIn.of_le hle (h entry)

/-- **A sentence of the top holds in every model.** -/
theorem sat_of_top (h : Sat (G.top V) φ) (M : Model V G) : Sat M.1 φ :=
  sat_of_le' M.2.1 h

/-- The top is a model when it has an outcome everywhere. -/
def Sig.topModel (G : Sig Φ) (V : Views σ) (hp : (G.top V).Progress) : Model V G :=
  ⟨G.top V, RelIsa.Le.refl _, hp⟩

/-- **Validity in the room is satisfaction on the top** (if the top is a model). -/
theorem thm_iff_top (hp : (G.top V).Progress) :
    (∀ M : (room V G).Mod, (room V G).Sat M φ) ↔ Sat (G.top V) φ :=
  ⟨fun h => h (G.topModel V hp), fun h M => sat_of_top h M⟩

/-- **A countermodel in the room is failure on the top** (if the top is a model). -/
theorem csa_iff_top (hp : (G.top V).Progress) :
    (∃ M : (room V G).Mod, ¬ (room V G).Sat M φ) ↔ ¬ Sat (G.top V) φ := by
  rw [← thm_iff_top hp]
  exact not_forall.symm

/-- Satisfaction is closed downwards along the model morphisms (refinement). -/
theorem sat_of_le {M M' : Model V G} (hle : M ≤ M') (h : Sat M'.1 φ) : Sat M.1 φ :=
  sat_of_le' hle h

/-- A sentence valid in a looser signature is valid in a tighter one. -/
theorem thm_mono (h : G ≤ G') (hv : ∀ M : (room V G).Mod, (room V G).Sat M φ) :
    ∀ M : (room V G').Mod, (room V G').Sat M φ :=
  fun M => hv ((corridor V h).mod.obj M)

end Silmaril.X86.Institution
