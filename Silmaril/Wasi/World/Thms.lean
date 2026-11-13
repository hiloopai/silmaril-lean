module

public import Silmaril.Wasi.World.Defs
public import Silmaril.Games.Reduct.Thms

@[expose] public section

/-!
# WASI worlds: the satisfaction condition and reducts

* `WasiInst.sat_map_iff`: **the satisfaction condition** of `WasiInst`, in the concrete form: a
  translated sentence holds in a component of `W'` iff the sentence holds in its reduct to `W`
  (inherited from `Silmaril.Games.GInst`).
* `World.wev_rel`, `World.wtrace_rel`: a world morphism does not change the named events of
  the moves it relates (worlds rename nothing; they only hide exports and widen imports).
* `World.ag_reduct`: **assume–guarantee sentences are preserved by reducts**: if a component of
  `W'` satisfies `ag A G`, so does its reduct to any world `W` it fits. `World.ag_map`: the
  same as an entailment `ag A G ⊨ (ag A G).map f` at `W'`.
* `ag_mono`: assume–guarantee sentences are safety sentences, inherited by refinements.
-/

namespace Silmaril.Wasi

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution

/-- **The satisfaction condition of `WasiInst`**. -/
theorem WasiInst.sat_map_iff {W W' : World} (f : W ⟶ W') (σ : W'.Model)
    (φ : GSen (nsig W.imports) (nsig W.exports)) :
    (WasiInst.I.obj W').Sat σ ((WasiInst.I.map f).sen φ) ↔
      φ.holds (Game.reduct (World.toGame.map f) σ) :=
  Iff.rfl

namespace World

variable {W W' : World}

/-- Moves related by a world morphism have the same event. -/
theorem wev_rel (f : W ⟶ W') {a : Move (nsig W'.imports) (nsig W'.exports)}
    {b : Move (nsig W.imports) (nsig W.exports)} (h : Game.Rel (toGame.map f) a b) :
    wev a = wev b := by
  cases h <;> rfl

/-- Plays related by a world morphism have the same events. -/
theorem wtrace_rel (f : W ⟶ W') {s : List (Move (nsig W'.imports) (nsig W'.exports))}
    {p : List (Move (nsig W.imports) (nsig W.exports))}
    (h : List.Forall₂ (Game.Rel (toGame.map f)) s p) : wtrace s = wtrace p := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    show wev _ :: wtrace _ = wev _ :: wtrace _
    rw [wev_rel f hab, ih]

/-- **Assume–guarantee sentences are preserved by reducts.** -/
theorem ag_reduct (f : W ⟶ W') {A G : List WEv → Prop} {σ : W'.Model}
    (h : (ag A G).holds σ) : (ag A G).holds (Game.reduct (toGame.map f) σ) := by
  intro p hp hA
  obtain ⟨-, s, hs, hr⟩ :=
    (Game.mem_reduct_iff_rel (G := toGame.obj W) (G' := toGame.obj W') (toGame.map f) σ p).1 hp
  have he : wtrace s = wtrace p := wtrace_rel f hr
  rw [← he] at hA ⊢
  exact h s hs hA

/-- An assume–guarantee sentence entails its translation along a world morphism. -/
theorem ag_map (f : W ⟶ W') {A G : List WEv → Prop} {σ : W'.Model}
    (h : (ag A G).holds σ) : (WasiInst.I.obj W').Sat σ ((WasiInst.I.map f).sen (ag A G)) :=
  (WasiInst.sat_map_iff f σ _).2 (ag_reduct f h)

end World

/-- Assume–guarantee sentences are inherited by refinements. -/
theorem ag_mono {I X : Set FnName} {A G : List WEv → Prop} {σ τ : Strategy (nsig I) (nsig X)}
    (hle : τ ≤ σ) (h : (ag A G).holds σ) : (ag A G).holds τ :=
  fun s hs hA => h s (hle hs) hA

end Silmaril.Wasi
