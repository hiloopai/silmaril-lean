module

public import Silmaril.Wasm.Atlas.Defs

/-!
# An atlas of Wasm semantics: the generic glue

* `Dir.Rel.comp`: recorded directions compose (by meet).
* `Transition.transfer` / `Transition.reflect` / `Transition.sat_iff`: satisfaction moves along a
  transition in its recorded direction, on its domain and sentence class.
* `Path.transfer`, `Path.sat_iff`: the same along a chain (`Path.toTransition`), and a chain of
  equality transitions is an equality transition (`Path.dir_of_allEqual`).
* `ChartAtlas.holds_base`: a sentence proved in any chart whose domain covers a point holds, at
  the image point, in the base chart (Core) when the chart's transition preserves;
  `ChartAtlas.sat_iff_of_equal`: two charts with equality transitions to the base agree on
  sentences and points with the same image.

The Wasm instances are in `Silmaril.Wasm.Atlas.{Core,Games,Component,Binaryen,SpecTec}`.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas

universe u v u' v' u'' v''

namespace Dir

theorem Rel.comp {d e : Dir} {p q r : Prop} (h₁ : d.Rel p q) (h₂ : e.Rel q r) :
    (d.comp e).Rel p r := by
  refine ⟨fun hf hp => ?_, fun hb hr => ?_⟩
  · simp only [Dir.comp, Bool.and_eq_true] at hf
    exact h₂.1 hf.2 (h₁.1 hf.1 hp)
  · simp only [Dir.comp, Bool.and_eq_true] at hb
    exact h₁.2 hb.1 (h₂.2 hb.2 hr)

@[simp] theorem equal_comp_equal : Dir.equal.comp Dir.equal = Dir.equal := rfl

theorem rel_equal_iff {p q : Prop} : Dir.equal.Rel p q ↔ (p ↔ q) :=
  ⟨fun h => ⟨h.1 rfl, h.2 rfl⟩, fun h => ⟨fun _ => h.1, fun _ => h.2⟩⟩

theorem Stronger.refl (d : Dir) : d.Stronger d := ⟨id, id⟩

theorem equal_stronger (d : Dir) : Dir.equal.Stronger d := ⟨fun _ => rfl, fun _ => rfl⟩

end Dir

namespace Transition

variable {A : Chart.{u, v}} {B : Chart.{u', v'}} {C : Chart.{u'', v''}}

/-- **Transfer** along a preserving transition. -/
theorem transfer (T : Transition A B) (hd : T.dir.fwd = true) {p : A.Pt} {φ : A.Sen}
    (hp : A.dom p) (hφ : T.cls φ) (h : A.Sat p φ) : B.Sat (T.pt p) (T.sen φ) :=
  (T.sat p φ hp hφ).1 hd h

/-- **Reflection** along a reflecting transition. -/
theorem reflect (T : Transition A B) (hd : T.dir.bwd = true) {p : A.Pt} {φ : A.Sen}
    (hp : A.dom p) (hφ : T.cls φ) (h : B.Sat (T.pt p) (T.sen φ)) : A.Sat p φ :=
  (T.sat p φ hp hφ).2 hd h

/-- An equality transition: satisfaction agrees on the domain and class. -/
theorem sat_iff (T : Transition A B) (hd : T.dir = .equal) {p : A.Pt} {φ : A.Sen}
    (hp : A.dom p) (hφ : T.cls φ) : A.Sat p φ ↔ B.Sat (T.pt p) (T.sen φ) :=
  Dir.rel_equal_iff.1 (hd ▸ T.sat p φ hp hφ)

@[simp] theorem comp_dir (T : Transition A B) (U : Transition B C) :
    (T.comp U).dir = T.dir.comp U.dir := rfl

@[simp] theorem comp_pt (T : Transition A B) (U : Transition B C) (p : A.Pt) :
    (T.comp U).pt p = U.pt (T.pt p) := rfl

@[simp] theorem comp_sen (T : Transition A B) (U : Transition B C) (φ : A.Sen) :
    (T.comp U).sen φ = U.sen (T.sen φ) := rfl

/-- Transfer along two transitions, each preserving. -/
theorem transfer₂ (T : Transition A B) (U : Transition B C) (hT : T.dir.fwd = true)
    (hU : U.dir.fwd = true) {p : A.Pt} {φ : A.Sen} (hp : A.dom p) (hφ : T.cls φ)
    (hψ : U.cls (T.sen φ)) (h : A.Sat p φ) : C.Sat (U.pt (T.pt p)) (U.sen (T.sen φ)) :=
  U.transfer hU (T.dom_pt p hp) hψ (T.transfer hT hp hφ h)

end Transition

namespace Path

theorem dir_of_allEqual : {A B : Chart.{u, v}} → (π : Path A B) → π.AllEqual →
    π.toTransition.dir = .equal
  | _, _, nil _, _ => rfl
  | _, _, cons T π, h => by
    obtain ⟨hT, hπ⟩ : T.dir = .equal ∧ π.AllEqual := h
    show T.dir.comp π.toTransition.dir = .equal
    rw [hT, dir_of_allEqual π hπ]; rfl

/-- **Transfer along a chain** whose composite preserves. -/
theorem transfer {A B : Chart.{u, v}} (π : Path A B) (hd : π.toTransition.dir.fwd = true)
    {p : A.Pt} {φ : A.Sen} (hp : A.dom p) (hφ : π.toTransition.cls φ) (h : A.Sat p φ) :
    B.Sat (π.toTransition.pt p) (π.toTransition.sen φ) :=
  π.toTransition.transfer hd hp hφ h

/-- **A chain of equality transitions** relates satisfaction both ways. -/
theorem sat_iff {A B : Chart.{u, v}} (π : Path A B) (hπ : π.AllEqual) {p : A.Pt}
    {φ : A.Sen} (hp : A.dom p) (hφ : π.toTransition.cls φ) :
    A.Sat p φ ↔ B.Sat (π.toTransition.pt p) (π.toTransition.sen φ) :=
  π.toTransition.sat_iff (dir_of_allEqual π hπ) hp hφ

end Path

namespace ChartAtlas

variable (𝔄 : ChartAtlas.{u, v})

/-- **A sentence proved in any chart whose domain covers a point holds in the base**, when that
chart's transition preserves on the sentence's class. -/
theorem holds_base (i : 𝔄.ι) (hd : (𝔄.toBase i).dir.fwd = true) {p : (𝔄.chart i).Pt}
    {φ : (𝔄.chart i).Sen} (hp : (𝔄.chart i).dom p) (hφ : (𝔄.toBase i).cls φ)
    (h : (𝔄.chart i).Sat p φ) : 𝔄.base.Sat ((𝔄.toBase i).pt p) ((𝔄.toBase i).sen φ) :=
  (𝔄.toBase i).transfer hd hp hφ h

/-- **Charts connected through the base by equality transitions agree**: a sentence proved in
chart `i` holds in chart `j` at any point and sentence with the same image in the base. -/
theorem sat_iff_of_equal (i j : 𝔄.ι) (hi : (𝔄.toBase i).dir = .equal)
    (hj : (𝔄.toBase j).dir = .equal) {p : (𝔄.chart i).Pt} {q : (𝔄.chart j).Pt}
    {φ : (𝔄.chart i).Sen} {ψ : (𝔄.chart j).Sen} (hp : (𝔄.chart i).dom p)
    (hq : (𝔄.chart j).dom q) (hφ : (𝔄.toBase i).cls φ) (hψ : (𝔄.toBase j).cls ψ)
    (hpt : (𝔄.toBase i).pt p = (𝔄.toBase j).pt q)
    (hsen : (𝔄.toBase i).sen φ = (𝔄.toBase j).sen ψ) :
    (𝔄.chart i).Sat p φ ↔ (𝔄.chart j).Sat q ψ := by
  rw [(𝔄.toBase i).sat_iff hi hp hφ, (𝔄.toBase j).sat_iff hj hq hψ, hpt, hsen]

end ChartAtlas

end Silmaril.Wasm.Atlas
