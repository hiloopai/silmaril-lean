module

public import Silmaril.Libc.Contract.Inv.Defs
public import Silmaril.Libc.Contract.Spec.Thms

/-!
# Invariants: setup along morphisms and products, framed contracts compose

PROVED (standard axioms), names in `Silmaril.Libc.Contracts`:

* the monoidal category of invariants (`InvObj.instMonoidalCategory`, `Defs`: every coherence law
  holds definitionally on ghost maps); `InvObj.toUnit_unique` (the unit is terminal),
  `InvObj.split` (a morphism is `I ⊢ J ∗ Rest`: the smaller invariant, on a part of the regions);
* **setup**: `InvObj.Establishes.map` (along a morphism), `InvObj.Establishes.tensor` (for
  disjoint initial regions);
* **framed contracts**: `CLib.HoldsIn.holds` and `CLib.HoldsIn.sat` (a library meeting a contract
  relative to an invariant object, under the frame convention, meets it in the institution);
  `CLib.HoldsIn.transport` (**transport along an invariant morphism** `φ : I ⟶ J`: a contract about
  `J`'s ghost state, proved relative to the finer invariant `I`, holds relative to the image of `I`,
  which entails `J`); `CLib.HoldsIn.client_frame` (memory apart from the library's reservation and
  scratch is unchanged by a call);
* **composition**: `CLib.HoldsIn.tensor`: two libraries with disjoint functions, each meeting its
  contract relative to its invariant, with the invariants inside disjoint reservations and each
  scratch region apart from the other's reservation, meet the tensor contract relative to the
  separating product `I₁ ⊗ I₂`.
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

open CategoryTheory MonoidalCategory

namespace InvObj

variable {Addr Val : Type}

theorem toUnit_unique (I : InvObj Addr Val) (f : I ⟶ 𝟙_ (InvObj Addr Val)) : f = toUnit I :=
  hom_ext rfl

/-- **A morphism is `I ⊢ J ∗ Rest`**: `I`'s invariant gives `J`'s at the projected state, on a part
of `I`'s regions. -/
theorem split {I J : InvObj Addr Val} (φ : I ⟶ J) {g : I.G} {m : Mem Addr Val} (h : I.inv g m) :
    J.inv (Hom.proj φ g) m ∧ J.own (Hom.proj φ g) ⊆ I.own g :=
  ⟨Hom.entails φ g m h, Hom.own_le φ g⟩

theorem Establishes.map {I J : InvObj Addr Val} {start : Mem Addr Val → Prop} {g0 : I.G}
    (h : I.Establishes start g0) (φ : I ⟶ J) : J.Establishes start (Hom.proj φ g0) :=
  fun m hm => Hom.entails φ g0 m (h m hm)

theorem Establishes.tensor {I J : InvObj Addr Val} {start start' : Mem Addr Val → Prop}
    {g0 : I.G} {h0 : J.G} (h : I.Establishes start g0) (h' : J.Establishes start' h0)
    (hd : Sep (I.own g0) (J.own h0)) :
    (I ⊗ J).Establishes (fun m => start m ∧ start' m) (g0, h0) :=
  fun m hm => ⟨h m hm.1, h' m hm.2, hd⟩

end InvObj

namespace CLib

variable {A : Api} {F F₁ F₂ : Set A.Fn} {Addr Val : Type}

/-- **A framed contract holds in the institution**, relative to the invariant. -/
theorem HoldsIn.holds {L : CLib A F Addr Val} {I : InvObj Addr Val} [Nonempty I.G]
    {C : Contract (Sig.mk' F I.G)} (h : L.HoldsIn I C) : Holds (L.toModel I.G) C I.inv where
  init := h.init
  safe := h.safe
  post f hf g m a m' r hI hp hs :=
    let ⟨g', hI', hq, _⟩ := h.post f hf g m a m' r hI hp hs; ⟨g', hI', hq⟩

theorem HoldsIn.sat {L : CLib A F Addr Val} {I : InvObj Addr Val} [Nonempty I.G]
    {C : Contract (Sig.mk' F I.G)} (h : L.HoldsIn I C) : Sat (L.toModel I.G) C :=
  ⟨_, h.holds⟩

/-- **Transport along an invariant morphism** `φ : I ⟶ J`: a contract about `J`'s abstract
state, proved relative to the finer invariant `I` (read through `φ`), holds relative to the
image of `I`, which entails `J`'s invariant. -/
theorem HoldsIn.transport {L : CLib A F Addr Val} {I J : InvObj Addr Val} [Nonempty I.G]
    [Nonempty J.G] (φ : I ⟶ J) {C : Contract (Sig.mk' F J.G)}
    (h : L.HoldsIn I (C.pull (InvObj.Hom.proj φ))) :
    Holds (L.toModel J.G) C (push (InvObj.Hom.proj φ) I.inv) ∧
      ∀ g m, push (InvObj.Hom.proj φ) I.inv g m → J.inv g m := by
  refine ⟨⟨fun m hm => ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨g, hi, hI⟩ := h.init m hm
    exact ⟨_, hi, g, rfl, hI⟩
  · rintro f hf _ m a ⟨g, rfl, hI⟩ hp
    exact h.safe f hf g m a hI hp
  · rintro f hf _ m a m' r ⟨g, rfl, hI⟩ hp hs
    obtain ⟨g', hI', hq, _⟩ := h.post f hf g m a m' r hI hp hs
    exact ⟨_, ⟨g', rfl, hI'⟩, hq⟩
  · rintro _ m ⟨g, rfl, hI⟩
    exact InvObj.Hom.entails φ g m hI

/-- **The client's memory is framed out**: an address apart from every region the invariant may
own (`D`) and from the call's scratch keeps its value. -/
theorem HoldsIn.client_frame {L : CLib A F Addr Val} {I : InvObj Addr Val} [Nonempty I.G]
    {C : Contract (Sig.mk' F I.G)} (h : L.HoldsIn I C) {D : Set Addr}
    (hD : ∀ g m, I.inv g m → I.own g ⊆ D) {f : A.Fn} {hf : f ∈ F} {g : I.G}
    {m m' : Mem Addr Val} {a : A.Arg f} {r : A.Ret f} (hI : I.inv g m) (hp : C.pre f hf g a)
    (hs : L.step f hf m a (some (m', r))) {x : Addr} (hx : x ∉ D) (hxs : x ∉ L.scratch m) :
    m' x = m x := by
  obtain ⟨g', hI', _, hfr⟩ := h.post f hf g m a m' r hI hp hs
  exact hfr x (fun h => hx (hD g m hI h)) (fun h => hx (hD g' m' hI' h)) hxs

/-- **Framed contracts compose** over the separating product. -/
theorem HoldsIn.tensor {L₁ : CLib A F₁ Addr Val} {L₂ : CLib A F₂ Addr Val}
    {I₁ I₂ : InvObj Addr Val} [Nonempty I₁.G] [Nonempty I₂.G]
    {C₁ : Contract (Sig.mk' F₁ I₁.G)} {C₂ : Contract (Sig.mk' F₂ I₂.G)}
    (hd : ∀ f, f ∈ F₁ → f ∉ F₂) {D₁ D₂ : Set Addr} (hD : Sep D₁ D₂)
    (hw₁ : ∀ g m, I₁.inv g m → I₁.own g ⊆ D₁) (hw₂ : ∀ g m, I₂.inv g m → I₂.own g ⊆ D₂)
    (hs₁ : ∀ m, Sep (L₁.scratch m) D₂) (hs₂ : ∀ m, Sep (L₂.scratch m) D₁)
    (h₁ : L₁.HoldsIn I₁ C₁) (h₂ : L₂.HoldsIn I₂ C₂) :
    (L₁.tensor L₂).HoldsIn (InvObj.tensor I₁ I₂) (C₁.tensor C₂) := by
  have sep : ∀ g₁ g₂ m₁ m₂, I₁.inv g₁ m₁ → I₂.inv g₂ m₂ → Sep (I₁.own g₁) (I₂.own g₂) :=
    fun g₁ g₂ m₁ m₂ h1 h2 x hx1 hx2 => hD x (hw₁ g₁ m₁ h1 hx1) (hw₂ g₂ m₂ h2 hx2)
  refine ⟨fun m hm => ?_, ?_, ?_⟩
  · obtain ⟨g1, hi1, hI1⟩ := h₁.init m hm.1
    obtain ⟨g2, hi2, hI2⟩ := h₂.init m hm.2
    exact ⟨(g1, g2), ⟨hi1, hi2⟩, hI1, hI2, sep g1 g2 m m hI1 hI2⟩
  · rintro f hf g m a ⟨hI1, hI2, _⟩ ⟨hp1, hp2⟩ hs
    rcases hs with ⟨h, hs⟩ | ⟨_, h, hs⟩
    · exact h₁.safe f h g.1 m a hI1 (hp1 h) hs
    · exact h₂.safe f h g.2 m a hI2 (hp2 h) hs
  · rintro f hf g m a m' r ⟨hI1, hI2, _⟩ ⟨hp1, hp2⟩ hs
    rcases hs with ⟨h, hs⟩ | ⟨hn, h, hs⟩
    · obtain ⟨g1', hI1', hq, hfr⟩ := h₁.post f h g.1 m a m' r hI1 (hp1 h) hs
      have hI2' : I₂.inv g.2 m' := I₂.frame g.2 m m' hI2 fun x hx =>
        have hx2 := hw₂ g.2 m hI2 hx
        (hfr x (fun h => hD x (hw₁ _ _ hI1 h) hx2) (fun h => hD x (hw₁ _ _ hI1' h) hx2)
          (fun h => hs₁ m x h hx2)).symm
      refine ⟨(g1', g.2), ⟨hI1', hI2', sep _ _ _ _ hI1' hI2'⟩,
        ⟨fun _ => hq, fun hn => absurd h hn, fun h2 => absurd h2 (hd f h), fun _ => rfl⟩, ?_⟩
      intro x hx hx' hxs
      exact hfr x (fun h => hx (Or.inl h)) (fun h => hx' (Or.inl h)) (fun h => hxs (Or.inl h))
    · obtain ⟨g2', hI2', hq, hfr⟩ := h₂.post f h g.2 m a m' r hI2 (hp2 h) hs
      have hI1' : I₁.inv g.1 m' := I₁.frame g.1 m m' hI1 fun x hx =>
        have hx1 := hw₁ g.1 m hI1 hx
        (hfr x (fun h => hD x hx1 (hw₂ _ _ hI2 h)) (fun h => hD x hx1 (hw₂ _ _ hI2' h))
          (fun h => hs₂ m x h hx1)).symm
      refine ⟨(g.1, g2'), ⟨hI1', hI2', sep _ _ _ _ hI1' hI2'⟩,
        ⟨fun h1 => absurd h1 hn, fun _ => rfl, fun _ => hq, fun hn => absurd h hn⟩, ?_⟩
      intro x hx hx' hxs
      exact hfr x (fun h => hx (Or.inr h)) (fun h => hx' (Or.inr h)) (fun h => hxs (Or.inr h))

end CLib

end Silmaril.Libc.Contracts
