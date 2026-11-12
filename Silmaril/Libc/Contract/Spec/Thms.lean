module

public import Silmaril.Libc.Contract.Spec.Defs

/-!
# Contracts: reducts are functorial, models meet the reducts of their contracts

PROVED (standard axioms), names in `Silmaril.Libc.Contract`:

* `Contract.restrict_ofTable`: along an inclusion, the reduct of a table's contract is the
  table's contract on the smaller set (so a hierarchy of signatures over one table is a chain of
  reducts);
* **refinement**: `Contract.Le.refl`, `Contract.Le.trans`, `Holds.mono`, `Sat.mono`;
* **the reduct of contracts is a functor** `Sigᵒᵖ → Type`: `Contract.restrict_id`,
  `Contract.restrict_comp`; sentence translation is a functor `Sig → Type`: `Contract.map_id`,
  `Contract.map_comp`; models: `Model.reduct_id`, `Model.reduct_comp` (definitional);
* **reducts of models meet reducts of contracts**: `Holds.restrict` (with the image invariant
  `push σ.proj I`), `Sat.restrict`; `Contract.le_map_restrict`: a contract is at least as strong
  as the translation of its reduct;
* **the satisfaction condition**, relative to an invariant: `holds_map_iff` (the translated
  contract holds for `M` relative to `I` iff the contract holds for the reduct relative to the
  image of `I`); with the invariant hidden: `sat_map_iff` (uses the surjectivity of the
  projection);
* **tensor**: `Holds.tensor`, `Sat.tensor`, `Returns.tensor`, `NonVacuous.tensor` (disjoint
  function sets), and the factors back: `Contract.le_restrict_inl`, `Contract.le_restrict_inr`,
  `Sat.tensor_inl`, `Sat.tensor_inr`;
* **non-vacuity**: `holds_canon` (every contract holds for its canonical model),
  `returns_canon`, `Contract.Feasible.nonVacuous` (a feasible contract has a model with a start
  state that always returns).
-/

@[expose] public section

namespace Silmaril.Libc.Contracts

variable {A : Api} {S T U : Sig A}

namespace Contract

theorem ext {C D : Contract S} (hi : ∀ g, C.init g ↔ D.init g)
    (hp : ∀ f hf g a, C.pre f hf g a ↔ D.pre f hf g a)
    (hq : ∀ f hf g a r h, C.post f hf g a r h ↔ D.post f hf g a r h) : C = D := by
  obtain ⟨i, p, q⟩ := C
  obtain ⟨i', p', q'⟩ := D
  have e1 : i = i' := funext fun g => propext (hi g)
  have e2 : p = p' :=
    funext fun f => funext fun hf => funext fun g => funext fun a => propext (hp f hf g a)
  have e3 : q = q' := funext fun f => funext fun hf => funext fun g => funext fun a =>
    funext fun r => funext fun h => propext (hq f hf g a r h)
  subst e1 e2 e3
  rfl

/-! ## Refinement -/

theorem Le.refl (C : Contract S) : C.Le C :=
  ⟨fun _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ _ h => h⟩

theorem Le.trans {C D E : Contract S} (h₁ : C.Le D) (h₂ : D.Le E) : C.Le E :=
  ⟨fun g h => h₁.1 g (h₂.1 g h), fun f hf g a h => h₂.2.1 f hf g a (h₁.2.1 f hf g a h),
    fun f hf g a r g' hp hq =>
      h₁.2.2 f hf g a r g' hp (h₂.2.2 f hf g a r g' (h₁.2.1 f hf g a hp) hq)⟩

/-! ## Functoriality -/

/-- The reduct along the identity is the contract. -/
theorem restrict_id (C : Contract S) : C.restrict (Sig.Hom.id S) = C := by
  apply Contract.ext
  · intro g
    constructor
    · rintro ⟨g', rfl, hi⟩; exact hi
    · intro hi; exact ⟨g, rfl, hi⟩
  · intro f hf g a
    exact ⟨fun h => h g rfl, fun h g' he => by subst he; exact h⟩
  · intro f hf g a r h
    constructor
    · rintro ⟨g', h', rfl, rfl, hq⟩; exact hq
    · intro hq; exact ⟨g, h, rfl, rfl, hq⟩

/-- **The reduct is functorial**: restricting along `τ`, then along `σ`, is restricting along
`σ ≫ τ`. -/
theorem restrict_comp (σ : Sig.Hom S T) (τ : Sig.Hom T U) (C : Contract U) :
    (C.restrict τ).restrict σ = C.restrict (σ.comp τ) := by
  apply Contract.ext
  · intro g
    constructor
    · rintro ⟨_, rfl, g'', rfl, hi⟩; exact ⟨g'', rfl, hi⟩
    · rintro ⟨g'', rfl, hi⟩; exact ⟨_, rfl, g'', rfl, hi⟩
  · intro f hf g a
    constructor
    · intro h g'' he; exact h _ he g'' rfl
    · intro h g' he g'' he'; subst he'; exact h g'' he
  · intro f hf g a r h
    constructor
    · rintro ⟨_, _, rfl, rfl, g'', h'', rfl, rfl, hq⟩; exact ⟨g'', h'', rfl, rfl, hq⟩
    · rintro ⟨g'', h'', rfl, rfl, hq⟩; exact ⟨_, _, rfl, rfl, g'', h'', rfl, rfl, hq⟩

theorem map_id (C : Contract S) : C.map (Sig.Hom.id S) = C := by
  apply Contract.ext
  · intro g; exact Iff.rfl
  · intro f hf g a; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hf, h⟩⟩
  · intro f hf g a r h; exact ⟨fun h' => h' hf, fun h' _ => h'⟩

theorem map_comp (σ : Sig.Hom S T) (τ : Sig.Hom T U) (C : Contract S) :
    (C.map σ).map τ = C.map (σ.comp τ) := by
  apply Contract.ext
  · intro g; exact Iff.rfl
  · intro f hf g a; exact ⟨fun ⟨_, h⟩ => h, fun ⟨hf', h⟩ => ⟨σ.le hf', hf', h⟩⟩
  · intro f hf g a r h; exact ⟨fun h' hf' => h' (σ.le hf') hf', fun h' _ hf' => h' hf'⟩

/-- **A contract is at least as strong as the translation of its reduct.** -/
theorem le_map_restrict (σ : Sig.Hom S T) (C : Contract T) : ((C.restrict σ).map σ).Le C := by
  refine ⟨fun g hi => ⟨g, rfl, hi⟩, fun f hf g a ⟨_, hp⟩ => hp g rfl, ?_⟩
  intro f hf g a r h _ hq hf'
  exact ⟨g, h, rfl, rfl, hq⟩

/-- **Along an inclusion, the reduct of a table's contract is the table's contract on the smaller
set.** -/
theorem restrict_ofTable {F F' : Set A.Fn} {G : Type} [Nonempty G] (h : F ⊆ F') (init : G → Prop)
    (t : (f : A.Fn) → FnSpec A G f) :
    (ofTable F' G init t).restrict (Sig.incl h) = ofTable F G init t := by
  apply Contract.ext
  · intro g
    constructor
    · rintro ⟨g', rfl, hi⟩; exact hi
    · intro hi; exact ⟨g, rfl, hi⟩
  · intro f hf g a
    exact ⟨fun h' => h' g rfl, fun h' g' he => by subst he; exact h'⟩
  · intro f hf g a r h
    constructor
    · rintro ⟨g', h', rfl, rfl, hq⟩; exact hq
    · intro hq; exact ⟨g, h, rfl, rfl, hq⟩

end Contract

theorem Model.reduct_id (M : Model S) : M.reduct (Sig.Hom.id S) = M := rfl

theorem Model.reduct_comp (σ : Sig.Hom S T) (τ : Sig.Hom T U) (M : Model U) :
    (M.reduct τ).reduct σ = M.reduct (σ.comp τ) := rfl

/-! ## Holds and satisfaction -/

variable {M : Model S} {C D : Contract S} {I : S.G → M.St → Prop}

/-- **A stronger contract holds for less**: what holds for `D` holds for every `C ≤ D`. -/
theorem Holds.mono (h : Holds M D I) (hle : C.Le D) : Holds M C I where
  init s hs := let ⟨g, hi, hI⟩ := h.init s hs; ⟨g, hle.1 g hi, hI⟩
  safe f hf g s a hI hp := h.safe f hf g s a hI (hle.2.1 f hf g a hp)
  post f hf g s a t r hI hp hs :=
    let ⟨g', hI', hq⟩ := h.post f hf g s a t r hI (hle.2.1 f hf g a hp) hs
    ⟨g', hI', hle.2.2 f hf g a r g' hp hq⟩

theorem Sat.mono (h : Sat M D) (hle : C.Le D) : Sat M C :=
  let ⟨I, hI⟩ := h; ⟨I, hI.mono hle⟩

/-- **The reduct of a model meets the reduct of its contract**, relative to the image of its
invariant. -/
theorem Holds.restrict {M : Model T} {C : Contract T} {I : T.G → M.St → Prop}
    (h : Holds M C I) (σ : Sig.Hom S T) :
    Holds (M.reduct σ) (C.restrict σ) (push σ.proj I) where
  init s hs := let ⟨g, hi, hI⟩ := h.init s hs; ⟨σ.proj g, ⟨g, rfl, hi⟩, ⟨g, rfl, hI⟩⟩
  safe f hf g s a hI hp := by
    obtain ⟨g', he, hI⟩ := hI
    exact h.safe f (σ.le hf) g' s a hI (hp g' he)
  post f hf g s a t r hI hp hs := by
    obtain ⟨g', he, hI⟩ := hI
    obtain ⟨h', hI', hq⟩ := h.post f (σ.le hf) g' s a t r hI (hp g' he) hs
    exact ⟨σ.proj h', ⟨h', rfl, hI'⟩, g', h', he, rfl, hq⟩

theorem Sat.restrict {M : Model T} {C : Contract T} (h : Sat M C) (σ : Sig.Hom S T) :
    Sat (M.reduct σ) (C.restrict σ) :=
  let ⟨_, hI⟩ := h; ⟨_, hI.restrict σ⟩

/-- **The satisfaction condition, relative to an invariant**: the translated contract holds for
`M` relative to `I` iff the contract holds for the reduct relative to the image of `I`. -/
theorem holds_map_iff (σ : Sig.Hom S T) (M : Model T) (C : Contract S)
    (I : T.G → M.St → Prop) :
    Holds M (C.map σ) I ↔ Holds (M.reduct σ) C (push σ.proj I) := by
  constructor
  · intro h
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · obtain ⟨g, hi, hI⟩ := h.init s hs
      exact ⟨σ.proj g, hi, g, rfl, hI⟩
    · rintro f hf _ s a ⟨g', rfl, hI⟩ hp
      exact h.safe f (σ.le hf) g' s a hI ⟨hf, hp⟩
    · rintro f hf _ s a t r ⟨g', rfl, hI⟩ hp hs
      obtain ⟨h', hI', hq⟩ := h.post f (σ.le hf) g' s a t r hI ⟨hf, hp⟩ hs
      exact ⟨σ.proj h', ⟨h', rfl, hI'⟩, hq hf⟩
  · intro h
    refine ⟨fun s hs => ?_, ?_, ?_⟩
    · obtain ⟨_, hi, g', rfl, hI⟩ := h.init s hs
      exact ⟨g', hi, hI⟩
    · rintro f hf' g' s a hI ⟨hf, hp⟩
      exact h.safe f hf (σ.proj g') s a ⟨g', rfl, hI⟩ hp
    · rintro f hf' g' s a t r hI ⟨hf, hp⟩ hs
      obtain ⟨_, ⟨h', rfl, hI'⟩, hq⟩ := h.post f hf (σ.proj g') s a t r ⟨g', rfl, hI⟩ hp hs
      exact ⟨h', hI', fun _ => hq⟩

theorem Holds.congr_inv {X : Model S} {C : Contract S} {I I' : S.G → X.St → Prop}
    (h : Holds X C I) (e : I = I') : Holds X C I' := e ▸ h

/-- Along a surjective projection, the image of the pulled-back invariant is the invariant. -/
theorem push_comp {St G G' : Type} {p : G' → G} (hp : Function.Surjective p)
    (I : G → St → Prop) : push p (fun g' s => I (p g') s) = I := by
  funext g s
  apply propext
  constructor
  · rintro ⟨g', rfl, h⟩; exact h
  · intro h; obtain ⟨g', rfl⟩ := hp g; exact ⟨g', rfl, h⟩

/-- **The satisfaction condition**: `M ⊨ σ(C)` iff `M|σ ⊨ C`. -/
theorem sat_map_iff (σ : Sig.Hom S T) (M : Model T) (C : Contract S) :
    Sat M (C.map σ) ↔ Sat (M.reduct σ) C := by
  constructor
  · rintro ⟨I, h⟩; exact ⟨_, (holds_map_iff σ M C I).1 h⟩
  · rintro ⟨I, h⟩
    exact ⟨fun g' s => I (σ.proj g') s,
      (holds_map_iff σ M C _).2 (h.congr_inv (push_comp σ.surj I).symm)⟩

/-! ## Tensor -/

section Tensor

variable {N : Model T} {E : Contract T} {J : T.G → N.St → Prop}

/-- **The tensor of models meets the tensor of contracts**, relative to the product of the
invariants, when the function sets are disjoint. -/
theorem Holds.tensor (hd : ∀ f, f ∈ S.F → f ∉ T.F) (h₁ : Holds M C I) (h₂ : Holds N E J) :
    Holds (M.tensor N) (C.tensor E) (fun g s => I g.1 s.1 ∧ J g.2 s.2) := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨g1, hi1, hI1⟩ := h₁.init s.1 hs.1
    obtain ⟨g2, hi2, hI2⟩ := h₂.init s.2 hs.2
    exact ⟨(g1, g2), ⟨hi1, hi2⟩, hI1, hI2⟩
  · rintro f hf g s a ⟨hI1, hI2⟩ ⟨hp1, hp2⟩ hs
    rcases hs with ⟨hfS, o1, hs, ho⟩ | ⟨_, hfT, o2, hs, ho⟩
    · cases o1 with
      | none => exact h₁.safe f hfS g.1 s.1 a hI1 (hp1 hfS) hs
      | some x => cases ho
    · cases o2 with
      | none => exact h₂.safe f hfT g.2 s.2 a hI2 (hp2 hfT) hs
      | some x => cases ho
  · rintro f hf g s a t r ⟨hI1, hI2⟩ ⟨hp1, hp2⟩ hs
    rcases hs with ⟨hfS, o1, hs, ho⟩ | ⟨hnS, hfT, o2, hs, ho⟩
    · cases o1 with
      | none => cases ho
      | some x =>
        obtain ⟨x1, x2⟩ := x
        cases ho
        obtain ⟨g1', hI1', hq⟩ := h₁.post f hfS g.1 s.1 a x1 x2 hI1 (hp1 hfS) hs
        exact ⟨(g1', g.2), ⟨hI1', hI2⟩, fun _ => hq, fun hn => absurd hfS hn,
          fun hT => absurd hT (hd f hfS), fun _ => rfl⟩
    · cases o2 with
      | none => cases ho
      | some x =>
        obtain ⟨x1, x2⟩ := x
        cases ho
        obtain ⟨g2', hI2', hq⟩ := h₂.post f hfT g.2 s.2 a x1 x2 hI2 (hp2 hfT) hs
        exact ⟨(g.1, g2'), ⟨hI1, hI2'⟩, fun hS => absurd hS hnS, fun _ => rfl,
          fun _ => hq, fun hn => absurd hfT hn⟩

theorem Sat.tensor (hd : ∀ f, f ∈ S.F → f ∉ T.F) (h₁ : Sat M C) (h₂ : Sat N E) :
    Sat (M.tensor N) (C.tensor E) :=
  let ⟨_, hI⟩ := h₁; let ⟨_, hJ⟩ := h₂; ⟨_, hI.tensor hd hJ⟩

theorem Returns.tensor (h₁ : Returns M C I) (h₂ : Returns N E J) :
    Returns (M.tensor N) (C.tensor E) (fun g s => I g.1 s.1 ∧ J g.2 s.2) := by
  rintro f hf g s a ⟨hI1, hI2⟩ ⟨hp1, hp2⟩
  by_cases hfS : f ∈ S.F
  · obtain ⟨t, r, hs⟩ := h₁ f hfS g.1 s.1 a hI1 (hp1 hfS)
    exact ⟨(t, s.2), r, Or.inl ⟨hfS, some (t, r), hs, rfl⟩⟩
  · have hfT : f ∈ T.F := hf.resolve_left hfS
    obtain ⟨t, r, hs⟩ := h₂ f hfT g.2 s.2 a hI2 (hp2 hfT)
    exact ⟨(s.1, t), r, Or.inr ⟨hfS, hfT, some (t, r), hs, rfl⟩⟩

theorem Contract.NonVacuous.tensor (hd : ∀ f, f ∈ S.F → f ∉ T.F) {C : Contract S}
    {E : Contract T} (h₁ : C.NonVacuous) (h₂ : E.NonVacuous) : (C.tensor E).NonVacuous := by
  obtain ⟨M, I, hM, rM, s, hs⟩ := h₁
  obtain ⟨N, J, hN, rN, t, ht⟩ := h₂
  exact ⟨M.tensor N, _, hM.tensor hd hN, rM.tensor rN, (s, t), hs, ht⟩

/-- **The left factor back**: the tensor contract, restricted to `S`, is at least as strong as
`C`. -/
theorem Contract.le_restrict_inl (hd : ∀ f, f ∈ S.F → f ∉ T.F) (C : Contract S)
    (E : Contract T) : C.Le ((C.tensor E).restrict (Sig.inl S T)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨⟨g1, g2⟩, rfl, hi, _⟩; exact hi
  · intro f hf g a hp g' he
    exact ⟨fun _ => by subst he; exact hp, fun hT => absurd hT (hd f hf)⟩
  · rintro f hf g a r h _ ⟨g', h', rfl, rfl, hq, _⟩
    exact hq hf

/-- **The right factor back.** -/
theorem Contract.le_restrict_inr (hd : ∀ f, f ∈ S.F → f ∉ T.F) (C : Contract S)
    (E : Contract T) : E.Le ((C.tensor E).restrict (Sig.inr S T)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨⟨g1, g2⟩, rfl, _, hi⟩; exact hi
  · intro f hf g a hp g' he
    exact ⟨fun hS => absurd hf (hd f hS), fun _ => by subst he; exact hp⟩
  · rintro f hf g a r h _ ⟨g', h', rfl, rfl, _, _, hq, _⟩
    exact hq hf

/-- A model of the tensor contract, seen through `S` only, meets `C`. -/
theorem Sat.tensor_inl (hd : ∀ f, f ∈ S.F → f ∉ T.F) {X : Model (Sig.tensor S T)}
    (h : Sat X (C.tensor E)) : Sat (X.reduct (Sig.inl S T)) C :=
  (h.restrict _).mono (Contract.le_restrict_inl hd C E)

theorem Sat.tensor_inr (hd : ∀ f, f ∈ S.F → f ∉ T.F) {X : Model (Sig.tensor S T)}
    (h : Sat X (C.tensor E)) : Sat (X.reduct (Sig.inr S T)) E :=
  (h.restrict _).mono (Contract.le_restrict_inr hd C E)

end Tensor

/-! ## Non-vacuity -/

/-- **Every contract holds for its canonical model**, relative to the identity invariant. -/
theorem holds_canon (C : Contract S) : Holds C.canon C (fun g s => g = s) := by
  refine ⟨fun s hs => ⟨s, hs, rfl⟩, ?_, ?_⟩
  · rintro f hf g _ a rfl hp hs
    rcases hs with hn | ⟨_, _, he, _⟩
    · exact hn hp
    · cases he
  · rintro f hf g _ a t r rfl hp hs
    rcases hs with hn | ⟨h, r', he, hq⟩
    · exact absurd hp hn
    · cases he
      exact ⟨t, rfl, hq⟩

theorem returns_canon {C : Contract S} (hF : C.Feasible) :
    Returns C.canon C (fun g s => g = s) := by
  rintro f hf g _ a rfl hp
  obtain ⟨r, g', hq⟩ := hF.2 f hf g a hp
  exact ⟨g', r, Or.inr ⟨g', r, rfl, hq⟩⟩

/-- **A feasible contract is non-vacuous.** -/
theorem Contract.Feasible.nonVacuous {C : Contract S} (hF : C.Feasible) : C.NonVacuous :=
  ⟨C.canon, _, holds_canon C, returns_canon hF, hF.1⟩

end Silmaril.Libc.Contracts
