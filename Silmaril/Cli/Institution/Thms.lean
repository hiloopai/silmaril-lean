module

public import Silmaril.Cli.Institution.Defs

/-!
# The CLI institution: level laws and transfer lemmas

PROVED (standard axioms):

* the level round trips: `inProj_embed`, `outProj_outEmbed`, and, below a level,
  `embed_inProj_embed`, `outProj_outEmbed_outProj`;
* **the levels form a chain of interfaces**: `hom_self`, `hom_comp` (for `L ≤ L'`, any `L''`) and the
  functor `Level.toSig : Level ⥤ Sig`; the same for the uniform morphisms (`homAll_comp`);
* **satisfaction through a level**: `sat_lift_iff` (a full model meets the lift of an `L`
  sentence iff its `L` reduct meets the sentence), `sat_liftAll_iff`;
* the shape of lifted sentences: `lift_iff`, `liftAll_iff`, `liftAll_le_lift`, and the
  standard sentences lifted (`lift_filter_iff`, `lift_prints_iff`);
* transfer: `Model.Sat.mono` (along refinement of the sentence), `Model.Sat.anti` (to a model
  with fewer runs: a finer process model), `Model.Sat.inf`.
-/

@[expose] public section

namespace Silmaril.Cli.Institution

open CategoryTheory

/-! ## Satisfaction -/

theorem Model.Sat.mono {A : Sig} {M : Model A} {φ ψ : Sen A} (h : M.Sat φ) (hφ : φ ≤ ψ) :
    M.Sat ψ := fun i o hr => hφ i o (h i o hr)

/-- **A model with fewer runs** (e.g. the program under a finer process or ISA model) satisfies
what the coarser one does. -/
theorem Model.Sat.anti {A : Sig} {M N : Model A} {φ : Sen A} (h : N.Sat φ) (hMN : M ≤ N) :
    M.Sat φ := fun i o hr => h i o (hMN i o hr)

theorem Model.Sat.inf {A : Sig} {M : Model A} {φ ψ : Sen A} (h : M.Sat φ) (h' : M.Sat ψ) :
    M.Sat (φ ⊓ ψ) := fun i o hr => ⟨h i o hr, h' i o hr⟩

theorem Model.sat_iff_le {A : Sig} (M : Model A) (φ : Sen A) : M.Sat φ ↔ M.Run ≤ φ := Iff.rfl

namespace Level

/-! ## Round trips -/

theorem inProj_embed : (L : Level) → (a : L.In) → L.inProj (L.embed a) = a
  | .status, () => rfl
  | .stream, _ => rfl
  | .command, _ => rfl
  | .full, _ => rfl

theorem outProj_outEmbed : (L : Level) → (o : L.Out) → L.outProj (L.outEmbed o) = o
  | .status, _ => rfl
  | .stream, _ => rfl
  | .command, _ => rfl
  | .full, _ => rfl

private theorem not_le_of_rank {L L' : Level} (h : L ≤ L') (hr : L'.rank < L.rank) : False := by
  have := le_iff_rank.mp h; omega

/-- Below a level, the default expansion is stable: `L'` keeps what `L` set. -/
theorem embed_inProj_embed {L L' : Level} (h : L ≤ L') (a : L.In) :
    L'.embed (L'.inProj (L.embed a)) = L.embed a := by
  cases L <;> cases L' <;>
    first | rfl | exact (not_le_of_rank h (by simp [rank])).elim

/-- Below a level, projecting through it loses nothing `L` sees. -/
theorem outProj_outEmbed_outProj {L L' : Level} (h : L ≤ L') (o : Obs) :
    L.outProj (L'.outEmbed (L'.outProj o)) = L.outProj o := by
  cases L <;> cases L' <;>
    first | rfl | exact (not_le_of_rank h (by simp [rank])).elim

/-- What `L` sees of a full invocation is what it sees through `L'` above it. -/
theorem inProj_embed_inProj {L L' : Level} (h : L ≤ L') (i : Input) :
    L.inProj (L'.embed (L'.inProj i)) = L.inProj i := by
  cases L <;> cases L' <;>
    first | rfl | exact (not_le_of_rank h (by simp [rank])).elim

/-! ## The chain of interfaces -/

theorem le_full (L : Level) : L ≤ .full := le_iff_rank.mpr (by cases L <;> simp [rank])

theorem hom_self (L : Level) : hom L L = 𝟙 L.sig := by
  apply Hom.ext
  · funext a b; apply propext
    show b = L.inProj (L.embed a) ↔ a = b
    rw [inProj_embed]; exact eq_comm
  · funext o; exact outProj_outEmbed L o

theorem hom_comp {L L' L'' : Level} (h : L ≤ L') :
    hom L L' ≫ hom L' L'' = hom L L'' := by
  apply Hom.ext
  · funext a c; apply propext
    show (∃ b, b = L'.inProj (L.embed a) ∧ c = L''.inProj (L'.embed b)) ↔
      c = L''.inProj (L.embed a)
    constructor
    · rintro ⟨b, rfl, rfl⟩; rw [embed_inProj_embed h]
    · rintro rfl; exact ⟨_, rfl, by rw [embed_inProj_embed h]⟩
  · funext o
    show L.outProj (L'.outEmbed (L'.outProj (L''.outEmbed o))) = L.outProj (L''.outEmbed o)
    exact outProj_outEmbed_outProj h _

theorem homAll_comp {L L' L'' : Level} (h : L ≤ L') :
    homAll L L' ≫ homAll L' L'' = homAll L L'' := by
  apply Hom.ext
  · funext a c; apply propext
    show (∃ b, L.inProj (L'.embed b) = a ∧ L'.inProj (L''.embed c) = b) ↔
      L.inProj (L''.embed c) = a
    constructor
    · rintro ⟨b, rfl, rfl⟩; exact (inProj_embed_inProj h _).symm
    · rintro rfl; exact ⟨_, inProj_embed_inProj h _, rfl⟩
  · funext o
    show L.outProj (L'.outEmbed (L'.outProj (L''.outEmbed o))) = L.outProj (L''.outEmbed o)
    exact outProj_outEmbed_outProj h _

/-- **The levels as a chain of interfaces** (default expansion). -/
def toSig : Level ⥤ Sig where
  obj := sig
  map {L L'} _ := hom L L'
  map_id L := hom_self L
  map_comp f _ := (hom_comp f.le).symm

/-- The levels as interfaces, along the uniform morphisms. -/
def toSigAll : Level ⥤ Sig where
  obj := sig
  map {L L'} _ := homAll L L'
  map_id L := by
    apply Hom.ext
    · funext a b; apply propext
      show L.inProj (L.embed b) = a ↔ a = b
      rw [inProj_embed]; exact eq_comm
    · funext o; exact outProj_outEmbed L o
  map_comp f _ := (homAll_comp f.le).symm

/-! ## Lifted sentences -/

theorem lift_iff {L : Level} (φ : Sen L.sig) (i : Input) (o : Obs) :
    lift φ i o ↔ ∀ a, i = L.embed a → φ a (L.outProj o) := Iff.rfl

/-- On a default invocation, the lift is the sentence. -/
theorem lift_embed_iff {L : Level} (φ : Sen L.sig) (a : L.In) (o : Obs) :
    lift φ (L.embed a) o ↔ φ a (L.outProj o) := by
  constructor
  · intro H; exact H a rfl
  · intro H a' he
    have he' : L.embed a = L.embed a' := he
    have : a' = a := by
      have := congrArg L.inProj he'; rw [inProj_embed, inProj_embed] at this; exact this.symm
    exact this ▸ H

theorem liftAll_iff {L : Level} (φ : Sen L.sig) (i : Input) (o : Obs) :
    liftAll φ i o ↔ φ (L.inProj i) (L.outProj o) :=
  ⟨fun H => H _ rfl, fun H _ he => he ▸ H⟩

/-- The uniform claim implies the default one. -/
theorem liftAll_le_lift {L : Level} (φ : Sen L.sig) : liftAll φ ≤ lift φ := by
  intro i o H a he
  have := (liftAll_iff φ i o).mp H
  have he' : i = L.embed a := he
  rw [he', inProj_embed] at this
  exact this

/-- **Satisfaction through a level.** -/
theorem sat_lift_iff {L : Level} (M : Model Level.full.sig) (φ : Sen L.sig) :
    M.Sat (lift φ) ↔ (L.reduct M).Sat φ := Hom.sat_sen_iff _ M φ

theorem sat_liftAll_iff {L : Level} (M : Model Level.full.sig) (φ : Sen L.sig) :
    M.Sat (liftAll φ) ↔ ((homAll L .full).mod M).Sat φ := Hom.sat_sen_iff _ M φ

/-- A sentence lifted from `L` to `L'`, then to the full level, is its lift. -/
theorem lift_hom {L L' : Level} (h : L ≤ L') (φ : Sen L.sig) :
    lift ((hom L L').sen φ) = lift φ := by
  show (hom L' .full).sen ((hom L L').sen φ) = (hom L .full).sen φ
  rw [← hom_comp (L'' := .full) h]
  exact (congrFun (Hom.sen_comp (hom L L') (hom L' .full)) φ).symm

end Level

/-! ## The standard sentences, lifted -/

open Level in
theorem lift_filter_iff (f : Bytes → Bytes) (s : Bytes) (o : Obs) :
    lift (Sen.filter f) { stdin := s } o ↔ o.stdout = f s ∧ o.exit = 0 :=
  lift_embed_iff (L := .stream) _ s o

open Level in
theorem lift_prints_iff (out : Bytes) (s : Bytes) (o : Obs) :
    lift (Sen.prints out) { stdin := s } o ↔ o.stdout = out ∧ o.exit = 0 :=
  lift_embed_iff (L := .stream) _ s o

end Silmaril.Cli.Institution
