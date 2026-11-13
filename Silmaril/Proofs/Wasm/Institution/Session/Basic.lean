module

public import Silmaril.Wasm.Institution.Session.Defs
public import Silmaril.Wasm.Binaryen.PassAPI.Instances

@[expose] public section

/-!
# Wasm session logics: proofs

Validity in the session logics is silmaril's `ExportRefines`/`ExportEquiv`; translations
between the logics (lowering, lifting, equivalence into refinement, closure of a contract into
`Eq`-refinement); hiding; and passes as uniformly valid families. See
`Silmaril.Wasm.Institution.Session.Thms` for the summary.
-/

namespace Silmaril.Wasm.Institution.Session

open CategoryTheory Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

variable {H : Type}

/-! ## Session relations -/

/-- Under `Eq` the session relation is equality: its `ub` rule never fires. -/
theorem sessionRel_eq_iff {bs bs' : List (Behaviour Val)} :
    SessionRel (· = ·) bs bs' ↔ bs = bs' := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons hb _ ih => exact congrArg₂ List.cons hb ih
    | ub h => exact absurd ((h .traps).trans (h .diverges).symm) (by intro e; cases e)
  · rintro rfl
    exact SessionRel.refl (fun _ => rfl) _

/-! ## Refinement of semantic objects -/

theorem Refines.refl {R : BRel} (hR : ∀ b, R b b) {X : Iface} (a : Obj H X) : Refines R a a :=
  ⟨fun _ _ _ h => h, fun _ _ _ _ bs hbs => ⟨bs, hbs, SessionRel.refl hR bs⟩⟩

theorem Refines.trans {R : BRel} (hR : ∀ x y z, R x y → R y z → R x z) {X : Iface}
    {a b c : Obj H X} (h₁ : Refines R a b) (h₂ : Refines R b c) : Refines R a c :=
  ⟨fun s xas hs hc => h₁.1 s xas hs (h₂.1 s xas hs hc),
   fun s xas sc hs bs hbs =>
    let ⟨bs', hbs', r⟩ := h₁.2 s xas sc hs bs hbs
    let ⟨bs'', hbs'', r'⟩ := h₂.2 s xas sc hs bs' hbs'
    ⟨bs'', hbs'', r.trans hR r'⟩⟩

theorem Refines.mono {R R' : BRel} (hRR : ∀ x y, R x y → R' x y) {X : Iface} {a b : Obj H X}
    (h : Refines R a b) : Refines R' a b :=
  ⟨h.1, fun s xas sc hs bs hbs =>
    let ⟨bs', hbs', r⟩ := h.2 s xas sc hs bs hbs
    ⟨bs', hbs', r.mono hRR⟩⟩

/-- **Hiding preserves refinement**: refinement through `Y` implies refinement through any
`X ⊆ Y`. -/
theorem Refines.restrict {R : BRel} {X Y : Iface} (f : X ⟶ Y) {a b : Obj H Y}
    (h : Refines R a b) : Refines R (a.restrict f) (b.restrict f) :=
  ⟨h.1, fun s xas sc hs => h.2 s xas (sc.widen f.le) hs⟩

theorem Equiv.restrict {R : BRel} {X Y : Iface} (f : X ⟶ Y) {a b : Obj H Y}
    (h : Equiv R a b) : Equiv R (a.restrict f) (b.restrict f) :=
  ⟨h.1.restrict f, h.2.restrict f⟩

theorem refines_flip_eq_iff {X : Iface} {a b : Obj H X} :
    Refines (fun x y : Behaviour Val => y = x) a b ↔ Refines (· = ·) a b :=
  ⟨Refines.mono fun _ _ e => e.symm, Refines.mono fun _ _ e => e.symm⟩

/-- `Eq`-equivalence is two-sided `Eq`-refinement. -/
theorem equiv_eq_iff {X : Iface} {a b : Obj H X} :
    Equiv (· = ·) a b ↔ Refines (· = ·) a b ∧ Refines (· = ·) b a :=
  and_congr Iff.rfl refines_flip_eq_iff

/-- **Every contract is `Eq`-refinement against a closure**: `a ⊑_R b` iff `a ⊑_Eq close R b`.
For `R = TrapsUB` this reads: `trapsNeverHappen` refinement is plain refinement against the
specification in which every trap is replaced by arbitrary behaviour. -/
theorem refines_close_iff (R : BRel) {X : Iface} {a b : Obj H X} :
    Refines (· = ·) a (close R b) ↔ Refines R a b := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun s xas sc hs bs hbs => ?_⟩
    obtain ⟨bs', ⟨bs'', hbs'', r⟩, e⟩ := h₂ s xas sc hs bs hbs
    rw [sessionRel_eq_iff] at e
    subst e
    exact ⟨bs'', hbs'', r⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, fun s xas sc hs bs hbs =>
      ⟨bs, h₂ s xas sc hs bs hbs, SessionRel.refl (fun _ => rfl) bs⟩⟩

/-- A semantic object refines its closure under a reflexive relation. -/
theorem refines_close_self {R : BRel} (hR : ∀ b, R b b) {X : Iface} (b : Obj H X) :
    Refines (· = ·) b (close R b) :=
  (refines_close_iff R).2 (Refines.refl hR b)

/-! ## Denotations and validity -/

variable (P : Profile) (host : HostSemantics H)

/-- Denotations are natural: hiding the denotation at `Y` is the denotation at `X`. -/
theorem den_restrict {X Y : Iface} (f : X ⟶ Y) (m : Module) :
    (den P host Y m).restrict f = den P host X m := rfl

/-- **At the full interface, refinement of denotations is `ExportRefines`.** -/
theorem refines_den_univ_iff {R : BRel} {m m' : Module} :
    Refines R (den P host Set.univ m) (den P host Set.univ m') ↔ ExportRefines R P host m m' :=
  ⟨fun h => ⟨fun s xas c' hs hi => h.1 s xas hs ⟨c', hi⟩,
      fun s xas script hs bs hbs => h.2 s xas (Script.univ script) hs bs hbs⟩,
   fun h => ⟨fun s xas hs ⟨c', hi⟩ => h.instantiates s xas c' hs hi,
      fun s xas sc hs bs hbs => h.obs s xas sc.1 hs bs hbs⟩⟩

/-- At the full interface, equivalence of denotations is `ExportEquiv`. -/
theorem equiv_den_univ_iff {R : BRel} {m m' : Module} :
    Equiv R (den P host Set.univ m) (den P host Set.univ m') ↔ ExportEquiv R P host m m' :=
  and_congr (refines_den_univ_iff P host) (refines_den_univ_iff P host)

/-- **Validity of `m ⊑ m'` in the Core refinement logic is `ExportRefines R`.** -/
theorem valid_coreRef_iff (R : BRel) (m m' : Module) :
    (coreRef P host R).Valid ((coreRef P host R).leSen Set.univ m m') ↔
      ExportRefines R P host m m' :=
  ((coreRef P host R).valid_leSen_iff _ _ _).trans (refines_den_univ_iff P host)

/-- Validity of `m ⊑ m'` in the Binaryen IR refinement logic is `ExportRefines R` of the
lowerings. -/
theorem valid_birRef_iff (R : BRel) (m m' : BModule) :
    (birRef P host R).Valid ((birRef P host R).leSen Set.univ m m') ↔
      ExportRefines R P host m.lower m'.lower :=
  ((birRef P host R).valid_leSen_iff _ _ _).trans (refines_den_univ_iff P host)

/-- **Validity of `m ⊑ m'` in the Core equivalence logic is `ExportEquiv R`.** -/
theorem valid_coreEquiv_iff (R : BRel) (m m' : Module) :
    (coreEquiv P host R).Valid ((coreEquiv P host R).leSen Set.univ m m') ↔
      ExportEquiv R P host m m' :=
  ((coreEquiv P host R).valid_leSen_iff _ _ _).trans (equiv_den_univ_iff P host)

theorem valid_birEquiv_iff (R : BRel) (m m' : BModule) :
    (birEquiv P host R).Valid ((birEquiv P host R).leSen Set.univ m m') ↔
      ExportEquiv R P host m.lower m'.lower :=
  ((birEquiv P host R).valid_leSen_iff _ _ _).trans (equiv_den_univ_iff P host)

/-- In the `Eq`-refinement logic, validity of the equation `m ≐ m'` is `ExportEquiv Eq`. -/
theorem valid_coreRef_eqSen_iff (m m' : Module) :
    (coreRef P host (· = ·)).Valid ((coreRef P host (· = ·)).eqSen Set.univ m m') ↔
      ExportEquiv (· = ·) P host m m' := by
  refine ((coreRef P host (· = ·)).valid_eqSen_iff _ _ _).trans ?_
  refine (equiv_eq_iff (a := den P host Set.univ m) (b := den P host Set.univ m')).symm.trans ?_
  exact equiv_den_univ_iff P host

/-- **Hiding**: a refinement valid through `Y` is valid through every `X ⊆ Y`. -/
theorem valid_leSen_restrict {Prog : Type} {d : ∀ X : Iface, Prog → Obj H X}
    (hd : ∀ {X Y : Iface} (f : X ⟶ Y) (p : Prog), (d Y p).restrict f = d X p)
    (R : BRel) {X Y : Iface} (f : X ⟶ Y) (p q : Prog)
    (h : (mk Prog d (fun _ => Refines R)).Valid ((mk Prog d (fun _ => Refines R)).leSen Y p q)) :
    (mk Prog d (fun _ => Refines R)).Valid ((mk Prog d (fun _ => Refines R)).leSen X p q) := by
  have h' := ((mk Prog d (fun _ => Refines R)).valid_leSen_iff Y p q).1 h
  refine ((mk Prog d (fun _ => Refines R)).valid_leSen_iff X p q).2 ?_
  have : Refines R ((d Y p).restrict f) ((d Y q).restrict f) := Refines.restrict f h'
  rwa [hd, hd] at this

/-! ## Translations between session logics -/

open ObsSemantics

/-- **Change of programs**: a map of programs preserving denotations is a translation of
session logics (identity on interfaces and semantic objects). -/
def progT {Prog Prog' : Type} {d : ∀ X : Iface, Prog → Obj H X}
    {d' : ∀ X : Iface, Prog' → Obj H X} (g : Prog → Prog') (hg : ∀ X p, d' X (g p) = d X p)
    (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) :
    Translation (𝟭 Iface) (mk Prog d Le) (mk Prog' d' Le) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog := g
  sem_den X p := hg X p
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := Iff.rfl

/-- **Lowering** Binaryen IR to Core, as a translation of session logics. -/
def lowerT (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) :
    Translation (𝟭 Iface) (mk BModule (fun X m => den P host X m.lower) Le)
      (mk Module (den P host) Le) :=
  progT BModule.lower (fun _ _ => rfl) Le

/-- **Lifting** Core into Binaryen IR (every instruction a leaf), as a translation. -/
def liftT (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) :
    Translation (𝟭 Iface) (mk Module (den P host) Le)
      (mk BModule (fun X m => den P host X m.lower) Le) :=
  progT BModule.lift (fun X m => by simp only [lower_lift]) Le

/-- **Contract closure**: the `R`-refinement logic translates into the `Eq`-refinement logic,
`t ⊑ u ↦ t ⊑ close R u`. -/
def closeT {Prog : Type} (d : ∀ X : Iface, Prog → Obj H X) (R : BRel) :
    Translation (𝟭 Iface) (mk Prog d (fun _ => Refines R)) (mk Prog d (fun _ => Refines (· = ·))) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog p := p
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .le t (.app R u)
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := refines_close_iff R

/-- **Equivalence into refinement**: the `Eq`-equivalence logic translates into the
`Eq`-refinement logic, `t ≈ u ↦ t ≐ u`. -/
def equivT {Prog : Type} (d : ∀ X : Iface, Prog → Obj H X) :
    Translation (𝟭 Iface) (mk Prog d (fun _ => Equiv (· = ·)))
      (mk Prog d (fun _ => Refines (· = ·))) where
  sem _ a := a
  sem_restrict _ _ := rfl
  prog p := p
  sem_den _ _ := rfl
  op o := o
  sem_op _ _ _ := rfl
  atom t u := .eq t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := equiv_eq_iff.symm

/-- **Core is a retract of Binaryen IR, up to satisfaction**: lifting a sentence to Binaryen IR
and lowering it back yields a sentence with the same models. (Syntactically, equations come back
as conjunctions of two refinements.) -/
theorem sat_lowerT_liftT_iff (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) {K : Sig Iface}
    (β : (mk Module (den P host) Le).Model K) (s : Sen (mk Module (den P host) Le) K) :
    (mk Module (den P host) Le).Sat K β ((lowerT P host Le).sen ((liftT P host Le).sen s)) ↔
      (mk Module (den P host) Le).Sat K β s :=
  ((lowerT P host Le).sat_sen_iff _ β _).trans ((liftT P host Le).sat_sen_iff K β s)

theorem progT_surjective {Prog Prog' : Type} {d : ∀ X : Iface, Prog → Obj H X}
    {d' : ∀ X : Iface, Prog' → Obj H X} (g : Prog → Prog') (hg : ∀ X p, d' X (g p) = d X p)
    (Le : ∀ X : Iface, Obj H X → Obj H X → Prop) (X : Iface) :
    Function.Surjective ((progT g hg Le).sem X) := fun a => ⟨a, rfl⟩

theorem closeT_surjective {Prog : Type} (d : ∀ X : Iface, Prog → Obj H X) (R : BRel)
    (X : Iface) : Function.Surjective ((closeT d R).sem X) := fun a => ⟨a, rfl⟩

theorem equivT_surjective {Prog : Type} (d : ∀ X : Iface, Prog → Obj H X) (X : Iface) :
    Function.Surjective ((equivT d).sem X) := fun a => ⟨a, rfl⟩

/-- **Coarsening, as an entailment of the `Eq`-refinement logic**: from `t ⊑ u` follows
`t ⊑ close R u` for every reflexive `R`, at every signature and scope. -/
theorem entails_close {Prog : Type} (d : ∀ X : Iface, Prog → Obj H X) {R : BRel}
    (hR : ∀ b, R b b) {K : Sig Iface} (Z : Iface) (τ : Z ⟶ K.iface)
    (t u : (mk Prog d (fun _ => Refines (· = ·))).Tm K.V) :
    ((mk Prog d (fun _ => Refines (· = ·))).room K).Entails {⟨Z, τ, .le t u⟩}
      ⟨Z, τ, .le t (.app R u)⟩ := by
  intro β hβ
  have h := hβ _ rfl
  exact Refines.trans (fun _ _ _ e e' => e.trans e') h (refines_close_self hR _)

/-- Sanity check through the institutions: `ExportRefines Eq` implies `ExportRefines R` for a
reflexive `R`, by `entails_close` and borrowing along `closeT`. (Silmaril proves this directly
for `TrapsUB`: `ExportRefines.trapsUB_of_eq`.) -/
theorem exportRefines_of_eq {R : BRel} (hR : ∀ b, R b b) {m m' : Module}
    (h : ExportRefines (· = ·) P host m m') : ExportRefines R P host m m' := by
  rw [← valid_coreRef_iff, (closeT (den P host) R).valid_iff (closeT_surjective _ R)]
  intro β _
  exact entails_close (den P host) hR Set.univ (𝟙 _) (.prog m) (.prog m') β
    (by rintro _ rfl; exact (valid_coreRef_iff P host _ m m').2 h β (fun _ h => h.elim))

/-! ## Passes are uniformly valid families -/

open Silmaril.Wasm.Binaryen.PassAPI in
/-- **A verified pass for the refinement contract `R` is exactly an invariant-preserving
transformation `f` such that every sentence `f m ⊑ m` (for valid `m`) is valid in the Binaryen
IR `R`-refinement logic.** -/
def passEquivValid (R : BRel) (hR : PassAPI.BRel R) :
    PassAPI.Pass (refinesContract R P host hR) ≃
      {f : BModule → BModule // (∀ m, m.Ok → (f m).Ok) ∧
        ∀ m, m.Ok → (birRef P host R).Valid ((birRef P host R).leSen Set.univ (f m) m)} where
  toFun p := ⟨p.run, fun _ h => p.inv_run h,
    fun _ h => (valid_birRef_iff P host R _ _).2 (p.sound h)⟩
  invFun f := ⟨f.1, fun h => f.2.1 _ h, fun h => (valid_birRef_iff P host R _ _).1 (f.2.2 _ h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Silmaril.Wasm.Binaryen.PassAPI in
/-- A verified pass for the equivalence contract is exactly an invariant-preserving
transformation whose sentences `f m ⊑ m` are valid in the Binaryen IR `Eq`-equivalence
logic. -/
def passEquivValidEquiv :
    PassAPI.Pass (equivContract P host) ≃
      {f : BModule → BModule // (∀ m, m.Ok → (f m).Ok) ∧
        ∀ m, m.Ok → (birEquiv P host (· = ·)).Valid
          ((birEquiv P host (· = ·)).leSen Set.univ (f m) m)} where
  toFun p := ⟨p.run, fun _ h => p.inv_run h,
    fun _ h => (valid_birEquiv_iff P host _ _ _).2 (p.sound h)⟩
  invFun f := ⟨f.1, fun h => f.2.1 _ h,
    fun h => (valid_birEquiv_iff P host _ _ _).1 (f.2.2 _ h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `SoundPass` (`Silmaril.Wasm.Binaryen.Contracts`) in terms of validity. -/
theorem soundPass_iff_valid (R : BRel) (f : BModule → BModule) :
    SoundPass R P host f ↔ ∀ m : BModule, m.Ok →
      (f m).Ok ∧ (birRef P host R).Valid ((birRef P host R).leSen Set.univ (f m) m) := by
  refine forall_congr' fun m => imp_congr_right fun _ => and_congr Iff.rfl ?_
  exact (valid_birRef_iff P host R _ _).symm

end Silmaril.Wasm.Institution.Session
