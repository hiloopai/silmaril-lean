module

public import Silmaril.Wasm.Institution.Generic.Defs
public import Silmaril.Wasm.Institution.Api.Defs
public import Silmaril.Compile.Category.Pass

@[expose] public section

/-!
# Languages as observational semantics; realisations as comorphisms

The institutions induced by the category of Wasm programs are built with Silmaril's generic
construction `ObsSemantics ⇒ institution` (`Silmaril.Wasm.Institution.Generic`), not by a second
institution construction.

* `obsSem L`: a language of the compiler category (`Silmaril.Compile.Category.Language`, in
  `Type`) as an observational semantics over its discrete category of interfaces: semantic
  objects are behaviour sets, a program denotes its behaviours, refinement `a ⊑ b` is
  `a ⊆ b`. Its institution `(obsSem L).inst` is the *behavioural institution* of `L`
  (the old `Language.inst` of `Silmaril/Compile/Category/Language.lean`, here with Silmaril's
  variables, scopes and formulas). `valid_leSen_iff`: `p ⊑ q` is valid iff
  `beh p ⊆ beh q`, i.e. `q` is refined by `p` (`Language.Refines q p` at equal interfaces).
* `Realiser L L'`: a total translation of programs whose target behaviours, read back along an
  injective map of observations, are exactly the source behaviours. It is a valid compiler at
  its read-back convention (`Realiser.compiler`), and a translation of observational semantics
  (`Realiser.translation`), hence an institution comorphism `(obsSem L).inst → (obsSem L').inst`
  (`Realiser.coHom`) that is model-expansive, so borrows entailment, when the read-back is
  surjective (`Realiser.entails_iff`, `Realiser.valid_iff`).

The convention of a realiser is a *read-back* convention (`Convention.ReadBack`), the case in
which an earlier development had the comorphism `Convention.comorphism`; Silmaril's translation
gives the same satisfaction condition (`Translation.sat_sen_iff`).
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Wasm.Institution

/-- **The observational semantics of a language**: behaviour sets over its discrete interfaces,
programs denoting their behaviours, refinement as inclusion, no operators. -/
def obsSem (L : Language.{0}) : ObsSemantics (Discrete L.Iface) where
  Sem _ := Set L.Obs
  restrict _ a := a
  restrict_id _ := rfl
  restrict_comp _ _ _ := rfl
  Prog := L.Prog
  den _ p := L.beh p
  Op := PEmpty
  op _ o _ := o.elim
  Le _ a b := a ⊆ b

/-- The behavioural institution of a language. -/
abbrev behInst (L : Language.{0}) : Silmaril.Inst.Institution₁ :=
  (obsSem L).inst

/-- **Validity of `p ⊑ q` in the behavioural institution is behaviour inclusion.** -/
theorem valid_leSen_iff (L : Language.{0}) (X : Discrete L.Iface) (p q : L.Prog) :
    (obsSem L).Valid ((obsSem L).leSen X p q) ↔ L.beh p ⊆ L.beh q :=
  (obsSem L).valid_leSen_iff X p q

/-- At equal interfaces, validity of `p ⊑ q` is behavioural refinement of `q` by `p`. -/
theorem valid_leSen_iff_refines (L : Language.{0}) (X : Discrete L.Iface) {p q : L.Prog}
    (h : L.iface p = L.iface q) :
    (obsSem L).Valid ((obsSem L).leSen X p q) ↔ L.Refines q p := by
  rw [valid_leSen_iff]
  exact ⟨fun hs => ⟨h, hs⟩, fun hr => hr.2⟩

/-- A **realiser** of `L` in `L'`: a total translation of programs whose target behaviours, read
back along an injective map of observations, are exactly the source behaviours. -/
structure Realiser (L L' : Language.{0}) where
  /-- The interface map. -/
  Φ : L.Iface → L'.Iface
  /-- The translation of programs. -/
  prog : L.Prog → L'.Prog
  /-- Reading target observations back. -/
  g : L'.Obs → L.Obs
  g_injective : Function.Injective g
  iface : ∀ p, L'.iface (prog p) = Φ (L.iface p)
  /-- Exact realisation. -/
  beh : ∀ p, g '' L'.beh (prog p) = L.beh p

namespace Realiser

variable {L L' : Language.{0}} (T : Realiser L L')

/-- The read-back convention of a realiser. -/
def conv : L ⟶ L' := ⟨T.Φ, fun o o' => o = T.g o'⟩

/-- The convention of a realiser is a read-back. -/
def readBack : Convention.ReadBack T.conv := ⟨T.g, fun _ _ => Iff.rfl⟩

/-- The translation is a valid compilation at the read-back convention. -/
theorem valid (p : L.Prog) : Valid T.conv p (T.prog p) := by
  refine (valid_iff_beh _ _ _).2 ⟨(T.iface p).symm, fun o' ho' => ⟨T.g o', ?_, rfl⟩⟩
  rw [← T.beh p]
  exact Set.mem_image_of_mem T.g ho'

/-- The (total) compiler of a realiser. -/
def compiler : Compiler L L' where
  conv := T.conv
  run p := some (T.prog p)
  sound p _ h := Option.some.inj h ▸ T.valid p

/-- The pass of a realiser, at its convention. -/
def pass : Pass T.conv := Pass.ofCompiler T.compiler

/-- Refinement is preserved and reflected by a realiser. -/
theorem refines_iff {p q : L.Prog} (hi : L.iface p = L.iface q) :
    L'.Refines (T.prog p) (T.prog q) ↔ L.Refines p q := by
  have hi' : L'.iface (T.prog q) = L'.iface (T.prog p) := by
    rw [T.iface, T.iface, hi]
  constructor
  · intro h
    refine ⟨hi.symm, ?_⟩
    rw [← T.beh p, ← T.beh q]
    exact Set.image_mono h.2
  · intro h
    refine ⟨hi', ?_⟩
    have hs : T.g '' L'.beh (T.prog q) ⊆ T.g '' L'.beh (T.prog p) := by
      rw [T.beh p, T.beh q]
      exact h.2
    exact (Set.image_subset_image_iff T.g_injective).1 hs

/-- The interface functor of a realiser. -/
def ifaceFunctor : Discrete L.Iface ⥤ Discrete L'.Iface :=
  Discrete.functor fun X => Discrete.mk (T.Φ X)

/-- **A realiser is a translation of observational semantics**: models read back along `g`,
programs translated, refinement atoms kept. -/
def translation : ObsSemantics.Translation T.ifaceFunctor (obsSem L) (obsSem L') where
  sem _ b := T.g '' b
  sem_restrict _ _ := rfl
  prog := T.prog
  sem_den _ p := T.beh p
  op o := o.elim
  sem_op _ o _ := o.elim
  atom t u := .le t u
  atom_mapVars _ _ _ := rfl
  atom_holds _ _ _ _ _ := (Set.image_subset_image_iff T.g_injective).symm

/-- **The comorphism of behavioural institutions of a realiser.** -/
def coHom : Silmaril.Logic.Institution.Inst.CoHom (behInst L) (behInst L') :=
  T.translation.coHom

/-- With a surjective read-back the semantic maps of the translation are surjective. -/
theorem sem_surjective (hg : Function.Surjective T.g) (X : Discrete L.Iface) :
    Function.Surjective (T.translation.sem X) := by
  intro B
  refine ⟨T.g ⁻¹' B, ?_⟩
  exact Set.image_preimage_eq B hg

/-- **Borrowing along a realiser** with a surjective read-back: entailment in the behavioural
institution of `L` is entailment of the translated sentences in that of `L'`. -/
theorem entails_iff (hg : Function.Surjective T.g) (K : Sig (Discrete L.Iface))
    (Γ : Set ((obsSem L).Sen K)) (s : (obsSem L).Sen K) :
    ((obsSem L).room K).Entails Γ s ↔
      ((obsSem L').room ((Sig.map T.ifaceFunctor).obj K)).Entails
        (T.translation.sen '' Γ) (T.translation.sen s) :=
  T.translation.entails_iff (T.sem_surjective hg) K Γ s

/-- Validity is preserved and reflected along a realiser with a surjective read-back. -/
theorem valid_iff (hg : Function.Surjective T.g) {K : Sig (Discrete L.Iface)}
    (s : (obsSem L).Sen K) :
    (obsSem L).Valid s ↔ (obsSem L').Valid (T.translation.sen s) :=
  T.translation.valid_iff (T.sem_surjective hg) s

/-- A realiser is a realising elaboration in the sense of silmaril-lean's factorisation API
(`Realises`), so valid compilations at composite conventions factor through it
(`Realises.factor`). -/
theorem realises :
    Realises T.conv Set.univ T.prog := by
  refine ⟨fun p _ => T.iface p, fun p _ => ?_⟩
  rw [Convention.ReadBack.lift_eq T.readBack]
  ext o'
  constructor
  · intro ho'
    have hm : T.g o' ∈ L.beh p := by
      rw [← T.beh p]
      exact Set.mem_image_of_mem T.g ho'
    exact hm
  · intro ho'
    have hm : T.g o' ∈ T.g '' L'.beh (T.prog p) := by
      rw [T.beh p]
      exact ho'
    obtain ⟨o'', ho'', he⟩ := hm
    have he' : o'' = o' := T.g_injective he
    exact he' ▸ ho''

/-- Composition of realisers. -/
def comp {L'' : Language.{0}} (U : Realiser L' L'') : Realiser L L'' where
  Φ := U.Φ ∘ T.Φ
  prog := U.prog ∘ T.prog
  g := T.g ∘ U.g
  g_injective := T.g_injective.comp U.g_injective
  iface p := by
    show L''.iface (U.prog (T.prog p)) = U.Φ (T.Φ (L.iface p))
    rw [U.iface, T.iface]
  beh p := by
    show (T.g ∘ U.g) '' L''.beh (U.prog (T.prog p)) = L.beh p
    rw [Set.image_comp, U.beh, T.beh]

end Realiser

end Silmaril.Wasm.Category
