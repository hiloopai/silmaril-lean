module

public import Silmaril.Wasm.FnInst.Models.Inst.Defs
public import Silmaril.Logic.Inst.Core.Thms

/-!
# The three model variants: validity, monotonicity and transfer

* `sat_body_iff`, `sat_sem_iff`: satisfaction in (a) and (c), unfolded;
* `valid_sem_iff`, `valid_body_iff`: validity in (c) and in (a) is the same: the sentence holds
  in every environment (`sat_bot_iff`: the least informative model already decides it);
* `valid_k_iff`: validity in (b) is validity in (a) for every semantics of the family;
* `sat_mono`: **monotonicity in information**: what holds with less information about the other
  bodies holds with more; `sat_bot_mono`;
* `transfer`: **the transfer theorem**: a sentence satisfied by the least informative model of
  `T` holds, translated, in every model of every signature `T` embeds into (every function of
  every module that contains the context);
* `distinctSome_anti`: a distinction (an environment of the model in which the sentence fails)
  found with more information is one with less information; the converse fails (`Frag.Thms`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open CategoryTheory Silmaril.Inst

variable {L : FnSyntax}

theorem sat_body_iff (S : FnSem L) {T : Sig L} (M : (bodyInst S).Mod T) (φ : (bodyInst S).Sen T) :
    M ⊨[bodyInst S] φ ↔ SemSat S (PMod.den S M) φ :=
  Iff.rfl

theorem sat_sem_iff (S : FnSem L) {T : Sig L} (E : (semInst S).Mod T) (φ : (semInst S).Sen T) :
    E ⊨[semInst S] φ ↔ SemSat S E φ :=
  Iff.rfl

/-- The least informative model satisfies `φ` iff `φ` holds in every environment. -/
theorem sat_bot_iff (S : FnSem L) {T : Sig L} (φ : Sen L T.n) :
    SemSat S ((PMod.bot T).den S) φ ↔ ∀ env : Env S T.n, Sen.Holds S env φ := by
  rw [PMod.den_bot]
  exact ⟨fun h env => h env trivial, fun h env _ => h env⟩

theorem valid_sem_iff (S : FnSem L) {T : Sig L} (φ : (semInst S).Sen T) :
    (semInst S).Valid φ ↔ ∀ env : Env S T.n, Sen.Holds S env φ :=
  ⟨fun h env => h (Set.univ : Set (Env S T.n)) env trivial, fun h _ env _ => h env⟩

theorem valid_body_iff (S : FnSem L) {T : Sig L} (φ : (bodyInst S).Sen T) :
    (bodyInst S).Valid φ ↔ ∀ env : Env S T.n, Sen.Holds S env φ := by
  constructor
  · intro h
    exact (sat_bot_iff S φ).1 (h (PMod.bot T))
  · intro h M env _
    exact h env

/-- Validity in (b) is validity in (a) for every semantics of the family. -/
theorem valid_k_iff {K : Type} (sems : K → FnSem L) {T : Sig L} (φ : (kInst sems).Sen T) :
    (kInst sems).Valid φ ↔ ∀ k, (bodyInst (sems k)).Valid (S := T) φ :=
  ⟨fun h k M => h ⟨k, M⟩, fun h M => h M.k M.m⟩

/-- **Monotonicity in information.** -/
theorem sat_mono (S : FnSem L) {T : Sig L} {M M' : PMod T} (h : M.Le M') {φ : Sen L T.n}
    (hφ : SemSat S (M.den S) φ) : SemSat S (M'.den S) φ :=
  semSat_mono S (PMod.den_anti S h) hφ

/-- What the least informative model satisfies, every model satisfies. -/
theorem sat_bot_mono (S : FnSem L) {T : Sig L} (M : PMod T) {φ : Sen L T.n}
    (hφ : SemSat S ((PMod.bot T).den S) φ) : SemSat S (M.den S) φ :=
  sat_mono S (PMod.bot_le M) hφ

/-- **Transfer.** A sentence satisfied by the least informative model of `T` holds, translated
along any signature morphism `σ : T ⟶ U`, in every model of `U`. -/
theorem transfer (S : FnSem L) {T U : Sig L} (σ : T ⟶ U) {φ : Sen L T.n}
    (hφ : SemSat S ((PMod.bot T).den S) φ) (M : (bodyInst S).Mod U) :
    M ⊨[bodyInst S] (bodyInst S).map σ φ := by
  have hred : SemSat S ((PMod.reduct σ M).den S) φ := sat_bot_mono S _ hφ
  exact ((bodyPlain S).sat_map σ M φ).2 hred

/-- The same, from validity. -/
theorem transfer_valid (S : FnSem L) {T U : Sig L} (σ : T ⟶ U) {φ : (bodyInst S).Sen T}
    (hφ : (bodyInst S).Valid φ) : (bodyInst S).Valid ((bodyInst S).map σ φ) :=
  fun M => transfer S σ (hφ (PMod.bot T)) M

/-- Some environment of `M` violates `φ`: an observable difference *in some completion*. -/
def DistinctSome (S : FnSem L) {T : Sig L} (M : PMod T) (φ : Sen L T.n) : Prop :=
  ∃ env ∈ M.den S, ¬ Sen.Holds S env φ

theorem distinctSome_iff (S : FnSem L) {T : Sig L} (M : PMod T) (φ : Sen L T.n) :
    DistinctSome S M φ ↔ ¬ SemSat S (M.den S) φ := by
  simp only [DistinctSome, SemSat, not_forall, exists_prop]

/-- A distinction found with more information is one with less. -/
theorem distinctSome_anti (S : FnSem L) {T : Sig L} {M M' : PMod T} (h : M.Le M')
    {φ : Sen L T.n} (hd : DistinctSome S M' φ) : DistinctSome S M φ := by
  obtain ⟨env, henv, hn⟩ := hd
  exact ⟨env, PMod.den_anti S h henv, hn⟩

/-- The comorphism (c) → (a) transfers validity: valid with semantic models, valid with
bodies. -/
theorem valid_body_of_sem (S : FnSem L) {T : Sig L} {φ : (semInst S).Sen T}
    (h : (semInst S).Valid φ) : (bodyInst S).Valid (S := T) φ :=
  fun M => h (PMod.den S M)

end Silmaril.Wasm.FnInst.Models
