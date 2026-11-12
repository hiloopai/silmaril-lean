module

public import Silmaril.Wasm.FnInst.Models.Version.Defs
public import Silmaril.Wasm.FnInst.Models.Inst.Thms

/-!
# Versions: conservative extension and its limits

* `valid_v_iff`: validity in the versioned institution is validity of the underlying sentence
  in every environment;
* `valid_up_iff`: **conservative extension** (syntax-only variant): along a version inclusion
  `v ≤ w`, a sentence allowed at `v` is valid at `v` iff its translation is valid at `w`;
* `valid_forget_iff`: forgetting the version neither adds nor removes validities;
* `admValid_anti`: in the context-restricting variant, validity transfers *down* (`w` to
  `v ≤ w`) when admissible behaviours grow with the version, and `admValid_of_valid`: what
  holds in every environment holds at every version. The upward direction fails
  (`Frag.Thms.not_admValid_up`).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

open CategoryTheory Silmaril.Inst

variable {L : FnSyntax} {V : Type} [Preorder V]

theorem valid_v_iff (S : FnSem L) (U : Versioned L V) {T : VSig L V} (φ : (vInst S U).Sen T) :
    (vInst S U).Valid φ ↔ ∀ env : Env S T.sig.n, Sen.Holds S env φ.1 := by
  constructor
  · intro h
    exact (sat_bot_iff S φ.1).1 (h (PMod.bot T.sig))
  · intro h M env _
    exact h env

/-- **Conservative extension** along a version inclusion. -/
theorem valid_up_iff (S : FnSem L) (U : Versioned L V) (T : Sig L) {v w : V} (h : v ≤ w)
    (φ : (vInst S U).Sen (⟨v, T⟩ : VSig L V)) :
    (vInst S U).Valid ((vInst S U).map (VSig.up T h) φ) ↔ (vInst S U).Valid φ := by
  rw [valid_v_iff, valid_v_iff]
  show (∀ env, Sen.Holds S env (Sen.map (fun i => i) φ.1)) ↔ _
  rw [show Sen.map (L := L) (fun i : Fin T.n => i) φ.1 = φ.1 from Sen.map_id φ.1]

theorem valid_forget_iff (S : FnSem L) (U : Versioned L V) {T : VSig L V}
    (φ : (vInst S U).Sen T) :
    (bodyInst S).Valid ((forget S U).sen T φ) ↔ (vInst S U).Valid φ := by
  rw [valid_v_iff]
  exact valid_body_iff S (T := T.sig) φ.1

/-- Context-restricting variant: validity transfers down along version inclusions. -/
theorem admValid_anti (S : FnSem L) {Adm : V → Set S.Den}
    (hAdm : ∀ {v w : V}, v ≤ w → Adm v ⊆ Adm w) {v w : V} (h : v ≤ w) {n : ℕ}
    {φ : Sen L n} (hw : AdmValid S Adm w φ) : AdmValid S Adm v φ :=
  fun env henv => hw env fun i => hAdm h (henv i)

omit [Preorder V] in
/-- What holds in every environment holds at every version. -/
theorem admValid_of_valid (S : FnSem L) (Adm : V → Set S.Den) (v : V) {n : ℕ} {φ : Sen L n}
    (h : ∀ env : Env S n, Sen.Holds S env φ) : AdmValid S Adm v φ :=
  fun env _ => h env

end Silmaril.Wasm.FnInst.Models
