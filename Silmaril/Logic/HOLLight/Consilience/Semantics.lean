module

public import Silmaril.Logic.HOLLight.Consilience.Kernel
public import Silmaril.Logic.HOLLight.Soundness

@[expose] public section

/-!
# Independent denotation and semantic correspondence

The semantic rules below use the standard HOL carriers: two-valued Booleans,
natural-number individuals, full function spaces and Hilbert choice. Models,
type valuations and environments are shared interfaces, but term evaluation
is an independent inductive relation. Its correspondence is proved by
induction in both directions, at arbitrary environments and types.
-/
namespace Silmaril.Logic.HOLLight.Consilience

universe u

inductive Denotes {sig : Signature} (M : Model.{u} sig) (ρ : TypeValuation.{u})
    (ν : FreeEnv M ρ) : {Γ : List Ty} → BoundEnv M ρ Γ →
    Term → (A : Ty) → Value M ρ A → Prop where
  | bound {Γ} (η : BoundEnv M ρ Γ) {i A}
      (lookup : Γ[i]? = some A) (wf : A.WellFormed sig.tyOps) :
      Denotes M ρ ν η (.bound i) A (η i A lookup)
  | free {Γ} (η : BoundEnv M ρ Γ) (n : Nat) {A} (wf : A.WellFormed sig.tyOps) :
      Denotes M ρ ν η (.free n A) A (ν n A)
  | equality {Γ} (η : BoundEnv M ρ Γ) {A} (wf : A.WellFormed sig.tyOps) :
      Denotes M ρ ν η (.equality A) (.arr A (.arr A .bool))
        (Carrier.eq (A.denote M.toTypeModel ρ))
  | choice {Γ} (η : BoundEnv M ρ Γ) {A} (wf : A.WellFormed sig.tyOps) :
      Denotes M ρ ν η (.choice A) (.arr (.arr A .bool) A)
        (Carrier.choose (A.denote M.toTypeModel ρ))
  | user {Γ} (η : BoundEnv M ρ Γ) {c s As}
      (lookup : sig.consts[c]? = some s) (scheme : s.WellFormed sig.tyOps)
      (arity : As.length = s.arity) (args : ∀ A ∈ As, A.WellFormed sig.tyOps) :
      Denotes M ρ ν η (.user c As) (s.body.instantiate As)
        (M.constantInstance ρ lookup scheme.2 As arity)
  | app {Γ} {η : BoundEnv M ρ Γ} {A B f x}
      {vf : Value M ρ (.arr A B)} {vx : Value M ρ A} :
      Denotes M ρ ν η f (.arr A B) vf → Denotes M ρ ν η x A vx →
      Denotes M ρ ν η (.app f x) B (vf vx)
  | lam {Γ} {η : BoundEnv M ρ Γ} {A B b} (wf : A.WellFormed sig.tyOps)
      {f : Value M ρ (.arr A B)} :
      (∀ x, Denotes M ρ ν (η.extend x) b B (f x)) →
      Denotes M ρ ν η (.lam A b) (.arr A B) f

namespace Denotes

theorem encode {sig} {M : Model.{u} sig} {ρ ν Γ} {η : BoundEnv M ρ Γ} {t A v}
    (h : Denotes M ρ ν η t A v) : Eval M ρ ν η t.encode A v := by
  induction h with
  | bound η lookup wf => exact .bvar η lookup wf
  | free η n wf => exact .fvar η n wf
  | equality η wf => exact .const η (.eq wf)
  | choice η wf => exact .const η (.select wf)
  | user η lookup scheme arity args => exact .const η (.user lookup scheme arity args)
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam wf ih

theorem decode {sig} {M : Model.{u} sig} {ρ ν Γ} {η : BoundEnv M ρ Γ} {t A v}
    (h : Eval M ρ ν η t A v) : Denotes M ρ ν η (Term.decode t) A v := by
  induction h with
  | bvar η lookup wf => exact .bound η lookup wf
  | fvar η n wf => exact .free η n wf
  | const η hc =>
    cases hc with
    | eq wf => exact .equality η wf
    | select wf => exact .choice η wf
    | user lookup scheme arity args => exact .user η lookup scheme arity args
  | app _ _ ihf ihx => exact .app ihf ihx
  | lam wf _ ih => exact .lam wf ih

@[simp] theorem encode_iff {sig} {M : Model.{u} sig} {ρ ν Γ}
    {η : BoundEnv M ρ Γ} {t A v} : Eval M ρ ν η t.encode A v ↔ Denotes M ρ ν η t A v :=
  ⟨fun h => by simpa using decode h, encode⟩

@[simp] theorem decode_iff {sig} {M : Model.{u} sig} {ρ ν Γ}
    {η : BoundEnv M ρ Γ} {t A v} :
    Denotes M ρ ν η (Term.decode t) A v ↔ Eval M ρ ν η t A v :=
  ⟨fun h => by simpa using encode h, decode⟩

end Denotes

def Holds {sig} (M : Model.{u} sig) (ρ : TypeValuation.{u}) (ν : FreeEnv M ρ)
    (p : Term) : Prop :=
  ∃ v, Denotes M ρ ν BoundEnv.empty p .bool v ∧ Carrier.Truth v

def Models {sig} (M : Model.{u} sig) (T : Theory) : Prop :=
  ∀ p ∈ T, ∀ ρ ν, Holds M ρ ν p

def Entails {sig} (M : Model.{u} sig) (H : Context) (p : Term) : Prop :=
  ∀ ρ ν, (∀ q ∈ H, Holds M ρ ν q) → Holds M ρ ν p

@[simp] theorem holds_encode_iff {sig} {M : Model.{u} sig} {ρ ν p} :
    HOLLight.Holds M ρ ν p.encode ↔ Holds M ρ ν p := by
  simp [HOLLight.Holds, Holds]

@[simp] theorem models_encode_iff {sig} {M : Model.{u} sig} {T} :
    HOLLight.Models M (encodeTheory T) ↔ Models M T := by
  simp [HOLLight.Models, Models, HOLLight.Valid, encodeTheory]

@[simp] theorem entails_encode_iff {sig} {M : Model.{u} sig} {H p} :
    HOLLight.Entails M (encodeContext H) p.encode ↔ Entails M H p := by
  simp [HOLLight.Entails, HOLLight.HypsTrue, Entails, encodeContext]

/-- Soundness transfers using the actual rule translation and semantic bridge. -/
theorem Proof.sound {sig T H p} (h : Proof sig T H p) (M : Model.{u} sig)
    (model : Models M T) : Entails M H p :=
  entails_encode_iff.mp (h.encode.sound M (models_encode_iff.mpr model))

end Silmaril.Logic.HOLLight.Consilience
