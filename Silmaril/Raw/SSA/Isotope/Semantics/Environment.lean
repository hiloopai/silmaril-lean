module

public import Silmaril.Raw.SSA.Isotope.Semantics.ValueModel

/-! Typed environments and their shared operational representations. Canonical
encoding supplies unit for free names absent from the context; representation
judgments leave those unobservable names unconstrained. -/

@[expose] public section

namespace Silmaril.Isotope.Semantics

universe u v

variable {κ : Type u} (F : κ → Type u)

/-- Runtime free values agree with all visible typed bindings. -/
def FreeEnv.Encodes {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    (γ : FreeEnv (Ty.denote F) Γ) (raw : ν → Value (Sigma F)) : Prop :=
  ∀ x A h, raw x = encodeValue F A (γ x A h)

/-- Encode visible bindings, using unit only for names absent from the context. -/
def FreeEnv.encode {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    (γ : FreeEnv (Ty.denote F) Γ) (x : ν) : Value (Sigma F) :=
  match h : Γ.lookup x with
  | some A => encodeValue F A (γ x A h)
  | none => .unit

@[simp] theorem FreeEnv.encode_lookup {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    (γ : FreeEnv (Ty.denote F) Γ) (x : ν) (A : Ty κ) (h : Γ.lookup x = some A) :
    encode F γ x = encodeValue F A (γ x A h) := by
  unfold encode
  split
  · rename_i B hb
    have eq : B = A := Option.some.inj (hb.symm.trans h)
    cases eq
    rfl
  · rename_i hb
    cases hb.symm.trans h

@[simp] theorem FreeEnv.encode_missing {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    (γ : FreeEnv (Ty.denote F) Γ) (x : ν) (h : Γ.lookup x = none) :
    encode F γ x = .unit := by
  unfold encode
  split <;> simp_all

theorem FreeEnv.encode_encodes {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    (γ : FreeEnv (Ty.denote F) Γ) : Encodes F γ (encode F γ) :=
  encode_lookup F γ

/-- Operational representation determines every typed free binding. -/
theorem FreeEnv.Encodes.unique {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)}
    {γ δ : FreeEnv (Ty.denote F) Γ} {raw : ν → Value (Sigma F)}
    (hγ : Encodes F γ raw) (hδ : Encodes F δ raw) : γ = δ := by
  funext x A h
  exact encodeValue_injective F A ((hγ x A h).symm.trans (hδ x A h))

theorem FreeEnv.encode_injective {ν : Type v} [DecidableEq ν] {Γ : Ctx ν (Ty κ)} :
    Function.Injective (encode F (Γ := Γ)) := by
  intro γ δ h
  exact (encode_encodes F γ).unique F (h ▸ encode_encodes F δ)

/-- Every raw bound value represents the typed value in that slot. -/
def BoundEnv.Encodes {n : Nat} {β : BoundCtx (Ty κ) n}
    (ρ : BoundEnv (Ty.denote F) β) (raw : Fin n → Value (Sigma F)) : Prop :=
  ∀ i, raw i = encodeValue F (β.get i) (ρ i)

def BoundEnv.encode {n : Nat} {β : BoundCtx (Ty κ) n}
    (ρ : BoundEnv (Ty.denote F) β) (i : Fin n) : Value (Sigma F) :=
  encodeValue F (β.get i) (ρ i)

theorem BoundEnv.encode_encodes {n : Nat} {β : BoundCtx (Ty κ) n}
    (ρ : BoundEnv (Ty.denote F) β) : Encodes F ρ (encode F ρ) := fun _ => rfl

theorem BoundEnv.encodes_iff {n : Nat} {β : BoundCtx (Ty κ) n}
    (ρ : BoundEnv (Ty.denote F) β) (raw : Fin n → Value (Sigma F)) :
    Encodes F ρ raw ↔ raw = encode F ρ := ⟨funext, fun h i => congrFun h i⟩

theorem BoundEnv.encode_injective {n : Nat} {β : BoundCtx (Ty κ) n} :
    Function.Injective (encode F (β := β)) := by
  intro ρ σ h
  funext i
  exact encodeValue_injective F (β.get i) (congrFun h i)

@[simp] theorem BoundEnv.encode_snoc {n : Nat} {β : BoundCtx (Ty κ) n} {A : Ty κ}
    (ρ : BoundEnv (Ty.denote F) β) (a : Ty.denote F A) :
    encode F (ρ.snoc a) = Fin.cases (encodeValue F A a) (encode F ρ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

end Silmaril.Isotope.Semantics
