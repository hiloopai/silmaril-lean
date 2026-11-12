module

public import Silmaril.SSA.Isotope.Types.Thms
public import Silmaril.Raw.SSA.Isotope.Ctx.Bound

/-! # Maps of primitive signatures

The instruction, type, and effect components commute with the source, target,
and effect assignments. Preservation of type formers is separate: sequential
syntax only needs products and unit, whereas case and iteration also need sums.
-/

@[expose] public section

universe u v w x y z a b c d

namespace Silmaril.Isotope

namespace Ctx

/-- Change every slot's type while retaining names and shadowing. -/
def mapTypes {ν : Type a} {τ : Type u} {υ : Type v} (f : τ → υ) : Ctx ν τ → Ctx ν υ
  | .nil => .nil
  | .snoc Γ n A => .snoc (mapTypes f Γ) n (f A)

@[simp] theorem mapTypes_id {ν : Type a} {τ : Type u} (Γ : Ctx ν τ) :
    Γ.mapTypes id = Γ := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => simp [mapTypes, ih]

@[simp] theorem mapTypes_comp {ν : Type a} {τ : Type u} {υ : Type v} {κ : Type w}
    (g : υ → κ) (f : τ → υ) (Γ : Ctx ν τ) :
    (Γ.mapTypes f).mapTypes g = Γ.mapTypes (g ∘ f) := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih => simp [mapTypes, ih]

@[simp] theorem lookup_mapTypes {ν : Type a} [DecidableEq ν] {τ : Type u} {υ : Type v}
    (f : τ → υ) (Γ : Ctx ν τ) (x : ν) :
    (mapTypes f Γ).lookup x = (Γ.lookup x).map f := by
  induction Γ with
  | nil => rfl
  | snoc Γ n A ih =>
      cases n with
      | none => simpa [mapTypes, lookup] using ih
      | some y => by_cases h : x = y <;> simp [mapTypes, lookup, h, ih]

end Ctx

namespace BoundCtx

/-- Change every bound slot's type without changing its de Bruijn index. -/
def mapTypes {τ : Type u} {υ : Type v} (f : τ → υ) : {n : Nat} → BoundCtx τ n → BoundCtx υ n
  | _, .nil => .nil
  | _, .snoc β A => .snoc (mapTypes f β) (f A)

@[simp] theorem mapTypes_id {τ : Type u} {n : Nat} (β : BoundCtx τ n) :
    β.mapTypes id = β := by
  induction β with
  | nil => rfl
  | snoc β A ih => simp [mapTypes, ih]

@[simp] theorem mapTypes_comp {τ : Type u} {υ : Type v} {κ : Type w}
    (g : υ → κ) (f : τ → υ) {n : Nat} (β : BoundCtx τ n) :
    (β.mapTypes f).mapTypes g = β.mapTypes (g ∘ f) := by
  induction β with
  | nil => rfl
  | snoc β A ih => simp [mapTypes, ih]

@[simp] theorem get_mapTypes {τ : Type u} {υ : Type v} (f : τ → υ)
    {n : Nat} (β : BoundCtx τ n) (i : Fin n) : (mapTypes f β).get i = f (β.get i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β A ih => exact Fin.cases rfl ih i

end BoundCtx

namespace Morphism

/-- A map of primitive signatures, allowing types and effects to vary. -/
structure SignatureMap (Φ : Type u) (Ψ : Type v) (τ : Type w) (υ : Type x)
    (ε : Type y) (δ : Type z) [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ] where
  instr : Φ → Ψ
  ty : τ → υ
  eff : ε → δ
  source : ∀ f, instrSrc (instr f) = ty (instrSrc f)
  target : ∀ f, instrTrg (instr f) = ty (instrTrg f)
  effect : ∀ f, instrEff (instr f) = eff (instrEff f)

namespace SignatureMap

variable {Φ : Type u} {Ψ : Type v} {τ : Type w} {υ : Type x} {ε : Type y} {δ : Type z}
variable [HasTy Φ τ] [HasTy Ψ υ] [HasEff Φ ε] [HasEff Ψ δ]

@[ext] theorem ext {f g : SignatureMap Φ Ψ τ υ ε δ}
    (hinstr : f.instr = g.instr) (hty : f.ty = g.ty) (heff : f.eff = g.eff) : f = g := by
  cases f
  cases g
  cases hinstr
  cases hty
  cases heff
  rfl

class PreservesProducts [HasProduct τ] [HasUnit τ] [HasProduct υ] [HasUnit υ]
    (g : SignatureMap Φ Ψ τ υ ε δ) : Prop where
  unit : g.ty Silmaril.unit = Silmaril.unit
  product : ∀ A B, g.ty (Silmaril.product A B) = Silmaril.product (g.ty A) (g.ty B)

class PreservesSums [HasCoproduct τ] [HasEmpty τ] [HasCoproduct υ] [HasEmpty υ]
    (g : SignatureMap Φ Ψ τ υ ε δ) : Prop where
  empty : g.ty Silmaril.empty = Silmaril.empty
  coprod : ∀ A B, g.ty (Silmaril.coprod A B) = Silmaril.coprod (g.ty A) (g.ty B)

attribute [simp] PreservesProducts.unit PreservesProducts.product PreservesSums.empty PreservesSums.coprod

/-- Effect preservation sends pure primitives to pure primitives. -/
theorem pure (g : SignatureMap Φ Ψ τ υ ε δ) {p : ε} (f : Φ) (h : IsPure p f) :
    IsPure (g.eff p) (g.instr f) := (g.effect f).trans (congrArg g.eff h)

/-- The identity primitive signature map. -/
def id : SignatureMap Φ Φ τ τ ε ε where
  instr := _root_.id
  ty := _root_.id
  eff := _root_.id
  source _ := rfl
  target _ := rfl
  effect _ := rfl

instance [HasProduct τ] [HasUnit τ] : PreservesProducts (id (Φ := Φ) (τ := τ) (ε := ε)) where
  unit := rfl
  product _ _ := rfl

instance [HasCoproduct τ] [HasEmpty τ] : PreservesSums (id (Φ := Φ) (τ := τ) (ε := ε)) where
  empty := rfl
  coprod _ _ := rfl

/-- Compose instruction, type, and effect translations componentwise. -/
def comp {Ω : Type b} {κ : Type c} {ξ : Type d} [HasTy Ω κ] [HasEff Ω ξ]
    (g : SignatureMap Ψ Ω υ κ δ ξ) (f : SignatureMap Φ Ψ τ υ ε δ) :
    SignatureMap Φ Ω τ κ ε ξ where
  instr := g.instr ∘ f.instr
  ty := g.ty ∘ f.ty
  eff := g.eff ∘ f.eff
  source a := (g.source (f.instr a)).trans (congrArg g.ty (f.source a))
  target a := (g.target (f.instr a)).trans (congrArg g.ty (f.target a))
  effect a := (g.effect (f.instr a)).trans (congrArg g.eff (f.effect a))

@[simp] theorem id_comp (f : SignatureMap Φ Ψ τ υ ε δ) : id.comp f = f :=
  ext rfl rfl rfl

@[simp] theorem comp_id (f : SignatureMap Φ Ψ τ υ ε δ) : f.comp id = f :=
  ext rfl rfl rfl

theorem comp_assoc {Ω : Type b} {κ : Type c} {ξ : Type d} [HasTy Ω κ] [HasEff Ω ξ]
    {Ω' : Type*} {κ' : Type*} {ξ' : Type*} [HasTy Ω' κ'] [HasEff Ω' ξ']
    (h : SignatureMap Ω Ω' κ κ' ξ ξ') (g : SignatureMap Ψ Ω υ κ δ ξ)
    (f : SignatureMap Φ Ψ τ υ ε δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  ext rfl rfl rfl

instance {Ω : Type b} {κ : Type c} {ξ : Type d} [HasTy Ω κ] [HasEff Ω ξ]
    [HasProduct τ] [HasUnit τ] [HasProduct υ] [HasUnit υ] [HasProduct κ] [HasUnit κ]
    (g : SignatureMap Ψ Ω υ κ δ ξ) (f : SignatureMap Φ Ψ τ υ ε δ)
    [g.PreservesProducts] [f.PreservesProducts] : (g.comp f).PreservesProducts where
  unit := by simp [comp]
  product A B := by simp [comp]

instance {Ω : Type b} {κ : Type c} {ξ : Type d} [HasTy Ω κ] [HasEff Ω ξ]
    [HasCoproduct τ] [HasEmpty τ] [HasCoproduct υ] [HasEmpty υ] [HasCoproduct κ] [HasEmpty κ]
    (g : SignatureMap Ψ Ω υ κ δ ξ) (f : SignatureMap Φ Ψ τ υ ε δ)
    [g.PreservesSums] [f.PreservesSums] : (g.comp f).PreservesSums where
  empty := by simp [comp]
  coprod A B := by simp [comp]

end SignatureMap
end Morphism
end Silmaril.Isotope
