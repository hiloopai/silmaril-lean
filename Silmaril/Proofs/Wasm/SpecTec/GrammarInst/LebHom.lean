module

public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Hom
public import Silmaril.Proofs.Wasm.SpecTec.GrammarInst.Scripts

/-!
# `entails_lebGram_iff` through the comorphism of an attribute homomorphism

`Grammar.lebGram` lives in the instance `inst lebAlg _`, with `List Nat` attributes. A SpecTec
script lives in `inst actAlg _`, with environment transformers. `lebHom` is the attribute-algebra
homomorphism between them: a list of numbers becomes the action that emits those numerals and
leaves the scope unchanged. It is injective, so `AttrHom.ofInjective` supplies the translation of
attribute actions.

`entails_lebGram_iff` relates two instances. Through `lebHom` it splits into two steps:

1. `lebImage_conservative`: the comorphism `obsCoHom lebHom.toFun` is conservative between
   `lebGram` and its translation `lebImage` (`obsCoHom_conservative`). The assertion
   "`BuN(W)` emits the numeral `m`" pulls back to "`lebGram` derives `[m]`".
2. `entails_bun_iff_lebImage`: inside the one instance `inst actAlg _`, the script theory and
   `lebImage` have the same `BuN` consequences. The script reports the value `numCase m` (a
   `uN(N)` case value). `lebImage` reports the bare numeral `natV m`.

Step 2 is proved from `entails_lebGram_iff` and step 1. It is not an independent proof. What the
comorphism adds is that the change of attribute domain is a generic, conservative translation
(step 1, no SpecTec in it). What is left is a comparison of two theories in one instance
(step 2). The comparison of the two production tables is still done by `bun_iff_lebGram`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.GrammarInst

open Silmaril
open Silmaril.Logic.Institution
open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (natV)

/-- The action that emits the given values and leaves the scope unchanged. -/
def pureAct (vs : List Value) : Act := fun ρ l ρ' => l = vs ∧ ρ' = ρ

/-- The action of a `lebAlg` attribute: emit its numbers as numerals. -/
def lebAct (l : List Nat) : Act := pureAct (l.map natV)

theorem pureAct_app (l₁ l₂ : List Value) :
    actApp (pureAct l₁) (pureAct l₂) = pureAct (l₁ ++ l₂) := by
  funext ρ l ρ'
  apply propext
  constructor
  · rintro ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, hρ⟩
    exact ⟨l₁, ρ, l₂, ⟨rfl, rfl⟩, ⟨rfl, hρ⟩, rfl⟩

theorem lebAct_injective : Function.Injective lebAct := by
  intro l₁ l₂ h
  have h₁ : lebAct l₂ VarEnv.empty (l₁.map natV) VarEnv.empty := h ▸ ⟨rfl, rfl⟩
  have hmap : l₁.map natV = l₂.map natV := h₁.1
  exact List.map_injective_iff.mpr (fun a b hab => by
    simpa [natV] using hab) hmap

/-- **The attribute homomorphism `lebAlg → actAlg`.** -/
noncomputable def lebHom : AttrHom Grammar.lebAlg actAlg :=
  AttrHom.ofInjective lebAct lebAct_injective rfl
    (fun l₁ l₂ => by
      show pureAct ((l₁ ++ l₂).map natV) = actApp (pureAct (l₁.map natV)) (pureAct (l₂.map natV))
      rw [pureAct_app, List.map_append])
    (fun _ => rfl)

/-- The translation of `lebGram` into the SpecTec attribute algebra. -/
noncomputable def lebImage : Nat → List (Grammar.Sym Nat Act) := mapProds lebHom Grammar.lebProds

/-- "Emits the numeral `m` from scope `ρ`." -/
def emitsNat (ρ : VarEnv) (m : Nat) : Act → Prop := fun a => ∃ ρ', a ρ [natV m] ρ'

theorem emitsNat_lebAct (ρ : VarEnv) (m : Nat) (l : List Nat) :
    emitsNat ρ m (lebHom.toFun l) ↔ l = [m] := by
  constructor
  · rintro ⟨ρ', hl, -⟩
    exact lebAct_injective (show lebAct l = lebAct [m] by
      show pureAct (l.map natV) = pureAct ([m].map natV)
      rw [← hl]
      rfl)
  · rintro rfl
    exact ⟨ρ, rfl, rfl⟩

/-- **Step 1, the comorphism**: `lebImage` entails "`W` emits `m`" iff `lebGram` derives `[m]`. -/
theorem lebImage_conservative (W : Nat) (ρ : VarEnv) (bs : Grammar.Bytes) (m : Nat) :
    (room actAlg Nat).Entails (prodAxioms lebImage) (Obs.toSen ⟨W, bs, emitsNat ρ m⟩) ↔
      (room Grammar.lebAlg Nat).Entails (prodAxioms Grammar.lebProds)
        (.derives (.nt W) bs (· = [m])) := by
  rw [lebImage, obsCoHom_conservative lebHom Grammar.lebProds ⟨W, bs, emitsNat ρ m⟩]
  have hQ : emitsNat ρ m ∘ lebHom.toFun = (· = [m]) :=
    funext fun l => propext (emitsNat_lebAct ρ m l)
  show (room Grammar.lebAlg Nat).Entails _ (.derives (.nt W) bs (emitsNat ρ m ∘ lebHom.toFun)) ↔ _
  rw [hQ]

/-- **Step 2, inside `inst actAlg`**: a script with the pinned `BuN` and the translated `lebGram`
have the same `BuN(W)` consequences, up to the `uN(N)` case wrapper on the value. -/
theorem entails_bun_iff_lebImage {env : Env} (hl : HasLeb env) (W : Nat) (ρ : VarEnv)
    (bs : Grammar.Bytes) (m : Nat) :
    Entails (scriptAxioms env) (derivesNT "BuN" (argW W) ρ bs (numCase m)) ↔
      (room actAlg Nat).Entails (prodAxioms lebImage) (Obs.toSen ⟨W, bs, emitsNat ρ m⟩) :=
  (entails_lebGram_iff hl W ρ bs m).symm.trans (lebImage_conservative W ρ bs m).symm

end Silmaril.Wasm.SpecTec.GrammarInst
