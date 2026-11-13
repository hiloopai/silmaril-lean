module

public import Silmaril.Wasm.Models.Realise.Defs
public import Silmaril.Wasm.Models.Model.Thms

/-!
# Embeddings as realisers: theorems and instances

* `Emb.entails_iff`, `Emb.valid_iff`: **borrowing** along an equality embedding whose total
  read-back is a bijection (from `Realiser.entails_iff`/`valid_iff`);
* `Emb.refines_iff`: refinement of calls is preserved and reflected;
* `Emb.comp_dir`, `Emb.comp_id`: the direction of a composite, and composition with the
  identity embedding has the same maps;
* the restricted Core models: `coreEmb` has a total read-back (`coreEmbTotal`), so
  `core|S → core|T` (`S ≤ T`) is a realiser and a Hets comorphism (`coreCoHom`), and
  `coreEmb_comp`: `core|S → core|T → core|U` composes to an equality embedding with the maps of
  `coreEmb` for `S ≤ U`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Models

open Silmaril.Compile.Category Silmaril.Wasm.Category Silmaril.Wasm.Institution
open Silmaril.Wasm.Numerics (Profile)

namespace WasmModel

variable {A B D : WasmModel}

/-- **Borrowing along an equality embedding** with a bijective total read-back. -/
theorem Emb.entails_iff (e : A.Emb B) (t : e.Total) (hinj : Function.Injective t.g)
    (hd : e.dir = .eq) (hs : Function.Surjective t.g) (K : Sig (CategoryTheory.Discrete Unit))
    (Γ : Set ((obsSem A.lang).Sen K)) (s : (obsSem A.lang).Sen K) :
    ((obsSem A.lang).room K).Entails Γ s ↔
      ((obsSem B.lang).room ((Sig.map (e.realiser t hinj hd).ifaceFunctor).obj K)).Entails
        ((e.realiser t hinj hd).translation.sen '' Γ) ((e.realiser t hinj hd).translation.sen s) :=
  (e.realiser t hinj hd).entails_iff hs K Γ s

/-- Validity is preserved and reflected along such an embedding. -/
theorem Emb.valid_iff (e : A.Emb B) (t : e.Total) (hinj : Function.Injective t.g)
    (hd : e.dir = .eq) (hs : Function.Surjective t.g) {K : Sig (CategoryTheory.Discrete Unit)}
    (s : (obsSem A.lang).Sen K) :
    (obsSem A.lang).Valid s ↔ (obsSem B.lang).Valid ((e.realiser t hinj hd).translation.sen s) :=
  (e.realiser t hinj hd).valid_iff hs s

/-- Refinement between calls is preserved and reflected along an equality embedding with an
injective total read-back. -/
theorem Emb.refines_iff (e : A.Emb B) (t : e.Total) (hinj : Function.Injective t.g)
    (hd : e.dir = .eq) (x y : A.lang.Prog) :
    B.lang.Refines ((e.realiser t hinj hd).prog x) ((e.realiser t hinj hd).prog y) ↔
      A.lang.Refines x y :=
  (e.realiser t hinj hd).refines_iff rfl

theorem Emb.comp_dir (e : A.Emb B) (f : B.Emb D) {d : EmbDir} (hd : e.dir.comp f.dir = some d) :
    (e.comp f hd).dir = d :=
  rfl

/-- Composing with the identity keeps the maps. -/
theorem Emb.comp_id (e : A.Emb B) :
    (e.comp (Emb.id B) (d := e.dir) (by cases e.dir <;> rfl)).pt = e.pt ∧
      (e.comp (Emb.id B) (d := e.dir) (by cases e.dir <;> rfl)).call = e.call :=
  ⟨rfl, rfl⟩

end WasmModel

/-! ## The restricted Core models -/

variable (P : Profile) (H : Type) {S T U : FeatureSet}

/-- The read-back of `coreEmb` is total (it is `some`). -/
def coreEmbTotal (h : S ≤ T) : (coreEmb P H h).Total := ⟨id, fun _ => rfl⟩

/-- **`core|S → core|T` is a realiser.** -/
def coreRealiser (h : S ≤ T) : Realiser (coreModel P H S).lang (coreModel P H T).lang :=
  (coreEmb P H h).realiser (coreEmbTotal P H h) Function.injective_id rfl

/-- **`core|S → core|T` as a Hets comorphism of behavioural institutions.** -/
def coreCoHom (h : S ≤ T) :
    Silmaril.Logic.Institution.Inst.CoHom (behInst (coreModel P H S).lang)
      (behInst (coreModel P H T).lang) :=
  (coreRealiser P H h).coHom

/-- `core|S → core|T` borrows validity (its read-back is the identity). -/
theorem coreEmb_valid_iff (h : S ≤ T) {K : Sig (CategoryTheory.Discrete Unit)}
    (s : (obsSem (coreModel P H S).lang).Sen K) :
    (obsSem (coreModel P H S).lang).Valid s ↔
      (obsSem (coreModel P H T).lang).Valid ((coreRealiser P H h).translation.sen s) :=
  (coreEmb P H h).valid_iff (coreEmbTotal P H h) Function.injective_id rfl
    Function.surjective_id s

/-- **Composition of restricted Core embeddings**: `core|S → core|T → core|U` is an equality
embedding with the maps of `core|S → core|U`. -/
theorem coreEmb_comp (h₁ : S ≤ T) (h₂ : T ≤ U) :
    ((coreEmb P H h₁).comp (coreEmb P H h₂) rfl).dir = .eq ∧
      ((coreEmb P H h₁).comp (coreEmb P H h₂) rfl).pt = (coreEmb P H (h₁.trans h₂)).pt ∧
      ((coreEmb P H h₁).comp (coreEmb P H h₂) rfl).call = (coreEmb P H (h₁.trans h₂)).call ∧
      ((coreEmb P H h₁).comp (coreEmb P H h₂) rfl).mod = (coreEmb P H (h₁.trans h₂)).mod :=
  ⟨rfl, rfl, rfl, rfl⟩

end Silmaril.Wasm.Models
