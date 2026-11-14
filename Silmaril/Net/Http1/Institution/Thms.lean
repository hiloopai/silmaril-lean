module

public import Silmaril.Net.Http1.Institution.Defs
import Silmaril.Proofs.Net.Http1.Institution

/-!
# The HTTP/1.1 institution: theorems and the institution

Proofs in `Silmaril/Proofs/Net/Http1/Institution.lean`, using only the standard axioms:

* `sat_map_iff`: **the satisfaction condition** `M ⊨ σ(φ) ↔ M|σ ⊨ φ`; `Sen.map_id`,
  `Sen.map_comp`: translation is functorial. So `inst : Sig ⥤ Room` is an institution and
  `classic` is its Goguen–Burstall form.
* `extension_conservative`, `ExtensionCompliant.reduct_vanilla`: an extension-compliant
  implementation's reduct to the standard vocabulary is vanilla, and an extended
  implementation satisfies a translated vanilla obligation iff its reduct does.
* `refModel_vanilla`: the reference server (`serve`'s request checks, framing and keep-alive
  decision, `HEAD` stripping and error responses) is a vanilla HTTP/1.1 implementation, for
  every compliant profile and every well-framed handler.
* `patchModel_extensionCompliant`: the reference server with a `PATCH` handler is
  extension-compliant for the `PATCH` extension (RFC 5789), so its reduct is vanilla
  (`patchModel_reduct_vanilla`).
* `clWins_violates`, `keepAlways_violates`: a `Content-Length`-first server violates
  `framesSafely`, and a server that always keeps the connection open violates
  `closesOnClTe`. Neither is vanilla (`clWins_not_vanilla`).
-/

@[expose] public section

namespace Silmaril.Net.Http1.Inst

open CategoryTheory Silmaril.Logic.Institution

theorem sat_map_iff {A B : Sig} (σ : A ⟶ B) (M : Model B) (φ : Sen A) :
    Sat M (φ.map σ) ↔ Sat (M.reduct σ) φ :=
  Proofs.Institution.sat_map_iff σ M φ

theorem Sen.map_id {A : Sig} (φ : Sen A) : φ.map (𝟙 A) = φ := Proofs.Institution.map_id φ

theorem Sen.map_comp {A B C : Sig} (σ : A ⟶ B) (τ : B ⟶ C) (φ : Sen A) :
    φ.map (σ ≫ τ) = (φ.map σ).map τ := Proofs.Institution.map_comp σ τ φ

/-- The room of a vocabulary: obligations, implementations (discrete), satisfaction. -/
def room (A : Sig) : Room.{0, 0, 0} :=
  ⟨Sen A, Cat.of (Discrete (Model A)), fun M φ => Sat (Discrete.as M) φ⟩

/-- The corridor of a signature morphism. -/
def corridor {A B : Sig} (σ : A ⟶ B) : room A ⟶ room B :=
  ⟨Sen.map σ, Discrete.functor fun (M : Model B) => Discrete.mk (M.reduct σ),
    fun M φ => sat_map_iff σ (Discrete.as M) φ⟩

/-- **The HTTP/1.1 institution**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun φ => Sen.map_id φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp σ τ := Room.hom_ext (funext fun φ => Sen.map_comp σ τ φ)
    (CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
      @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

/-- The HTTP/1.1 institution in the direct form. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

theorem extension_conservative {M F C : Type} (X : Model (Std.extend M F C)) (φ : Sen Std) :
    Sat X (φ.map (Std.incl M F C)) ↔ Sat (X.reduct (Std.incl M F C)) φ :=
  sat_map_iff (Std.incl M F C) X φ

theorem ExtensionCompliant.reduct_vanilla {M F C : Type} {T : List (Sen (Std.extend M F C))}
    {X : Model (Std.extend M F C)} (h : ExtensionCompliant T X) :
    Vanilla (X.reduct (Std.incl M F C)) :=
  ⟨h.1, fun φ hφ => (extension_conservative X φ).1 (h.2.1 _ (List.mem_map_of_mem hφ))⟩

theorem refModel_vanilla {cfg : ServerConfig} {H : Handler} (hp : cfg.profile.Compliant)
    (hH : Handler.WellFramed H) : Vanilla (refModel cfg H) :=
  Proofs.Institution.refModel_vanilla hp hH

theorem patchModel_extensionCompliant : ExtensionCompliant patchTheory patchModel :=
  Proofs.Institution.patchModel_extensionCompliant

theorem patchModel_reduct_vanilla : Vanilla (patchModel.reduct (Std.incl Unit Empty Empty)) :=
  patchModel_extensionCompliant.reduct_vanilla

theorem clWins_violates (cfg : ServerConfig) (H : Handler) :
    Violates (refModel { cfg with profile := Profile.clWins } H) .framesSafely :=
  Proofs.Institution.clWins_violates cfg H

theorem clWins_not_vanilla (cfg : ServerConfig) (H : Handler) :
    ¬ Vanilla (refModel { cfg with profile := Profile.clWins } H) := fun h =>
  clWins_violates cfg H (h.2 _ (by simp [rfcCore]))

theorem keepAlways_violates (cfg : ServerConfig) (H : Handler) :
    Violates (⟨StdMethod.token, StdField.name, StdCoding.name, keepAlwaysImpl cfg H⟩ : Model Std)
      .closesOnClTe :=
  Proofs.Institution.keepAlways_violates cfg H

end Silmaril.Net.Http1.Inst
