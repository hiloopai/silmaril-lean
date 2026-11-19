module

public import Silmaril.Containers.Adapter.Defs
import Silmaril.Proofs.Containers.Adapter.Basic

public section
namespace Silmaril.Containers.Adapter
variable {E F G : Type}

theorem sat_image_iff (f : Adapter E F) (M : Model E) (φ : Spec F) :
    (f.image M).Sat φ ↔ M.Sat (f.pull φ) :=
  ⟨fun h b hb => h _ ⟨b, hb, rfl⟩, fun h _ ⟨b, hb, he⟩ => he ▸ h b hb⟩

theorem reflectsNoUB_comp {f : Adapter E F} {g : Adapter F G}
    (hf : f.ReflectsNoUB) (hg : g.ReflectsNoUB) : (f.comp g).ReflectsNoUB :=
  fun b h => hf b (hg (f.run b) h)

theorem source_noUB {f : Adapter E F} (hf : f.ReflectsNoUB) {M : Model E}
    (h : (f.image M).Sat Spec.noUB) : M.Sat Spec.noUB :=
  fun b hb => hf b (h _ ⟨b, hb, rfl⟩)

/-- Permissive UB refinement can implement source UB by a particular crash. -/
theorem maskUB_refines (signal : Nat) (M : Model E) :
    ((maskUB signal).image M).RefinesUB M :=
  Silmaril.Proofs.Containers.Adapter.maskUB_refines signal M

/-- Such a semantic refinement does not reflect a noUB certificate back to its source. -/
theorem maskUB_not_reflects (signal : Nat) : ¬ (maskUB (E := E) signal).ReflectsNoUB :=
  fun h => h (.done [] (.undefined .other)) trivial

end Silmaril.Containers.Adapter
