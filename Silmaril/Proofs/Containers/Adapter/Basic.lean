module

public import Silmaril.Containers.Adapter.Defs

public section
namespace Silmaril.Proofs.Containers.Adapter
open Silmaril.Containers
variable {E : Type}

theorem maskUB_refines (signal : Nat) (M : Model E) :
    ((Adapter.maskUB signal).image M).RefinesUB M := by
  rintro _ ⟨b, hb, rfl⟩
  cases b with
  | done t s =>
    cases s with
    | undefined u => exact .inr ⟨t, u, hb, List.prefix_refl t⟩
    | _ => exact .inl hb
  | _ => exact .inl hb

end Silmaril.Proofs.Containers.Adapter
