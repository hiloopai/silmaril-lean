module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Component.Defs
public import Silmaril.Wasm.Component.Reference.LinkSound.Thms

/-!
# The component charts: `Linked2.sound` as a semi-comorphism

* `Component.refToIRUniv`: reference → IR, reflecting universal sentences: a safety property of
  the IR's observations (e.g. "no trap play") holds of the reference machine.
* `Component.refToIRExist`: reference → IR, preserving existential sentences.
* `Component.ref_of_ir`: the first, stated directly.

Both rest on `Linked2.sound` (every Core profile and component choice profile). The converse
(completeness of the IR for the reference machine) is not proved here, so neither is an
equality transition.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Component

open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

variable (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) {σ : Type}
  (impl : Silmaril.Wasm.Component.Canon.HostImpl (core3P P) σ) (h₀ : σ)

theorem refObs_subset (l : Linked2) (hl : Dom l) (c : Call) :
    refObs prof impl h₀ l c ⊆ irObs P l c := by
  rintro b ⟨h, hvs, hb⟩
  obtain ⟨hEg, hEi, hIg, hIi, har, hff, hW, hN, hn, hS⟩ := hl
  exact ⟨h, hvs, Linked2.sound P prof l hEg hEi hIg hIi har hff hW hN hn hS impl h₀ ⟨c.1, h⟩ c.2
    hvs b hb⟩

/-- **`Linked2.sound` as a semi-comorphism**: the IR reflects universal sentences. -/
def refToIRUniv : Transition (refChart prof impl h₀) (irChart P) :=
  BTrans.ofSubsetUniv id id (fun _ h => h) (refObs_subset P prof impl h₀)

/-- **`Linked2.sound` as a semi-comorphism**: reference witnesses are IR witnesses. -/
def refToIRExist : Transition (refChart prof impl h₀) (irChart P) :=
  BTrans.ofSubsetExist id id (fun _ h => h) (refObs_subset P prof impl h₀)

/-- **A safety property of the IR holds of the reference machine.** -/
theorem ref_of_ir {l : Linked2} (hl : Dom l) {s : BSen Call Outcome} (hs : s.Universal)
    (h : (irChart P).Sat l s) : (refChart prof impl h₀).Sat l s :=
  BSen.sat_of_subset_univ (refObs_subset P prof impl h₀ l hl) hs h

end Silmaril.Wasm.Atlas.Component
