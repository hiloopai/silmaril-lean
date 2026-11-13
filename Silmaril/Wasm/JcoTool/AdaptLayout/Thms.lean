module

public import Silmaril.Wasm.JcoTool.AdaptLayout.Defs
public import Silmaril.Wasm.JcoTool.Adapt.Thms

/-!
# The general layout's certificate

* `newAdaptL_eq`: `newAdaptL` writes `Adapt.newAdapt`'s bytes (when it writes anything).
* **`newAdaptL_layout`**: every output of `newAdaptL` (the general layout, with or without
  adapters) parses to a component whose reading (`readA`) is the layout its plan describes
  (`expectedA`), and whose reference translation is valid at `Features.all`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.AdaptLayout

open Silmaril.Wasm.JcoTool.Adapt (except_bind_ok refChecked_ok)

theorem checkA_ok {p : Adapt.Plan} {b : ByteArray} (h : checkA p b = .ok ()) :
    ∃ x, xparse b = .ok x ∧ readA (namesOf p) x = some (expectedA p) := by
  unfold checkA at h
  split at h
  · rename_i x hx
    split at h
    · rename_i hl
      exact ⟨x, hx, eq_of_beq hl⟩
    · cases h
  · cases h

/-- The bytes `newAdaptL` writes are `Adapt.newAdapt`'s. -/
theorem newAdaptL_eq {core : ByteArray}
    {wit : Option ((String × String) × List (String × String) × String)}
    {ads : List (String × ByteArray)} {g : Bool} {b : ByteArray} {ls : List String}
    (h : newAdaptL core wit ads g = .ok (b, ls)) :
    ∃ p ls', Adapt.plan core wit ads g = .ok p ∧ Adapt.newAdapt core wit ads g = .ok (b, ls') ∧
      checkA p b = .ok () := by
  unfold newAdaptL at h
  obtain ⟨p, hp, h⟩ := except_bind_ok h
  obtain ⟨⟨b', ls'⟩, hb, h⟩ := except_bind_ok h
  obtain ⟨u, hc, h⟩ := except_bind_ok h
  cases h
  have hn : Adapt.newAdapt core wit ads g = .ok (b, ls') := by
    unfold Adapt.newAdapt
    rw [hp]
    exact hb
  exact ⟨p, ls', hp, hn, hc⟩

/-- **The general layout's certificate**: an output of `newAdaptL` parses to a component whose
reading is the layout the plan describes, and which the reference validator accepts. -/
theorem newAdaptL_layout {core : ByteArray}
    {wit : Option ((String × String) × List (String × String) × String)}
    {ads : List (String × ByteArray)} {g : Bool} {b : ByteArray} {ls : List String}
    (h : newAdaptL core wit ads g = .ok (b, ls)) :
    ∃ p x c ct, Adapt.plan core wit ads g = .ok p ∧ xparse b = .ok x ∧
      readA (namesOf p) x = some (expectedA p) ∧
      LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct := by
  obtain ⟨p, ls', hp, hn, hc⟩ := newAdaptL_eq h
  obtain ⟨x, hx, hr⟩ := checkA_ok hc
  obtain ⟨x', c, ct, hx', ht, hv, _⟩ := Adapt.newAdapt_valid hn
  have e : x' = x := by
    rw [hx] at hx'
    exact (Except.ok.inj hx').symm
  subst e
  exact ⟨p, x', c, ct, hp, hx, hr, ht, hv⟩

end Silmaril.Wasm.JcoTool.AdaptLayout
