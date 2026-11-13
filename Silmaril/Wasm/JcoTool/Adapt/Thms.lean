module

public import Silmaril.Wasm.JcoTool.Adapt.Defs
public import Silmaril.Wasm.JcoTool.LayoutRefX.Thms
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# What the general layout guarantees

`wasm-jco new --adapt …`, and `wasm-jco new` on a module outside the certified layout's
fragment, write the bytes of `Adapt.newAdapt`. **`newAdapt_valid`**: those bytes parse
(`xparse`) to a component whose reference translation (`LayoutRefX.toRefX`, core modules read by
silmaril's verified decoder) is `Reference.Valid` at `Features.all`, and the layout reading of
the parsed component is the reading of its reference translation. Nothing is claimed about
the layout itself (which import feeds which core function): that is tested against
wit-component (`tools/wasm-jco/tests/adapt.sh`, `general.sh`, `wit-component.sh`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.Adapt

theorem refChecked_ok {b b' : ByteArray} {ls ls' : List String}
    (h : refChecked b ls = .ok (b', ls')) :
    b' = b ∧ ∃ ct, ToolV.refCheckX b = .ok ct := by
  unfold refChecked at h
  split at h
  · rename_i ct hc
    cases h
    exact ⟨rfl, ct, hc⟩
  · cases h

theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **Every output of the general layout is valid** (silmaril's reference validator, every
feature gate on). -/
theorem newAdapt_valid {core : ByteArray}
    {wit : Option ((String × String) × List (String × String) × String)}
    {ads : List (String × ByteArray)} {g : Bool} {b : ByteArray} {ls : List String}
    (h : newAdapt core wit ads g = .ok (b, ls)) :
    ∃ x c ct, xparse b = .ok x ∧
      LayoutRefX.toRefX Silmaril.Wasm.Binary.Core.decode? x = some c ∧
      Silmaril.Wasm.Component.Reference.Valid Silmaril.Wasm.Component.Features.all c ct ∧
      ∀ names, Layout.read names x = LayoutRef.readRef names c := by
  unfold newAdapt newAdaptOf at h
  obtain ⟨p, _, h⟩ := except_bind_ok h
  obtain ⟨c, _, h⟩ := except_bind_ok h
  obtain ⟨b0, _, h⟩ := except_bind_ok h
  obtain ⟨rfl, ct, hc⟩ := refChecked_ok h
  obtain ⟨x, c', hx, ht, hv, hr⟩ := ToolV.refCheckX_valid hc
  exact ⟨x, c', ct, hx, ht, hv, hr⟩

/-- `needsGeneralOf` on the input's decoded module (`wasm-jco new` decodes the input once with
`CoreDecode.decodeF`, equal to silmaril's `decode?`) is `needsGeneral`. -/
theorem needsGeneralOf_decodeF (core : ByteArray) :
    needsGeneralOf (Silmaril.Wasm.Perf.CoreDecode.decodeF core) core = needsGeneral core :=
  rfl

end Silmaril.Wasm.JcoTool.Adapt
