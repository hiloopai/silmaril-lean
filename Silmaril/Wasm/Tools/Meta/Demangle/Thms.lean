module

public import Silmaril.Wasm.Tools.Meta.Demangle.Defs
public import Silmaril.Wasm.Tools.Meta.Names.Thms

/-!
# `wasm-tools demangle`: what it changes

* `demangle_ok`: **the output is the module header and, for each section of the parsed input,
  its rewrite** (`demangleItem`); a successful run means the input parsed as a module.
* `demangleItem_eq_bytes`: **every section that is not a `name` section is written back
  unchanged**, byte for byte, when its size field is minimal (as every encoder writes it);
  with `parseBinary_sound` the output differs from the input only in name sections and in
  non-minimal size fields.
* `demangleName_utf8`: demangled names are UTF-8 (they come from Rust or C++ demangler text or
  are the input name).
* `demangleSub_id`, `demangleMap_indices`: demangling keeps every subsection's id and every
  map's indices, and only replaces names.
* `demangle_names_roundtrip`: **the new name section decodes to the demangled subsections**
  (wasmparser reads back what was written), given the demangled names fit the limits.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Meta.Demangle

open Silmaril.Wasm.Tools.Meta

/-- A unit that parses read its header first. -/
theorem parseUnit_header {f : Nat} {e : Option Enc} {bs : List UInt8} {enc : Enc}
    {items : List Item} (h : parseUnit (f + 1) e bs = .ok (enc, items)) :
    ∃ rest, readHeader e bs = .ok (enc, rest) := by
  simp only [parseUnit, bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨enc', rest⟩, hh, _, _, rfl, _⟩ := h
  exact ⟨rest, hh⟩

/-- **The output of `demangle`**: the input parsed as a module, and the output is the module
header followed by each section's rewrite. -/
theorem demangle_ok {bs out : List UInt8} (h : demangle bs = .ok out) :
    ∃ items, parseBinary bs = .ok (.module, items) ∧
      out = Enc.module.header ++ items.flatMap demangleItem := by
  unfold demangle at h
  split at h
  · cases h
  · rename_i hnc
    split at h
    · cases h
    · rename_i enc items hp
      simp only [Except.ok.injEq] at h
      have hhdr := parseUnit_header (f := bs.length + 1) hp
      obtain ⟨rest, hr⟩ := hhdr
      cases enc with
      | module => exact ⟨items, hp, h.symm⟩
      | component => exact absurd hr (hnc rest)

/-- A section that is not a custom section is rewritten to its raw bytes. -/
theorem demangleSecBody_ne {id : UInt8} {body : List UInt8} (h : id ≠ 0) :
    demangleSecBody id body = rawSec id body := by
  simp [demangleSecBody, h]

/-- A custom section that is not named `name` is rewritten to its raw bytes. -/
theorem demangleSecBody_other {body nm data : List UInt8} (hc : customOf body = .ok (nm, data))
    (hn : nm ≠ nameName) : demangleSecBody 0 body = rawSec 0 body := by
  simp [demangleSecBody, hc, hn]

/-- **Sections other than `name` sections are kept byte for byte** (with a minimal size
field). -/
theorem demangleItem_eq_bytes (s : Sec) (hmin : s.size = encU32 s.body.length)
    (hother : s.id ≠ 0 ∨ ∃ nm data, customOf s.body = .ok (nm, data) ∧ nm ≠ nameName) :
    demangleItem (.sec s) = s.bytes := by
  rw [demangleItem, ← rawSec_eq_bytes s hmin]
  rcases hother with hid | ⟨nm, data, hc, hn⟩
  · exact demangleSecBody_ne hid
  · have h0 : s.id = 0 ∨ s.id ≠ 0 := by
      by_cases h : s.id = 0
      · exact Or.inl h
      · exact Or.inr h
    rcases h0 with h0 | h0
    · rw [h0]; exact demangleSecBody_other hc hn
    · exact demangleSecBody_ne h0

/-- Demangled names are UTF-8. -/
theorem demangleName_utf8 (n : List UInt8) (h : utf8Ok n = true) :
    utf8Ok (demangleName n) = true := by
  unfold demangleName
  split
  · exact h
  · split
    · exact utf8Ok_toUTF8 _
    · split
      · exact utf8Ok_toUTF8 _
      · exact h

/-- Demangling keeps a subsection's id. -/
theorem demangleSub_id (s : NSub) : (demangleSub s).id = s.id := by
  cases s <;> rfl

/-- Demangling keeps a map's indices. -/
theorem demangleMap_indices (m : NMap) : (demangleMap m).map (·.1) = m.map (·.1) := by
  simp [demangleMap, Function.comp_def]

/-- **The rewritten name section reads back**: wasmparser decodes the new contents to the
demangled subsections, when those are well formed (`ModSubOk`: names within the limits;
`demangleName_utf8` gives their UTF-8 validity). -/
theorem demangle_names_roundtrip {subs : List NSub}
    (hwf : ∀ s ∈ subs.map demangleSub, ModSubOk true s) :
    decodeNames true (encNames (subs.map demangleSub)) = .ok (subs.map demangleSub) :=
  decodeNames_encNames hwf

end Silmaril.Wasm.Tools.Meta.Demangle

end
