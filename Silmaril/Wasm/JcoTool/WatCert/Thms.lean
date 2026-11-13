module

public import Silmaril.Wasm.JcoTool.WatCert.Defs
public import Silmaril.Wasm.JcoTool.KCoreEmit.Thms

/-!
# Core WAT with a certificate: theorems

* `certify_sound`: an accepted text denotes the module `m` of the certificate in silmaril's Core
  3.0 text grammar (`Text.Core.Encodes`), the certificate's bytes encode `m` in the Core 3.0
  binary grammar (`Binary.Core.Encodes`), and silmaril's verified decoder reads nothing but `m`
  from them.
* `checkedText_sound`, `checkedBytes_sound`: the same for what a tool prints and writes.
* `text_bytes_same`: a printed text and written bytes of the same template denote one module.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.WatCert

open Silmaril.Wasm

/-- **The certificate is sound.** -/
theorem certify_sound {t : String} {m : Module} {b : ByteArray} (h : certify t = .ok (m, b)) :
    Text.Core.Encodes t m ∧ Binary.Core.Encodes b.data.toList m ∧
      ∀ m', Binary.Core.decode? b = some m' → m' = m := by
  unfold certify at h
  cases hp : KCoreEmit.parseWat t with
  | none => simp [hp] at h
  | some m₀ =>
    cases he : Silmaril.Wasm.Binaryen.Exe.encodeModule? m₀ with
    | error e => simp [hp, he] at h
    | ok bs =>
      simp only [hp, he, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have e : (ByteArray.mk bs.toArray).data.toList = bs := by simp
      have hb : Binary.Core.Encodes (ByteArray.mk bs.toArray).data.toList m₀ :=
        e ▸ Silmaril.Wasm.Binaryen.Exe.encodeModule?_sound he
      refine ⟨KCoreEmit.parseWat_sound hp, hb, fun m' hd => ?_⟩
      exact Binary.Core.functional (Binary.Core.decode?_sound hd) hb

/-- A printed text denotes the module of its certificate. -/
theorem checkedText_sound {t t' : String} (h : checkedText t = .ok t') :
    t' = t ∧ ∃ m b, certify t = .ok (m, b) ∧ Text.Core.Encodes t m := by
  unfold checkedText at h
  cases hc : certify t with
  | error e => simp [hc, Functor.map, Except.map] at h
  | ok p =>
    simp only [hc, Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨h.symm, p.1, p.2, rfl, (certify_sound hc).1⟩

/-- Written bytes encode the module of the text's certificate. -/
theorem checkedBytes_sound {t : String} {b : ByteArray} (h : checkedBytes t = .ok b) :
    ∃ m, certify t = .ok (m, b) ∧ Text.Core.Encodes t m ∧ Binary.Core.Encodes b.data.toList m := by
  unfold checkedBytes at h
  cases hc : certify t with
  | error e => simp [hc, Functor.map, Except.map] at h
  | ok p =>
    simp only [hc, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨h1, h2, -⟩ := certify_sound hc
    exact ⟨p.1, rfl, h1, h2⟩

/-- **The text and the bytes of one template denote one module.** -/
theorem text_bytes_same {t t' : String} {b : ByteArray} (ht : checkedText t = .ok t')
    (hb : checkedBytes t = .ok b) :
    ∃ m, Text.Core.Encodes t' m ∧ Binary.Core.Encodes b.data.toList m := by
  obtain ⟨rfl, -⟩ := checkedText_sound ht
  obtain ⟨m, -, h1, h2⟩ := checkedBytes_sound hb
  exact ⟨m, h1, h2⟩

end Silmaril.Wasm.JcoTool.WatCert
