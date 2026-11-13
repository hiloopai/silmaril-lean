module

public import Silmaril.Wasm.JcoTool.RefSimpleI.Defs
public import Silmaril.Proofs.Wasm.JcoTool.RefSimpleI.Read
public import Silmaril.Wasm.JcoTool.RefSimple.Thms

/-!
# The reference machine runs the bytes with imports as their IR component

Proofs of the reading in `Silmaril.Proofs.Wasm.JcoTool.RefSimpleI.Read`.

* **`readSimpleI_ref`**: bytes that `readSimpleI` reads as `s` are the reference component
  `s.toRef` (`ToolV.refCore3 b = .ok s.toRef`), and `s` is in the fragment of `SimpleI.sound`.
* **`readSimpleI_sound`**: with import `k` bound to host function `k` of a host `g` that answers
  in the IR's types (`SimpleI.HostOk`), every behaviour of the reference machine instantiating
  the component the bytes are and calling export `j` on reference images of well-typed IR values
  is matched by `s.toComp` over `impSem P` (`IRObsI`: the IR play makes the component import
  calls `g` answers). The one hypothesis is that the core module instantiates.
* **`newRefI_correct`**, **`newRefI_sound`**: `wasm-jco new --ref` for a world with imports
  writes such bytes, with the world's imports and exports.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimpleI

open Silmaril.Wasm.Component (ValTy FuncTy Comp)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

theorem readSimpleI_ok {b : ByteArray} {s : SimpleI} (h : readSimpleI b = .ok s) :
    ∃ c, ToolV.refCore3 b = .ok c ∧ ofRefI? c = some s ∧ checkI s = true := by
  obtain ⟨c, hc, h₂⟩ := New.bind_ok h
  refine ⟨c, hc, ?_⟩
  split at h₂
  · cases h₂
  · rename_i s' ho
    split at h₂
    · rename_i hk
      cases h₂
      exact ⟨ho, hk⟩
    · cases h₂

/-- **The bytes are the reference component of a simple component with imports in the
fragment.** -/
theorem readSimpleI_ref {b : ByteArray} {s : SimpleI} (h : readSimpleI b = .ok s) :
    ToolV.refCore3 b = .ok s.toRef ∧ s.Good ∧ s.FloatFree ∧ s.Arity ∧
      ((∃ I, s.mod.IsInst I) → s.Inst) := by
  obtain ⟨c, hc, ho, hk⟩ := readSimpleI_ok h
  rw [ofRefI?_toRef ho]
  exact ⟨hc, checkI_spec hk⟩

/-- **The reference machine runs the bytes as `s.toComp`, imports answered by a host.** -/
theorem readSimpleI_sound {b : ByteArray} {s : SimpleI} (h : readSimpleI b = .ok s)
    (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (hi : ∃ I, s.mod.IsInst I)
    (g : Silmaril.Wasm.Component.Runtime.HostFuncId → List Silmaril.Wasm.Component.Value.Val →
      Option (List Silmaril.Wasm.Component.Value.Val)) (hg : s.HostOk g)
    (j : Fin s.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList s.exports[j].ty.params vs = true) (o : Outcome)
    (ho : o ∈ exportBehavioursI prof (answerHost P g) () s.toRef s.imports s.exports[j].name
      (vs.map toRefVal)) :
    IRObsI (s.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g o := by
  obtain ⟨-, hgd, hf, ha, hin⟩ := readSimpleI_ref h
  exact SimpleI.sound P prof s hgd (hin hi) hf ha g hg j vs hvs o ho

/-- **What `wasm-jco new --ref` writes for a world with imports.** -/
theorem newRefI_correct {core : ByteArray} {w : Silmaril.Wasm.Wit.Binary.World} {b : ByteArray}
    {s : SimpleI} (h : newRefI core w = .ok (b, s)) :
    expectedIface w = .ok (s.imports, s.exports.map fun e => (e.name, e.ty)) ∧
      readSimpleI b = .ok s := by
  obtain ⟨⟨ims, xs⟩, he, h₁⟩ := New.bind_ok h
  obtain ⟨x, -, h₂⟩ := New.bind_ok h₁
  split at h₂
  · rename_i b' _hb
    obtain ⟨s', hr, h₃⟩ := New.bind_ok h₂
    split at h₃
    · rename_i heq
      cases h₃
      obtain ⟨h₁', h₂'⟩ := heq
      exact ⟨by rw [he, h₁', h₂'], hr⟩
    · cases h₃
  · cases h₂

/-- **The bytes `wasm-jco new --ref` writes for a world with imports run on the reference
machine as `s.toComp`.** -/
theorem newRefI_sound {core : ByteArray} {w : Silmaril.Wasm.Wit.Binary.World} {b : ByteArray}
    {s : SimpleI} (h : newRefI core w = .ok (b, s)) :
    expectedIface w = .ok (s.imports, s.exports.map fun e => (e.name, e.ty)) ∧
      ToolV.refCore3 b = .ok s.toRef ∧
      ∀ (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind), (∃ I, s.mod.IsInst I) →
        ∀ g, s.HostOk g → ∀ (j : Fin s.exports.length) (vs : List Silmaril.Wasm.Component.Val),
          ValTy.checkList s.exports[j].ty.params vs = true → ∀ o : Outcome,
          o ∈ exportBehavioursI prof (answerHost P g) () s.toRef s.imports s.exports[j].name
            (vs.map toRefVal) →
          IRObsI (s.toComp.den (impSem P)) ⟨j, by simp [SimpleI.toComp]⟩ vs g o := by
  obtain ⟨he, hr⟩ := newRefI_correct h
  exact ⟨he, (readSimpleI_ref hr).1, fun P prof hi g hg j vs hvs o ho =>
    readSimpleI_sound hr P prof hi g hg j vs hvs o ho⟩

end Silmaril.Wasm.JcoTool.RefSimpleI
