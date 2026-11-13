module

public import Silmaril.Wasm.JcoTool.RefSimple.Defs
public import Silmaril.Proofs.Wasm.JcoTool.RefSimple.Read
public import Silmaril.Wasm.Component.Reference.Sound.Thms
public import Silmaril.Wasm.JcoTool.LayoutRef.Thms
public import Silmaril.Wasm.Perf.CoreDecode.Thms

/-!
# The reference machine runs the bytes as their IR component

Proofs of the reading in `Silmaril.Proofs.Wasm.JcoTool.RefSimple.Read`.

* **`readSimple_ref`**: bytes that `readSimple` reads as `s` are the reference component
  `s.toRef` (`ToolV.refCore3 b = .ok s.toRef`: `xparse`, `LayoutRef.toRef`, silmaril's verified
  core decoder), and `s` is in the fragment of the soundness theorem.
* **`readSimple_sound`**: every behaviour of the reference machine (silmaril's component
  instantiation and machine over `core3P P`, at every component choice profile) instantiating
  the component the bytes are and calling export `j` on the reference images of well-typed IR
  values is an IR observation of the call in `s.toComp.den (modSem P)`: a returned call answers
  IR values whose images are the results, a trap answers `none`. The one hypothesis is that the
  core module instantiates (`∃ I, s.mod.IsInst I`).
* **`readSimple_sound_seq`**: the same for sequences of calls on one instance.
* **`newRef_correct`**, **`newRef_sound`**: `wasm-jco new --ref` writes bytes that read back as a
  simple component whose exports are the world's functions at their IR types (names and types,
  in order), so the two theorems above hold for the bytes the tool writes.
* **`rdRef_sound`**: for the algebra (`Emit.binCompX` with `rd := rdRef`), a package's meaning
  `rdRef a = some C` is `s.toComp` for a simple component `s` that the package is, in the
  reference syntax, and the reference machine runs as `C`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.RefSimple

open Silmaril.Wasm.Component (Syntax.Component)
open Silmaril.Wasm.Component (ValTy FuncTy Comp)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

theorem readSimple_ok {b : ByteArray} {s : Simple} (h : readSimple b = .ok s) :
    ∃ c, ToolV.refCore3 b = .ok c ∧ ofRef? c = some s ∧ check s = true := by
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

/-- **The bytes are the reference component of a simple component in the fragment.** -/
theorem readSimple_ref {b : ByteArray} {s : Simple} (h : readSimple b = .ok s) :
    ToolV.refCore3 b = .ok s.toRef ∧ s.Good ∧ s.FloatFree ∧ s.Arity ∧
      funcExportNames s.mod.mod = s.mod.exports.map (·.1) := by
  obtain ⟨c, hc, ho, hk⟩ := readSimple_ok h
  rw [ofRef?_toRef ho]
  exact ⟨hc, check_spec hk⟩

/-- **The reference machine runs the bytes as `s.toComp`** (single calls). -/
theorem readSimple_sound {b : ByteArray} {s : Simple} (h : readSimple b = .ok s) (P : Profile)
    (prof : Silmaril.Wasm.Component.ProfileKind) (hi : ∃ I, s.mod.IsInst I)
    (j : Fin s.exports.length) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList s.exports[j].ty.params vs = true) (o : Outcome)
    (ho : o ∈ exportBehaviours prof (refHost P) () s.toRef [] s.exports[j].name
      (vs.map toRefVal)) :
    IRObs (k := s.toComp.exports.length) (s.toComp.den (modSem P))
      ⟨j, by simp [Simple.toComp]⟩ vs o := by
  obtain ⟨-, hg, hf, ha, hn⟩ := readSimple_ref h
  exact Simple.sound P prof s hg hf ⟨hi, hn⟩ ha j vs hvs o ho

/-- **The reference machine runs the bytes as `s.toComp`** (sequences of calls on one
instance). -/
theorem readSimple_sound_seq {b : ByteArray} {s : Simple} (h : readSimple b = .ok s)
    (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind) (hi : ∃ I, s.mod.IsInst I)
    (calls : List (Fin s.exports.length × List Silmaril.Wasm.Component.Val))
    (j : Fin s.exports.length) (vs : List Silmaril.Wasm.Component.Val) (ht : TypedCalls s calls)
    (hvs : ValTy.checkList s.exports[j].ty.params vs = true)
    (p : List (List Silmaril.Wasm.Component.Value.Val) × Outcome)
    (hp : p ∈ seqBehaviours prof (refHost P) () s.toRef
      (calls.map fun q => (s.exports[q.1].name, q.2.map toRefVal)) s.exports[j].name
      (vs.map toRefVal)) :
    ∃ wss : List (List Silmaril.Wasm.Component.Val), p.1 = wss.map (·.map toRefVal) ∧
      seqMoves s calls wss ∈ s.toComp.den (modSem P) ∧
      SeqIRObs s (s.toComp.den (modSem P)) calls wss j vs p.2 := by
  obtain ⟨-, hg, hf, ha, hn⟩ := readSimple_ref h
  exact Simple.sound_seq P prof s hg hf ⟨hi, hn⟩ ha calls j vs ht hvs p hp

/-- **What `wasm-jco new --ref` writes.** -/
theorem newRef_correct {core : ByteArray} {w : Silmaril.Wasm.Wit.Binary.World} {b : ByteArray}
    {s : Simple} (h : newRef core w = .ok (b, s)) :
    ∃ x, expectedExports w = .ok (s.exports.map fun e => (e.name, e.ty)) ∧
      emitRef core (s.exports.map fun e => (e.name, e.ty)) = .ok x ∧ x.encode = some b ∧
      readSimple b = .ok s := by
  obtain ⟨xs, he, h₁⟩ := New.bind_ok h
  obtain ⟨x, hx, h₂⟩ := New.bind_ok h₁
  split at h₂
  · rename_i b' hb
    obtain ⟨s', hr, h₃⟩ := New.bind_ok h₂
    split at h₃
    · rename_i heq
      cases h₃
      exact ⟨x, heq ▸ he, heq ▸ hx, hb, hr⟩
    · cases h₃
  · cases h₂

/-- **The bytes `wasm-jco new --ref` writes run on the reference machine as `s.toComp`**, whose
exports are the world's functions. -/
theorem newRef_sound {core : ByteArray} {w : Silmaril.Wasm.Wit.Binary.World} {b : ByteArray}
    {s : Simple} (h : newRef core w = .ok (b, s)) :
    expectedExports w = .ok (s.exports.map fun e => (e.name, e.ty)) ∧
      ToolV.refCore3 b = .ok s.toRef ∧
      ∀ (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind), (∃ I, s.mod.IsInst I) →
        ∀ (j : Fin s.exports.length) (vs : List Silmaril.Wasm.Component.Val),
          ValTy.checkList s.exports[j].ty.params vs = true → ∀ o : Outcome,
          o ∈ exportBehaviours prof (refHost P) () s.toRef [] s.exports[j].name
            (vs.map toRefVal) →
          IRObs (k := s.toComp.exports.length) (s.toComp.den (modSem P))
            ⟨j, by simp [Simple.toComp]⟩ vs o := by
  obtain ⟨_, he, -, -, hr⟩ := newRef_correct h
  exact ⟨he, (readSimple_ref hr).1, fun P prof hi j vs hvs o ho =>
    readSimple_sound hr P prof hi j vs hvs o ho⟩

/-- **A package's meaning under `rdRef` is the IR component the reference machine runs it
as.** -/
theorem rdRef_sound {a : Silmaril.Wasm.Component.BinaryAsync.AstX} {C : Comp NumModule}
    (h : rdRef a = some C) :
    ∃ (x : XComp) (s : Simple), xcompOfX a = some x ∧
      LayoutRef.toRef Silmaril.Wasm.Binary.Core.decode? x = some s.toRef ∧ C = s.toComp ∧
      s.Good ∧ s.FloatFree ∧ s.Arity ∧ funcExportNames s.mod.mod = s.mod.exports.map (·.1) := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨x, hx, c, hc, s', ho, hk⟩ : ∃ x, xcompOfX a = some x ∧ ∃ c,
      LayoutRef.toRef Silmaril.Wasm.Binary.Core.decode? x = some c ∧ ∃ s', ofRef? c = some s' ∧
        (if check s' then some s' else none) = some s := by
    simpa [simpleOfX, Option.bind_eq_some_iff, Silmaril.Wasm.Perf.CoreDecode.decodeF_eq] using hs
  have hk' : check s' = true ∧ s' = s := by
    split at hk
    · rename_i hc'; exact ⟨hc', Option.some.inj hk⟩
    · cases hk
  obtain ⟨hc1, rfl⟩ := hk'
  exact ⟨x, s', hx, by rw [ofRef?_toRef ho]; exact hc, rfl, check_spec hc1⟩

end Silmaril.Wasm.JcoTool.RefSimple
