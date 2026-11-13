module

public import Silmaril.Wasm.Wac.EndToEndR.Defs
public import Silmaril.Wasm.Perf.Splice.Thms
public import Silmaril.Wasm.Perf.CanonB.Thms

/-!
# WAC: the tool's pipeline is the verified one whenever that succeeds

`composeTextR_of_ok`, `composeImpTextR_of_ok`, `composeWatTextR_of_ok`: when the text passes
`TextCheck.checkText` and the verified pipeline (`EndToEnd.composeText`, `WatOut.composeImpText`, `WatOut.composeWatText`) succeeds,
`wasm-wac` writes its output, so `EndToEnd.composeText_correct`,
`WatOut.composeWatText_correct` and the theorems built on them hold of what the tool writes.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.EndToEndR

theorem composeWasmRawF_eq (env : PkgEnv) (noms : List (String × Bridge.NomTable))
    (raw : List (String × ByteArray)) (d : FuncAlias.Document) :
    composeWasmRawF env noms raw d = Emit.composeWasmRaw env noms raw d := by
  simp only [composeWasmRawF, Emit.composeWasmRaw, ← Silmaril.Wasm.Perf.Splice.splice_eq_spliceF]
  rfl

/-- The `ByteArray` pipeline is `EndToEnd.composeText`. -/
theorem composeTextF_eq (src : String) (raw : List (String × ByteArray)) :
    composeTextF src raw = EndToEnd.composeText src raw := by
  unfold composeTextF EndToEnd.composeText
  generalize Bridge.readDocX src = r
  cases r with
  | error e => rfl
  | ok d =>
    dsimp only
    generalize EndToEnd.readPkgs raw (Bridge.pkgKeysX d) = q
    cases q with
    | error e => rfl
    | ok p =>
      obtain ⟨env, noms, rs⟩ := p
      dsimp only
      rw [composeWasmRawF_eq]
      unfold Emit.composeWasmX
      generalize Emit.composeWasmRaw env noms rs d = w
      cases w <;> rfl

theorem composeTextR_of_ok {src : String} {raw : List (String × ByteArray)}
    {r : ByteArray × Option SpliceX.PkgTableX × Bool} (hc : TextCheck.checkText src = .ok ())
    (h : EndToEnd.composeText src raw = .ok r) : composeTextR src raw = .ok r := by
  simp [composeTextR, composeTextF_eq, hc, h]

theorem composeImpTextR_of_ok {src : String} {raw : List (String × ByteArray)} {b : ByteArray}
    (hc : TextCheck.checkText src = .ok ()) (h : WatOut.composeImpText src raw = .ok b) :
    composeImpTextR src raw = .ok b := by
  simp [composeImpTextR, hc, h]

theorem composeWatTextR_of_ok {src : String} {raw : List (String × ByteArray)} {t : String}
    (hc : TextCheck.checkText src = .ok ()) (h : WatOut.composeWatText src raw = .ok t) :
    composeWatTextR src raw = .ok t := by
  simp [composeWatTextR, hc, h]

/-- The fallback is used only when the verified pipeline fails. -/
theorem composeTextR_cases (src : String) (raw : List (String × ByteArray))
    (r : ByteArray × Option SpliceX.PkgTableX × Bool) (h : composeTextR src raw = .ok r) :
    EndToEnd.composeText src raw = .ok r ∨
      (∃ e, EndToEnd.composeText src raw = .error e) ∧ composeTextU src raw = .ok r := by
  unfold composeTextR at h
  rw [composeTextF_eq] at h
  split at h
  · cases h
  split at h
  · next r' h1 => exact Or.inl (h1.trans h)
  · next e h1 =>
    split at h
    · next r'' h2 => exact Or.inr ⟨⟨e, h1⟩, h2.trans h⟩
    · cases h

end Silmaril.Wasm.Wac.EndToEndR
