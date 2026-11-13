module

public import Silmaril.Proofs.Wasm.OCaml.SpecTecEval.SlicePin
public import Silmaril.Proofs.Wasm.OCaml.SpecTecEval.SliceMain
public import Silmaril.Proofs.Wasm.OCaml.SpecTecEval.BinPin
public import Silmaril.Proofs.Wasm.OCaml.SpecTecEval.CmpPin
public import Silmaril.Proofs.Wasm.OCaml.SpecTecEval.SliceGeneric

/-!
# SpecTec's own `reduce_exp` on slices: the pin has the strict bound, main has the fix

`runSlice p es i n` runs `Il.Eval.reduce_exp Env.empty (es[i : n])` — the **imported OCaml
source** of `spectec/src/il/eval.ml` — in the semantics `Silmaril.ML.OCaml`, for a list `es` of
natural-number literals. `p` is `pinProgram` (`WebAssembly/spec@608711107b`, the pin of every
SpecTec result in Silmaril) or `mainProgram` (`@e7a9df7cd`, after upstream's
`f4f22691f "[spectec] Fix reduction of slices at boundary"`).

* `slice_pin_agrees`: at the pin, the OCaml agrees with `Broken.sliceEvalMl?`, the
  transcription of `eval.ml:284` with the **strict** bound `i + n < |es|`;
* `slice_main_agrees`: on main, it agrees with `Sem.Value.slice?`, Silmaril's corrected port
  (`i + n ≤ |es|`);
* `bin_pin_agrees`, `cmp_pin_agrees`: on `BinE`/`CmpE` over numerals, the pinned OCaml
  agrees with Silmaril's `Sem.evalExp`, which was transcribed from it by hand (part of the
  "transcription trust" of `Sem`);
* `slice3_pin`, `slice3_main`, `slice_boundary_all`: the same for **every** list of three
  numerals `[a, b, c]` (the shape stays concrete), by kernel evaluation with `a`, `b`, `c`
  free (`kernel_rfl`);
* `slice_boundary`: at the boundary `1 + 2 = |[7, 8, 9]|` the pin's interpreter does not
  reduce the slice (it returns `Error (SliceE …)`), while main returns `Ok (ListE [8, 9])`.

This turns item U2 of `docs/projects/spectec/README.md` into a statement about the OCaml code
itself rather than about a transcription of it. It also settles the question left open in
`Sem/Value.lean`: on these inputs `Lib.List.take` and `Lib.List.drop` do not raise
`Failure` at the boundary (main returns `Ok`).

Each run is checked by the kernel (`decide +kernel`); the test cases are finitely many
(`sliceCases`, `opCases`): every boundary case for lists of length 0, 1 and 3, and cases on either side
of it. A statement for all lists needs a program logic for the imported code
(`docs/projects/wasm-wasi.md`, Gaps).
-/

@[expose] public section
namespace Silmaril.Wasm.OCaml.SpecTecEval

open Silmaril.ML.OCaml

theorem agreesSlice_none {o : SliceOut} (h : agreesSlice none o = true) : o = .errorSlice := by
  cases o <;> simp_all [agreesSlice]

theorem agreesSlice_some {o : SliceOut} {ws : List Silmaril.SpecTec.Sem.Value} {ns : List Nat}
    (hw : ws.mapM natOf? = some ns) (h : agreesSlice (some (.list ws)) o = true) : o = .ok ns := by
  cases o with
  | ok ms =>
    simp only [agreesSlice, hw, beq_iff_eq, Option.some.injEq] at h
    rw [h]
  | errorSlice => simp [agreesSlice] at h
  | other => simp [agreesSlice] at h

/-- **The boundary, in the OCaml.** At `1 + 2 = |[7, 8, 9]|` the pinned interpreter leaves
the slice unreduced (`Error (SliceE …)`), while the interpreter on main reduces it to
`ListE [8, 9]`. -/
theorem slice_boundary :
    sliceOut (runSlice pinProgram [7, 8, 9] 1 2) = .errorSlice ∧
      sliceOut (runSlice mainProgram [7, 8, 9] 1 2) = .ok [8, 9] := by
  have hc : ([7, 8, 9], 1, 2) ∈ sliceCases := by decide
  have hp := List.all_eq_true.mp slice_pin_agrees _ hc
  have hm := List.all_eq_true.mp slice_main_agrees _ hc
  dsimp only at hp hm
  rw [sliceEvalMl?_list] at hp
  have hs : Silmaril.SpecTec.Sem.Value.slice? (.list ([7, 8, 9].map natV)) 1 2 =
      some (.list [natV 8, natV 9]) := by
    simp [Silmaril.SpecTec.Sem.Value.slice?]
  rw [hs] at hm
  exact ⟨agreesSlice_none (by simpa using hp), agreesSlice_some rfl hm⟩

/-- **The boundary, in the OCaml, for every list of three numerals.** The pinned interpreter
leaves `[a, b, c][1 : 2]` unreduced (`Error (SliceE …)`); on main it is `[b, c]`. -/
theorem slice_boundary_all (a b c : Nat) :
    answerTags (runSlice pinProgram [a, b, c] 1 2) = some (1, 22) ∧
      answerElems (runSlice mainProgram [a, b, c] 1 2) = some [numE b, numE c] :=
  ⟨(Prod.mk.inj (slice3_pin a b c)).1, (Prod.mk.inj (slice3_main a b c)).1⟩

end Silmaril.Wasm.OCaml.SpecTecEval
