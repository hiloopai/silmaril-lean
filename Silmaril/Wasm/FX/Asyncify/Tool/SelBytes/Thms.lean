module

public import Silmaril.Wasm.FX.Asyncify.Tool.Thms
public import Silmaril.Wasm.FX.Asyncify.Tool.SelSim.Thms

/-!
# The selective tool on bytes

`asyncifyBytesSelective` (`--selective`, `Silmaril.Wasm.FX.Asyncify.Tool.Selective`) decodes, runs
the selective pass and encodes. `asyncifyBytesSel_correct` is `asyncifyBytes_correct` for it:
the input decodes (soundly) to a module of the fragment with source program `P`, the output
bytes encode a module read back as `asyncifyProg (selProg P)`, with the protocol's globals and the
same exported functions, and every call within `DepthBound` has the same behaviours in the input
(suspending) and in the output (asyncify protocol), by `asyncify_beh_sel` (`Tool/SelSim`).

New statements (short proofs, the pattern of `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Bytes`).
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm

variable {σ : Type}

theorem asyncifySelective_eq {m m' : Module} {pages : Nat}
    (h : asyncifySelective m pages = .ok m') :
    ∃ P, recognize m = .ok P ∧ m' = asyncifyModule m (selProg P) pages := by
  unfold asyncifySelective at h
  cases hr : recognize m with
  | error e => rw [hr] at h; cases h
  | ok P =>
    rw [hr] at h
    refine ⟨P, rfl, ?_⟩
    by_cases h1 : (m.exports.any fun e => e.name == stateExport || e.name == memoryExport) = true
    · simp [h1] at h
    · by_cases h2 : P.sb + 4 * P.frameWords ≤ 65536 * pages ∧ pages < 65536
      · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, Except.ok.injEq, and_self] at h
        exact h.symm
      · simp [h1, h2] at h

/-- The three stages of `asyncifyBytesSelective`: decode, transform, encode. -/
theorem asyncifyBytesSel_inv {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytesSelective b pages = .ok b') :
    ∃ m m' bs, Binary.Core.decode? b = some m ∧ asyncifySelective m pages = .ok m' ∧
      Binaryen.Exe.encodeModule? m' = .ok bs ∧ b' = ⟨bs.toArray⟩ := by
  unfold asyncifyBytesSelective at h
  split at h
  · cases h
  · rename_i m hd
    split at h
    · cases h
    · rename_i m' ha
      split at h
      · rename_i bs he
        exact ⟨m, m', bs, hd, ha, he, (Except.ok.inj h).symm⟩
      · cases h

/-- **The selective tool on bytes**: the stages read back. -/
theorem asyncifyBytesSel_spec {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytesSelective b pages = .ok b') :
    ∃ m P m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b.data.toList m ∧
      P.WF ∧ envOf m = some P.env ∧ m' = asyncifyModule m (selProg P) pages ∧
      Binary.Core.Encodes b'.data.toList m' ∧ envOfLax m' = some (asyncifyProg (selProg P)) ∧
      globalsOfLax m' = some P.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) := by
  obtain ⟨m, m', bs, hd, ha, he, hb'⟩ := asyncifyBytesSel_inv h
  obtain ⟨P, hr, hm'⟩ := asyncifySelective_eq ha
  obtain ⟨hwf, henv⟩ := recognize_sound hr
  have henv' : envOf m = some (selProg P).env := by rw [selProg_env]; exact henv
  have henc : Binary.Core.Encodes b'.data.toList m' := by
    rw [hb']; simpa using Binaryen.Exe.encodeModule?_sound he
  refine ⟨m, P, m', hd, Binary.Core.decode?_sound hd, hwf, henv, hm', henc, ?_, ?_, ?_⟩
  · rw [hm']; exact envOfLax_asyncifyModule henv' pages
  · rw [hm']; exact globalsOfLax_asyncifyModule m (selProg P) pages
  · rw [hm']; exact exportFunc_asyncifyModule m (selProg P) pages

/-- **End to end, `--selective`.** When `asyncifyBytesSelective` turns `b` into `b'`, the input
decodes to `m` (source program `P`), `b'` encodes a module read back as
`asyncifyProg (selProg P)` with the protocol's globals and the same exported functions, and for
every defined function `e`, arguments of the right number, deterministic host and source run
within `DepthBound`, the call in `m` (suspending) and in `b'` (asyncify protocol) have the same
behaviours. -/
theorem asyncifyBytesSel_correct {b b' : ByteArray} {pages : Nat}
    (h : asyncifyBytesSelective b pages = .ok b') :
    ∃ m P m', Binary.Core.decode? b = some m ∧ Binary.Core.Encodes b'.data.toList m' ∧
      envOf m = some P.env ∧ envOfLax m' = some (asyncifyProg (selProg P)) ∧
      globalsOfLax m' = some P.tGlobals ∧ (∀ name, exportFunc m' name = exportFunc m name) ∧
      ∀ {σ : Type} (H : Host σ) {e : Nat} {fn : FnSrc} (args : List W) (s : σ),
        P.fnAt e = some fn → args.length = fn.nparams → DepthBound P H (srcCfg e fn args, s) →
        srcInit P.env e args = some (srcCfg e fn args) ∧
        tgtInit (selProg P) e args s = some (tgtSt (selProg P) e (selFn P fn) args s) ∧
        beh (srcStep P.env H) (srcCfg e fn args, s) =
          beh (tgtStep (asyncifyProg (selProg P)) H) (tgtSt (selProg P) e (selFn P fn) args s) := by
  obtain ⟨m, P, m', hd, -, hwf, henv, -, he, hlax, hgl, hex⟩ := asyncifyBytesSel_spec h
  refine ⟨m, P, m', hd, he, henv, hlax, hgl, hex, fun {_} H {e} {fn} args s hfn hargs hb => ?_⟩
  have hfn' : (selProg P).fnAt e = some (selFn P fn) := by rw [selProg_fnAt, hfn]; rfl
  exact ⟨srcInit_eq hfn args, tgtInit_eq hfn' args s,
    asyncify_beh_sel P hwf H hfn hfn' args hargs s hb⟩

/-- info: 'Silmaril.Wasm.FX.Asyncify.Tool.asyncifyBytesSel_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms asyncifyBytesSel_correct

end Silmaril.Wasm.FX.Asyncify.Tool
