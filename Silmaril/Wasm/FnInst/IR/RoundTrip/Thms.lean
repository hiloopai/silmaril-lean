module

public import Silmaril.Wasm.FnInst.IR.Bodies.Thms

/-!
# Round trips between the body variants

The translations go one way; the reverse maps (`compileFunc` after `decompileFunc`, `toBFunc?`
after recognition) are partial or not inverse on syntax. They are inverse up to equivalence,
which is what makes the variants equivalent where the translations are exact:

* `ssa_roundtrip_equiv`: for a decompilable SSA function `s`, `compileFunc (decompileFunc s)`
  is equivalent to `s`;
* `frag_roundtrip_equiv`: for a fragment function whose SSA translation decompiles, the result
  is equivalent to it (the round trip `frag → ssa → frag`);
* `bir_roundtrip_equiv`: re-lowering the recognised function of a Binaryen body, where
  `toBFunc?` succeeds, gives a Binaryen body equivalent to it in every environment (the syntax
  can differ, for example in `select` annotations).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open Silmaril.Wasm.SSA
open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

theorem ssa_roundtrip_equiv (E : Type) {h : Hole} (s : (ssaDec E).Body h) :
    Beh.Equiv (compileFunc ((ofSSA E).body h s).1).Run s.1.Run := fun _ _ =>
  compileFunc_iff.trans (decompileFunc_iff (Option.some_get s.2.2).symm)

theorem frag_roundtrip_equiv {f g : FragFunc} (hg : decompileFunc (compileFunc f) = some g) :
    Beh.Equiv g.Run f.Run :=
  compile_decompile_equiv hg

theorem bir_roundtrip_equiv (H : Type) {h : Hole} (b : BirBody h) {ty : TypeIdx} {bf : BFunc}
    (hl : toBFunc? ty b.recog = some bf) :
    ∃ b' : BirBody h, b'.1 = bf ∧ ∀ e : Store H × ModuleInst,
      Beh.Equiv ((bir H).den e h b') ((bir H).den e h b) := by
  obtain ⟨b', hb', hr⟩ := lower_body (h := h)
    ⟨b.recog, hasType_of_ofBFunc? b.recog_spec, b.recog_native⟩ hl
  refine ⟨b', hb', fun e => ?_⟩
  rw [equiv_bir_iff, hr]
  exact fun _ _ => Iff.rfl

end Silmaril.Wasm.FnInst.IR
