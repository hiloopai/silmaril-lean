module

public import Silmaril.Wasm.Institution.Components.Defs
public import Silmaril.Proofs.Wasm.Institution.Components.PairInr
public import Silmaril.Wasm.Component.Env.Thms

@[expose] public section

/-!
# Wrapping preserves meaning

`wrap_denU : (wrap m).denU C = modU C m` for every core semantics `C` and module `m`. The
wrapper's denotation is the environment extension `ext` of the forwarded imports by the core
instance, followed by the export handler. The export handler only calls the new instance
(`splitH_comp_implsH_append`), so the pairing laws (`pair_comp_sumMap`) and the right projection
(`PairInr.pair_restrict_inr`) reduce it to the instance alone. The masking handlers then collapse
into `narrowH`/`widenH`.
-/

namespace Silmaril.Wasm.Institution.Components

open Silmaril.Games Silmaril.Wasm.Component

/-- Splitting at `0` is forwarding to the right. -/
theorem splitH_zero : splitH 0 = Handler.ofHom (Sig.Hom.inr sigU sigU) := by
  funext q
  simp [splitH, Handler.ofHom, Sig.Hom.inr]

/-- The forwarded imports, read at `n` functions, under the import mask, are `narrowH`. -/
theorem maskH_comp_implsN_fwd (n : Nat) :
    (maskH n).comp (implsN n ((List.range n).map Impl.fwd) n) = narrowH n := by
  funext q
  show (implsH n ((List.range n).map Impl.fwd) (q.1.val, q.2)).interp (maskH n) = narrowH n q
  rw [implsH_fwd]
  simp [maskH, Target.prog, q.1.isLt, narrowH, Prog.interp_call]

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Wrapping preserves meaning.** -/
theorem wrap_denU (m : M) : (wrap m).denU C = modU C m := by
  simp only [wrap, Comp.denU, denNodes, Node.den, Node.width, envAfter, List.length_map, modU]
  have hx : ((List.range (CoreModule.exports m).length).map fun j =>
      (⟨(Option.map Prod.fst (CoreModule.exports m)[j]?).getD "", anyTy,
        Impl.fwd ((CoreModule.imports m).length + j)⟩ : Silmaril.Wasm.Component.Export)).map Silmaril.Wasm.Component.Export.impl =
      [] ++ (List.range (CoreModule.exports m).length).map
        fun i => Impl.fwd ((CoreModule.imports m).length + i) := by
    simp [List.map_map, Function.comp_def]
  have hA : (splitH (CoreModule.imports m).length).comp
      (exportsH ((CoreModule.imports m).length + (CoreModule.exports m).length)
        ((List.range (CoreModule.exports m).length).map fun j =>
          (⟨(Option.map Prod.fst (CoreModule.exports m)[j]?).getD "", anyTy,
            Impl.fwd ((CoreModule.imports m).length + j)⟩ : Silmaril.Wasm.Component.Export))) =
      (Handler.sum (implsH (CoreModule.imports m).length [])
        (maskH (CoreModule.exports m).length)).comp (splitH 0) := by
    rw [exportsH, hx]
    exact splitH_comp_implsH_append (σ := []) (fun _ h => by cases h)
  rw [ext, coreNode, Strategy.comp_assoc, Strategy.comp_assoc, ← Strategy.ofHandler_comp]
  rw [show (splitH (CoreModule.imports m).length).comp (exportsH _ _) = _ from hA,
    Strategy.ofHandler_comp, ← Strategy.comp_assoc (Strategy.pair _ _),
    Handler.sum_eq_sumMap, Strategy.pair_comp_sumMap, splitH_zero,
    show ∀ σ : Strategy sigU (sigU ⊕ₛ sigU),
      σ.comp (Strategy.ofHandler (Handler.ofHom (Sig.Hom.inr sigU sigU))) =
        σ.restrict (Sig.Hom.inr sigU sigU) from fun _ => rfl,
    PairInr.pair_restrict_inr]
  rw [Strategy.comp_assoc, Strategy.comp_assoc, ← Strategy.ofHandler_comp (widenH _),
    widenH_comp_maskH, ← Strategy.comp_assoc, ← Strategy.ofHandler_comp, maskH_comp_implsN_fwd]

/-- Wrapping adequacy holds for every core semantics. -/
theorem wrapAdequate : WrapAdequate C := wrap_denU C

end Silmaril.Wasm.Institution.Components
