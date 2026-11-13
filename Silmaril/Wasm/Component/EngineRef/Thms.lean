module

public import Silmaril.Wasm.Component.EngineRef.Defs
public import Silmaril.Wasm.Component.Lime1Ref.Defs
import Silmaril.Proofs.Wasm.Component.EngineRef.Call

/-!
# The reference-machine half over any engine: theorems

All proved; proofs in `Silmaril.Proofs.Wasm.Component.EngineRef.{Inst,CallPath,Call}` (the
instantiation and call phases of `Reference.refToSpec_of_arity`, re-run over an arbitrary
engine as `Param.Core3R` re-ran them over `core3R P V I`).

* `refToSpecE_of_facts`: for a simple component `c` in the fragment of `refToSpec_of_arity`
  (`Good`, `FloatFree`, `Arity`), the instantiation facts `InstFacts E ofCore c cs ci addr` and
  the run facts of the core activation of export `x` on the lowered arguments give: every
  behaviour of calling `x` on `c.toRef.map ofCore` over `E` (reference host without host
  functions, any component choice profile) is in `specOut x Out Div`;
* `refToSpecEOn_of_facts`: hence `RefToSpecEOn E ofCore emb D` for a domain `D` on which these
  facts hold with `specOut x Out Div` contained in the engine's specification
  `exportSpecE E emb c x vs`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.EngineRef

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Runtime

/-- **The reference-machine half over any engine, from its instantiation and run facts.** -/
theorem refToSpecE_of_facts {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} (prof : ProfileKind) (c : Simple) (hc : c.Good)
    (hf : c.FloatFree) (ha : c.Arity) {cs : E.Store (CanonHost E)} {ci : E.Inst}
    {addr : Nat → E.FuncAddr} (hF : InstFacts E ofCore c cs ci addr) (x : SimpleExport)
    (hx : x ∈ c.exports) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) {Out : Set (Option (List Flat))} {Div : Prop}
    (hRF : RunFacts E cs (addr x.core) (lowerArgs x.ty.params vs) (ValTy.flatList x.ty.results)
      Out Div) :
    exportBehaviours prof (refHostE E) () (c.toRef.map ofCore) [] x.name (vs.map toRefVal) ⊆
      specOut x Out Div :=
  Silmaril.Proofs.Wasm.Component.EngineRef.refToSpecE_of_facts prof c hc hf ha hF x hx vs hvs hRF

/-- **The machine half on a domain from the engine facts**: if every component of the domain
`D` in the fragment has instantiation facts, and every typed call of one of its exports has run
facts whose outcomes are in the engine's specification, then `RefToSpecEOn E ofCore emb D`. -/
theorem refToSpecEOn_of_facts {E : Engine} [∀ a b, Decidable (E.ExternSub a b)]
    {ofCore : Silmaril.Wasm.Module → E.Module} {emb : NumModule → E.Module}
    {D : Simple → Prop}
    (h : ∀ c, D c → c.Good → c.FloatFree → c.Inst → c.Arity →
      ∃ (cs : E.Store (CanonHost E)) (ci : E.Inst) (addr : Nat → E.FuncAddr),
        InstFacts E ofCore c cs ci addr ∧
        ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
          ∃ (Out : Set (Option (List Flat))) (Div : Prop),
            RunFacts E cs (addr x.core) (lowerArgs x.ty.params vs)
              (ValTy.flatList x.ty.results) Out Div ∧
            specOut x Out Div ⊆ exportSpecE E emb c x vs) :
    Silmaril.Wasm.Component.Lime1Ref.RefToSpecEOn E ofCore emb D := by
  intro prof c hD hc hf hi ha x hx vs hvs b hb
  obtain ⟨cs, ci, addr, hF, hR⟩ := h c hD hc hf hi ha
  obtain ⟨Out, Div, hRF, hsub⟩ := hR x hx vs hvs
  exact hsub (refToSpecE_of_facts prof c hc hf ha hF x hx vs hvs hRF hb)

end Silmaril.Wasm.Component.EngineRef
