module

public import Silmaril.Wasm.JcoTool.KReadComp.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KReadComp.Denote
public import Silmaril.Wasm.Component.Streams.NetGame.Thms

/-!
# Generated modules on Core 3.0 as realisations in the stream game

Proofs of the wiring in `Silmaril.Proofs.Wasm.JcoTool.KReadComp.Denote`.

* **`obsComp_denU`** (no hypothesis): the component of an observed runtime denotes its strategy
  reading, `(obsComp O).denU obsSem = O.game`; so `obsComp_realizes`: an observation that reads
  as `T` gives a realisation of `T` in the stream game (`StreamGame.Realizes`, and
  `NetGame.game obsSem`, the `VSem` of networks).
* **`gen_realizes`** (no hypothesis beyond `CoreGen.OK`): the
  component of a generated module on Core 3.0 (`CoreGen`, well formed) **realises its kernel's
  transformer `trV k`**, in the stream game and as the network semantics `NetGame.game obsSem`.
  This discharges the realisation hypotheses of `KGame`, `NetGame` and `NetSem` for concrete
  components whose core module is the generated module run on Core.
* `gen_seq`: two of them plugged (`Algebra.seq`) realise the composite, and chain networks of
  their kernels have the outcomes of the pipe of the composite.
* **`gen_equiv_compose`**: **the composition of equivalent generated components is equivalent**:
  generated modules of equivalent kernels plug to `CompEquiv` components (under `obsSem`), and
  chains of their kernels have the same outcomes.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KReadComp

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.NetSem (chainOut pipeOut)
open Silmaril.Wasm.JcoTool.KRead (Obs)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.Numerics (GrowKind)

variable {σ : Type}

/-- **The component of an observed runtime denotes its strategy reading.** -/
theorem obsComp_denU (O : Obs) : (obsComp O).denU obsSem = O.game :=
  Silmaril.Proofs.Wasm.JcoTool.KReadComp.obsComp_denU O

/-- An observation that reads as `T` gives a realisation of `T` in the stream game. -/
theorem obsComp_realizes {O : Obs} {T : Tr σ Val Val} (h : O.Reads T) :
    Algebra.StreamGame.Realizes obsSem (obsComp O) T :=
  ⟨rfl, by simp [obsComp, Algebra.length_reexport], (obsComp_denU O).trans
    (Silmaril.Wasm.JcoTool.KRead.game_eq_den h)⟩

section
variable (o : GrowKind → Nat → Nat → Nat → Bool)

/-- **A generated module on Core 3.0 realises its kernel's transformer** in the stream game. -/
theorem gen_realizes {g : CoreGen} (hg : g.OK) :
    Algebra.StreamGame.Realizes obsSem (obsComp (g.obs o)) (trV g.k) :=
  obsComp_realizes (Silmaril.Wasm.JcoTool.KRead.core_reads hg.1 o hg.2.1 hg.2.2.2.2 hg.2.2.1 hg.2.2.2.1)

/-- The same, as the network semantics `NetGame.game obsSem` (the `VSem` of `NetSem`). -/
theorem gen_vsem {g : CoreGen} (hg : g.OK) :
    (Streams.NetGame.game obsSem).Realizes (obsComp (g.obs o)) (trV g.k) :=
  Streams.NetGame.realizes_game_iff.2 (gen_realizes o hg)

/-- **Two generated modules on Core, plugged, realise the composite of their kernels**, and the
chain networks of the kernels have the outcomes of the pipe of the composite. -/
theorem gen_seq {g₁ g₂ : CoreGen} (h₁ : g₁.OK) (h₂ : g₂.OK) :
    Algebra.StreamGame.Realizes obsSem (Algebra.seq (obsComp (g₁.obs o)) (obsComp (g₂.obs o)))
        ((trV g₁.k).comp (trV g₂.k)) ∧
      ∀ xs, chainOut xs (trV g₁.k) (trV g₂.k) = pipeOut xs ((trV g₁.k).comp (trV g₂.k)) :=
  Streams.NetGame.chain_realizes (gen_realizes o h₁) (gen_realizes o h₂)

/-- **The composition of equivalent generated components is equivalent.** -/
theorem gen_equiv_compose {g₁ g₁' g₂ g₂' : CoreGen} (h₁ : g₁.OK) (h₁' : g₁'.OK) (h₂ : g₂.OK)
    (h₂' : g₂'.OK) (e₁ : (trV g₁.k).Equiv (trV g₁'.k)) (e₂ : (trV g₂.k).Equiv (trV g₂'.k)) :
    Algebra.CompEquiv obsSem (Algebra.seq (obsComp (g₁.obs o)) (obsComp (g₂.obs o)))
        (Algebra.seq (obsComp (g₁'.obs o)) (obsComp (g₂'.obs o))) ∧
      ∀ xs, chainOut xs (trV g₁.k) (trV g₂.k) = chainOut xs (trV g₁'.k) (trV g₂'.k) :=
  Streams.NetGame.equiv_compose (gen_realizes o h₁) (gen_realizes o h₁')
    (gen_realizes o h₂) (gen_realizes o h₂') e₁ e₂

end

end Silmaril.Wasm.JcoTool.KReadComp
