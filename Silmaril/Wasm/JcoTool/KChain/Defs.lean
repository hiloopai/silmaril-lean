module

public import Silmaril.Wasm.JcoTool.KDrop.Defs
public import Silmaril.Wasm.Component.Algebra.Ops.Defs

/-!
# Chains of generated modules of any length, in the component algebra

`KGame` links chains of **two** generated modules (`KDrop.genD`) to the stream game. This module
gives the objects for chains of **any** nonempty length:

* `trsN k ks`: the transformer of the kernels `k :: ks`, composed left to right
  (`trV k ⟫ (trV k₁ ⟫ (…))`), with its state type (a dependent pair, since every composition
  changes the state type);
* `seqN c cs`: the components `c :: cs` plugged left to right (`seq c (seq c₁ (…))`);
* `kernels p ps`: the kernels of a list of (component, kernel) pairs.

The theorems are in `KChain.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KChain

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (trV)

/-- **The composite of the kernels `k :: ks`**, left to right, with its state type. -/
def trsN : KM → List KM → (σ : Type) × Tr σ Val Val
  | k, [] => ⟨KSt, trV k⟩
  | k, k' :: ks => ⟨KSt × (trsN k' ks).1, (trV k).comp (trsN k' ks).2⟩

variable {M : Type} [CoreModule M]

/-- **The plug of the components `c :: cs`**, left to right. -/
def seqN : Comp M → List (Comp M) → Comp M
  | c, [] => c
  | c, c' :: cs => Algebra.seq c (seqN c' cs)

/-- The kernels of a nonempty list of (component, kernel) pairs. -/
def kernels (p : Comp M × KM) (ps : List (Comp M × KM)) : List KM := p.2 :: ps.map Prod.snd

/-- The components of a nonempty list of (component, kernel) pairs, plugged. -/
def plugN (p : Comp M × KM) (ps : List (Comp M × KM)) : Comp M := seqN p.1 (ps.map Prod.fst)

/-- The composite transformer of a nonempty list of (component, kernel) pairs. -/
def trN (p : Comp M × KM) (ps : List (Comp M × KM)) : (σ : Type) × Tr σ Val Val :=
  trsN p.2 (ps.map Prod.snd)

end Silmaril.Wasm.JcoTool.KChain
