module

public import Silmaril.Wasm.JcoTool.KNet.Defs
public import Silmaril.Wasm.Component.Streams.Live.Thms

/-!
# Liveness of networks of generated modules: definitions

`KNet` runs generated modules (`KDrop.genD`) as nodes of any `Net` network (`MNet`, `MStep`), and
its theorems hold once the sinks have dropped their inputs. Here: that point is reached.

* `KFits k N`: **the kernel's bounds**. The generated module keeps the kernel's buffer and its
  output in fixed regions of memory (`CAP` bytes each) and traps (by design: `unreachable`)
  when a step of the kernel would overflow them. `KFits` says this never happens on any input:
  feeding any chunk of at most `N` bytes, or flushing, from any state the kernel reaches. It is
  the condition of `KCore.kimpl_complete` (`fitsF`, `fitsS`), quantified over the reachable
  states.
* `MDone M m`: every network node has finished (`NSt.Finished`: input dropped, outputs closed)
  and every module has exited; in particular every sink has dropped its input.
* `MEnabled M m`: some node or module can step. `MExec M r`: a maximal execution under an
  arbitrary scheduler (each step is a step of some node or module, or nothing can step and the
  system stays).
* `MNet.Live M`: the hypotheses of the liveness theorems: the network is well placed
  (`MNet.OK`), numbered along its streams (`Network.Topo`), has a consistent assignment of
  specifications (`Live.Setting`, which bounds what every node reads and writes), and every
  module's kernel fits (`KFits`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KNet

/-- **The kernel's bounds hold** on every chunk of at most `N` bytes and at every flush, from every
state the kernel reaches. -/
def KFits (k : KM) (N : Nat) : Prop :=
  ∀ xs bs : List Nat, (∀ b ∈ xs, b < 256) → (∀ b ∈ bs, b < 256) → bs.length ≤ N →
    fitsF k (k.tr.feed k.tr.init xs).1 bs 0 = true ∧ fitsS 0 k.flush (k.tr.feed k.tr.init xs).1 0 = true

/-- Every node has finished and every module has exited. -/
def MDone (M : MNet) (m : MSys M.net) : Prop :=
  ∀ i, (M.gen i = none → (m.ns i).Finished) ∧ (M.gen i ≠ none → (m.ms i).mode = .exited)

/-- Some node or module can step. -/
def MEnabled (M : MNet) (m : MSys M.net) : Prop := ∃ m', MStep M m m'

/-- **A maximal execution** under an arbitrary scheduler. -/
def MExec (M : MNet) (r : Nat → MSys M.net) : Prop :=
  r 0 = MSys.init M ∧ ∀ n, MStep M (r n) (r (n + 1)) ∨ (¬ MEnabled M (r n) ∧ r (n + 1) = r n)

/-- **The hypotheses of liveness.** -/
structure _root_.Silmaril.Wasm.JcoTool.KNet.MNet.Live (M : MNet) : Prop where
  ok : M.OK
  topo : M.net.Topo
  spec : ∃ L, Silmaril.Proofs.Wasm.Component.Streams.Live.Consistent M.net L
  fits : ∀ i k N, M.gen i = some (k, N) → KFits k N

/-- **A chain of generated modules of any length** as a network with modules: `KDrop.kchain`
(source, the kernels `ks`, sink), node `i + 1` run as `genD ks[i] (Nb i)`. -/
def kchainM (xs : List Val) (ks : List KM) (Nb : Nat → Nat) : MNet where
  net := Silmaril.Wasm.JcoTool.KDrop.kchain xs ks
  gen i := if h : 0 < i.val ∧ i.val ≤ ks.length then some (ks[i.val - 1]'(by omega), Nb (i.val - 1))
    else none

/-- The sink of `kchainM`. -/
def snkM (xs : List Val) (ks : List KM) (Nb : Nat → Nat) : Fin (kchainM xs ks Nb).net.k :=
  ⟨ks.length + 1, by simp [kchainM, Silmaril.Wasm.JcoTool.KDrop.kchain]⟩

end Silmaril.Wasm.JcoTool.KLive
