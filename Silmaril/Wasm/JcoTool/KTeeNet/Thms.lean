module

public import Silmaril.Wasm.JcoTool.KTeeNet.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KTeeNet.Main

/-!
# Networks with generated kernels and tees: theorems

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KTeeNet.Main`.

* **`greach_abs`**: in any well-formed network whose module nodes run `KDrop.genD` or
  `KTee.genT` (`GNet.OK`), every reachable system stands for a reachable system of the network
  (`Net.Reach`): the network nodes are the same, the modules are related to their nodes by
  `KDrop.RelD` and `KTee.RelT`. So every `Net`/`Pipes` theorem holds for networks of generated
  kernels and tees.
* **`gtee_correct`**, `gtee_safe`: source → **generated tee** → (generated `k₁` → sink₁,
  generated `k₂` → sink₂): each sink, once it has dropped its input, holds its branch's kernel run
  on the whole input (also when the other branch stopped early), and at every point a prefix of
  it. No hypothesis on the kernels (safety and correctness at the end; liveness of the tee
  module is not proved, see `docs/projects/wasm-components.md`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KTeeNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Net (Reach Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KNet (MSys)

/-- **The refinement**: a reachable system with generated kernels and tees stands for a reachable
system of the network. -/
theorem greach_abs {M : GNet} (hM : M.OK) {m : MSys M.net} (h : GReach M m) :
    ∃ s, Reach M.net s ∧ s.st = m.st ∧ ∀ i, M.gen i = none → s.ns i = m.ns i := by
  obtain ⟨s, hR, hst, hns⟩ := Silmaril.Proofs.Wasm.JcoTool.KTeeNet.greach_abs hM h
  exact ⟨s, hR, hst, fun i hi => (hns i).1 hi⟩

/-- **Reachable kernel modules keep their buffers in bounds** (or have exited): the bounds
`KCoreRun.genD_safe` needs for their Core 3.0 runs. -/
theorem greach_buf {M : GNet} (hM : M.OK) {m : MSys M.net} (h : GReach M m) {i : Fin M.net.k}
    {k : KM} {N : Nat} (hg : M.gen i = some (.kern k N)) :
    (m.ms i).mode = .exited ∨
      ((m.ms i).g Silmaril.Wasm.JcoTool.KCore.BLEN ≤ Silmaril.Wasm.JcoTool.KCore.CAP ∧
        (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OLEN ≤ Silmaril.Wasm.JcoTool.KCore.CAP ∧
        (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OOFF ≤ (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OLEN) :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeNet.greach_buf hM h hg

/-- The fully generated tee network is well placed. -/
theorem gtee_ok (xs : List Val) {N : Nat} (k₁ k₂ : KM) {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) : (gtee xs N k₁ k₂ N₁ N₂).OK :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeNet.gtee_ok xs k₁ k₂ h h₁ h₂

/-- **A tee whose tee and branches are generated modules is correct.** -/
theorem gtee_correct {xs : List Val} {N : Nat} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (gtee xs N k₁ k₂ N₁ N₂).net}
    (hm : GReach _ m) :
    (∀ b, (m.ns (4 : Fin 6)).rd = .gone b → (m.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
      (∀ b, (m.ns (5 : Fin 6)).rd = .gone b → (m.ns (5 : Fin 6)).got = (trV k₂).run xs) :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeNet.gtee_correct h h₁ h₂ hm

/-- At every point each sink of the fully generated tee holds a prefix of its output. -/
theorem gtee_safe {xs : List Val} {N : Nat} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (gtee xs N k₁ k₂ N₁ N₂).net}
    (hm : GReach _ m) :
    (m.ns (4 : Fin 6)).got <+: (trV k₁).run xs ∧ (m.ns (5 : Fin 6)).got <+: (trV k₂).run xs :=
  Silmaril.Proofs.Wasm.JcoTool.KTeeNet.gtee_safe h h₁ h₂ hm

end Silmaril.Wasm.JcoTool.KTeeNet
