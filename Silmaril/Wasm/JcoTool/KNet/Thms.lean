module

public import Silmaril.Wasm.JcoTool.KNet.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KNet.Main

/-!
# Networks with generated modules: theorems

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KNet.Main`.

* **`mreach_abs`**: in any well-formed network whose module nodes run `KDrop.genD` (`MNet.OK`),
  every reachable system stands for a reachable system of the network (`Net.Reach`): the
  network nodes are the same, the modules are related to their nodes by `KDrop.RelD`. So every
  `Net`/`Pipes` theorem holds for networks of generated modules.
* **`ktee_correct`**, `ktee_safe`: a tee whose two branches are generated modules: each sink, once
  it has dropped its input, holds its branch's kernel run on the whole input (also when the other
  branch stopped early), and at every point a prefix of it.
* `kchain2_correct`: two generated modules in a chain hold the composite `T ⟫ U`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Net (Reach Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)

/-- **The refinement**: a reachable system with generated modules stands for a reachable system
of the network. -/
theorem mreach_abs {M : MNet} (hM : M.OK) {m : MSys M.net} (h : MReach M m) :
    ∃ s, Reach M.net s ∧ s.st = m.st ∧ ∀ i, M.gen i = none → s.ns i = m.ns i := by
  obtain ⟨s, hR, hst, hns⟩ := Silmaril.Proofs.Wasm.JcoTool.KNet.mreach_abs hM h
  exact ⟨s, hR, hst, fun i hi => (hns i).1 hi⟩

/-- **A tee of generated modules is correct.** -/
theorem ktee_correct {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (ktee xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) :
    (∀ b, (m.ns (4 : Fin 6)).rd = .gone b → (m.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
      (∀ b, (m.ns (5 : Fin 6)).rd = .gone b → (m.ns (5 : Fin 6)).got = (trV k₂).run xs) :=
  Silmaril.Proofs.Wasm.JcoTool.KNet.ktee_correct h₁ h₂ h

/-- At every point each sink of a tee of generated modules holds a prefix of its output. -/
theorem ktee_safe {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (ktee xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) :
    (m.ns (4 : Fin 6)).got <+: (trV k₁).run xs ∧ (m.ns (5 : Fin 6)).got <+: (trV k₂).run xs :=
  Silmaril.Proofs.Wasm.JcoTool.KNet.ktee_safe h₁ h₂ h

/-- Two generated modules in a chain hold the composite. -/
theorem kchain2_correct {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (kchain2 xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) {b : Bool}
    (hb : (m.ns (3 : Fin 4)).rd = .gone b) : (m.ns (3 : Fin 4)).got = ((trV k₁).comp (trV k₂)).run xs :=
  Silmaril.Proofs.Wasm.JcoTool.KNet.kchain2_correct h₁ h₂ h hb

end Silmaril.Wasm.JcoTool.KNet
