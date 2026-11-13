module

public import Silmaril.Wasm.JcoTool.KNetCore.Defs
public import Silmaril.Proofs.Wasm.JcoTool.KNetCore.Main

/-!
# Networks of generated modules on Core 3.0: theorems

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KNetCore.Main`.

* **`creach_abs`**: in a live network (`KNet.MNet.Live`: well placed, topologically numbered, a
  consistent specification, every kernel's bounds), with distinct built-ins as distinct host
  functions, every reachable system in which **every generated module runs on Core 3.0**
  (`CStep`: Core invocations of its callback, `KRead.CRStepU`) stands for a reachable system of the
  model (`KNet.MReach`): the same drop store and network nodes, every module's Core store holding
  the model machine. So the model's theorems (`KNet`, `KLive`, `Net`, `Pipes`) hold with the
  modules' WebAssembly run by Core 3.0 instead of the fragment semantics `KDrop.dexec`, for **every
  network**, not only the single-module pipe of `KRead`.
* **`ktee_core_correct`**: the tee of two generated modules, run on Core 3.0: each sink, once it
  has dropped its input, holds its branch's kernel run.

Hypotheses that remain: the start (`CRel` of the model's start: each module's Core store holds
its machine after the lift; `KCoreHost.genD_lift_host` gives it for one module instantiated on the
host store, the network's setup store stands for the lifts' calls), the deterministic profile, and
injective host-call encodings (as in `KRead`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KNetCore

open Silmaril.Wasm.Execution.Core (Store ModuleInst)
open Silmaril.Wasm.Numerics (GrowKind)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.Component.Streams.Net (Reach Sys)
open Silmaril.Wasm.JcoTool.KCore (BI trV)
open Silmaril.Wasm.JcoTool.KNet (MNet MSys MReach)
open Silmaril.Wasm.JcoTool.KLive (KFits)

variable {H : Type}

/-- **The refinement**: a reachable system whose modules run on Core 3.0 stands for a reachable
system of the model. -/
theorem creach_abs {o : GrowKind → Nat → Nat → Nat → Bool} {hb : BI → H} {ma : Nat} {M : MNet}
    (hL : M.Live) (hinj : Function.Injective hb) {mi : Fin M.net.k → ModuleInst} {a : Fin M.net.k → Nat}
    {c₀ c : CSys H M.net} (h0 : CRel hb ma M mi a (MSys.init M) c₀) (h : CSteps o hb ma M a c₀ c) :
    ∃ m, MReach M m ∧ CRel hb ma M mi a m c :=
  Silmaril.Proofs.Wasm.JcoTool.KNetCore.creach_abs hL hinj h0 h

/-- **A tee of generated modules, run on Core 3.0, is correct.** -/
theorem ktee_core_correct {o : GrowKind → Nat → Nat → Nat → Bool} {hb : BI → H} {ma : Nat}
    {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (f₁ : KFits k₁ N₁) (f₂ : KFits k₂ N₂) (hinj : Function.Injective hb)
    {mi : Fin 6 → ModuleInst} {a : Fin 6 → Nat}
    {c₀ c : CSys H (Silmaril.Wasm.JcoTool.KNet.ktee xs k₁ k₂ N₁ N₂).net}
    (h0 : CRel hb ma _ mi a (MSys.init _) c₀) (h : CSteps o hb ma _ a c₀ c) :
    (∀ b, (c.ns (4 : Fin 6)).rd = .gone b → (c.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
      (∀ b, (c.ns (5 : Fin 6)).rd = .gone b → (c.ns (5 : Fin 6)).got = (trV k₂).run xs) := by
  obtain ⟨m, hR, -, hns, -⟩ := creach_abs (Silmaril.Wasm.JcoTool.KLive.ktee_live h₁ h₂ f₁ f₂) hinj h0 h
  rw [hns]
  exact Silmaril.Wasm.JcoTool.KNet.ktee_correct h₁ h₂ hR

end Silmaril.Wasm.JcoTool.KNetCore
