module

public import Silmaril.Wasm.JcoTool.KFit.Thms
public import Silmaril.Wasm.JcoTool.KDropEmit.Thms
public import Silmaril.Wasm.Component.Streams.KernelWat.Thms

/-!
# The bytes the tools write for chains and tees, and the liveness of what they denote

Byte-level statements for the networks the tests build, from the generators' theorems:

* `kchain_tool_live`: for a chain of any length, the bytes `wasm-jco kcore … -o` writes for each
  stage encode `KCoreEmit.toModule (genD kᵢ Nᵢ)` (`KDropEmit.kdrop_bytes`, silmaril's verified
  encoder), and every maximal execution of the chain of those modules ends with the sink holding
  the kernels' composite (`KLive.kchain_exec_correct`).
* **`ktee_tool_live`**: for a tee, the bytes of both branches encode their generated modules, the
  bytes `wasm-streams-gen tee … -o` writes encode the module its certified text denotes
  (`KernelWat.teeBytes_sound`: the certificate, checked per output), and every maximal execution
  of the tee network whose branches are those modules ends with each sink holding its branch's
  run (`KLive.ktee_exec_correct`).

What is not claimed: that the tee template's module behaves as the `Net` tee node (the tee in the
liveness theorem); the template has a byte-level certificate, not a semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KLiveEmit

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KCoreEmit (wasmOf toModule)
open Silmaril.Wasm.JcoTool.KDropEmit (toolGen)
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KDrop (runs genD)

/-- **A chain of any length, from the bytes to the end of every execution.** -/
theorem kchain_tool_live {xs : List Val} {ks : List KM} {Nb : Nat → Nat} {names : Nat → String}
    {bs : Nat → ByteArray} (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    (hfit : ∀ (i : Nat) (h : i < ks.length), KFits ks[i] (Nb i))
    (hb : ∀ (i : Nat) (h : i < ks.length), wasmOf (toolGen false ks[i] (Nb i)) (names i) = .ok (bs i)) :
    (∀ (i : Nat) (h : i < ks.length),
      Silmaril.Wasm.Binary.Core.Encodes (bs i).data.toList (toModule (genD ks[i] (Nb i)) (names i))) ∧
    ∀ {r : Nat → MSys (kchainM xs ks Nb).net}, MExec _ r →
      ∃ n, ∀ j, n ≤ j → r j = r n ∧ ((r n).ns (snkM xs ks Nb)).got = runs ks xs := by
  refine ⟨fun i h => KDropEmit.kdrop_bytes (hb i h), fun hr => ?_⟩
  obtain ⟨n, hn⟩ := kchain_exec_correct hN hws hfit hr
  exact ⟨n, fun j hj => ⟨(hn j hj).1, (hn j hj).2.2⟩⟩

/-- **A tee, from the bytes to the end of every execution**: the branches' bytes encode their
generated modules, the tee's bytes encode its certified text's module, and every maximal
execution of the tee of the generated branches ends with both sinks correct. -/
theorem ktee_tool_live {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ batch : Nat} {n₁ n₂ nt : String}
    {b₁ b₂ bt : ByteArray} (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (f₁ : KFits k₁ N₁) (f₂ : KFits k₂ N₂)
    (hb₁ : wasmOf (toolGen false k₁ N₁) n₁ = .ok b₁) (hb₂ : wasmOf (toolGen false k₂ N₂) n₂ = .ok b₂)
    (hbt : Silmaril.Wasm.Component.Streams.KernelWat.teeBytes nt batch = .ok bt) :
    Silmaril.Wasm.Binary.Core.Encodes b₁.data.toList (toModule (genD k₁ N₁) n₁) ∧
    Silmaril.Wasm.Binary.Core.Encodes b₂.data.toList (toModule (genD k₂ N₂) n₂) ∧
    (∃ m, Silmaril.Wasm.Text.Core.Encodes
        (Silmaril.Wasm.Component.Streams.KernelWat.teeWat nt
          (Silmaril.Wasm.Component.Streams.KernelWat.clampBatch batch)) m ∧
      Silmaril.Wasm.Binary.Core.Encodes bt.data.toList m) ∧
    ∀ {r : Nat → MSys (ktee xs k₁ k₂ N₁ N₂).net}, MExec _ r →
      ∃ n, ∀ j, n ≤ j → r j = r n ∧ ((r n).ns (4 : Fin 6)).got = (trV k₁).run xs ∧
        ((r n).ns (5 : Fin 6)).got = (trV k₂).run xs :=
  ⟨KDropEmit.kdrop_bytes hb₁, KDropEmit.kdrop_bytes hb₂,
    Silmaril.Wasm.Component.Streams.KernelWat.teeBytes_sound hbt,
    fun hr => ktee_exec_correct h₁ h₂ f₁ f₂ hr⟩

/-- The same for small kernels, with no hypothesis on the kernels. -/
theorem ktee_tool_live_small {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ batch : Nat} {n₁ n₂ nt : String}
    {b₁ b₂ bt : ByteArray} (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (s₁ : KFit.Small k₁ = true) (s₂ : KFit.Small k₂ = true)
    (hb₁ : wasmOf (toolGen false k₁ N₁) n₁ = .ok b₁) (hb₂ : wasmOf (toolGen false k₂ N₂) n₂ = .ok b₂)
    (hbt : Silmaril.Wasm.Component.Streams.KernelWat.teeBytes nt batch = .ok bt) :
    Silmaril.Wasm.Binary.Core.Encodes b₁.data.toList (toModule (genD k₁ N₁) n₁) ∧
    Silmaril.Wasm.Binary.Core.Encodes b₂.data.toList (toModule (genD k₂ N₂) n₂) ∧
    ∀ {r : Nat → MSys (ktee xs k₁ k₂ N₁ N₂).net}, MExec _ r →
      ∃ n, ∀ j, n ≤ j → r j = r n ∧ ((r n).ns (4 : Fin 6)).got = (trV k₁).run xs ∧
        ((r n).ns (5 : Fin 6)).got = (trV k₂).run xs := by
  obtain ⟨e₁, e₂, -, h⟩ := ktee_tool_live (xs := xs) h₁ h₂ (KFit.small_fits s₁ h₁.2)
    (KFit.small_fits s₂ h₂.2) hb₁ hb₂ hbt
  exact ⟨e₁, e₂, h⟩

end Silmaril.Wasm.JcoTool.KLiveEmit
