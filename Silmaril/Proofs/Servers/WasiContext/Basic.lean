module

public import Silmaril.Servers.WasiContext.Defs

/-!
# Proofs: `wasi:http` components, hosts as contexts
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.WasiContext

open Silmaril.Servers.Exchange
open Silmaril.Games Silmaril.Wasi Silmaril.Servers.Calls Silmaril.Servers.WasiHttp
open Silmaril.Servers.WasiContext

variable {Y : Silmaril.Games.Sig.{0}} {X : Set FnName}

theorem linkServer_eq (η : Host Y proxyImports)
    (σ : Silmaril.Games.Strategy (nsig proxyImports) (nsig X)) :
    linkServer η σ = readExch (interacts η σ) := by
  ext t
  exact ⟨fun ⟨s, hs, u, hu, p, hz, hf⟩ => ⟨u, ⟨hu, s, hs, p, hz⟩, hf⟩,
    fun ⟨u, ⟨hu, s, hs, p, hz⟩, hf⟩ => ⟨s, hs, u, hu, p, hz, hf⟩⟩

end Silmaril.Proofs.Servers.WasiContext
