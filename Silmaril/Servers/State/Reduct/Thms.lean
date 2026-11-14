module

public import Silmaril.Servers.State.Reduct.Defs
public import Silmaril.Servers.State.Thms
import Silmaril.Proofs.Servers.State.Reduct

@[expose] public section

/-!
# Reducts of servers: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.State`. Proofs in
`Silmaril.Proofs.Servers.State.Reduct`.

* **`Server.hists_comap`**: every history of `M.comap f g`, with its requests mapped by `f`,
  is a history of `M` with its responses mapped by `g` (a forward simulation of hosts: the
  same state, runs and responses);
* **`Server.hists_mapResp`**: the histories of `M.mapResp g` are exactly the histories of `M`
  with their responses mapped by `g`;
* `Server.closed_comap`: reading a closed server through maps reads its handler through them;
* `Server.Refines.mapResp`: reading responses through `g` preserves refinement.
-/

namespace Silmaril.Servers.State

variable {σ Req Resp Req' Resp' : Type}

theorem Server.closed_comap (f : Req → Req') (g : Resp' → Resp) (B : Atomic σ Req' Resp')
    (s₀ : σ) : Server.closed (B.comap f g) s₀ = (Server.closed B s₀).comap f g := rfl

theorem Ev.map_id_id : Ev.map (id : Req → Req) (id : Resp → Resp) = id := by
  funext e; cases e <;> rfl

/-- **The histories of a reduct are mapped histories of the server.** -/
theorem Server.hists_comap {M : Server Req' Resp'} {f : Req → Req'} {g : Resp' → Resp}
    {H : Hist Req Resp} (h : (M.comap f g).Hists H) :
    ∃ H', M.Hists H' ∧ H.map (Ev.map f id) = H'.map (Ev.map id g) :=
  Proofs.Servers.State.Reduct.hists_comap h

/-- **The histories of `M` with responses read through `g`.** -/
theorem Server.hists_mapResp {M : Server Req Resp} {g : Resp → Resp'} {H : Hist Req Resp'} :
    (M.mapResp g).Hists H ↔ ∃ H', M.Hists H' ∧ H = H'.map (Ev.map id g) :=
  Proofs.Servers.State.Reduct.hists_mapResp

theorem Server.Refines.mapResp {M N : Server Req Resp} (h : M.Refines N) (g : Resp → Resp') :
    (M.mapResp g).Refines (N.mapResp g) := fun _ hH =>
  let ⟨H', hM, he⟩ := Server.hists_mapResp.1 hH
  Server.hists_mapResp.2 ⟨H', h H' hM, he⟩

end Silmaril.Servers.State
