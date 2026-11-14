module

public import Silmaril.Servers.Examples.Dice.Defs
public import Silmaril.Servers.Hosts.Thms
import Silmaril.Proofs.Servers.Examples.Dice.Basic

/-!
# Example: a dice server over a random host — theorems

* **Must, for every host** (`dice_sat`, `dice_mustAll`): with six faces, every observation of
  the server under every stateful host (pure, oracle, seeded or chaotic) meets the
  specification; so does every subset of hosts, for example a seeded family
  (`dice_mustAll_seeded`), and the per-request reading (`perRequest_sat`).
* **May** (`dice_maySome_six`): some host lets `/roll` answer `6`; under the zero host no run
  does (`zero_not_maySix`). "May roll 6" is a property of a set of hosts, not of one run.
* **The planted bug**: with seven faces the must property fails (`buggy_not_mustAll`, witness:
  the host that draws `6`), yet it holds under the zero host (`buggy_mustAll_zero`). A run under
  `zero` passing its checks is therefore no evidence for the general property; a failing run
  under a host of the quantified set refutes it (`Hosts.not_mustAll_of_witness`).
* **A fresh instance per request** (`perRequest_roll_const`): every `/roll` is answered with the
  face of the host's first draw from its initial state, which is what the runtime harness
  observes of `wasmtime serve`.
-/

@[expose] public section

namespace Silmaril.Servers.Examples.Dice

open Silmaril.Servers Silmaril.Servers.Hosts Silmaril.Servers.Observe
open Silmaril.Net.Http (Request Response)
open Silmaril.Proofs.Servers.Examples.Dice (server_sat_atomic one one_mem)

/-- **For every host, the six-faced dice server meets its specification.** -/
theorem dice_sat {σ : Type} (h : Stateful σ Unit UInt64) : (server 6 h).Sat spec :=
  server_sat_atomic _ _ fun _ _ _ _ hm => Proofs.Servers.Examples.Dice.machine_ok h hm

theorem dice_mustAll (σ : Type) : MustAll Set.univ (openDice 6 σ) (Obs.sen spec) :=
  fun h _ => (Beh.must_ofModel_iff _ _).2 (dice_sat h)

theorem dice_mustAll_seeded {S σ : Type} (gen : S → Stateful σ Unit UInt64) :
    MustAll (seeded gen) (openDice 6 σ) (Obs.sen spec) :=
  (dice_mustAll σ).anti (Set.subset_univ _)

theorem perRequest_sat {σ : Type} (h : Stateful σ Unit UInt64) : (perRequest 6 h).Sat spec :=
  server_sat_atomic _ _ fun _ _ _ _ ⟨_, hm⟩ => Proofs.Servers.Examples.Dice.machine_ok h hm

/-- **A fresh instance per request answers every `/roll` alike**: the face of the host's first
draw from its initial state. -/
theorem perRequest_roll_const {σ : Type} (h : Stateful σ Unit UInt64) :
    (perRequest 6 h).Sat (Sen.atomic (A := Http.sig) fun (r : Request) (s : Response) =>
      r.target.pathWithQuery = rollPath → s = rollResp (face 6 (h.step h.init ()).1)) :=
  server_sat_atomic _ _ fun _ _ _ _ hs hp => Proofs.Servers.Examples.Dice.perRequest_roll h hp hs

/-- **Some host lets `/roll` answer `6`** (the host drawing `5`). -/
theorem dice_maySome_six : MaySome Set.univ (openDice 6 Unit) rollsSix :=
  ⟨constHost 5, trivial, .run (one (getReq rollPath) (rollResp 6)),
    ⟨_, rfl, one_mem (q₁ := ()) ⟨rfl, rfl⟩⟩, ⟨⟨0, 0⟩, by simp [one, Trace.seq], by simp [one, Trace.seq]⟩⟩

/-- **Under the zero host, no run answers `/roll` with `6`.** -/
theorem zero_not_maySix : ¬ (openDice 6 Unit zeroHost).May rollsSix :=
  Proofs.Servers.Examples.Dice.zero_not_maySix

/-- **The seven-faced variant fails the must property** under the host drawing `6`. -/
theorem buggy_not_mustAll : ¬ MustAll Set.univ (openDice 7 Unit) (Obs.sen spec) :=
  Proofs.Servers.Examples.Dice.buggy_not_mustAll

/-- **Yet it passes under the zero host.** -/
theorem buggy_mustAll_zero : MustAll {zeroHost} (openDice 7 Unit) (Obs.sen spec) :=
  Proofs.Servers.Examples.Dice.buggy_mustAll_zero

end Silmaril.Servers.Examples.Dice
