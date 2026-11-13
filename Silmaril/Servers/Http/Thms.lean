module

public import Silmaril.Servers.Http.Defs
public import Silmaril.Servers.Core.Thms

/-!
# HTTP interfaces: theorems

* The views `status`, `path` and `final` see every response (`status_resp_surjective`,
  `path_resp_surjective`, `final_resp_surjective`), so linearizability translates along them;
  for example, a server's status codes are linearizable exactly when the server is
  linearizable for the specification read on status codes (`sat_lin_status`).

* The stateless origin of a web is the stateless machine of its answer
  (`Http.machine_ofTargets`), so on well-formed traces its trace sentence is the web's atomic
  sentence (`Http.originSen_ofTargets_iff`), and its atomic-handler server has exactly the
  well-formed traces answering as the web does (`Http.server_ofTargets_tr_iff`).
* The atomic-handler server of an origin satisfies the origin's trace sentence
  (`Http.server_sat_originSen`), in particular the resource store of `Silmaril.Net.Http`
  (`Http.store_sat`).
* A status sentence read at the full interface is about the status of each response
  (`Http.sen_allStatus`).
-/

@[expose] public section

namespace Silmaril.Servers.Http

open Silmaril.Net.Http

theorem machine_ofTargets (W : Origin.Web) :
    machine (Origin.ofTargets W) = Machine.ofRel (A := sig) fun r s => s = Origin.webAnswer W r := by
  funext q r s q'
  cases q; cases q'
  apply propext
  simp only [machine, Origin.ofTargets, Origin.ofFun, Machine.ofRel]
  exact ⟨fun h => (congrArg Prod.fst h).symm, fun h => by rw [h]⟩

/-- **A web's origin is linearizable exactly when every response is the web's answer.** -/
theorem originSen_ofTargets_iff (W : Origin.Web) {t : Trace sig} (hw : Sen.WF t) :
    originSen (Origin.ofTargets W) () t ↔ webSen W t := by
  rw [originSen, machine_ofTargets]
  exact Sen.lin_ofRel_iff _ hw

theorem server_ofTargets_tr_iff (W : Origin.Web) (t : Trace sig) :
    ((machine (Origin.ofTargets W)).server ()).Tr t ↔ Sen.WF t ∧ webSen W t := by
  rw [machine_ofTargets]
  exact Machine.server_ofRel_tr_iff _ t

theorem server_sat_originSen {σ : Type} (O : Origin σ) (s₀ : σ) :
    ((machine O).server s₀).Sat (originSen O s₀) :=
  Machine.server_sat_lin _ _

/-- The atomic-handler server of the resource store is linearizable with respect to it. -/
theorem store_sat (S₀ : Store) : ((machine storeOrigin).server S₀).Sat (originSen storeOrigin S₀) :=
  server_sat_originSen _ _

theorem sen_allStatus (c : Status) :
    status.sen (allStatus c) = Sen.atomic fun (_ : Request) (s : Response) => s.status = c :=
  Hom.sen_atomic (A := statusSig) (B := sig) status _

/-- The coarser HTTP views see every response, so linearizability translates along them
(`Hom.sen_lin`). -/
theorem status_resp_surjective : Function.Surjective (status : Hom statusSig sig).resp :=
  fun c => ⟨Response.simple c [], rfl⟩

theorem path_resp_surjective : Function.Surjective (path : Hom pathSig sig).resp :=
  fun s => ⟨s, rfl⟩

theorem final_resp_surjective : Function.Surjective (final : Hom sig exchSig).resp :=
  fun s => ⟨([], s), rfl⟩

/-- **A server's status codes are linearizable for `S` exactly when the server is linearizable
for `S` read on status codes.** -/
theorem sat_lin_status {M : Model sig} {S : SeqSpec statusSig} :
    M.Sat (Sen.lin (Hom.seq (A := statusSig) (B := sig) status S)) ↔
      (Hom.mod (A := statusSig) (B := sig) status M).Sat (Sen.lin S) :=
  Hom.sat_lin_iff (A := statusSig) (B := sig) status status_resp_surjective

end Silmaril.Servers.Http
