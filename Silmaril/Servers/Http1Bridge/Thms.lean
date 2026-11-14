module

public import Silmaril.Servers.Http1Bridge.Defs
public import Silmaril.Net.Http1.Institution.Thms
import Silmaril.Proofs.Servers.Http1Bridge.Basic

/-!
# The exchange reading of the HTTP/1.1 institution: theorems

* **Response obligations are trace sentences** (`sat_iff_server_sat`): for every obligation
  with an exchange relation `R` (`respRel M φ = some R`), the model satisfies it in the
  HTTP/1.1 institution iff the implementation's server satisfies the atomic sentence of `R`.
* **The reference server**: for a compliant profile and a well-framed handler, the server of
  the reference implementation of `Silmaril.Net.Http1.Pipeline` sends no content in answer to
  `HEAD` and only well-framed responses, as core trace sentences (`refServer_headNoContent`,
  `refServer_wellFramed`).
* **Refinement of servers transfers response obligations** (`sat_of_refines`): an
  implementation (of any platform) whose server refines the server of a model satisfying a
  response obligation satisfies its trace sentence.
* **Connection obligations are not observed by the exchange reading**
  (`closesOnClTe_not_observable`): the reference implementation and its keep-alive-always
  variant have the same server, yet one closes after `Transfer-Encoding` with `Content-Length`
  (RFC 9112 §6.3) and the other does not.
-/

@[expose] public section

namespace Silmaril.Servers.Http1Bridge

open Silmaril.Servers
open Silmaril.Net.Http1 Silmaril.Net.Http1.Inst

/-- **A response obligation holds iff the server satisfies its atomic trace sentence.** -/
theorem sat_iff_server_sat {A : Inst.Sig} (M : Inst.Model A) {φ : Inst.Sen A}
    {R : RequestHead × Body → ResponseHead × Body → Prop} (h : respRel M φ = some R) :
    Inst.Sat M φ ↔ (implServer M.impl).Sat (Sen.atomic (A := wireSig) R) :=
  (Proofs.Servers.Http1Bridge.sat_iff_forall M φ h).trans
    (Proofs.Servers.Http1Bridge.server_sat_iff M.impl R).symm

/-- A model refining the server of a model with a response obligation satisfies its sentence. -/
theorem sat_of_refines {A : Inst.Sig} (M : Inst.Model A) {φ : Inst.Sen A}
    {R : RequestHead × Body → ResponseHead × Body → Prop} (h : respRel M φ = some R)
    (hM : Inst.Sat M φ) {N : Silmaril.Servers.Model wireSig} (hN : N.Refines (implServer M.impl)) :
    N.Sat (Sen.atomic (A := wireSig) R) :=
  Model.sat_of_refines hN ((sat_iff_server_sat M h).1 hM)

theorem refServer_headNoContent {cfg : ServerConfig} {H : Handler} (hp : cfg.profile.Compliant)
    (hH : Handler.WellFramed H) :
    (implServer (refImpl cfg H)).Sat (Sen.atomic (A := wireSig) fun q p =>
      q.1.line.method = methodHEAD → encBody p.2 = []) :=
  (sat_iff_server_sat (refModel cfg H) (φ := .headNoContent) rfl).1
    ((refModel_vanilla hp hH).2 _ (by simp [rfcCore]))

theorem refServer_wellFramed {cfg : ServerConfig} {H : Handler} (hp : cfg.profile.Compliant)
    (hH : Handler.WellFramed H) :
    (implServer (refImpl cfg H)).Sat (Sen.atomic (A := wireSig) fun q p =>
      p.1.Valid ∧ p.2.Fits (responseBodyLength q.1.line.method p.1.line.code p.1.fields)) :=
  (sat_iff_server_sat (refModel cfg H) (φ := .wellFramed) rfl).1
    ((refModel_vanilla hp hH).2 _ (by simp [rfcCore]))

/-- **Connection obligations are not observed**: two implementations with the same server,
one closing after `Transfer-Encoding` with `Content-Length` and one not. -/
theorem closesOnClTe_not_observable :
    ∃ M N : Inst.Model Std, implServer M.impl = implServer N.impl ∧
      Inst.Sat M .closesOnClTe ∧ ¬ Inst.Sat N .closesOnClTe :=
  ⟨⟨StdMethod.token, StdField.name, StdCoding.name, refImpl {} patchHandler⟩,
    ⟨StdMethod.token, StdField.name, StdCoding.name, keepAlwaysImpl {} patchHandler⟩, rfl,
    patchModel_reduct_vanilla.2 _ (by simp [rfcCore]), keepAlways_violates {} patchHandler⟩

end Silmaril.Servers.Http1Bridge
