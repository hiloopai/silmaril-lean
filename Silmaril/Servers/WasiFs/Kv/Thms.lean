module

public import Silmaril.Servers.WasiFs.Kv.Defs
public import Silmaril.Servers.WasiFs.Thms
public import Silmaril.Servers.State.Reduct.Thms
public import Silmaril.Servers.State.Component.Thms
import Silmaril.Proofs.Servers.WasiFs.Kv

@[expose] public section

/-!
# The file-backed `wasi:http` store as the key-value store: theorems (header)

PROVED (standard axioms), namespace `Silmaril.Servers.WasiFs`. Proofs in
`Silmaril.Proofs.Servers.WasiFs.Kv`.

* **`keyName_injective`**: the file names of the store are injective (`k` and two hexadecimal
  digits per octet, or `n`), so **`keyFile_eq_iff`**: two targets share a file exactly when
  they have the same path-with-query; on targets in origin form the layout is injective
  (`keyFile_injOn`);
* `fileStoreStep_viewN`: a step of the file store through `keyFile root`, seen through
  `viewN root`, is a `storeStep` of the request in origin form;
* **`fileStoreNF_hists`**: the histories of `fileStoreNF` are the histories of the file store
  on short requests with their responses read through `noFields` (`Server.hists_mapResp`);
* **`wasiStoreSmall_refines_kv`**, `wasiStoreSmall_linearizable_kv`: the store component, on
  short requests, refines the closed server of `kvNF` from the store its initial files hold,
  and is linearizable with respect to it;
* **`wasiStoreSmall_kv`**: every history of the store component, with its targets in origin
  form, is a history of the component-state key-value server `kvServer (viewN root fs₀)` of
  state model (a) with its responses read without header fields.
-/

namespace Silmaril.Servers.WasiFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.Component
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

theorem keyName_injective : Function.Injective keyName :=
  Proofs.Servers.WasiFs.Kv.keyName_injective

theorem keyFile_eq_iff (root : String) (t t' : Target) :
    keyFile root t = keyFile root t' ↔ t.pathWithQuery = t'.pathWithQuery :=
  Proofs.Servers.WasiFs.Kv.keyFile_eq_iff root t t'

theorem keyFile_injOn (root : String) {t t' : Target} (ht : originForm t = t)
    (ht' : originForm t' = t') (h : keyFile root t = keyFile root t') : t = t' := by
  rw [← ht, ← ht', originForm, originForm, (keyFile_eq_iff root t t').1 h]

theorem fileStoreStep_viewN (root : String) (fs : Fs) (r : Request) :
    storeStep (viewN root fs) (normReq r) =
      ((fileStoreStep (keyFile root) fs r).1, viewN root (fileStoreStep (keyFile root) fs r).2) :=
  Proofs.Servers.WasiFs.Kv.fileStoreStep_viewN root fs r

theorem fileStoreNF_hists (root : String) (fs₀ : Fs) {H : Hist Request Response} :
    (fileStoreNF root fs₀).Hists H ↔
      ∃ H', (Server.closed ((Atomic.ofFun (fileStoreStep (keyFile root))).guard smallReq) fs₀).Hists H' ∧
        H = H'.map (Ev.map id noFields) := by
  rw [Proofs.Servers.WasiFs.Kv.fileStoreNF_eq]
  exact Server.hists_mapResp

theorem wasiStoreSmall_refines_kv (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStoreSmall root fs₀).Refines (Server.closed kvNF (viewN root fs₀)) :=
  fun H hH => (Proofs.Servers.WasiFs.Kv.fileStoreNFAbs root fs₀).refines H
    (wasiStoreSmall_refines root h₀ H hH)

theorem wasiStoreSmall_linearizable_kv (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    (wasiStoreSmall root fs₀).Sat (Linearizable kvNF (viewN root fs₀)) :=
  (wasiStoreSmall_refines_kv root h₀).sat (closed_linearizable kvNF _)

/-- **The store component is the component-state key-value store** on targets in origin form,
without header fields. -/
theorem wasiStoreSmall_kv (root : String) {fs₀ : Fs} (h₀ : Small fs₀)
    {H : Hist Request Response} (hH : (wasiStoreSmall root fs₀).Hists H) :
    ∃ H', (kvServer (viewN root fs₀)).Hists H' ∧
      H.map (Ev.map normReq id) = H'.map (Ev.map id noFields) := by
  obtain ⟨H', hH', he⟩ := Server.hists_comap (M := Server.closed (kv.guard smallReq) (viewN root fs₀))
    (f := normReq) (g := noFields) (wasiStoreSmall_refines_kv root h₀ H hH)
  exact ⟨H', (Proofs.Servers.WasiFs.Kv.guardAbs kv smallReq (viewN root fs₀)).refines H' hH', he⟩

end Silmaril.Servers.WasiFs
