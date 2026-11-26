module

public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SQLite.TrackA.Read.Adapter
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Coalgebra Node)

private def finish {Backing : Type} (call : SeekCall) (acquired : PageRead.Outcome Backing) :
    Read.Outcome Backing :=
  let returned := call.resume ⟨acquired.result, acquired.cache⟩
  ⟨returned.1, acquired.file, returned.2, acquired.trace⟩

private theorem localReturn {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (call : SeekCall) (result : Except PageRead.FillError Bytes)
    (layer : (lower call cache).unfold none = .ret (call.resume ⟨result, cache⟩)) :
    let out := finish call (⟨result, file, cache, []⟩ : PageRead.Outcome Backing)
    Returns (lower call cache) (handleVfs backing) file out ∧ Observes (lower call cache) out := by
  constructor
  · refine ⟨none, .refl, ?_⟩
    simp only [Coalgebra.handle, layer]
    rfl
  · exact ⟨none, none, .nil _, .refl, layer⟩

private theorem lower_execution {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (call : SeekCall) :
    let out := finish call (PageRead.Acquire.acquire backing file cache
      call.request.target call.request.page)
    Returns (lower call cache) (handleVfs backing) file out ∧ Observes (lower call cache) out := by
  let target := call.request.target
  let page := call.request.page
  dsimp only
  cases hit : PageRead.CacheHit.lookup cache call.request.target call.request.page with
  | some bytes =>
    rw [PageRead.Acquire.acquire_hit backing file cache target page hit]
    apply localReturn
    simp [lower, hit]
  | none =>
    rw [PageRead.Acquire.acquire_miss backing file cache target page hit]
    cases slot : cache call.request.target with
    | none =>
      rw [show PageRead.fill backing file cache target page =
        ⟨.error .unavailableSlot, file, cache, []⟩ by simp [PageRead.fill, target, slot]]
      apply localReturn
      simp [lower, hit, slot]
    | some contents =>
      cases contents with
      | resident other bytes =>
        rw [show PageRead.fill backing file cache target page =
          ⟨.error .unavailableSlot, file, cache, []⟩ by simp [PageRead.fill, target, slot]]
        apply localReturn
        simp [lower, hit, slot]
      | vacant =>
        by_cases admitted : call.request.page.Admitted
        · let reply := (backing file page.request).1
          let after := (backing file page.request).2
          let accepted := PageRead.accept page.size reply
          let updated := match accepted with
            | .ok bytes => cache.install target page bytes
            | .error _ => cache
          have layer : (lower call cache).unfold none = .vis page.request some := by
            simp [lower, hit, slot, admitted]
            rfl
          rw [show PageRead.fill backing file cache target page =
            ⟨accepted, after, updated, [⟨page.request, reply⟩]⟩ by
              simp [PageRead.fill, target, page, slot, admitted, reply, after, accepted, updated]
              rfl]
          constructor
          · let interpreted := (lower call cache).unfold.handle (T := VfsSignature) (handleVfs backing)
            have step : interpreted (none, file, []) = .tau (some reply, after, [⟨page.request, reply⟩]) := by
              simp [interpreted, Coalgebra.handle, layer, handleVfs, reply, after]
              rfl
            exact ⟨some reply, .single (.inl (.tau step)), rfl⟩
          · exact ⟨some reply, some reply, .cons ⟨none, .refl, .vis layer reply⟩ (.nil _), .refl, rfl⟩
        · rw [show PageRead.fill backing file cache target page =
            ⟨.error .invalidPage, file, cache, []⟩ by simp [PageRead.fill, target, page, slot, admitted]]
          apply localReturn
          simp [lower, hit, slot, admitted]

theorem lowered_observations_eq (request : Acquire) (key : Int64) (cache : PageRead.Cache) :
    (lower (stagedCall request key) cache).observes = (lower (vmCall request key) cache).observes := by
  have leaf : (fun view => Read.seekLeaf view request.page.number key) =
      fun view => Read.runLeaf view request.page.number key :=
    funext fun view => Read.seekLeaf_eq_runLeaf view request.page.number key
  simp only [stagedCall, vmCall, leaf]

theorem interpretations_agree {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (request : Acquire) (key : Int64) :
    let out := Read.runStaged backing file cache request.target request.page key
    Returns (pagerTree (stagedCall request key)) (handlePager backing cache) file out ∧
      Returns (lower (vmCall request key) cache) (handleVfs backing) file out ∧
      Trace.Valid backing file out.exchanges out.file ∧
      Observes (lower (vmCall request key) cache) out := by
  let acquired := PageRead.Acquire.acquire backing file cache request.target request.page
  let reply : Acquired := ⟨acquired.result, acquired.cache⟩
  refine ⟨⟨some reply, .single (.inl (.tau rfl)), rfl⟩, ?_⟩
  rw [Read.staged_eq_composed]
  exact ⟨(lower_execution backing file cache (vmCall request key)).1,
    Read.composed_trace backing file cache request.target request.page key,
    (lower_execution backing file cache (vmCall request key)).2⟩

end Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter
