module

public import Silmaril.Proofs.Servers.WasiFs.Mut
public import Silmaril.Proofs.Servers.WasiFs.Put
public import Silmaril.Proofs.Servers.State.OwnedFs

@[expose] public section

/-!
# Proofs: the file-backed store component as a server

* **`run_spec`**: for files shorter than `2^64 - 1` octets, the complete run of `handle` makes
  the response of `specStep` and leaves its files, for every request;
* `specStep_small`, `specStep_frame`: `specStep` keeps the files short and writes only key
  files;
* `storeAbs`: the abstraction of the component's server onto `specStep` (invariant: short
  files, and the files that are not key files as initially);
* `storeSmallAbs`: on short requests, onto `fileStoreStep (keyFile root)` read without header
  fields;
* `storeHost_fsOk`: every read-only filesystem answer of the host passes the check of the
  `FsMore` 0.2 theory over the tree of the files at that point.
-/

namespace Silmaril.Proofs.Servers.WasiFs

open Silmaril.Games Silmaril.Wasi Silmaril.Servers.WasiHttp Silmaril.Servers.WasiExamples
open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.WasiFs
open Silmaril.Servers.Calls
open Silmaril.Wasm.Component (Val)
open Silmaril.Net.Http (Request Response Method Target)
open Silmaril.Cli (Fs FPath)

theorem run_spec (root : String) {fs : Fs} (hs : Small fs) (q : Request) :
    respOf 1 (runStore root fs q) = some (specStep root fs q).1 ∧
      (replay root fs (runStore root fs q)).files = (specStep root fs q).2 := by
  cases hm : q.method with
  | get => exact run_get root fs q false (by simp [hm]) hs
  | head => exact run_get root fs q true (by simp [hm]) hs
  | put => exact run_put root fs q hm
  | delete => exact run_delete root fs q hm
  | options => exact run_other root fs q (by simp [hm, kindOf])
  | post => exact run_other root fs q (by simp [hm, kindOf])
  | connect => exact run_other root fs q (by simp [hm, kindOf])
  | trace => exact run_other root fs q (by simp [hm, kindOf])
  | patch => exact run_other root fs q (by simp [hm, kindOf])
  | other t => exact run_other root fs q (by simp [hm, kindOf])

theorem specStep_small (root : String) {fs : Fs} (hs : Small fs) (q : Request) :
    Small (specStep root fs q).2 := by
  intro p c hp
  unfold specStep at hp
  split at hp
  · exact hs p c hp
  · rename_i hb
    revert hp
    cases hm : q.method <;>
      simp only [fileStoreStep, hm, kindOf] at hb ⊢ <;> try exact hs p c
    · simp only [Silmaril.Cli.Fs.set]
      split
      · intro h; cases h; simpa [maxRead] using hb
      · exact hs p c
    · cases hf : fs (keyFile root q.target) <;> simp only
      · exact hs p c
      · simp only [Silmaril.Cli.Fs.set]
        split
        · intro h; cases h
        · exact hs p c

theorem specStep_frame (root : String) (fs : Fs) (q : Request) (p : FPath)
    (hp : ∀ t, keyFile root t ≠ p) : (specStep root fs q).2 p = fs p := by
  unfold specStep
  split
  · rfl
  · exact Proofs.Servers.State.OwnedFs.fileStoreStep_frame _ fs q p hp

/-- The component's handler, from short files, is `specStep`. -/
theorem handler_spec (root : String) {fs : Fs} (hs : Small fs) {q : Request} {resp : Response}
    {fs' : Fs} (h : storeHandler root fs q resp fs') : specStep root fs q = (resp, fs') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨r1, r2⟩ := run_spec root hs q
  rw [h1] at r1
  cases r1
  rw [h2, r2]

/-- **The store component's server as its specification.** -/
def storeAbs (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    Abstraction (wasiStore root fs₀) (Atomic.ofFun (specStep root)) fs₀ where
  inv fs := Small fs ∧ Frame (keyFile root) fs₀ fs
  α := id
  inv_init := ⟨h₀, fun _ _ => rfl⟩
  α_init := rfl
  inv_handler (s : Fs) q resp (s' : Fs) hs h := by
    have e := handler_spec root hs.1 h
    have e2 := congrArg Prod.snd e
    simp only at e2
    subst e2
    exact ⟨specStep_small root hs.1 q, fun p hp => (specStep_frame root s q p hp).trans (hs.2 p hp)⟩
  inv_env _ _ _ h := h.elim
  sim (s : Fs) q resp (s' : Fs) hs h := handler_spec root hs.1 h
  env_hidden _ _ _ h := h.elim

/-- **On short requests**, the component's server as `fileStore` without header fields. -/
def storeSmallAbs (root : String) {fs₀ : Fs} (h₀ : Small fs₀) :
    Abstraction (wasiStoreSmall root fs₀)
      ((Atomic.ofFun (fileStoreStep (keyFile root))).mapResp noFields |>.guard smallReq) fs₀ where
  inv fs := Small fs ∧ Frame (keyFile root) fs₀ fs
  α := id
  inv_init := ⟨h₀, fun _ _ => rfl⟩
  α_init := rfl
  inv_handler (s : Fs) q resp (s' : Fs) hs h :=
    (storeAbs root h₀).inv_handler s q resp s' hs h.2
  inv_env _ _ _ h := h.elim
  sim (s : Fs) q resp (s' : Fs) hs h := by
    obtain ⟨hq, h⟩ := h
    have e := handler_spec root hs.1 h
    have hb : ¬ (kindOf q.method = .put ∧ maxRead ≤ q.content.length) :=
      fun ⟨_, hb⟩ => absurd hq (by unfold smallReq; omega)
    simp only [specStep, hb, ite_false] at e
    refine ⟨hq, (fileStoreStep (keyFile root) s q).1, ?_, ?_⟩
    · show fileStoreStep (keyFile root) s q = ((fileStoreStep (keyFile root) s q).1, s')
      rw [← (Prod.mk.inj e).2]
    · exact (Prod.mk.inj e).1.symm
  env_hidden _ _ _ h := h.elim

/-- **The read-only filesystem answers of the store's host pass the `FsMore` 0.2 checks**
over the tree of the files as they are at that point. -/
theorem storeHost_fsOk (root : String) (q : Request) (fs : Fs) (past : List WEv) (f : FnName)
    (a : List Val) (hf : f ∈ fsList) (hm : mutating f a = false) :
    Versions.FsMore.fsOk Versions.FsMore.v2 (treeOf [root] (replay root fs past).files)
      (Versions.FsMore.fsState Versions.FsMore.v2 (treeOf [root] (replay root fs past).files)
        (fsEvents past))
      (.imp f a (storeHost root q fs past f a)) = true := by
  have h : storeHost root q fs past f a =
      Versions.FsMore.fsImplV Versions.FsMore.v2 (treeOf [root] (replay root fs past).files)
        [root.toList] (fsEvents past) f a := by
    simp [storeHost, hf, hm]
  rw [h]
  exact Versions.FsMore.fsImplV_ok (by decide) _ _ _ _ _

end Silmaril.Proofs.Servers.WasiFs
