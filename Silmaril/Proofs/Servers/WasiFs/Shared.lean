module

public import Silmaril.Servers.WasiFs.Shared.Defs
public import Silmaril.Servers.WasiFs.Kv.Thms

@[expose] public section

/-!
# Proofs: the file-backed `wasi:http` store over shared files

* `handler_spec`: from short files, a run of the component is `specStep`;
* `safeAbs`: the abstraction onto the safety specification (the constant map);
* `restrict_update_in`, `restrict_update_out`, `storeStep_restrict`, `storeStep_restrict_out`:
  the store on the keys of `K` (as in `Silmaril.Proofs.Servers.State.SharedFs`);
* `onAbs`: with the files of the keys of `K` untouched, the abstraction onto `kvOnNF K`.
-/

namespace Silmaril.Proofs.Servers.WasiFs.Shared

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Servers.WasiFs Silmaril.Servers.WasiExamples
open Silmaril.Net.Http (Request Response Target Store storeStep)
open Silmaril.Cli (Fs FPath)

theorem handler_spec (root : String) {fs : Fs} (hs : Small fs) {q : Request} {resp : Response}
    {fs' : Fs} (h : storeHandler root fs q resp fs') : specStep root fs q = (resp, fs') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨r1, r2⟩ := run_spec root hs q
  rw [h1] at r1
  cases r1
  rw [h2, r2]

/-- **Safety**, whatever the environment does (keeping the files short). -/
def safeAbs (root : String) {fs₀ : Fs} {E : Fs → Fs → Prop} (h₀ : Small fs₀)
    (hE : Keeps E Small) : Abstraction (wasiShared root fs₀ E) (safeNF root) () where
  inv := Small
  α _ := ()
  inv_init := h₀
  α_init := rfl
  inv_handler (s : Fs) q resp (s' : Fs) hs h := by
    have e := handler_spec root hs h.2
    have e2 := congrArg Prod.snd e
    simp only at e2
    rw [← e2]; exact specStep_small root hs q
  inv_env := hE
  sim (s : Fs) q resp (s' : Fs) hs h :=
    ⟨s, hs, (congrArg Prod.fst (handler_spec root hs h.2)).symm⟩
  env_hidden _ _ _ _ := rfl

theorem restrict_update_in {K : Target → Prop} [DecidablePred K] (S : Store) {t : Target}
    (ht : K t) (v : Option (List UInt8)) :
    restrictKeys K (S.update t v) = (restrictKeys K S).update t v := by
  funext t'
  by_cases h : t' = t
  · subst h; simp [restrictKeys, Store.update, ht]
  · simp [restrictKeys, Store.update, h]

theorem restrict_update_out {K : Target → Prop} [DecidablePred K] (S : Store) {t : Target}
    (ht : ¬ K t) (v : Option (List UInt8)) :
    restrictKeys K (S.update t v) = restrictKeys K S := by
  funext t'
  by_cases h : t' = t
  · subst h; simp [restrictKeys, ht]
  · simp [restrictKeys, Store.update, h]

theorem storeStep_restrict {K : Target → Prop} [DecidablePred K] (S : Store) {r : Request}
    (hr : K r.target) :
    storeStep (restrictKeys K S) r = ((storeStep S r).1, restrictKeys K (storeStep S r).2) := by
  have hS : restrictKeys K S r.target = S r.target := by simp [restrictKeys, hr]
  cases hm : r.method <;> cases hf : S r.target <;>
    simp [storeStep, hm, hf, hS, Silmaril.Net.Http.Store.get, restrict_update_in S hr]

theorem storeStep_restrict_out {K : Target → Prop} [DecidablePred K] (S : Store) {r : Request}
    (hr : ¬ K r.target) : restrictKeys K (storeStep S r).2 = restrictKeys K S := by
  cases hm : r.method <;> cases hf : S r.target <;>
    simp [storeStep, hm, hf, restrict_update_out S hr]

/-- **The keys of `K` untouched**: the component as `kvOnNF K`. -/
def onAbs (root : String) {fs₀ : Fs} (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (h₀ : Small fs₀) (hE : Keeps E Small) (hU : Untouched E (keyOn root K)) :
    Abstraction (wasiShared root fs₀ E) (kvOnNF K) (restrictKeys K (viewN root fs₀)) where
  inv := Small
  α s := restrictKeys K (viewN root s)
  inv_init := h₀
  α_init := rfl
  inv_handler := (safeAbs root h₀ hE).inv_handler
  inv_env := hE
  sim (s : Fs) q resp (s' : Fs) hs h := by
    have e := handler_spec root hs h.2
    have hb : ¬ (kindOf q.method = .put ∧ maxRead ≤ q.content.length) :=
      fun ⟨_, hb⟩ => absurd h.1 (by unfold smallReq; omega)
    simp only [specStep, hb, ite_false] at e
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    have hv : storeStep (viewN root s) (normReq q) =
        ((fileStoreStep (keyFile root) s q).1, viewN root s') := by
      rw [fileStoreStep_viewN, e2]
    refine ⟨(fileStoreStep (keyFile root) s q).1, ⟨h.1, fun hK => ?_, fun hK => ⟨⟨_, _, hv⟩, ?_⟩⟩,
      e1.symm⟩
    · rw [storeStep_restrict _ hK, hv]
    · have := storeStep_restrict_out (viewN root s) hK
      rw [hv] at this
      exact this
  env_hidden (s : Fs) (s' : Fs) _ h := by
    funext t
    by_cases hK : K t
    · by_cases ho : originForm t = t
      · simp only [restrictKeys, hK, ite_true, viewN, ho]
        exact hU s s' h (keyFile root t) ⟨t, hK, ho, rfl⟩
      · simp [restrictKeys, hK, viewN, ho]
    · simp [restrictKeys, hK]

end Silmaril.Proofs.Servers.WasiFs.Shared
