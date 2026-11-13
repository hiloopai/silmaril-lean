module

public import Silmaril.Servers.State.SharedFs.Defs
public import Silmaril.Servers.State.OwnedFs.Thms

@[expose] public section

/-!
# Proofs: servers over shared files

* `staticSafeAbs`, `storeSafeAbs`: abstractions onto the safety specifications;
* `staticAnswer_congr`: the static answer depends only on the file the target names;
* `storeKeysAbs`: with key files untouched, the abstraction onto the component-state store;
* `storeStep_restrict`, `restrict_update_out`: a step on a key of `K` commutes with
  `restrictKeys K`, and an update of another key is invisible to it;
* `storeOnAbs`: with the files of the keys of `K` untouched, the abstraction onto `kvOn K`.
-/

namespace Silmaril.Proofs.Servers.State.SharedFs

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Servers.State.Component Silmaril.Net.Http Silmaril.Cli

/-- The static server over shared files as its safety specification. -/
def staticSafeAbs (loc : Target → Option FPath) {fs₀ : Fs} {E : Fs → Fs → Prop}
    {I : Fs → Prop} (h₀ : I fs₀) (hE : Keeps E I) :
    Abstraction (sharedStatic loc fs₀ E) (staticSafe loc I) () where
  inv := I
  α _ := ()
  inv_init := h₀
  α_init := rfl
  inv_handler (s : Fs) r resp (s' : Fs) hs h := by
    have h' : (staticAnswer loc s r, s) = (resp, s') := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h'
    exact hs
  inv_env := hE
  sim (s : Fs) r resp (s' : Fs) hs h := by
    have h' : (staticAnswer loc s r, s) = (resp, s') := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h'
    exact ⟨s, hs, rfl⟩
  env_hidden _ _ _ _ := rfl

/-- The store over shared files as its safety specification. -/
def storeSafeAbs {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    (E : Fs → Fs → Prop) : Abstraction (sharedStore enc fs₀ E) storeSafe () where
  inv _ := True
  α _ := ()
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ _ := trivial
  sim (s : Fs) r resp (s' : Fs) _ h := by
    have h' : fileStoreStep enc s r = (resp, s') := h
    exact ⟨view enc s, view enc s', by rw [fileStoreStep_view hinj, h']⟩
  env_hidden _ _ _ _ := rfl

theorem staticAnswer_congr (loc : Target → Option FPath) {fs fs' : Fs} (r : Request)
    (h : (loc r.target).bind fs = (loc r.target).bind fs') :
    staticAnswer loc fs r = staticAnswer loc fs' r := by
  unfold staticAnswer; rw [h]

/-- With the key files untouched, the store over shared files as the component-state store. -/
def storeKeysAbs {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    {E : Fs → Fs → Prop} (hE : Untouched E fun p => ∃ t, enc t = p) :
    Abstraction (sharedStore enc fs₀ E) kv (view enc fs₀) where
  inv _ := True
  α := view enc
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ _ := trivial
  sim (s : Fs) r resp (s' : Fs) _ h := by
    have h' : fileStoreStep enc s r = (resp, s') := h
    show storeStep (view enc s) r = (resp, view enc s')
    rw [fileStoreStep_view hinj, h']
  env_hidden (s : Fs) (s' : Fs) _ h := by
    funext t; exact hE s s' h (enc t) ⟨t, rfl⟩

/-! ## Linearizability on the untouched keys -/

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
    simp [storeStep, hm, hf, hS, Store.get, restrict_update_in S hr]

theorem storeStep_restrict_out {K : Target → Prop} [DecidablePred K] (S : Store) {r : Request}
    (hr : ¬ K r.target) : restrictKeys K (storeStep S r).2 = restrictKeys K S := by
  cases hm : r.method <;> cases hf : S r.target <;>
    simp [storeStep, hm, hf, restrict_update_out S hr]

/-- With the files of the keys of `K` untouched, the store over shared files as `kvOn K`. -/
def storeOnAbs {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs)
    (K : Target → Prop) [DecidablePred K] {E : Fs → Fs → Prop}
    (hE : Untouched E fun p => ∃ t, K t ∧ enc t = p) :
    Abstraction (sharedStore enc fs₀ E) (kvOn K) (restrictKeys K (view enc fs₀)) where
  inv _ := True
  α s := restrictKeys K (view enc s)
  inv_init := trivial
  α_init := rfl
  inv_handler _ _ _ _ _ _ := trivial
  inv_env _ _ _ _ := trivial
  sim (s : Fs) r resp (s' : Fs) _ h := by
    have h' : fileStoreStep enc s r = (resp, s') := h
    have hv : storeStep (view enc s) r = (resp, view enc s') := by
      rw [fileStoreStep_view hinj, h']
    refine ⟨fun hK => ?_, fun hK => ⟨⟨_, _, hv⟩, ?_⟩⟩
    · rw [storeStep_restrict _ hK, hv]
    · have := storeStep_restrict_out (view enc s) hK
      rw [hv] at this
      exact this
  env_hidden (s : Fs) (s' : Fs) _ h := by
    funext t
    by_cases hK : K t
    · simp only [restrictKeys, hK, ite_true]
      exact hE s s' h (enc t) ⟨t, hK, rfl⟩
    · simp [restrictKeys, hK]

end Silmaril.Proofs.Servers.State.SharedFs
