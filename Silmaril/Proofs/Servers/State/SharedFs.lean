module

public import Silmaril.Servers.State.SharedFs.Defs
public import Silmaril.Servers.State.OwnedFs.Thms

@[expose] public section

/-!
# Proofs: servers over shared files

* `staticSafeAbs`, `storeSafeAbs`: abstractions onto the safety specifications;
* `staticAnswer_congr`: the static answer depends only on the file the target names;
* `storeKeysAbs`: with key files untouched, the abstraction onto the component-state store.
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

end Silmaril.Proofs.Servers.State.SharedFs
