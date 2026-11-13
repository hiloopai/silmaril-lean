module

public import Silmaril.Http.State.OwnedFs.Defs
public import Silmaril.Http.State.Thms

@[expose] public section

/-!
# Proofs: servers over a file system that they alone edit

* `view_set`, **`fileStoreStep_view`**: for an injective layout, a step of the file-backed
  store is a step of `storeStep` on the store the files hold;
* `fileStoreStep_frame`: a step writes only files of keys;
* `fileStoreAbs`, `staticAbs`: the abstractions onto the component-state store and onto the
  stateless static specification;
* `docRoot_safe`: a document root names files under its preopen, without `..`.
-/

namespace Silmaril.Proofs.Http.State.OwnedFs

open Silmaril.Http.State Silmaril.Http.State.OwnedFs Silmaril.Http.State.Component
open Silmaril.Net.Http Silmaril.Cli

theorem view_set {enc : Target → FPath} (hinj : Function.Injective enc) (fs : Fs) (t : Target)
    (v : Option (List UInt8)) : view enc (fs.set (enc t) v) = (view enc fs).update t v := by
  funext t'
  by_cases h : t' = t
  · subst h; simp [view, Fs.set, Store.update]
  · simp [view, Fs.set, Store.update, h, hinj.ne h]

@[simp] theorem view_apply (enc : Target → FPath) (fs : Fs) (t : Target) :
    view enc fs t = fs (enc t) := rfl

theorem fileStoreStep_view {enc : Target → FPath} (hinj : Function.Injective enc) (fs : Fs)
    (r : Request) :
    storeStep (view enc fs) r = ((fileStoreStep enc fs r).1, view enc (fileStoreStep enc fs r).2) := by
  cases hm : r.method <;> cases hf : fs (enc r.target) <;>
    simp [storeStep, fileStoreStep, hm, hf, view_set hinj, Store.get, getAnswer]

theorem fileStoreStep_frame (enc : Target → FPath) (fs : Fs) (r : Request) (p : FPath)
    (hp : ∀ t, enc t ≠ p) : (fileStoreStep enc fs r).2 p = fs p := by
  cases hm : r.method <;> cases hf : fs (enc r.target) <;>
    simp [fileStoreStep, hm, hf, Fs.set, Ne.symm (hp r.target)]

/-- The file-backed store as the component-state store. -/
def fileStoreAbs {enc : Target → FPath} (hinj : Function.Injective enc) (fs₀ : Fs) :
    Abstraction (fileStore enc fs₀) kv (view enc fs₀) where
  inv := Frame enc fs₀
  α := view enc
  inv_init _ _ := rfl
  α_init := rfl
  inv_handler (s : Fs) r resp (s' : Fs) hF h p hp := by
    have h' : fileStoreStep enc s r = (resp, s') := h
    have h2 := congrArg Prod.snd h'
    simp only at h2
    rw [← h2, fileStoreStep_frame enc s r p hp]; exact hF p hp
  inv_env _ _ _ h := h.elim
  sim (s : Fs) r resp (s' : Fs) _ h := by
    have h' : fileStoreStep enc s r = (resp, s') := h
    show storeStep (view enc s) r = (resp, view enc s')
    rw [fileStoreStep_view hinj, h']
  env_hidden _ _ _ h := h.elim

/-- The static file server as the stateless server that answers from `fs₀`. -/
def staticAbs (loc : Target → Option FPath) (fs₀ : Fs) :
    Abstraction (staticServer loc fs₀) (staticSpec loc fs₀) () where
  inv s := s = fs₀
  α _ := ()
  inv_init := rfl
  α_init := rfl
  inv_handler (s : Fs) r resp (s' : Fs) hs h := by
    have h' : (staticAnswer loc s r, s) = (resp, s') := h
    obtain ⟨-, rfl⟩ := Prod.mk.inj h'
    exact hs
  inv_env _ _ _ h := h.elim
  sim (s : Fs) r resp (s' : Fs) hs h := by
    have h' : (staticAnswer loc s r, s) = (resp, s') := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h'
    show staticAnswer loc s r = staticAnswer loc fs₀ r
    rw [hs]
  env_hidden _ _ _ h := h.elim

theorem docRoot_safe {root : String} {t : Target} {p : FPath} (h : docRoot root t = some p) :
    p.root = root ∧ ".." ∉ p.rel := by
  unfold docRoot at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, by assumption⟩

end Silmaril.Proofs.Http.State.OwnedFs
