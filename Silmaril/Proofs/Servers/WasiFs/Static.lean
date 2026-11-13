module

public import Silmaril.Servers.WasiFs.Static.Defs
public import Silmaril.Servers.State.SharedFs.Defs

@[expose] public section

/-!
# Proofs: the static file server as a `wasi:http` component, given `Task.staticRuns`

* `staticAbs`: over files nobody else edits, the abstraction onto the static file server's
  step (the files never change);
* `sharedAbs`: over files that others change keeping `I`, onto `staticSafe (docRoot root) I`.
-/

namespace Silmaril.Proofs.Servers.WasiFs.Static

open Silmaril.Servers.State Silmaril.Servers.State.OwnedFs Silmaril.Servers.State.SharedFs
open Silmaril.Servers.WasiFs
open Silmaril.Net.Http (Request Response Target)
open Silmaril.Cli (Fs FPath)

theorem handler_of {root : String} (ht : Task.staticRuns root) {fs : Fs} (hs : Small fs)
    (hr : RootDir root fs) {q : Request} {resp : Response} {fs' : Fs}
    (h : staticHandler root fs q resp fs') :
    resp = staticAnswer (docRoot root) fs q ∧ fs' = fs := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨r1, r2⟩ := ht fs q hs hr
  rw [h1] at r1
  exact ⟨Option.some.inj r1, h2.trans r2⟩

/-- Over files nobody else edits: the stateless specification. -/
def staticAbs {root : String} (ht : Task.staticRuns root) {fs₀ : Fs} (h₀ : Small fs₀)
    (hr : RootDir root fs₀) :
    Abstraction (wasiStatic root fs₀) (Atomic.ofFun (staticStep (docRoot root))) fs₀ where
  inv fs := fs = fs₀
  α := id
  inv_init := rfl
  α_init := rfl
  inv_handler (s : Fs) q resp (s' : Fs) hs h := by
    subst hs; exact (handler_of ht h₀ hr h).2
  inv_env _ _ _ h := h.elim
  sim (s : Fs) q resp (s' : Fs) hs h := by
    subst hs
    obtain ⟨h1, h2⟩ := handler_of ht h₀ hr h
    show staticStep (docRoot root) s q = (resp, s')
    rw [h1, h2]; rfl
  env_hidden _ _ _ h := h.elim

/-- Over files that others change keeping `I`: the safety specification. -/
def sharedAbs {root : String} (ht : Task.staticRuns root) {fs₀ : Fs} {E : Fs → Fs → Prop}
    {I : Fs → Prop} (hI : ∀ fs, I fs → Small fs ∧ RootDir root fs) (h₀ : I fs₀)
    (hE : Keeps E I) :
    Abstraction (wasiStaticShared root fs₀ E) (staticSafe (docRoot root) I) () where
  inv := I
  α _ := ()
  inv_init := h₀
  α_init := rfl
  inv_handler (s : Fs) q resp (s' : Fs) hs h := by
    rw [(handler_of ht (hI s hs).1 (hI s hs).2 h).2]; exact hs
  inv_env := hE
  sim (s : Fs) q resp (s' : Fs) hs h := ⟨s, hs, (handler_of ht (hI s hs).1 (hI s hs).2 h).1⟩
  env_hidden _ _ _ _ := rfl

end Silmaril.Proofs.Servers.WasiFs.Static
