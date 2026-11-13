module

public import Silmaril.Proofs.Wasm.Component.Streams.Callback.Sim

/-!
# The generated driver loop in a pipe: refinement and correctness

* `cb_sim`: every step of the module is a step of the pipe's node `1` on the abstract states, or
  leaves the store and the abstract state unchanged (a pass of `$pump` that calls no built-in).
* `creach_abs`: every reachable system of the pipe with the module (`CReach`) stands for a reachable
  system of `Pipes.pipe xs T` (`CSys.abs`), and the module's local invariant holds.
* So the correctness of `Pipes` carries over: `cb_pipe_correct`, `cb_pipe_safe`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event blocked)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Pipes
open Silmaril.Wasm.Component.Streams.Callback
open Silmaril.Proofs.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Live

variable {σ : Type} {T : Tr σ Val Val} {xs : List Val} {batch wmax : Nat}

/-- A step that calls no built-in: the store and the abstract state stay. -/
def Stutter (c : CSys σ) (st' : DStore) (cb' : CB σ) : Prop :=
  st' = c.st ∧ (cb'.abs T : NSt σ) = c.cb.abs T

theorem stutter_flush {c : CSys σ} (h : c.cb.Inv T) (hpd : c.cb.pdrop = false)
    (hwp : c.cb.wpend = false) (hout : c.cb.out = []) (he : c.cb.eof = true)
    (hf : c.cb.flushed = false) (hd : c.cb.dead = false) :
    Stutter (T := T) c c.st { c.cb with flushed := true, out := T.flush c.cb.s } := by
  have hr : c.cb.rdropped = true := by
    cases hr : c.cb.rdropped
    · have := h.i5 he hr hpd
      rw [hd] at this
      cases this
    · rfl
  exact ⟨rfl, abs_flush hout hr hf hd hwp⟩

/-- **One step of the module refines a step of the node, or stutters.** -/
theorem cb_sim {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) (h : c.cb.Inv T)
    (hb : 0 < batch) {st' : DStore} {cb' : CB σ}
    (hs : CBStep T (rh 0) (wh 1) ((pipe xs T).ws 1) batch wmax c.st c.cb st' cb') :
    Stutter (T := T) c st' cb' ∨
      NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st' (cb'.abs T : NSt σ) := by
  cases hs with
  | dropR _ hpd hds => exact Or.inr (sim_dropR h hpd hds)
  | waitW hpc => exact Or.inl ⟨rfl, abs_pc (by simp [hpc]) (by simp)⟩
  | write hpc _ hwp hd hne hds => exact Or.inr (sim_write hR hpc hwp hd hne hds)
  | flush _ hpd hwp hout he hf hd => exact Or.inl (stutter_flush h hpd hwp hout he hf hd)
  | waitEof hpc _ hwp h0 => exact Or.inl ⟨rfl, abs_wait h0 hwp hpc⟩
  | stopEnd _ _ hwp h0 => exact Or.inl ⟨rfl, (abs_stopReading _).trans (abs_reset h0 hwp)⟩
  | dropW hpc _ hwp h0 _ hfd _ hrd hds => exact Or.inr (sim_dropW hpc hwp h0 hfd hrd hds)
  | waitR hpc _ hwp h0 => exact Or.inl ⟨rfl, abs_wait h0 hwp hpc⟩
  | read hpc _ hwp h0 he hrp hds => exact Or.inr (sim_read hR h hb hpc hwp h0 he hrp hds)
  | evIn hpc hw => exact Or.inr (sim_evIn hR h hpc hw)
  | evOut hpc hw => exact Or.inr (sim_evOut hR h hpc hw)

/-! ## The abstract system -/

theorem abs_init : CSys.abs xs T (CSys.init xs T) = init (pipe xs T) := by
  have h1 : (CB.init T).abs T = NSt.init (N1 xs T) := by
    unfold CB.init
    split <;> simp [CB.abs, CB.absOut, CB.fl, CB.stopReading, NSt.init, N1] <;> rfl
  show Sys.mk _ _ = Sys.mk _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => rfl
  | ⟨n + 3, hn⟩ => exact absurd (show n + 3 < 3 from hn) (by omega)

theorem abs_src {c : CSys σ} {st' : DStore} {x' : NSt Unit} :
    CSys.abs xs T { c with st := st', src := x' } =
      ⟨st', Function.update (CSys.abs xs T c).ns 0 x'⟩ := by
  show Sys.mk _ _ = Sys.mk _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => simp; rfl
  | ⟨1, _⟩ => simp; rfl
  | ⟨2, _⟩ => simp; rfl
  | ⟨n + 3, hn⟩ => exact absurd (show n + 3 < 3 from hn) (by omega)

theorem abs_snk {c : CSys σ} {st' : DStore} {x' : NSt Unit} :
    CSys.abs xs T { c with st := st', snk := x' } =
      ⟨st', Function.update (CSys.abs xs T c).ns 2 x'⟩ := by
  show Sys.mk _ _ = Sys.mk _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => simp; rfl
  | ⟨1, _⟩ => simp; rfl
  | ⟨2, _⟩ => simp; rfl
  | ⟨n + 3, hn⟩ => exact absurd (show n + 3 < 3 from hn) (by omega)

theorem abs_cb {c : CSys σ} {st' : DStore} {cb' : CB σ} :
    CSys.abs xs T { c with st := st', cb := cb' } =
      ⟨st', Function.update (CSys.abs xs T c).ns 1 (cb'.abs T : NSt σ)⟩ := by
  show Sys.mk _ _ = Sys.mk _ _
  congr 1
  funext i
  match i with
  | ⟨0, _⟩ => simp; rfl
  | ⟨1, _⟩ => simp; rfl
  | ⟨2, _⟩ => simp; rfl
  | ⟨n + 3, hn⟩ => exact absurd (show n + 3 < 3 from hn) (by omega)

theorem abs_stutter {c : CSys σ} {st' : DStore} {cb' : CB σ} (h : Stutter (T := T) c st' cb') :
    CSys.abs xs T { c with st := st', cb := cb' } = CSys.abs xs T c := by
  rw [abs_cb, h.1, h.2]
  show Sys.mk _ _ = Sys.mk _ _
  congr 1
  funext i
  by_cases hi : i = 1
  · subst hi; simp; rfl
  · exact Function.update_of_ne hi _ _

/-- **Every reachable system with the module stands for a reachable system of the pipe.** -/
theorem creach_abs (hb : 0 < batch) {c : CSys σ} (h : CReach xs T batch wmax c) :
    Reach (pipe xs T) (CSys.abs xs T c) ∧ c.cb.Inv T := by
  induction h with
  | refl => exact ⟨abs_init ▸ Steps.refl _, inv_init T⟩
  | tail _ hs ih =>
    obtain ⟨hR, hI⟩ := ih
    cases hs with
    | src hn => exact ⟨abs_src ▸ Steps.tail hR (Step.node 0 hn), hI⟩
    | snk hn => exact ⟨abs_snk ▸ Steps.tail hR (Step.node 2 hn), hI⟩
    | cb hn =>
      refine ⟨?_, inv_cbstep hI hn⟩
      rcases cb_sim hR hI hb hn with hst | hst
      · rw [abs_stutter hst]; exact hR
      · rw [abs_cb]; exact Steps.tail hR (Step.node 1 hst)

end Silmaril.Proofs.Wasm.Component.Streams.Callback
