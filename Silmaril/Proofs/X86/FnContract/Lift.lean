module

public import Silmaril.X86.FnContract.Defs
public import Silmaril.X86.Extends.Thms

/-!
# Function contracts: refinement, frames, stack slots and transfer along extensions

Proofs behind `Silmaril.X86.FnContract.Thms`. `total_lift`: a total spec on `I` is total on
every extension `J` of `I`, read through the extension's view.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.FnContract

open Silmaril.X86 (State Word sysv64)
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.FnContract
open Silmaril.Process (Memory)

variable {σ τ : Type} {I : Isa σ}

theorem rsp_ne {a b : Word} (h : b = a + 8#64) : b ≠ a := by
  subst h; intro e; bv_omega

theorem total_mono {S T : Spec σ} (h : S.Total I) (hs : S.Sub T) : T.Total I := by
  intro s hl ha he
  obtain ⟨t, hr, res⟩ := h s hl ha (hs.entry s he)
  exact ⟨t, hr, res.silent, res.abi,
    res.frame.mono (fun a ha' => hs.footprint s a he ha'), hs.post s t he res.post⟩

theorem total_frame {S : Spec σ} (h : S.Total I) {F : Memory → Prop}
    (hF : ∀ s, Stable (S.footprint s) F) :
    Spec.Total I ⟨fun s => S.entry s ∧ F (I.mem s), S.footprint,
      fun s t => S.post s t ∧ F (I.mem t)⟩ := by
  intro s hl ha he
  obtain ⟨t, hr, res⟩ := h s hl ha he.1
  exact ⟨t, hr, res.silent, res.abi, res.frame, res.post, hF s _ _ res.frame he.2⟩

theorem retOf_of_readBytes {core : State} {memory : Memory} {x : Word}
    (h : memory.readBytes (core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [x])) :
    retOf core memory = x := by
  simp [retOf, h, Silmaril.X86.wordOfBytes?_encodeWords]

theorem total_lift {J : Isa τ} (E : I.Extends J) {S : Spec σ} (h : S.Total I) :
    (S.comap E.view).Total J := by
  intro x hl ha he
  rw [E.core, E.mem] at ha
  obtain ⟨t, hr, res⟩ := h (E.view x) (E.live x hl) ha he
  refine ⟨E.put x t, E.reaches hr, ?_, ?_, ?_, ?_⟩
  · rw [E.upd, E.core, E.mem, E.view_put, res.silent]
  · rw [E.core, E.mem, E.core, E.view_put]; exact res.abi
  · rw [E.mem, E.mem, E.view_put]; exact res.frame
  · show S.post (E.view x) (E.view (E.put x t)); rw [E.view_put]; exact res.post

end Silmaril.Proofs.X86.FnContract
