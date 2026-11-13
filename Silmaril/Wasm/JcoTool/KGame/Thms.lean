module

public import Silmaril.Wasm.JcoTool.KDrop.Thms
public import Silmaril.Wasm.JcoTool.KNet.Thms
public import Silmaril.Wasm.Component.Streams.NetGame.Thms
public import Silmaril.Wasm.Component.Streams.Cancel.Thms

/-!
# Generated modules in the stream game

The chains and tees of generated modules (`KDrop.kchain`, `KNet.ktee`), run over the Component
Model's drop behaviour, finish with the outcome that the stream game (`Algebra.StreamGame.den`,
as the network semantics `NetGame.game`) assigns to their transformers:

* `kchain2_game`: the sink of `source → genD k₁ → genD k₂ → sink` holds an outcome of the chain
  network of `trV k₁` and `trV k₂` (`NetSem.chainOut`), which is the outcome of the pipe of the
  composite (`pipeOut`); and for any components realising `trV k₁` and `trV k₂` in the stream
  game, their plug `Algebra.seq` realises the composite.
* `kchain2_equiv`: **equivalent kernels give equivalent compositions**: if `trV k₁ ≈ trV k₁'` and
  `trV k₂ ≈ trV k₂'`, the plugs of their realisations are `CompEquiv`, and the two chains of
  generated modules finish with the same output.
* `ktee_game`: the two sinks of a tee of generated modules hold the outcome of the tee network of
  `trV k₁` and `trV k₂` (`NetSem.teeOut`).
* `mreach_good`: every store a network of generated modules reaches has no zero-length buffer,
  so `Streams.Cancel.cstep` answers every built-in call of the run as `Drop.dstep` does
  (`Cancel.dstep_cstep`): the theorems hold in the model with cancellation and zero-length
  copies too.

What is assumed: the realisations (`StreamGame.Realizes C c (trV k)`) are hypotheses; that the
core module of `genD k N` realises `trV k` in the Core 3.0 semantics is the realise part's open
item (`κ`, `VSem`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KGame

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.NetSem
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KDrop (KReach KSys runs)
open Silmaril.Wasm.JcoTool.KNet (MNet MSys MReach ktee)

variable {M : Type} [CoreModule M] {C : CoreSem M}

theorem runs_two (k₁ k₂ : KM) (xs : List Val) : runs [k₁, k₂] xs = (trV k₂).run ((trV k₁).run xs) :=
  rfl

/-- **A chain of two generated modules finishes with the stream game's outcome** of the
composite, and realisations of the kernels plug to a realisation of the composite. -/
theorem kchain2_game {c d : Comp M} {xs : List Val} {k₁ k₂ : KM} {Nb : Nat → Nat}
    (hc : Algebra.StreamGame.Realizes C c (trV k₁)) (hd : Algebra.StreamGame.Realizes C d (trV k₂))
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) {m : KSys [k₁, k₂].length} (h : KReach xs [k₁, k₂] Nb m)
    {b : Bool} (hb : m.snk.rd = .gone b) :
    Algebra.StreamGame.Realizes C (Algebra.seq c d) ((trV k₁).comp (trV k₂)) ∧
      chainOut xs (trV k₁) (trV k₂) m.snk.got ∧ pipeOut xs ((trV k₁).comp (trV k₂)) m.snk.got := by
  have hg : m.snk.got = (trV k₂).run ((trV k₁).run xs) :=
    (KDrop.kchain_correct hN (by simp) h hb).trans (runs_two k₁ k₂ xs)
  have hch : chainOut xs (trV k₁) (trV k₂) m.snk.got := (chainOut_iff xs _ _ _).2 hg
  obtain ⟨hr, he⟩ := NetGame.chain_realizes (C := C) hc hd
  exact ⟨hr, hch, he xs ▸ hch⟩

/-- **Equivalent kernels compose to equivalent components**, and chains of their generated
modules finish with the same output. -/
theorem kchain2_equiv {c c' d d' : Comp M} {xs : List Val} {k₁ k₁' k₂ k₂' : KM}
    {Nb Nb' : Nat → Nat} (hc : Algebra.StreamGame.Realizes C c (trV k₁))
    (hc' : Algebra.StreamGame.Realizes C c' (trV k₁')) (hd : Algebra.StreamGame.Realizes C d (trV k₂))
    (hd' : Algebra.StreamGame.Realizes C d' (trV k₂')) (h₁ : (trV k₁).Equiv (trV k₁'))
    (h₂ : (trV k₂).Equiv (trV k₂')) (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256)
    (hN' : ∀ i, 0 < Nb' i ∧ Nb' i ≤ 256) {m : KSys [k₁, k₂].length} {m' : KSys [k₁', k₂'].length}
    (h : KReach xs [k₁, k₂] Nb m) (h' : KReach xs [k₁', k₂'] Nb' m') {b b' : Bool}
    (hb : m.snk.rd = .gone b) (hb' : m'.snk.rd = .gone b') :
    Algebra.CompEquiv C (Algebra.seq c d) (Algebra.seq c' d') ∧ m.snk.got = m'.snk.got := by
  obtain ⟨heq, hout⟩ := NetGame.equiv_compose (C := C) hc hc' hd hd' h₁ h₂
  have h1 : chainOut xs (trV k₁) (trV k₂) m.snk.got := (kchain2_game hc hd hN h hb).2.1
  have h2 : chainOut xs (trV k₁') (trV k₂') m'.snk.got := (kchain2_game hc' hd' hN' h' hb').2.1
  rw [← hout xs] at h2
  exact ⟨heq, ((chainOut_iff xs _ _ _).1 h1).trans ((chainOut_iff xs _ _ _).1 h2).symm⟩

/-- **A tee of generated modules finishes with the stream game's outcome** of the tee network. -/
theorem ktee_game {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (ktee xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) {b₁ b₂ : Bool}
    (hb₁ : (m.ns (4 : Fin 6)).rd = .gone b₁) (hb₂ : (m.ns (5 : Fin 6)).rd = .gone b₂) :
    teeOut xs (trV k₁) (trV k₂) ((m.ns (4 : Fin 6)).got, (m.ns (5 : Fin 6)).got) := by
  obtain ⟨c₁, c₂⟩ := KNet.ktee_correct h₁ h₂ h
  rw [c₁ b₁ hb₁, c₂ b₂ hb₂]
  exact (teeOut_iff xs _ _ _).2 rfl

/-- **The stores of networks of generated modules have no zero-length buffer**, so the
cancellation model answers every built-in call of their runs as the drop model does. -/
theorem mreach_good {N : MNet} (hN : N.OK) {m : MSys N.net} (h : MReach N m) :
    Cancel.GoodS m.st := by
  obtain ⟨s, hR, hst, -⟩ := KNet.mreach_abs hN h
  exact hst ▸ Cancel.reach_good hR

end Silmaril.Wasm.JcoTool.KGame
