module

public import Silmaril.Wasm.JcoTool.KChain.Defs
public import Silmaril.Wasm.JcoTool.KGame.Thms
public import Silmaril.Wasm.Component.Streams.Laws.Thms

/-!
# Chains of generated modules of any length finish with the stream game's outcome

`KGame.kchain2_game` and `kchain2_equiv` are about chains of two generated modules. Here the
chain `source → genD k₀ → genD k₁ → … → genD kₙ → sink` has any nonempty list of kernels:

* `trsN_run`: the composite `trsN k ks` runs the kernels in order (`KDrop.runs`);
* `trsN_congr`: kernels pairwise equivalent give equivalent composites;
* `plugN_realizes`: realisations of the kernels in the stream game plug (`Algebra.seq`, left to
  right) to a realisation of the composite;
* **`kchainN_game`**: once the sink of a chain of generated modules has dropped its input, it holds
  the composite's run on the input, which is the outcome of the pipe network of the composite
  (`NetSem.pipeOut`), and the plug of the realisations realises the composite;
* **`kchainN_equiv`**: **equivalent kernels give equivalent compositions**, for chains of any
  length: the plugs are `CompEquiv`, and two finished chains of generated modules hold the same
  output.

What is assumed: as in `KGame`, the realisations `StreamGame.Realizes C c (trV k)` are hypotheses
(the realise part's `κ`, `VSem`).
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KChain

open Silmaril.Wasm.Component
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.NetSem
open Silmaril.Wasm.Component.Streams.Kernel (KM)
open Silmaril.Wasm.JcoTool.KCore (trV)
open Silmaril.Wasm.JcoTool.KDrop (KReach KSys runs)

/-- The composite runs the kernels in order. -/
theorem trsN_run (k : KM) (ks : List KM) (xs : List Val) :
    (trsN k ks).2.run xs = runs (k :: ks) xs := by
  induction ks generalizing k xs with
  | nil => rfl
  | cons k' ks ih =>
    show ((trV k).comp (trsN k' ks).2).run xs = runs (k :: k' :: ks) xs
    rw [Tr.run_comp', ih]
    rfl

/-- Pairwise equivalent kernels give equivalent composites. -/
theorem trsN_congr {k k' : KM} {ks ks' : List KM}
    (h : List.Forall₂ (fun a b => (trV a).Equiv (trV b)) (k :: ks) (k' :: ks')) :
    (trsN k ks).2.Equiv (trsN k' ks').2 := by
  induction ks generalizing k k' ks' with
  | nil =>
    cases ks' with
    | nil => exact (List.forall₂_cons.1 h).1
    | cons _ _ => cases (List.forall₂_cons.1 h).2
  | cons a ks ih =>
    cases ks' with
    | nil => cases (List.forall₂_cons.1 h).2
    | cons b ks' =>
      obtain ⟨h₀, h₁⟩ := List.forall₂_cons.1 h
      exact Tr.comp_congr h₀ (ih h₁)

variable {M : Type} [CoreModule M] {C : CoreSem M}

/-- **Realisations plug to a realisation of the composite.** -/
theorem plugN_realizes (p : Comp M × KM) (ps : List (Comp M × KM))
    (hr : ∀ q ∈ p :: ps, Algebra.StreamGame.Realizes C q.1 (trV q.2)) :
    Algebra.StreamGame.Realizes C (plugN p ps) (trN p ps).2 := by
  induction ps generalizing p with
  | nil => exact hr p (List.mem_singleton_self p)
  | cons q ps ih =>
    have hq : Algebra.StreamGame.Realizes C (plugN q ps) (trN q ps).2 :=
      ih q fun r hm => hr r (List.mem_cons_of_mem p hm)
    exact (NetGame.chain_realizes (hr p List.mem_cons_self) hq).1

omit [CoreModule M] in
theorem kernels_length (p : Comp M × KM) (ps : List (Comp M × KM)) :
    (kernels p ps).length = ps.length + 1 := by
  simp [kernels]

/-- **A chain of generated modules of any length finishes with the stream game's outcome** of
the composite, and the plug of realisations of its kernels realises the composite. -/
theorem kchainN_game {p : Comp M × KM} {ps : List (Comp M × KM)} {xs : List Val}
    {Nb : Nat → Nat} (hr : ∀ q ∈ p :: ps, Algebra.StreamGame.Realizes C q.1 (trV q.2))
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ps.length + 1 < 2 ^ 26)
    {m : KSys (kernels p ps).length} (h : KReach xs (kernels p ps) Nb m) {b : Bool}
    (hb : m.snk.rd = .gone b) :
    Algebra.StreamGame.Realizes C (plugN p ps) (trN p ps).2 ∧
      m.snk.got = (trN p ps).2.run xs ∧ pipeOut xs (trN p ps).2 m.snk.got := by
  have hg : m.snk.got = (trN p ps).2.run xs := by
    rw [KDrop.kchain_correct hN (by rw [kernels_length]; exact hws) h hb, trN, trsN_run]
    rfl
  exact ⟨plugN_realizes p ps hr, hg, (pipeOut_iff xs _ _).2 hg⟩

/-- **Equivalent kernels compose to equivalent components, for chains of any length**, and
finished chains of their generated modules hold the same output. -/
theorem kchainN_equiv {p p' : Comp M × KM} {ps ps' : List (Comp M × KM)} {xs : List Val}
    {Nb Nb' : Nat → Nat} (hr : ∀ q ∈ p :: ps, Algebra.StreamGame.Realizes C q.1 (trV q.2))
    (hr' : ∀ q ∈ p' :: ps', Algebra.StreamGame.Realizes C q.1 (trV q.2))
    (he : List.Forall₂ (fun q q' => (trV q.2).Equiv (trV q'.2)) (p :: ps) (p' :: ps'))
    (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hN' : ∀ i, 0 < Nb' i ∧ Nb' i ≤ 256)
    (hws : ps.length + 1 < 2 ^ 26) (hws' : ps'.length + 1 < 2 ^ 26)
    {m : KSys (kernels p ps).length} {m' : KSys (kernels p' ps').length}
    (h : KReach xs (kernels p ps) Nb m) (h' : KReach xs (kernels p' ps') Nb' m') {b b' : Bool}
    (hb : m.snk.rd = .gone b) (hb' : m'.snk.rd = .gone b') :
    Algebra.CompEquiv C (plugN p ps) (plugN p' ps') ∧ m.snk.got = m'.snk.got := by
  have hk : List.Forall₂ (fun a b => (trV a).Equiv (trV b)) (kernels p ps) (kernels p' ps') := by
    simp only [kernels]
    refine List.forall₂_cons.2 ⟨(List.forall₂_cons.1 he).1, ?_⟩
    exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (List.forall₂_cons.1 he).2)
  have hT : (trN p ps).2.Equiv (trN p' ps').2 := trsN_congr hk
  obtain ⟨-, g, -⟩ := kchainN_game hr hN hws h hb
  obtain ⟨-, g', -⟩ := kchainN_game hr' hN' hws' h' hb'
  refine ⟨NetSem.VSem.Realizes.equiv (NetGame.game C) (plugN_realizes p ps hr)
    (plugN_realizes p' ps' hr') hT, ?_⟩
  rw [g, g', (hT xs).2]

end Silmaril.Wasm.JcoTool.KChain
