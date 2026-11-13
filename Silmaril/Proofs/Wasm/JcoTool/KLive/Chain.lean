module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Main

/-!
# Chains of any length and tees of generated modules are live

`kchainM_live` and `ktee_live`: the hypotheses of liveness (`MNet.Live`) hold for a chain of
generated modules of any length (`kchainM`, on `KDrop.kchain`) and for a tee whose branches are
generated modules (`KNet.ktee`), given the kernels' bounds. `kchainM_correct`: the sink of a
chain, once it has dropped its input, holds the kernels' composite.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Net (Network NSt Reach Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.Component.Streams.Live (Consistent Setting)

variable {xs : List Val} {ks : List KM} {Nb : Nat → Nat}

theorem kchainM_gen {i : Fin (kchainM xs ks Nb).net.k} {k : KM} {N : Nat}
    (hg : (kchainM xs ks Nb).gen i = some (k, N)) :
    ∃ h : 0 < i.val ∧ i.val ≤ ks.length, k = ks[i.val - 1]'(by omega) ∧ N = Nb (i.val - 1) := by
  simp only [kchainM] at hg
  split at hg
  · rename_i h
    simp only [Option.some.injEq, Prod.mk.injEq] at hg
    exact ⟨h, hg.1.symm, hg.2.symm⟩
  · cases hg

theorem kchainM_node {i : Fin (kchainM xs ks Nb).net.k} (h : 0 < i.val ∧ i.val ≤ ks.length) :
    (kchainM xs ks Nb).net.node i =
      Silmaril.Wasm.JcoTool.KDrop.node (ks[i.val - 1]'(by omega)) (i.val - 1) i.val := by
  have h0 : i.val ≠ 0 := by omega
  have hl : i.val ≠ ks.length + 1 := by omega
  have hk : ks[i.val - 1]? = some (ks[i.val - 1]'(by omega)) := List.getElem?_eq_getElem _
  simp [kchainM, kchain, chainT, h0, hl, hk, Silmaril.Wasm.JcoTool.KDrop.node]

/-- **A chain of generated modules is well placed.** -/
theorem kchainM_ok (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26) :
    (kchainM xs ks Nb).OK where
  node i k N hg := by
    obtain ⟨h, rfl, -⟩ := kchainM_gen hg
    exact ⟨_, _, kchainM_node h⟩
  size i k N hg := by
    obtain ⟨-, -, rfl⟩ := kchainM_gen hg
    exact hN _
  ws := by simp only [kchainM, kchain]; omega
  wf := kchain_wf xs ks

/-- **A chain is numbered along its streams.** -/
theorem kchain_topo : (kchainM xs ks Nb).net.Topo := by
  intro c hc
  simp only [kchainM, kchain] at hc ⊢
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The specification of node `i` of a chain: what it reads. -/
def chainL (xs : List Val) (ks : List KM) (Nb : Nat → Nat) (i : Fin (kchainM xs ks Nb).net.k) : List Val :=
  if i.val = 0 then [] else runs (ks.take (i.val - 1)) xs

theorem chainL_succ {j : Nat} (hj : j < ks.length) :
    runs (ks.take (j + 1)) xs = (chainT xs ks (j + 1)).run (runs (ks.take j) xs) := by
  rw [Silmaril.Proofs.Wasm.JcoTool.KDrop.runs_succ hj]
  have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hj
  simp [chainT, hk]

/-- A node with an input `c` reads what node `c` writes. -/
theorem chain_cons_inp (i : Fin (kchainM xs ks Nb).net.k) (c : Nat)
    (hc : ((kchainM xs ks Nb).net.node i).inp = some c) :
    chainL xs ks Nb i = ((kchainM xs ks Nb).net.node ((kchainM xs ks Nb).net.wr c).1).T.run
      (chainL xs ks Nb ((kchainM xs ks Nb).net.wr c).1) := by
  have hik : i.val < ks.length + 2 := i.isLt
  have h0 : i.val ≠ 0 := by
    intro h; simp [kchainM, kchain, h] at hc
  have hcv : c = i.val - 1 := by
    have hc' : (if i.val = 0 then none else some (i.val - 1)) = some c := hc
    simp only [h0, ↓reduceIte] at hc'
    exact (Option.some.inj hc').symm
  have hlt : c < ks.length + 2 := by omega
  have hw : ((kchainM xs ks Nb).net.wr c).1 = ⟨c, hlt⟩ := Fin.ext (Nat.mod_eq_of_lt hlt)
  rw [hw]
  show (if i.val = 0 then [] else runs (ks.take (i.val - 1)) xs) =
    (chainT xs ks c).run (if c = 0 then [] else runs (ks.take (c - 1)) xs)
  simp only [h0, ↓reduceIte]
  rw [← hcv]
  rcases Nat.eq_zero_or_pos c with hc0 | hcp
  · rw [hc0]
    simp [chainT, srcK, Tr.run, Tr.feed, runs]
  · obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
    have hj : j < ks.length := by omega
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact chainL_succ hj

/-- **The chain's specification is consistent.** -/
theorem chain_cons : Consistent (kchainM xs ks Nb).net (chainL xs ks Nb) := by
  intro i
  refine ⟨fun hn => ?_, chain_cons_inp i⟩
  have h0 : i.val = 0 := by
    by_contra h
    simp [kchainM, kchain, h] at hn
  simp [chainL, h0]

/-- **A chain of generated modules satisfies the hypotheses of liveness.** -/
theorem kchainM_live (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    (hfit : ∀ (i : Nat) (h : i < ks.length), KFits ks[i] (Nb i)) : (kchainM xs ks Nb).Live where
  ok := kchainM_ok hN hws
  topo := kchain_topo
  spec := ⟨_, chain_cons⟩
  fits i k N hg := by
    obtain ⟨h, rfl, rfl⟩ := kchainM_gen hg
    exact hfit _ _

/-- **The sink of a chain of generated modules**, once it has dropped its input, holds the
kernels' composite. -/
theorem kchainM_correct (hN : ∀ i, 0 < Nb i ∧ Nb i ≤ 256) (hws : ks.length < 2 ^ 26)
    {m : MSys (kchainM xs ks Nb).net} (h : MReach _ m) {b : Bool}
    (hb : (m.ns (snkM xs ks Nb)).rd = .gone b) : (m.ns (snkM xs ks Nb)).got = runs ks xs := by
  obtain ⟨s, hR, -, hns⟩ := Silmaril.Wasm.JcoTool.KNet.mreach_abs (kchainM_ok hN hws) h
  have hg : (kchainM xs ks Nb).gen (snkM xs ks Nb) = none := by
    unfold kchainM
    dsimp only
    split
    · rename_i h; exact absurd h.2 (by show ¬ (ks.length + 1 ≤ ks.length); omega)
    · rfl
  have hsnk : s.ns (snkM xs ks Nb) = m.ns (snkM xs ks Nb) := hns _ hg
  have hR' : Reach (kchain xs ks) s := hR
  have hspec := Silmaril.Proofs.Wasm.JcoTool.KDrop.chain_spec hR' ks.length le_rfl
  rw [List.take_length] at hspec
  have hb' : (s.ns ⟨ks.length + 1, by show ks.length + 1 < ks.length + 2; omega⟩).rd = .gone b := by
    have h1 : (s.ns (snkM xs ks Nb)).rd = .gone b := by rw [hsnk]; exact hb
    exact h1
  have ht := Silmaril.Wasm.Component.Streams.Pipes.net_sink_eof (kchain_wf xs ks) hR'
    ⟨ks.length + 1, by show ks.length + 1 < ks.length + 2; omega⟩ (by simp [kchain]) (fun _ => by simp [kchain, chainT, sinkK]) hb'
  subst ht
  rw [← hsnk]
  exact hspec.2 hb'

/-! ## Tees -/

/-- **A tee of generated modules satisfies the hypotheses of liveness.** -/
theorem ktee_live {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256)
    (f₁ : KFits k₁ N₁) (f₂ : KFits k₂ N₂) : (ktee xs k₁ k₂ N₁ N₂).Live where
  ok := Silmaril.Proofs.Wasm.JcoTool.KNet.ktee_ok xs k₁ k₂ h₁ h₂
  topo := (Silmaril.Wasm.Component.Streams.Live.tee_setting xs (trV k₁) (trV k₂)).topo
  spec := ⟨_, (Silmaril.Wasm.Component.Streams.Live.tee_setting xs (trV k₁) (trV k₂)).cons⟩
  fits i k N hg := by
    simp only [ktee] at hg
    split_ifs at hg
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact f₁
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact f₂

end Silmaril.Proofs.Wasm.JcoTool.KLive
