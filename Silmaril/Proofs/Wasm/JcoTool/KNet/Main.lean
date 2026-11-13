module

public import Silmaril.Wasm.JcoTool.KNet.Defs
public import Silmaril.Wasm.JcoTool.KDrop.Thms
public import Silmaril.Wasm.Component.Streams.Pipes.Thms

/-!
# Networks with generated modules: the refinement

`mreach_abs`: every reachable system of a network with generated modules stands for a reachable
system of the network (`Net.Reach`), the modules through `KDrop.RelD` (transported along the
equation of their node), so every theorem about `Net` networks holds for it. Then the tee
(`ktee_correct`) and the two-module chain (`kchain2_correct`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (MS trV)
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet

/-- The machine `ms` runs the node `Nd`, which is `Silmaril.Wasm.JcoTool.KDrop.node k c c'`, in the state `x`. -/
def RelN (Nd : Node) (k : KM) (ws : Nat) (ms : MS) (x : NSt Nd.σ) : Prop :=
  ∃ c c', ∃ h : Nd = Silmaril.Wasm.JcoTool.KDrop.node k c c', RelD (rh c) (wh c') ws ms (cast (congrArg (fun N : Node => NSt N.σ) h) x)

theorem relN_init {Nd : Node} {k : KM} {c c' : Nat} (ws : Nat) (h : Nd = Silmaril.Wasm.JcoTool.KDrop.node k c c') :
    RelN Nd k ws (initMSD k (rh (Nd.inp.getD 0)) (wh (Nd.outs.headD 0)) ws) (NSt.init Nd) := by
  subst h
  exact ⟨c, c', rfl, init_rel k c c' ws⟩

/-- A step of a module running a node is a step of the node, or changes neither. -/
theorem relN_step {Nd : Node} {k : KM} {N ws : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : ws < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Nd.σ} (hR : RelN Nd k ws ms x)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelN Nd k ws ms' x' ∧ (NStep Nd ws st x st' x' ∨ (st' = st ∧ x' = x)) := by
  obtain ⟨c, c', hn, hR⟩ := hR
  subst hn
  obtain ⟨x', hR', hx⟩ := step_sim hN hs hR h
  exact ⟨x', ⟨c, c', rfl, hR'⟩, hx⟩

/-- The system with modules `m` stands for the network system `s`. -/
def Abs (M : MNet) (m : MSys M.net) (s : Sys M.net) : Prop :=
  s.st = m.st ∧ ∀ i, (M.gen i = none → s.ns i = m.ns i) ∧
    ∀ k N, M.gen i = some (k, N) → RelN (M.net.node i) k (M.net.ws i) (m.ms i) (s.ns i)

theorem abs_init {M : MNet} (hM : M.OK) : Abs M (MSys.init M) (init M.net) := by
  refine ⟨rfl, fun i => ⟨fun _ => rfl, fun k N hg => ?_⟩⟩
  obtain ⟨c, c', hn⟩ := hM.node i k N hg
  simpa only [MSys.init, initM, hg, init] using relN_init (M.net.ws i) hn

theorem abs_node {M : MNet} {m : MSys M.net} {s : Sys M.net} (hR : Reach M.net s) (hA : Abs M m s)
    {i : Fin M.net.k} {st' : DStore} {x' : NSt (M.net.node i).σ} (hg : M.gen i = none)
    (hn : NStep (M.net.node i) (M.net.ws i) m.st (m.ns i) st' x') :
    ∃ s', Reach M.net s' ∧ Abs M ⟨st', Function.update m.ns i x', m.ms⟩ s' := by
  obtain ⟨hst, hns⟩ := hA
  rw [← hst, ← (hns i).1 hg] at hn
  refine ⟨_, .tail hR (.node i hn), rfl, fun j => ⟨fun hj => ?_, fun k N hj => ?_⟩⟩
  · by_cases hji : j = i
    · subst hji; simp
    · simp only [Function.update_of_ne hji]; exact (hns j).1 hj
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    simp only [Function.update_of_ne hji]
    exact (hns j).2 k N hj

/-- The other modules keep their relation. -/
theorem abs_rest {M : MNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s) {i : Fin M.net.k}
    {m' : MS} {j : Fin M.net.k} (hji : j ≠ i) {k : KM} {N : Nat} (hj : M.gen j = some (k, N)) :
    RelN (M.net.node j) k (M.net.ws j) (Function.update m.ms i m' j) (s.ns j) := by
  rw [Function.update_of_ne hji]
  exact (hA.2 j).2 k N hj

/-- The module itself, with its new machine. -/
theorem abs_self {M : MNet} {m : MSys M.net} {i : Fin M.net.k} {k : KM} {N : Nat} {m' : MS}
    {x : NSt (M.net.node i).σ} (hg : M.gen i = some (k, N)) (hR' : RelN (M.net.node i) k (M.net.ws i) m' x)
    {k' : KM} {N' : Nat} (hj : M.gen i = some (k', N')) :
    RelN (M.net.node i) k' (M.net.ws i) (Function.update m.ms i m' i) x := by
  rw [hg] at hj
  obtain ⟨rfl, rfl⟩ : k = k' ∧ N = N' := by simpa using hj
  simpa using hR'

theorem abs_mod_step {M : MNet} {m : MSys M.net} {s : Sys M.net} (hR : Reach M.net s)
    (hA : Abs M m s) {i : Fin M.net.k} {k : KM} {N : Nat} {st' : DStore} {m' : MS}
    {x' : NSt (M.net.node i).σ} (hg : M.gen i = some (k, N))
    (hR' : RelN (M.net.node i) k (M.net.ws i) m' x')
    (hn : NStep (M.net.node i) (M.net.ws i) m.st (s.ns i) st' x') :
    ∃ s', Reach M.net s' ∧ Abs M ⟨st', m.ns, Function.update m.ms i m'⟩ s' := by
  rw [← hA.1] at hn
  refine ⟨_, .tail hR (.node i hn), rfl, fun j => ⟨fun hj => ?_, fun k' N' hj => ?_⟩⟩
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    dsimp only; rw [Function.update_of_ne hji]; exact (hA.2 j).1 hj
  · by_cases hji : j = i
    · subst hji
      simpa using abs_self (m := m) hg hR' hj
    · dsimp only; rw [Function.update_of_ne hji (f := s.ns)]
      exact abs_rest hA hji hj

theorem abs_mod {M : MNet} (hM : M.OK) {m : MSys M.net} {s : Sys M.net} (hR : Reach M.net s)
    (hA : Abs M m s) {i : Fin M.net.k} {k : KM} {N : Nat} {st' : DStore} {m' : MS}
    (hg : M.gen i = some (k, N)) (hd : DRStep (genD k N) m.st (m.ms i) st' m') :
    ∃ s', Reach M.net s' ∧ Abs M ⟨st', m.ns, Function.update m.ms i m'⟩ s' := by
  have hs : M.net.ws i < 2 ^ 28 := by
    have := i.isLt; have := hM.ws; simp only [Network.ws]; omega
  obtain ⟨x', hR', hx⟩ := relN_step (hM.size i k N hg) hs ((hA.2 i).2 k N hg) hd
  rcases hx with hn | ⟨rfl, rfl⟩
  · exact abs_mod_step hR hA hg hR' hn
  · refine ⟨s, hR, hA.1, fun j => ⟨(hA.2 j).1, fun k' N' hj => ?_⟩⟩
    by_cases hji : j = i
    · subst hji; exact abs_self hg hR' hj
    · exact abs_rest hA hji hj

/-- **The refinement**: every reachable system with generated modules stands for a reachable
system of the network. -/
theorem mreach_abs {M : MNet} (hM : M.OK) {m : MSys M.net} (h : MReach M m) :
    ∃ s, Reach M.net s ∧ Abs M m s := by
  induction h with
  | refl => exact ⟨_, .refl _, abs_init hM⟩
  | tail _ hs ih =>
    obtain ⟨s, hR, hA⟩ := ih
    cases hs with
    | node i hg hn => exact abs_node hR hA hg hn
    | mod i hg hd => exact abs_mod hM hR hA hg hd

/-! ## The tee and the chain -/

open Silmaril.Wasm.Component.Streams.Pipes (teeNet chain teeNet_wf chain_wf)

theorem ktee_ok (xs : List Val) (k₁ k₂ : KM) {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) : (ktee xs k₁ k₂ N₁ N₂).OK where
  node i k N hg := by
    simp only [ktee] at hg
    split_ifs at hg with ha hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨1, 3, by simp [ktee, teeNet, ha, Silmaril.Wasm.Component.Streams.Pipes.stage, Silmaril.Wasm.JcoTool.KDrop.node]⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨2, 4, by simp [ktee, teeNet, hb, Silmaril.Wasm.Component.Streams.Pipes.stage, Silmaril.Wasm.JcoTool.KDrop.node]⟩
  size i k N hg := by
    simp only [ktee] at hg
    split_ifs at hg <;> simp only [Option.some.injEq, Prod.mk.injEq] at hg <;>
      obtain ⟨rfl, rfl⟩ := hg <;> assumption
  ws := by simp [ktee]
  wf := teeNet_wf xs _ _

theorem kchain2_ok (xs : List Val) (k₁ k₂ : KM) {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) : (kchain2 xs k₁ k₂ N₁ N₂).OK where
  node i k N hg := by
    simp only [kchain2] at hg
    split_ifs at hg with ha hb
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨0, 1, by simp [kchain2, chain, ha, Silmaril.Wasm.Component.Streams.Pipes.stage, Silmaril.Wasm.JcoTool.KDrop.node]⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl⟩ := hg
      exact ⟨1, 2, by simp [kchain2, chain, hb, Silmaril.Wasm.Component.Streams.Pipes.stage, Silmaril.Wasm.JcoTool.KDrop.node]⟩
  size i k N hg := by
    simp only [kchain2] at hg
    split_ifs at hg <;> simp only [Option.some.injEq, Prod.mk.injEq] at hg <;>
      obtain ⟨rfl, rfl⟩ := hg <;> assumption
  ws := by simp [kchain2]
  wf := chain_wf xs _ _

/-- **A tee of generated modules is correct**: each sink, once it has dropped its input, holds
its branch's kernel run on the whole input. -/
theorem ktee_correct {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (ktee xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) :
    (∀ b, (m.ns (4 : Fin 6)).rd = .gone b → (m.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
      (∀ b, (m.ns (5 : Fin 6)).rd = .gone b → (m.ns (5 : Fin 6)).got = (trV k₂).run xs) := by
  obtain ⟨s, hR, -, hns⟩ := mreach_abs (ktee_ok xs k₁ k₂ h₁ h₂) h
  have e4 : s.ns (4 : Fin 6) = m.ns (4 : Fin 6) := (hns (4 : Fin 6)).1 rfl
  have e5 : s.ns (5 : Fin 6) = m.ns (5 : Fin 6) := (hns (5 : Fin 6)).1 rfl
  obtain ⟨c4, c5⟩ := Silmaril.Wasm.Component.Streams.Pipes.tee_correct xs (trV k₁) (trV k₂) hR
  exact ⟨fun b hb => e4 ▸ c4 b (e4 ▸ hb), fun b hb => e5 ▸ c5 b (e5 ▸ hb)⟩

/-- At every point each sink of the tee holds a prefix of its branch's output. -/
theorem ktee_safe {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (ktee xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) :
    (m.ns (4 : Fin 6)).got <+: (trV k₁).run xs ∧ (m.ns (5 : Fin 6)).got <+: (trV k₂).run xs := by
  obtain ⟨s, hR, -, hns⟩ := mreach_abs (ktee_ok xs k₁ k₂ h₁ h₂) h
  have e4 : s.ns (4 : Fin 6) = m.ns (4 : Fin 6) := (hns (4 : Fin 6)).1 rfl
  have e5 : s.ns (5 : Fin 6) = m.ns (5 : Fin 6) := (hns (5 : Fin 6)).1 rfl
  obtain ⟨c4, c5⟩ := Silmaril.Wasm.Component.Streams.Pipes.tee_safe xs (trV k₁) (trV k₂) hR
  exact ⟨e4 ▸ c4, e5 ▸ c5⟩

/-- **Two generated modules in a chain** (`Pipes.chain`): the sink holds the composite. -/
theorem kchain2_correct {xs : List Val} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h₁ : 0 < N₁ ∧ N₁ ≤ 256)
    (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (kchain2 xs k₁ k₂ N₁ N₂).net} (h : MReach _ m) {b : Bool}
    (hb : (m.ns (3 : Fin 4)).rd = .gone b) : (m.ns (3 : Fin 4)).got = ((trV k₁).comp (trV k₂)).run xs := by
  obtain ⟨s, hR, -, hns⟩ := mreach_abs (kchain2_ok xs k₁ k₂ h₁ h₂) h
  have e3 : s.ns (3 : Fin 4) = m.ns (3 : Fin 4) := (hns (3 : Fin 4)).1 rfl
  exact e3 ▸ Silmaril.Wasm.Component.Streams.Pipes.chain_eq_comp xs (trV k₁) (trV k₂) hR (e3 ▸ hb)

end Silmaril.Proofs.Wasm.JcoTool.KNet
