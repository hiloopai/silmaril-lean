module

public import Silmaril.Wasm.JcoTool.KTeeNet.Defs
public import Silmaril.Wasm.JcoTool.KTee.Thms
public import Silmaril.Wasm.JcoTool.KDrop.Thms
public import Silmaril.Wasm.Component.Streams.Pipes.Thms

/-!
# Networks with generated kernels and tees: the refinement

`greach_abs`: every reachable system of a `GNet` stands for a reachable system of its network
(`Net.Reach`), the kernel modules through `KDrop.RelD`, the tees through `KTee.RelT`. Then the
fully generated tee (`gtee_correct`, `gtee_safe`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KTeeNet

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop (DStore)
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore (MS trV byteOf u8v)
open Silmaril.Wasm.JcoTool.KDrop (DRStep genD initMSD RelD)
open Silmaril.Wasm.JcoTool.KTee (genT initMST teeNode RelT trB nrm)
open Silmaril.Wasm.JcoTool.KNet (MSys)
open Silmaril.Wasm.JcoTool.KTeeNet

/-- The machine `ms` runs the node `Nd` as the generated program `g`, in the state `x`. -/
def RelG (Nd : Node) (g : Gen) (ws : Nat) (ms : MS) (x : NSt Nd.σ) : Prop :=
  match g with
  | .kern k _ => ∃ c c', ∃ h : Nd = Silmaril.Wasm.JcoTool.KDrop.node k c c',
      RelD (rh c) (wh c') ws ms (cast (congrArg (fun N : Node => NSt N.σ) h) x)
  | .tee _ => ∃ a b c, ∃ h : Nd = teeNode a b c,
      RelT (rh a) (wh b) (wh c) ws ms (cast (congrArg (fun N : Node => NSt N.σ) h) x)

/-- A step of a module running a node is a step of the node, or changes neither. -/
theorem relG_step {Nd : Node} {g : Gen} {ws : Nat} (hN : 0 < g.N ∧ g.N ≤ 256) (hs : ws < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Nd.σ} (hR : RelG Nd g ws ms x)
    (h : DRStep g.prog st ms st' ms') :
    ∃ x', RelG Nd g ws ms' x' ∧ (NStep Nd ws st x st' x' ∨ (st' = st ∧ x' = x)) := by
  cases g with
  | kern k N =>
    obtain ⟨c, c', hn, hR⟩ := hR
    subst hn
    obtain ⟨x', hR', hx⟩ := Silmaril.Wasm.JcoTool.KDrop.step_sim hN hs hR h
    exact ⟨x', ⟨c, c', rfl, hR'⟩, hx⟩
  | tee N =>
    obtain ⟨a, b, c, hn, hR⟩ := hR
    subst hn
    obtain ⟨x', hR', hx⟩ := Silmaril.Wasm.JcoTool.KTee.step_sim hN hs hR h
    exact ⟨x', ⟨a, b, c, rfl, hR'⟩, hx⟩

/-- The system with modules `m` stands for the network system `s`. -/
def Abs (M : GNet) (m : MSys M.net) (s : Sys M.net) : Prop :=
  s.st = m.st ∧ ∀ i, (M.gen i = none → s.ns i = m.ns i) ∧
    ∀ g, M.gen i = some g → RelG (M.net.node i) g (M.net.ws i) (m.ms i) (s.ns i)

theorem abs_init {M : GNet} (hM : M.OK) : Abs M (GSys.init M) (init M.net) := by
  refine ⟨rfl, fun i => ⟨fun _ => rfl, fun g hg => ?_⟩⟩
  cases g with
  | kern k N =>
    obtain ⟨c, c', hn⟩ := hM.kern i k N hg
    simp only [GSys.init, initG, hg, init]
    rw [hn]
    exact ⟨c, c', rfl, Silmaril.Wasm.JcoTool.KDrop.init_rel k c c' _⟩
  | tee N =>
    obtain ⟨a, b, c, hn⟩ := hM.tee i N hg
    simp only [GSys.init, initG, hg, init]
    rw [hn]
    exact ⟨a, b, c, rfl, Silmaril.Wasm.JcoTool.KTee.init_rel a b c _⟩

theorem abs_node {M : GNet} {m : MSys M.net} {s : Sys M.net} (hR : Reach M.net s) (hA : Abs M m s)
    {i : Fin M.net.k} {st' : DStore} {x' : NSt (M.net.node i).σ} (hg : M.gen i = none)
    (hn : NStep (M.net.node i) (M.net.ws i) m.st (m.ns i) st' x') :
    ∃ s', Reach M.net s' ∧ Abs M ⟨st', Function.update m.ns i x', m.ms⟩ s' := by
  obtain ⟨hst, hns⟩ := hA
  rw [← hst, ← (hns i).1 hg] at hn
  refine ⟨_, .tail hR (.node i hn), rfl, fun j => ⟨fun hj => ?_, fun g hj => ?_⟩⟩
  · by_cases hji : j = i
    · subst hji; simp
    · simp only [Function.update_of_ne hji]; exact (hns j).1 hj
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    simp only [Function.update_of_ne hji]
    exact (hns j).2 g hj

/-- A module that stepped with the node keeps every module's relation. -/
theorem abs_mod_step {M : GNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s) {i : Fin M.net.k}
    {g : Gen} {st' : DStore} {m' : MS} {x' : NSt (M.net.node i).σ} (hg : M.gen i = some g)
    (hR' : RelG (M.net.node i) g (M.net.ws i) m' x') :
    Abs M ⟨st', m.ns, Function.update m.ms i m'⟩ ⟨st', Function.update s.ns i x'⟩ := by
  refine ⟨rfl, fun j => ⟨fun hj => ?_, fun g' hj => ?_⟩⟩
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    show Function.update s.ns i x' j = m.ns j
    rw [Function.update_of_ne hji]; exact (hA.2 j).1 hj
  · show RelG _ g' _ (Function.update m.ms i m' j) (Function.update s.ns i x' j)
    by_cases hji : j = i
    · subst hji
      have hgg : g' = g := Option.some.inj (hj.symm.trans hg)
      rw [hgg]; simpa using hR'
    · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      exact (hA.2 j).2 g' hj

/-- A module that stuttered keeps every module's relation. -/
theorem abs_mod_stutter {M : GNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s) {i : Fin M.net.k}
    {g : Gen} {m' : MS} (hg : M.gen i = some g)
    (hR' : RelG (M.net.node i) g (M.net.ws i) m' (s.ns i)) :
    Abs M ⟨m.st, m.ns, Function.update m.ms i m'⟩ s := by
  refine ⟨hA.1, fun j => ⟨(hA.2 j).1, fun g' hj => ?_⟩⟩
  show RelG _ g' _ (Function.update m.ms i m' j) (s.ns j)
  by_cases hji : j = i
  · subst hji
    have hgg : g' = g := Option.some.inj (hj.symm.trans hg)
    rw [hgg]; simpa using hR'
  · rw [Function.update_of_ne hji]; exact (hA.2 j).2 g' hj

theorem abs_mod {M : GNet} (hM : M.OK) {m : MSys M.net} {s : Sys M.net} (hR : Reach M.net s)
    (hA : Abs M m s) {i : Fin M.net.k} {g : Gen} {st' : DStore} {m' : MS}
    (hg : M.gen i = some g) (hd : DRStep g.prog m.st (m.ms i) st' m') :
    ∃ s', Reach M.net s' ∧ Abs M ⟨st', m.ns, Function.update m.ms i m'⟩ s' := by
  have hs : M.net.ws i < 2 ^ 28 := by
    have := i.isLt; have := hM.ws; simp only [Network.ws]; omega
  obtain ⟨x', hR', hx⟩ := relG_step (hM.size i g hg) hs ((hA.2 i).2 g hg) hd
  rcases hx with hn | ⟨hst, hxx⟩
  · have hn' : NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' := hA.1 ▸ hn
    exact ⟨_, .tail hR (.node i hn'), abs_mod_step hA hg hR'⟩
  · rw [hst]
    exact ⟨s, hR, abs_mod_stutter hA hg (hxx ▸ hR')⟩

/-- **The refinement**: every reachable system with generated kernels and tees stands for a
reachable system of the network. -/
theorem greach_abs {M : GNet} (hM : M.OK) {m : MSys M.net} (h : GReach M m) :
    ∃ s, Reach M.net s ∧ Abs M m s := by
  induction h with
  | refl => exact ⟨_, .refl _, abs_init hM⟩
  | tail _ hs ih =>
    obtain ⟨s, hR, hA⟩ := ih
    cases hs with
    | node i hg hn => exact abs_node hR hA hg hn
    | mod i hg hd => exact abs_mod hM hR hA hg hd

/-- **Reachable kernel modules keep their buffers in bounds** (or have exited). -/
theorem greach_buf {M : GNet} (hM : M.OK) {m : MSys M.net} (h : GReach M m) {i : Fin M.net.k}
    {k : KM} {N : Nat} (hg : M.gen i = some (.kern k N)) :
    (m.ms i).mode = .exited ∨
      ((m.ms i).g Silmaril.Wasm.JcoTool.KCore.BLEN ≤ Silmaril.Wasm.JcoTool.KCore.CAP ∧
        (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OLEN ≤ Silmaril.Wasm.JcoTool.KCore.CAP ∧
        (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OOFF ≤ (m.ms i).g Silmaril.Wasm.JcoTool.KCore.OLEN) := by
  obtain ⟨s, -, hA⟩ := greach_abs hM h
  obtain ⟨c, c', hn, hR⟩ := (hA.2 i).2 _ hg
  by_cases hex : (m.ms i).mode = .exited
  · exact .inl hex
  · right
    unfold RelD at hR
    simp only [hex, ↓reduceIte] at hR
    exact ⟨hR.1.2.2.2.1, hR.1.2.2.2.2.1, hR.1.2.2.2.2.2⟩

/-! ## The generated tee -/

theorem teeNetB_wf {σ τ : Type} (xs : List Val) (T : Tr σ Val Val) (U : Tr τ Val Val) :
    (teeNetB xs T U).WF :=
  Silmaril.Proofs.Wasm.Component.Streams.Net.Network.WF.of_check rfl

theorem gtee_kern (xs : List Val) {N : Nat} (k₁ k₂ : KM) {N₁ N₂ : Nat} (i : Fin 6) (k : KM) (N' : Nat)
    (hg : (gtee xs N k₁ k₂ N₁ N₂).gen i = some (.kern k N')) :
    ∃ c c', (gtee xs N k₁ k₂ N₁ N₂).net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c' := by
  simp only [gtee] at hg
  by_cases h1 : i.val = 1
  · simp [h1] at hg
  by_cases h2 : i.val = 2
  · simp only [h2, ↓reduceIte] at hg
    obtain ⟨rfl, rfl⟩ := hg
    exact ⟨1, 3, by simp [gtee, teeNetB, h2, Silmaril.Wasm.Component.Streams.Pipes.stage,
      Silmaril.Wasm.JcoTool.KDrop.node]⟩
  by_cases h3 : i.val = 3
  · simp only [h3, ↓reduceIte] at hg
    obtain ⟨rfl, rfl⟩ := hg
    exact ⟨2, 4, by simp [gtee, teeNetB, h3, Silmaril.Wasm.Component.Streams.Pipes.stage,
      Silmaril.Wasm.JcoTool.KDrop.node]⟩
  · simp [h1, h2, h3] at hg

theorem gtee_tee (xs : List Val) {N : Nat} (k₁ k₂ : KM) {N₁ N₂ : Nat} (i : Fin 6) (N' : Nat)
    (hg : (gtee xs N k₁ k₂ N₁ N₂).gen i = some (.tee N')) :
    ∃ a b c, (gtee xs N k₁ k₂ N₁ N₂).net.node i = teeNode a b c := by
  simp only [gtee] at hg
  by_cases h1 : i.val = 1
  · exact ⟨0, 1, 2, by simp [gtee, teeNetB, h1]⟩
  · by_cases h2 : i.val = 2 <;> by_cases h3 : i.val = 3 <;> simp [h1, h2, h3] at hg

theorem gtee_ok (xs : List Val) {N : Nat} (k₁ k₂ : KM) {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) : (gtee xs N k₁ k₂ N₁ N₂).OK where
  kern := gtee_kern xs k₁ k₂
  tee := gtee_tee xs k₁ k₂
  size i g hg := by
    simp only [gtee] at hg
    split_ifs at hg <;> simp only [Option.some.injEq] at hg <;> subst hg <;> assumption
  ws := by simp [gtee]
  wf := teeNetB_wf xs _ _

theorem byteOf_lt (v : Val) : byteOf v < 256 := by
  cases v
  case u8 x => exact x.isLt
  all_goals exact (by decide : (0 : Nat) < 256)

theorem byteOf_nrm (v : Val) : byteOf (nrm v) = byteOf v := by
  show (BitVec.ofNat 8 (byteOf v)).toNat = byteOf v
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (byteOf_lt v)

theorem trV_feed_nrm (k : KM) (s : KSt) (xs : List Val) :
    (trV k).feed s (xs.map nrm) = (trV k).feed s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, Tr.feed]
    have hstep : (trV k).step s (nrm x) = (trV k).step s x := by
      simp [trV, byteOf_nrm]
    rw [hstep, ih]

theorem trV_run_nrm (k : KM) (xs : List Val) : (trV k).run (xs.map nrm) = (trV k).run xs := by
  simp only [Tr.run, trV_feed_nrm]

theorem trB_run (xs : List Val) : trB.run xs = xs.map nrm := by
  simp [Tr.run, Silmaril.Proofs.Wasm.JcoTool.KTee.trB_feed, Silmaril.Proofs.Wasm.JcoTool.KTee.trB_flush]

theorem gtee_spec {xs : List Val} {k₁ k₂ : KM} {s : Sys (teeNetB xs (trV k₁) (trV k₂))}
    (h : Reach (teeNetB xs (trV k₁) (trV k₂)) s) :
    Silmaril.Proofs.Wasm.Component.Streams.Net.SpecOK s 4 ((trV k₁).run xs) ∧
      Silmaril.Proofs.Wasm.Component.Streams.Net.SpecOK s 5 ((trV k₂).run xs) := by
  have hwf := teeNetB_wf xs (trV k₁) (trV k₂)
  have h0 := Silmaril.Wasm.Component.Streams.Pipes.net_src hwf h 0 rfl
  have h1 : Silmaril.Proofs.Wasm.Component.Streams.Net.SpecOK s 1 xs :=
    Silmaril.Wasm.Component.Streams.Pipes.net_spec hwf h 1 (c := 0) rfl [] h0
  have h2 : Silmaril.Proofs.Wasm.Component.Streams.Net.SpecOK s 2 (xs.map nrm) := by
    have := Silmaril.Wasm.Component.Streams.Pipes.net_spec hwf h 2 (c := 1) rfl _ h1
    rw [← trB_run]; exact this
  have h3 : Silmaril.Proofs.Wasm.Component.Streams.Net.SpecOK s 3 (xs.map nrm) := by
    have := Silmaril.Wasm.Component.Streams.Pipes.net_spec hwf h 3 (c := 2) rfl _ h1
    rw [← trB_run]; exact this
  have h4 := Silmaril.Wasm.Component.Streams.Pipes.net_spec hwf h 4 (c := 3) rfl _ h2
  have h5 := Silmaril.Wasm.Component.Streams.Pipes.net_spec hwf h 5 (c := 4) rfl _ h3
  rw [← trV_run_nrm k₁ xs, ← trV_run_nrm k₂ xs]
  exact ⟨h4, h5⟩

/-- **The fully generated tee is correct**: each sink, once it has dropped its input, holds its
branch's kernel run on the whole input. -/
theorem gtee_correct {xs : List Val} {N : Nat} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (gtee xs N k₁ k₂ N₁ N₂).net}
    (hm : GReach _ m) :
    (∀ b, (m.ns (4 : Fin 6)).rd = .gone b → (m.ns (4 : Fin 6)).got = (trV k₁).run xs) ∧
      (∀ b, (m.ns (5 : Fin 6)).rd = .gone b → (m.ns (5 : Fin 6)).got = (trV k₂).run xs) := by
  obtain ⟨s, hR, -, hns⟩ := greach_abs (gtee_ok xs k₁ k₂ h h₁ h₂) hm
  have e4 : s.ns (4 : Fin 6) = m.ns (4 : Fin 6) := (hns (4 : Fin 6)).1 rfl
  have e5 : s.ns (5 : Fin 6) = m.ns (5 : Fin 6) := (hns (5 : Fin 6)).1 rfl
  have hwf := teeNetB_wf xs (trV k₁) (trV k₂)
  obtain ⟨c4, c5⟩ := gtee_spec hR
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [← e4] at hb ⊢
    have := Silmaril.Wasm.Component.Streams.Pipes.net_sink_eof hwf hR 4 rfl (fun _ => rfl) hb
    subst this
    exact c4.2 hb
  · rw [← e5] at hb ⊢
    have := Silmaril.Wasm.Component.Streams.Pipes.net_sink_eof hwf hR 5 rfl (fun _ => rfl) hb
    subst this
    exact c5.2 hb

/-- At every point each sink of the fully generated tee holds a prefix of its output. -/
theorem gtee_safe {xs : List Val} {N : Nat} {k₁ k₂ : KM} {N₁ N₂ : Nat} (h : 0 < N ∧ N ≤ 256)
    (h₁ : 0 < N₁ ∧ N₁ ≤ 256) (h₂ : 0 < N₂ ∧ N₂ ≤ 256) {m : MSys (gtee xs N k₁ k₂ N₁ N₂).net}
    (hm : GReach _ m) :
    (m.ns (4 : Fin 6)).got <+: (trV k₁).run xs ∧ (m.ns (5 : Fin 6)).got <+: (trV k₂).run xs := by
  obtain ⟨s, hR, -, hns⟩ := greach_abs (gtee_ok xs k₁ k₂ h h₁ h₂) hm
  have e4 : s.ns (4 : Fin 6) = m.ns (4 : Fin 6) := (hns (4 : Fin 6)).1 rfl
  have e5 : s.ns (5 : Fin 6) = m.ns (5 : Fin 6) := (hns (5 : Fin 6)).1 rfl
  obtain ⟨c4, c5⟩ := gtee_spec hR
  exact ⟨e4 ▸ c4.1, e5 ▸ c5.1⟩

end Silmaril.Proofs.Wasm.JcoTool.KTeeNet
