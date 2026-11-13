module

public import Silmaril.Wasm.JcoTool.KLive.Defs
public import Silmaril.Wasm.JcoTool.KGame.Thms

/-!
# Networks of generated modules terminate

Every step of a generated module is a step of its `Net` node, which decreases the network's
potential (`Live.reach_pot_lt`), or a step that changes neither the store nor the node; the only
such step resumes `WR` with nothing left to write and leaves `WR` (`step_sim_w`: a write of a
nonempty output changes the store, `dstep_write_ne`). So `2 · pot + #(modules in WR)` decreases
along every step of a network with modules (`mstep_dec`), and there is no infinite execution
(`no_infinite_mrun`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Live

/-! ## A write of a nonempty output changes the store -/

/-- A write to a stream whose reader has gone ends the copy. -/
theorem write_gone_st {c c' : DChan} {xs : List Val} {r : Res} (hr : c.r.gone = true)
    (h : c.write xs = some (c', r)) : c.w.st = .idle ∧ c'.w.st = .done := by
  unfold DChan.write at h
  split at h
  · cases h
  · rename_i hg
    have hst : c.w.st = .idle := by simp only [not_or, ne_eq, not_not] at hg; exact hg.2.1
    split at h
    · cases h; exact ⟨hst, rfl⟩
    · cases h

/-- A write to a reader with no buffer starts a copy. -/
theorem write_wait_st {c c' : DChan} {xs : List Val} {r : Res} (hr : c.r.gone = false)
    (hc : c.rcap = none) (h : c.write xs = some (c', r)) : c.w.st = .idle ∧ c'.w.st = .copying := by
  unfold DChan.write at h
  split at h
  · cases h
  · rename_i hg
    have hst : c.w.st = .idle := by simp only [not_or, ne_eq, not_not] at hg; exact hg.2.1
    simp only [hr, hc, Bool.false_eq_true, ↓reduceIte] at h
    cases h; exact ⟨hst, rfl⟩

/-- A write into a reader's buffer with room sends at least one item. -/
theorem write_copy_sent {c c' : DChan} {xs : List Val} {r : Res} {n : Nat} (hr : c.r.gone = false)
    (hc : c.rcap = some n) (hn : n ≠ 0) (h : c.write xs = some (c', r)) :
    c.sent.length < c'.sent.length := by
  unfold DChan.write at h
  split at h
  · cases h
  · rename_i hg
    have hx : xs ≠ [] := by simp only [not_or] at hg; exact hg.2.2
    simp only [hr, hc, Bool.false_eq_true, ↓reduceIte] at h
    cases h
    have hm : 0 < min n xs.length := Nat.lt_min.2 ⟨Nat.pos_of_ne_zero hn, List.length_pos_iff.2 hx⟩
    simp only [List.length_append, List.length_take]
    omega

theorem chan_write_ne {c c' : DChan} {xs : List Val} {r : Res} (hg : c.rcap ≠ some 0)
    (h : c.write xs = some (c', r)) : c' ≠ c := by
  intro he
  cases hr : c.r.gone
  · cases hc : c.rcap with
    | none =>
      obtain ⟨h1, h2⟩ := write_wait_st hr hc h
      rw [he, h1] at h2; cases h2
    | some n =>
      have hlt := write_copy_sent hr hc (fun e => hg (by rw [hc, e])) h
      rw [he] at hlt; omega
  · obtain ⟨h1, h2⟩ := write_gone_st hr h
    rw [he, h1] at h2; cases h2

/-- **A `stream.write` changes the store**, on a store without zero-length read buffers. -/
theorem dstep_write_ne {st st₁ : DStore} {w : Nat} {xs : List Val} {r : Res}
    (hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS st) (h : dstep st (.streamWrite w xs) = some (st₁, r)) :
    st₁ ≠ st := by
  simp only [dstep] at h
  split at h
  · rename_i s _
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    have hne : q.1 ≠ st.chans s := chan_write_ne (hG s).2 hq
    intro hst
    have hc : (st.setChan s q.1).chans s = st.chans s := by rw [(Prod.mk.inj he).1, hst]
    simp [DStore.setChan, Silmaril.Wasm.Component.Async.upd] at hc
    exact hne hc
  · cases h

/-! ## The weight of a module resuming `WR` -/

/-- `1` for a ready module in `WR`. -/
def wv (ms : MS) : Nat :=
  match ms.mode with
  | .ready => if ms.g PC = pWR then 1 else 0
  | _ => 0

theorem wv_le (ms : MS) : wv ms ≤ 1 := by
  unfold wv
  split
  · split <;> omega
  · omega

/-- **From `WR`**: the module leaves `WR` without a built-in, or it writes a nonempty output. -/
theorem wr_cases {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pWR)
    (h : DRStep (genD k N) st ms st' ms') :
    ms'.g PC ≠ pWR ∨ ∃ xs r, dstep st (.streamWrite (wh c') xs) = some (st', r) := by
  obtain ⟨code, s', hx, -, hst, hms⟩ := ready_inv hm h
  have hc : dexec dWR FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pWR, pWTR, pWTW, pRD, pEOI, inv0] using cb_at hx
  have hg' : ms'.g = s'.g := by rw [hms]
  rcases dexec_ite_ret hc with ⟨-, hA⟩ | ⟨-, hB⟩
  · obtain ⟨-, -, -, -, hgs⟩ := wr_reset hA
    left
    rw [hg', hgs]
    simp only [upd_apply, ite_true]
    split <;> (try split) <;> decide
  · obtain ⟨st₁, res, hd, hR⟩ := write_call (ms := ms) hok.2.1 rfl rfl hok.2.2.2.2.2 hok.2.2.2.2.1 hB
    have hst₁ : s'.st = st₁ := noCall_st (by simp [noCall, noCall_onWriteD, yield_]) hR
    right
    exact ⟨_, _, by rw [hst, hst₁]; exact hd⟩

/-- **`WR` with the weight**: a write is a node step; resuming leaves `WR`. -/
theorem sim_wr_w {k : KM} {N c c' s : Nat} (hs : s < 2 ^ 28) {st st' : DStore} {ms ms' : MS}
    {x : NSt KSt} (hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS st) (hok : okD ms (rh c) (wh c') s)
    (hm : ms.mode = .ready) (hpc : ms.g PC = pWR) (hout : outIs x (.idle ms.pending))
    (hnr : NxtRel ms x) (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧
      (NStep (node k c c') s st x st' x' ∨ (st' = st ∧ x' = x ∧ wv ms' < wv ms)) := by
  obtain ⟨x', h1, h2⟩ := sim_wr hs hok hm hpc hout hnr h
  refine ⟨x', h1, ?_⟩
  rcases h2 with h2 | ⟨hst, hxx⟩
  · exact .inl h2
  · have hw : wv ms = 1 := by simp [wv, hm, hpc]
    rcases wr_cases hok hm hpc h with hpc' | ⟨xs, r, hd⟩
    · have hw' : wv ms' = 0 := by
        unfold wv
        split
        · simp [hpc']
        · rfl
      exact .inr ⟨hst, hxx, by omega⟩
    · exact absurd hst (dstep_write_ne hG hd)

/-- **The simulation, with the weight**: a step of the module is a step of its node, or changes
neither the store nor the node and leaves `WR`. -/
theorem step_sim_w {k : KM} {N c c' s : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : s < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt KSt}
    (hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS st) (hR : RelD (rh c) (wh c') s ms x)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelD (rh c) (wh c') s ms' x' ∧
      (NStep (node k c c') s st x st' x' ∨ (st' = st ∧ x' = x ∧ wv ms' < wv ms)) := by
  by_cases hex : ms.mode = .exited
  · exact (no_step_exited hex h).elim
  obtain ⟨hok, hL⟩ := relD_live hR hex
  rcases hL with ⟨hm, hpc, hk, h0, hoff, hrd, hout⟩ | ⟨hm, hpc, hk, h0, hoff, hrp, hrd, hout⟩ |
    ⟨hm, hpc, -, -, hout⟩ | ⟨hm, hpc, hk, hrd, hout⟩ | ⟨hm, hpc, hout, hnr⟩ |
    ⟨hm, hpc, hout, hnr, hne⟩ | ⟨hm, hpc, hrd, hout⟩ | ⟨hm, hpc, hrd, hout⟩
  · obtain ⟨x', h1, h2⟩ := sim_rd hN hs hok hm hpc hk h0 hoff hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_wtr hs hok hm hpc hk h0 hoff hrp hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_wtrd hok hm hpc hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_eoi hok hm hpc hk hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · exact sim_wr_w hs hG hok hm hpc hout hnr h
  · obtain ⟨x', h1, h2⟩ := sim_wtw hs hok hm hpc hout hnr hne h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_cl hok hm hpc hrd hout h
    exact ⟨x', h1, .inl h2⟩
  · obtain ⟨x', h1, h2⟩ := sim_dead hok hm hpc hrd hout h
    exact ⟨x', h1, .inl h2⟩

theorem relN_step_w {Nd : Node} {k : KM} {N ws : Nat} (hN : 0 < N ∧ N ≤ 256) (hs : ws < 2 ^ 28)
    {st st' : DStore} {ms ms' : MS} {x : NSt Nd.σ}
    (hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS st) (hR : RelN Nd k ws ms x)
    (h : DRStep (genD k N) st ms st' ms') :
    ∃ x', RelN Nd k ws ms' x' ∧ (NStep Nd ws st x st' x' ∨ (st' = st ∧ x' = x ∧ wv ms' < wv ms)) := by
  obtain ⟨c, c', hn, hR⟩ := hR
  subst hn
  obtain ⟨x', hR', hx⟩ := step_sim_w hN hs hG hR h
  exact ⟨x', ⟨c, c', rfl, hR'⟩, hx⟩

/-! ## The measure of a network with modules -/

/-- The number of modules resuming `WR`. -/
def wsum {net : Network} (ms : Fin net.k → MS) : Nat :=
  ((List.finRange net.k).map fun i => wv (ms i)).sum

theorem sum_map_update {n : Nat} (l : List (Fin n)) (hnd : l.Nodup) (f : Fin n → MS) (i : Fin n)
    (v : MS) :
    (l.map fun j => wv (Function.update f i v j)).sum + (if i ∈ l then wv (f i) else 0) =
      (l.map fun j => wv (f j)).sum + (if i ∈ l then wv v else 0) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hnd).1
    have ih' := ih (List.nodup_cons.1 hnd).2
    by_cases hai : a = i
    · subst hai
      have hrest : (l.map fun j => wv (Function.update f a v j)) = l.map fun j => wv (f j) :=
        List.map_congr_left fun j hj => by
          have hja : j ≠ a := fun e => ha (e ▸ hj)
          rw [Function.update_of_ne hja]
      simp only [List.map_cons, List.sum_cons, Function.update_self, List.mem_cons, true_or,
        ↓reduceIte, hrest]
      omega
    · have hmem : (i ∈ a :: l) = (i ∈ l) := by simp [List.mem_cons, Ne.symm hai]
      simp only [List.map_cons, List.sum_cons, Function.update_of_ne hai, hmem]
      omega

theorem wsum_update {net : Network} (ms : Fin net.k → MS) (i : Fin net.k) (m' : MS) :
    wsum (Function.update ms i m') + wv (ms i) = wsum ms + wv m' := by
  have h := sum_map_update (List.finRange net.k) (List.nodup_finRange _) ms i m'
  simp only [List.mem_finRange, ↓reduceIte] at h
  exact h

/-- **The measure**: twice the network's potential, plus the modules resuming `WR`. -/
def mu {M : MNet} {L : Fin M.net.k → List Val} (S : Setting M.net L) (m : MSys M.net)
    (s : Sys M.net) : Nat :=
  2 * pot (bB S) (bBo S) s + wsum m.ms

theorem ws_lt {M : MNet} (hM : M.OK) (i : Fin M.net.k) : M.net.ws i < 2 ^ 28 := by
  have := i.isLt; have := hM.ws; simp only [Network.ws]; omega

/-- A node step, with the network step it is. -/
theorem abs_node_step {M : MNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s)
    {i : Fin M.net.k} {st' : DStore} {x' : NSt (M.net.node i).σ} (hg : M.gen i = none)
    (hn : NStep (M.net.node i) (M.net.ws i) m.st (m.ns i) st' x') :
    Step M.net s ⟨st', Function.update s.ns i x'⟩ ∧
      Abs M ⟨st', Function.update m.ns i x', m.ms⟩ ⟨st', Function.update s.ns i x'⟩ := by
  obtain ⟨hst, hns⟩ := hA
  have hn' : NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' := by
    rw [hst, (hns i).1 hg]; exact hn
  refine ⟨.node i hn', rfl, fun j => ⟨fun hj => ?_, fun k N hj => ?_⟩⟩
  · by_cases hji : j = i
    · subst hji; simp
    · simp only [Function.update_of_ne hji]; exact (hns j).1 hj
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    simp only [Function.update_of_ne hji]
    exact (hns j).2 k N hj

/-- A module step that is a node step. -/
theorem abs_mod_nstep {M : MNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s)
    {i : Fin M.net.k} {k : KM} {N : Nat} {st' : DStore} {m' : MS} {x' : NSt (M.net.node i).σ}
    (hg : M.gen i = some (k, N)) (hR' : RelN (M.net.node i) k (M.net.ws i) m' x')
    (hn : NStep (M.net.node i) (M.net.ws i) m.st (s.ns i) st' x') :
    Step M.net s ⟨st', Function.update s.ns i x'⟩ ∧
      Abs M ⟨st', m.ns, Function.update m.ms i m'⟩ ⟨st', Function.update s.ns i x'⟩ := by
  have hn' : NStep (M.net.node i) (M.net.ws i) s.st (s.ns i) st' x' := by rw [hA.1]; exact hn
  refine ⟨.node i hn', rfl, fun j => ⟨fun hj => ?_, fun k' N' hj => ?_⟩⟩
  · have hji : j ≠ i := by rintro rfl; rw [hg] at hj; simp at hj
    dsimp only; rw [Function.update_of_ne hji]; exact (hA.2 j).1 hj
  · by_cases hji : j = i
    · subst hji
      simpa using abs_self (m := m) hg hR' hj
    · dsimp only; rw [Function.update_of_ne hji (f := s.ns)]
      exact abs_rest hA hji hj

/-- **Every step decreases the measure**, for a suitable abstraction of the next system. -/
theorem mstep_dec {M : MNet} (hM : M.OK) {L : Fin M.net.k → List Val} (S : Setting M.net L)
    {m m' : MSys M.net} {s : Sys M.net} (hRs : Reach M.net s) (hA : Abs M m s)
    (hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS m.st) (h : MStep M m m') :
    ∃ s', Reach M.net s' ∧ Abs M m' s' ∧ mu S m' s' < mu S m s := by
  cases h with
  | node i hg hn =>
    obtain ⟨hstep, hA'⟩ := abs_node_step hA hg hn
    have hlt := Silmaril.Wasm.Component.Streams.Live.reach_pot_lt S hRs hstep
    exact ⟨_, .tail hRs hstep, hA', by unfold mu; dsimp only; omega⟩
  | mod i hg hd =>
    rename_i k N st' m'
    obtain ⟨x', hR', hx⟩ := relN_step_w (hM.size i k N hg) (ws_lt hM i) hG ((hA.2 i).2 k N hg) hd
    have hW := wsum_update m.ms i m'
    have hwle := wv_le m'
    rcases hx with hn | ⟨rfl, rfl, hlt⟩
    · obtain ⟨hstep, hA'⟩ := abs_mod_nstep hA hg hR' hn
      have hlt := Silmaril.Wasm.Component.Streams.Live.reach_pot_lt S hRs hstep
      exact ⟨_, .tail hRs hstep, hA', by unfold mu; dsimp only; omega⟩
    · refine ⟨s, hRs, ⟨hA.1, fun j => ⟨(hA.2 j).1, fun k' N' hj => ?_⟩⟩, ?_⟩
      · by_cases hji : j = i
        · subst hji; exact abs_self hg hR' hj
        · exact abs_rest hA hji hj
      · unfold mu; dsimp only; omega

/-- **No infinite execution** of a network with generated modules. -/
theorem no_infinite_mrun {M : MNet} (hM : M.OK) {L : Fin M.net.k → List Val} (S : Setting M.net L)
    (r : Nat → MSys M.net) (h0 : MReach M (r 0)) : ¬ ∀ n, MStep M (r n) (r (n + 1)) := by
  intro hs
  have hreach : ∀ n, MReach M (r n) := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact MSteps.tail ih (hs n)
  obtain ⟨s₀, hR₀, hA₀⟩ := Silmaril.Proofs.Wasm.JcoTool.KNet.mreach_abs hM h0
  have hdec : ∀ n, ∃ s, Reach M.net s ∧ Abs M (r n) s ∧ mu S (r n) s + n ≤ mu S (r 0) s₀ := by
    intro n
    induction n with
    | zero => exact ⟨s₀, hR₀, hA₀, by simp⟩
    | succ n ih =>
      obtain ⟨s, hR, hA, hle⟩ := ih
      have hG : Silmaril.Wasm.Component.Streams.Cancel.GoodS (r n).st :=
        Silmaril.Wasm.JcoTool.KGame.mreach_good hM (hreach n)
      obtain ⟨s', hR', hA', hlt⟩ := mstep_dec hM S hR hA hG (hs n)
      exact ⟨s', hR', hA', by omega⟩
  obtain ⟨s, -, -, hle⟩ := hdec (mu S (r 0) s₀ + 1)
  omega

end Silmaril.Proofs.Wasm.JcoTool.KLive
