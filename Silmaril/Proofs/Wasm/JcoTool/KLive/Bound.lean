module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Mod

/-!
# A pending read of a module holds at most `N` items

`cb c`, the items copied into the reader's open buffer plus its capacity left, is set by a read
of `n` items to `n` and never grows otherwise (`read_cb`, `write_cb`, …). Only the reader of a
stream reads it, and a module reads its input with its read size `N` (`mod_op`: the store
operation of a module step is one built-in on its own ends, or an event of its set). So in
every reachable system the input stream of every module `i` has `cb ≤ N i` (`mreach_rb`), which
is what makes the module's read events well formed (`wfD`: at most 256 items) and its feed loop
fit (`KFits`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked packCopy CopyResult upd Obj)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS Out rh wh tblOf joinedOf NStep Node Reach
  Sys)
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Net (Coh Inv tblOf_rh)

/-! ## The reader's open buffer -/

/-- The items in the reader's open buffer and the room left. -/
def cb (c : DChan) : Nat := c.rgot.length + c.rcap.getD 0

theorem read_cb {c c' : DChan} {n : Nat} {r : Res} (h : c.read n = some (c', r)) :
    cb c' ≤ max (cb c) n := by
  unfold DChan.read at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; simp [cb]
      · cases h
    · split at h
      · cases h; simp [cb]
      · cases h
      · cases h; simp [cb]

theorem write_cb {c c' : DChan} {xs : List Val} {r : Res} (h : c.write xs = some (c', r)) :
    cb c' ≤ cb c := by
  unfold DChan.write at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; simp [cb]
      · cases h
    · split at h
      · cases h; simp [cb]
      · rename_i n hn
        cases h
        simp only [cb, hn, List.length_append, List.length_take, Option.getD_some]
        split <;> simp

theorem takeR_cb {c c' : DChan} {p : Nat} {ys : List Val} (h : c.takeR = some (c', p, ys)) :
    cb c' = 0 := by
  unfold DChan.takeR at h
  split at h
  · cases h
  · cases h; simp [cb]

theorem takeW_cb {c c' : DChan} {p : Nat} (h : c.takeW = some (c', p)) : cb c' = cb c := by
  unfold DChan.takeW at h
  split at h
  · cases h
  · cases h; simp [cb]

theorem dropR_cb {c c' : DChan} (h : c.dropR = some c') : cb c' = cb c := by
  unfold DChan.dropR at h
  split at h
  · cases h
  · cases h; simp [cb]

theorem dropW_cb {c c' : DChan} (h : c.dropW = some c') : cb c' = cb c := by
  unfold DChan.dropW at h
  split at h
  · cases h
  · cases h; simp [cb]

/-! ## Built-ins and events at the store -/

theorem setChan_chans (st : DStore) (s d : Nat) (c : DChan) :
    (st.setChan s c).chans d = if d = s then c else st.chans d := by
  simp [DStore.setChan, Silmaril.Wasm.Component.Async.upd]

/-- A channel operation on stream `s` keeps the bound of every stream. -/
theorem chanOp_cb {st : DStore} {s d : Nat} {c' : DChan} (h : cb c' ≤ cb (st.chans s)) :
    cb ((st.setChan s c').chans d) ≤ cb (st.chans d) := by
  rw [setChan_chans]
  split
  · rename_i hd; rw [hd]; exact h
  · exact le_refl _

/-- What a built-in does to the bound of stream `d`. -/
def CbStep (st st' : DStore) (o : DOp) (d : Nat) : Prop :=
  cb (st'.chans d) ≤ cb (st.chans d) ∨
    ∃ h n, o = .streamRead h n ∧ st.tbl h = some (.streamR d) ∧ cb (st'.chans d) ≤ max (cb (st.chans d)) n

theorem cb_new {st st' : DStore} {r : Res} (h : dstep st .streamNew = some (st', r)) (d : Nat) :
    CbStep st st' .streamNew d := by
  simp only [dstep, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  left
  simp only [Silmaril.Wasm.Component.Async.upd]
  split
  · simp [cb]
  · exact le_refl _

/-- An operation on the stream behind a handle keeps the bounds. -/
theorem cb_chanOp {st st' : DStore} {s : Nat} {q : DChan × Res} {r : Res} (hq : cb q.1 ≤ cb (st.chans s))
    (he : (st.setChan s q.1, q.2) = (st', r)) (d : Nat) : cb (st'.chans d) ≤ cb (st.chans d) := by
  rw [← (Prod.mk.inj he).1]
  exact chanOp_cb hq

theorem cb_write {st st' : DStore} {w : Nat} {xs : List Val} {r : Res}
    (h : dstep st (.streamWrite w xs) = some (st', r)) (d : Nat) : CbStep st st' (.streamWrite w xs) d := by
  simp only [dstep] at h
  split at h
  · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    exact .inl (cb_chanOp (write_cb hq) he d)
  · cases h

theorem cb_read {st st' : DStore} {hr n : Nat} {r : Res}
    (h : dstep st (.streamRead hr n) = some (st', r)) (d : Nat) : CbStep st st' (.streamRead hr n) d := by
  simp only [dstep] at h
  split at h
  · rename_i s hs
    obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1]
    by_cases hd : d = s
    · subst hd
      refine .inr ⟨hr, n, rfl, hs, ?_⟩
      simp only [setChan_chans, ↓reduceIte]
      exact read_cb hq
    · exact .inl (by simp only [setChan_chans, hd, ↓reduceIte, le_refl])
  · cases h

theorem cb_dropR {st st' : DStore} {hr : Nat} {r : Res}
    (h : dstep st (.streamDropR hr) = some (st', r)) (d : Nat) : CbStep st st' (.streamDropR hr) d := by
  simp only [dstep] at h
  split at h
  · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1]
    exact .inl (chanOp_cb (le_of_eq (dropR_cb hq)))
  · cases h

theorem cb_dropW {st st' : DStore} {w : Nat} {r : Res}
    (h : dstep st (.streamDropW w) = some (st', r)) (d : Nat) : CbStep st st' (.streamDropW w) d := by
  simp only [dstep] at h
  split at h
  · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
    rw [← (Prod.mk.inj he).1]
    exact .inl (chanOp_cb (le_of_eq (dropW_cb hq)))
  · cases h

theorem cb_other {st st' : DStore} {o : DOp} {r : Res}
    (ho : o = .wsNew ∨ ∃ hj s, o = .join hj s) (h : dstep st o = some (st', r)) (d : Nat) :
    CbStep st st' o d := by
  rcases ho with rfl | ⟨hj, s, rfl⟩
  · simp only [dstep, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .inl (le_refl _)
  · simp only [dstep] at h
    split at h <;> (try split at h) <;> (try cases h) <;> exact .inl (le_refl _)

/-- **A built-in keeps the bound of every stream**, except a read, which may raise the bound of
the stream it reads to its size. -/
theorem dstep_cb {st st' : DStore} {o : DOp} {r : Res} (h : dstep st o = some (st', r)) (d : Nat) :
    cb (st'.chans d) ≤ cb (st.chans d) ∨
      ∃ h n, o = .streamRead h n ∧ st.tbl h = some (.streamR d) ∧ cb (st'.chans d) ≤ max (cb (st.chans d)) n := by
  cases o with
  | streamNew => exact cb_new h d
  | streamWrite w xs => exact cb_write h d
  | streamRead hr n => exact cb_read h d
  | streamDropR hr => exact cb_dropR h d
  | streamDropW w => exact cb_dropW h d
  | wsNew => exact cb_other (.inl rfl) h d
  | join hj s => exact cb_other (.inr ⟨hj, s, rfl⟩) h d

/-- **Delivering an event keeps the bound of every stream.** -/
theorem takeEv_cb {st st' : DStore} {h : Nat} {e : Event} (ht : takeEv st h = some (st', e)) (d : Nat) :
    cb (st'.chans d) ≤ cb (st.chans d) := by
  unfold takeEv at ht
  split at ht
  · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 ht
    rw [← (Prod.mk.inj he).1]
    exact chanOp_cb (by rw [takeR_cb hq]; exact Nat.zero_le _)
  · obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 ht
    rw [← (Prod.mk.inj he).1]
    exact chanOp_cb (le_of_eq (takeW_cb hq))
  · cases ht

theorem wait_cb {st st' : DStore} {s h : Nat} {e : Event} (hw : DWait st s h st' e) (d : Nat) :
    cb (st'.chans d) ≤ cb (st.chans d) :=
  takeEv_cb hw.2.2 d

/-! ## The store operation of a module step -/

/-- The store change of one step of a module with input `c`, output `c'` and read size `N`: none,
a read of `N` items of its input, a write or drop of its own ends, or an event. -/
def ModOp (c c' N : Nat) (st st' : DStore) : Prop :=
  st' = st ∨ (∃ r, dstep st (.streamRead (rh c) N) = some (st', r)) ∨
    (∃ o r, (o = .streamDropR (rh c) ∨ o = .streamDropW (wh c') ∨ ∃ xs, o = .streamWrite (wh c') xs) ∧
      dstep st o = some (st', r)) ∨
    (∃ s h e, DWait st s h st' e)

/-- The rest of `RD` after `stream.read` makes no call. -/
theorem noCall_rdRest (k : KM) : noCall (.ite (isE (.l LR) blocked) (.seq (.gset PC (.c pWTR))
    (.ret waitCode)) (.seq (onReadD k (.l LR)) yield_)) = true := by
  simp [noCall, noCall_onReadD, yield_]

theorem op_rd {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS} (hN : N ≤ 256)
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pRD)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨code, s', hx, -, hst, -⟩ := ready_inv hm h
  have hc : dexec (dRD k N) FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pRD, pWTR, pWTW, inv0] using cb_at hx
  rw [dRD, dexec_seq_norm (s₁ := sL (inv0 ms [0, 0, 0] st)) (by simp [dexec, E.eval, sL, M32])] at hc
  rcases dexec_ite_ret hc with ⟨-, hA⟩ | ⟨-, hB⟩
  · obtain ⟨st₁, res, hd, -, hs₁, -⟩ := dropFlush_exec (s := sL (inv0 ms [0, 0, 0] st)) hok.1
      (ks_ofD hok.2.2.2.1 rfl) hA
    exact .inr (.inr (.inl ⟨_, res, .inl rfl, by rw [hst, hs₁]; exact hd⟩))
  have hNm : N < M32 := by simp only [M32]; omega
  rcases read_call (s := sL (inv0 ms [0, 0, 0] st)) hok.1 hNm hB with
    ⟨st₁, p, xs, hd, -, -, hR⟩ | ⟨st₁, hd, hR⟩
  · have hs₁ : s'.st = st₁ := noCall_st (noCall_rdRest k) hR
    exact .inr (.inl ⟨_, by rw [hst, hs₁]; exact hd⟩)
  · have hs₁ : s'.st = st₁ := noCall_st (noCall_rdRest k) hR
    exact .inr (.inl ⟨_, by rw [hst, hs₁]; exact hd⟩)

theorem op_wr {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pWR)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨code, s', hx, -, hst, -⟩ := ready_inv hm h
  have hc : dexec dWR FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pWR, pWTR, pWTW, pRD, pEOI, inv0] using cb_at hx
  rcases dexec_ite_ret hc with ⟨-, hA⟩ | ⟨-, hB⟩
  · obtain ⟨-, hs₁, -⟩ := wr_reset hA
    exact .inl (by rw [hst, hs₁]; rfl)
  · obtain ⟨st₁, res, hd, hR⟩ := write_call (ms := ms) hok.2.1 rfl rfl hok.2.2.2.2.2 hok.2.2.2.2.1 hB
    have hs₁ : s'.st = st₁ := noCall_st (by simp [noCall, noCall_onWriteD, yield_]) hR
    exact .inr (.inr (.inl ⟨_, _, .inr (.inr ⟨_, rfl⟩), by rw [hst, hs₁]; exact hd⟩))

theorem op_eoi {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pEOI)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨code, s', hx, -, hst, -⟩ := ready_inv hm h
  have hc : dexec (dEOI k) FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pEOI, pWTR, pWTW, pRD, inv0] using cb_at hx
  obtain ⟨st₁, res, hd, -, hs₁, -⟩ := dropFlush_exec (s := inv0 ms [0, 0, 0] st) hok.1
    (ks_ofD hok.2.2.2.1 rfl) hc
  exact .inr (.inr (.inl ⟨_, res, .inl rfl, by rw [hst, hs₁]; exact hd⟩))

theorem op_cl {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pCL)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨code, s', hx, -, hst, -⟩ := ready_inv hm h
  have hc : dexec dCL FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pCL, pWTR, pWTW, pRD, pEOI, pWR, inv0] using cb_at hx
  obtain ⟨st₁, res, hd, -, hs₁⟩ := dCL_exec hok.2.1 hc
  exact .inr (.inr (.inl ⟨_, res, .inr (.inl rfl), by rw [hst, hs₁]; exact hd⟩))

theorem op_dead {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hok : okD ms (rh c) (wh c') s) (hm : ms.mode = .ready) (hpc : ms.g PC = pDEAD)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨code, s', hx, -, hst, -⟩ := ready_inv hm h
  have hc : dexec dDEAD FUEL (inv0 ms [0, 0, 0] st) = some (.ret code, s') := by
    simpa [hpc, caseOf, pEOI, pWTR, pWTW, pRD, pWR, pCL, pDEAD, inv0] using cb_at hx
  obtain ⟨st₁, res, hd, -, hs₁, -⟩ := dDEAD_exec hok.1 hc
  exact .inr (.inr (.inl ⟨_, res, .inl rfl, by rw [hst, hs₁]; exact hd⟩))

/-- A waiting module's step: an event, and a case without calls. -/
theorem op_wait {k : KM} {N c c' s : Nat} {st st' : DStore} {ms ms' : MS}
    (hm : ms.mode = .waiting s) (hpc : ms.g PC = pWTR ∨ ms.g PC = pWTRD ∨ ms.g PC = pWTW)
    (h : DRStep (genD k N) st ms st' ms') : ModOp c c' N st st' := by
  obtain ⟨hd, st₁, e, hw, -, code, s', hx, -, hst, -⟩ := event_inv hm h
  have hc := cb_at hx
  have hg : (inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁).g PC = ms.g PC := by
    simp [inv0, deliver_g]
  have hnc : noCall (caseOf k N ((inv0 (deliver e ms) [e.code.toNat, e.index, e.payload] st₁).g PC)) = true := by
    rw [hg]
    rcases hpc with h1 | h1 | h1 <;>
      simp [h1, caseOf, pWTR, pWTW, pWTRD, pRD, pEOI, pWR, pCL, pDEAD, dWTR, dWTRD, dWTW, noCall,
        noCall_onReadD, noCall_onWriteD, yield_]
  have hs₁ : s'.st = st₁ := noCall_st hnc hc
  exact .inr (.inr (.inr ⟨s, hd, e, by rw [hst, hs₁]; exact hw⟩))

/-- **The store operation of a module step.** -/
theorem mod_op {k : KM} {N c c' s : Nat} (hN : N ≤ 256) {st st' : DStore} {ms ms' : MS}
    {x : NSt KSt} (hR : RelD (rh c) (wh c') s ms x) (h : DRStep (genD k N) st ms st' ms') :
    ModOp c c' N st st' := by
  by_cases hex : ms.mode = .exited
  · exact (no_step_exited hex h).elim
  obtain ⟨hok, hL⟩ := relD_live hR hex
  rcases hL with ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩ |
    ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩ | ⟨hm, hpc, -⟩
  · exact op_rd hN hok hm hpc h
  · exact op_wait hm (.inl hpc) h
  · exact op_wait hm (.inr (.inl hpc)) h
  · exact op_eoi hok hm hpc h
  · exact op_wr hok hm hpc h
  · exact op_wait hm (.inr (.inr hpc)) h
  · exact op_cl hok hm hpc h
  · exact op_dead hok hm hpc h

/-- **The bound after a module step**: unchanged or lower, except on its own input, which it
reads with size `N`. -/
theorem modOp_cb {c c' N : Nat} {st st' : DStore} (h : ModOp c c' N st st') (d : Nat) :
    cb (st'.chans d) ≤ cb (st.chans d) ∨
      (st.tbl (rh c) = some (.streamR d) ∧ cb (st'.chans d) ≤ max (cb (st.chans d)) N) := by
  rcases h with rfl | ⟨r, hd⟩ | ⟨o, r, ho, hd⟩ | ⟨s, h, e, hw⟩
  · exact .inl (le_refl _)
  · rcases dstep_cb hd d with h1 | ⟨h, n, he, ht, h2⟩
    · exact .inl h1
    · cases he
      exact .inr ⟨ht, h2⟩
  · rcases dstep_cb hd d with h1 | ⟨h, n, he, -, -⟩
    · exact .inl h1
    · rcases ho with rfl | rfl | ⟨xs, rfl⟩ <;> cases he
  · exact .inl (wait_cb hw d)

/-- **The bound after a node step**: unchanged or lower, except on the node's input. -/
theorem nstep_cb {Nd : Node} {ws : Nat} {st st' : DStore} {x x' : NSt Nd.σ}
    (h : NStep Nd ws st x st' x') (d : Nat) :
    cb (st'.chans d) ≤ cb (st.chans d) ∨ ∃ c, Nd.inp = some c ∧ st.tbl (rh c) = some (.streamR d) := by
  cases h with
  | readBlk hi _ _ _ hd =>
    rcases dstep_cb hd d with h1 | ⟨h, n, he, ht, -⟩
    · exact .inl h1
    · cases he; exact .inr ⟨_, hi, ht⟩
  | readNow hi _ _ _ hd =>
    rcases dstep_cb hd d with h1 | ⟨h, n, he, ht, -⟩
    · exact .inl h1
    · cases he; exact .inr ⟨_, hi, ht⟩
  | write _ _ _ _ hd =>
    rcases dstep_cb hd d with h1 | ⟨h, n, he, -, -⟩
    · exact .inl h1
    · cases he
  | waitIn _ hw => exact .inl (wait_cb hw d)
  | waitOut _ _ hw => exact .inl (wait_cb hw d)
  | dropIn _ _ hd =>
    rcases dstep_cb hd d with h1 | ⟨h, n, he, -, -⟩
    · exact .inl h1
    · cases he
  | dropOut _ _ _ hd =>
    rcases dstep_cb hd d with h1 | ⟨h, n, he, -, -⟩
    · exact .inl h1
    · cases he

/-! ## The invariant -/

/-- **The input of every module holds at most `N` items in its reader's buffer.** -/
def RB (M : MNet) (m : MSys M.net) : Prop :=
  ∀ i k N c c', M.gen i = some (k, N) → M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c' → cb (m.st.chans (rh c)) ≤ N

/-- Under a coherent store, a readable handle names its own stream. -/
theorem coh_rh {net : Network} {st : DStore} (hc : Coh net st) {c d : Nat}
    (h : st.tbl (rh c) = some (.streamR d)) : d = rh c := by
  rw [hc.1] at h
  exact (tblOf_rh h).1

theorem rh_inj {c c' : Nat} (h : rh c = rh c') : c = c' := by
  simp only [rh] at h; omega

/-- Two nodes reading the same stream are one node. -/
theorem same_reader {M : MNet} (hM : M.OK) {i j : Fin M.net.k} {c : Nat}
    (hi : (M.net.node i).inp = some c) (hj : (M.net.node j).inp = some c) : i = j :=
  (hM.wf.inp_rd i c hi).2.symm.trans (hM.wf.inp_rd j c hj).2

theorem inp_of {M : MNet} {i : Fin M.net.k} {k : KM} {c c' : Nat}
    (hn : M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c') : (M.net.node i).inp = some c := by
  rw [hn]; rfl

theorem rb_node {M : MNet} (hM : M.OK) {m : MSys M.net} (hc : Coh M.net m.st) (hB : RB M m)
    {j : Fin M.net.k} {st' : DStore} {x' : NSt (M.net.node j).σ} (hg : M.gen j = none)
    (hn : NStep (M.net.node j) (M.net.ws j) m.st (m.ns j) st' x') :
    RB M ⟨st', Function.update m.ns j x', m.ms⟩ := by
  intro i k N c c' hi hni
  rcases nstep_cb hn (rh c) with h1 | ⟨cj, hcj, ht⟩
  · exact h1.trans (hB i k N c c' hi hni)
  · have hcc : c = cj := rh_inj (coh_rh hc ht)
    have hij : i = j := same_reader hM (inp_of hni) (hcc ▸ hcj)
    rw [hij, hg] at hi
    cases hi

theorem rb_mod {M : MNet} (hM : M.OK) {m : MSys M.net} (hc : Coh M.net m.st) (hB : RB M m)
    {j : Fin M.net.k} {k : KM} {N : Nat} {cj cj' : Nat} {st' : DStore} {m' : MS}
    (hg : M.gen j = some (k, N)) (hnj : M.net.node j = Silmaril.Wasm.JcoTool.KDrop.node k cj cj')
    (hop : ModOp cj cj' N m.st st') : RB M ⟨st', m.ns, Function.update m.ms j m'⟩ := by
  intro i k' N' c c' hi hni
  rcases modOp_cb hop (rh c) with h1 | ⟨ht, h2⟩
  · exact h1.trans (hB i k' N' c c' hi hni)
  · have hcc : cj = c := rh_inj (coh_rh hc ht).symm
    have hij : i = j := same_reader hM (inp_of hni) (hcc ▸ inp_of hnj)
    rw [hij, hg] at hi
    obtain ⟨rfl, rfl⟩ : k = k' ∧ N = N' := by simpa using hi
    have hb : cb (m.st.chans (rh c)) ≤ N := hB i k N c c' (hij ▸ hg) hni
    exact h2.trans (max_le hb (le_refl _))

theorem rb_init (M : MNet) : RB M (MSys.init M) := by
  intro i k N c c' _ _
  simp [MSys.init, Silmaril.Wasm.Component.Streams.Net.initStore, cb]

/-- **The bound holds in every reachable system**, with an abstraction of it. -/
theorem mreach_rb {M : MNet} (hM : M.OK) {m : MSys M.net} (h : MReach M m) :
    ∃ s, Reach M.net s ∧ Abs M m s ∧ RB M m := by
  induction h with
  | refl => exact ⟨_, .refl _, abs_init hM, rb_init M⟩
  | tail _ hs ih =>
    obtain ⟨s, hR, hA, hB⟩ := ih
    have hc : Coh M.net _ := hA.1 ▸ (Silmaril.Proofs.Wasm.Component.Streams.Net.reach_inv hM.wf hR).coh
    cases hs with
    | node i hg hn =>
      obtain ⟨s', hR', hA'⟩ := abs_node hR hA hg hn
      exact ⟨s', hR', hA', rb_node hM hc hB hg hn⟩
    | mod i hg hd =>
      obtain ⟨s', hR', hA'⟩ := abs_mod hM hR hA hg hd
      obtain ⟨ci, ci', hn, hRel⟩ := (hA.2 i).2 _ _ hg
      have hop := mod_op (hM.size i _ _ hg).2 hRel hd
      exact ⟨s', hR', hA', rb_mod hM hc hB hg hn hop⟩

end Silmaril.Proofs.Wasm.JcoTool.KLive
