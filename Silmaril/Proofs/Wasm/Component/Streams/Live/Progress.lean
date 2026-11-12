module

public import Silmaril.Proofs.Wasm.Component.Streams.Live.Ready

/-!
# Progress: a system with an unfinished node can step

`progress`: in a reachable system of a well-formed network whose nodes are numbered along the
streams (`Network.Topo`), if some node has not finished, some node can step. The node itself can
step, except when it waits for a read with nothing pending on its input stream; then its writer
can step (it has an event, items to write, or an end to drop), or its writer has nothing to write
and has not finished, and the argument moves upstream to a node of smaller index.

The steps (`en_read`, `en_dropIn`, `en_waitIn`, `en_write`, `en_dropOut`, `en_waitOut`) are
built from `Silmaril.Proofs.Wasm.Component.Streams.Live.Ready`: under the protocol invariant the
built-in a node calls does not trap. The positivity fact `excl` (the writer's and the reader's
buffers are never both open) rules out a writer and a reader both waiting for each other.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Proofs.Wasm.Component.Streams.Net

variable {net : Network}

/-- A live reader never finds an empty open buffer. -/
theorem wbuf_ne_nil {W : WV} {ack : List Val} {c : DChan} (hW : WInv W ack c)
    (hr : c.r.gone = false) : c.wbuf ≠ some [] := by
  cases W with
  | idle => rw [hW.2.2.1]; simp
  | busy xs =>
    obtain ⟨-, -, -, hle, -, hb, -⟩ := hW
    rw [(hb hr).1]
    split
    · simp
    · rename_i hne
      intro h
      have h' : xs.drop c.wp = [] := Option.some.inj h
      have : xs.length ≤ c.wp := List.drop_eq_nil_iff.1 h'
      omega
  | dead => rw [hW.2.2.2.2.1]; simp
  | closed d => rw [hW.2.1]; simp

/-- The stream invariant of node `i`'s input `c`, seen from node `i`. -/
theorem chan_in (hwf : net.WF) {s : Sys net} (hI : Inv net s) {i : Fin net.k} {c : Nat}
    (hinp : (net.node i).inp = some c) :
    c < net.m ∧ ∃ o, wOut s c = some o ∧
      ChanInv o.st.view o.ack (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) := by
  obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
  obtain ⟨o, ho, hinv⟩ := hI.chan c hm
  rw [hrd] at hinv
  exact ⟨hm, o, ho, hinv⟩

/-- The stream invariant of node `i`'s output `j` (stream `c`), seen from node `i`. -/
theorem chan_out (hwf : net.WF) {s : Sys net} (hI : Inv net s) {i : Fin net.k} {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) {o : Out} (hj : (s.ns i).outs[j]? = some o) :
    c < net.m ∧ ChanInv o.st.view o.ack (s.ns (net.rd c)).rd (s.ns (net.rd c)).got
      (s.st.chans (rh c)) := by
  obtain ⟨hm, -⟩ := hwf.out_wr i j c hout
  obtain ⟨o', ho', hinv⟩ := hI.chan c hm
  have he : o' = o := by
    rw [wOut_eq hwf s hout, hj] at ho'
    exact (Option.some.inj ho').symm
  rw [he] at hinv
  exact ⟨hm, hinv⟩

/-! ## The steps a node can take -/

theorem en_read (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) (hrd : (s.ns i).rd = .idle)
    (hd : (net.node i).T.done (s.ns i).s = false) : Enabled net s := by
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hI hinp
  rw [hrd] at hinv
  obtain ⟨-, hr, hst, -, -, hev⟩ := hinv.2.1
  have hev' : (s.st.chans (rh c)).w.gone = true → (s.st.chans (rh c)).r.ev.isSome := by
    intro hw; rw [hev, hw]; rfl
  obtain ⟨c', res, hread, hres⟩ :=
    read_ok (n := 1) hr hst hev' (wbuf_ne_nil hinv.1 hr) Nat.one_pos
  have hds := dstep_read_eq hI.coh hm hr hread
  rcases hres with rfl | ⟨p, ys, rfl⟩
  · exact ⟨_, Step.node i (NStep.readBlk hinp hrd hd Nat.one_pos hds)⟩
  · exact ⟨_, Step.node i (NStep.readNow hinp hrd hd Nat.one_pos hds)⟩

theorem en_dropIn (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) (hstop : (s.ns i).mayStop (net.node i).T) :
    Enabled net s := by
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hI hinp
  have hok : (s.st.chans (rh c)).r.gone = false ∧ (s.st.chans (rh c)).r.st ≠ .copying := by
    rcases hstop with h | ⟨h, -⟩
    · rw [h] at hinv
      obtain ⟨-, hr, hst, -⟩ := hinv.2.1
      exact ⟨hr, by rw [hst]; decide⟩
    · rw [h] at hinv
      obtain ⟨-, hr, hst, -⟩ := hinv.2.1
      exact ⟨hr, by rw [hst]; decide⟩
  obtain ⟨c', hdrop⟩ := dropR_ok hok.1 hok.2
  exact ⟨_, Step.node i (NStep.dropIn hinp hstop (dstep_dropR_eq hI.coh hm hok.1 hdrop))⟩

theorem en_waitIn (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) (hr : (s.st.chans (rh c)).r.gone = false)
    (hev : (s.st.chans (rh c)).r.ev.isSome) : Enabled net s := by
  obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
  obtain ⟨st', e, hw⟩ := wait_rh_ok hI.coh hm hr hev
  rw [hrd] at hw
  exact ⟨_, Step.node i (NStep.waitIn hinp hw)⟩

theorem en_write (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) {q a : List Val}
    (hj : (s.ns i).outs[j]? = some ⟨.idle q, a⟩) (hq : q ≠ []) : Enabled net s := by
  obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
  obtain ⟨hw, hst, -, -, hev⟩ := hinv.1
  have hev' : (s.st.chans (rh c)).r.gone = true → (s.st.chans (rh c)).w.ev.isSome := by
    intro hr; rw [hev, hr]; rfl
  have hl : 0 < q.length := List.length_pos_iff.2 hq
  have hx : q.take q.length ≠ [] := by simpa using hq
  obtain ⟨c', r, hwr⟩ := write_ok hw hst hev' hx
  exact ⟨_, Step.node i (NStep.write hout hj hl (le_refl _) (dstep_write_eq hI.coh hm hw hwr))⟩

theorem en_dropOut (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) (hrd : ∃ b, (s.ns i).rd = .gone b) {a : List Val}
    {d : Bool} (hj : (s.ns i).outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨
      (s.ns i).outs[j]? = some ⟨.dead, a⟩ ∧ d = true) : Enabled net s := by
  have hok : c < net.m ∧ (s.st.chans (rh c)).w.gone = false ∧
      (s.st.chans (rh c)).w.st ≠ .copying := by
    rcases hj with ⟨hj, -⟩ | ⟨hj, -⟩
    · obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
      obtain ⟨hw, hst, -⟩ := hinv.1
      exact ⟨hm, hw, by rw [hst]; decide⟩
    · obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
      obtain ⟨hw, hst, -⟩ := hinv.1
      exact ⟨hm, hw, by rw [hst]; decide⟩
  obtain ⟨c', hdrop⟩ := dropW_ok hok.2.1 hok.2.2
  exact ⟨_, Step.node i (NStep.dropOut hout hrd hj (dstep_dropW_eq hI.coh hok.1 hok.2.1 hdrop))⟩

theorem en_waitOut (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) {o : Out} (hj : (s.ns i).outs[j]? = some o)
    (hw : (s.st.chans (rh c)).w.gone = false) (hev : (s.st.chans (rh c)).w.ev.isSome) :
    Enabled net s := by
  obtain ⟨hm, hwr⟩ := hwf.out_wr i j c hout
  obtain ⟨st', e, hwt⟩ := wait_wh_ok hI.coh hm hw hev
  rw [hwr] at hwt
  exact ⟨_, Step.node i (NStep.waitOut hout hj hwt)⟩

/-! ## Who can step -/

/-- A node that has not dropped its input has one. -/
theorem input_of_live {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    (hg : ∀ b, (s.ns i).rd ≠ .gone b) : ∃ c, (net.node i).inp = some c := by
  cases hinp : (net.node i).inp with
  | none => exact absurd ((hI.node i).src hinp).1 (hg true)
  | some c => exact ⟨c, rfl⟩

/-- An idle input: read, or drop the input if `T` is done. -/
theorem en_input_idle (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) (hrd : (s.ns i).rd = .idle) : Enabled net s := by
  by_cases hd : (net.node i).T.done (s.ns i).s = true
  · exact en_dropIn hwf hI i hinp (Or.inr ⟨hrd, Or.inl hd⟩)
  · exact en_read hwf hI i hinp hrd (by simpa using hd)

/-- The reader of a stream whose writer is blocked in a write (its buffer is open) can step. -/
theorem en_reader (hwf : net.WF) {s : Sys net} (hI : Inv net s) {c : Nat} (hm : c < net.m)
    {xs ack : List Val} (hinv : ChanInv (.busy xs) ack (s.ns (net.rd c)).rd (s.ns (net.rd c)).got
      (s.st.chans (rh c)))
    (hr : (s.st.chans (rh c)).r.gone = false) (hrc : (s.st.chans (rh c)).rcap = none) :
    Enabled net s := by
  have hinp : (net.node (net.rd c)).inp = some c := hwf.rd_inp c hm
  have hw : (s.st.chans (rh c)).w.gone = false := hinv.1.1
  have hR := hinv.2.1
  cases hRd : (s.ns (net.rd c)).rd with
  | idle => exact en_input_idle hwf hI _ hinp hRd
  | busy =>
    have hRb : RInv .busy (s.ns (net.rd c)).got (s.st.chans (rh c)) := hRd ▸ hR
    exact en_waitIn hwf hI _ hinp hr (hRb.2.2.2.2.2.2.1 hw hrc)
  | ended =>
    have hRe : RInv .ended (s.ns (net.rd c)).got (s.st.chans (rh c)) := hRd ▸ hR
    exact absurd hRe.2.2.2.1 (by simp [hw])
  | gone b =>
    have hRg : RInv (.gone b) (s.ns (net.rd c)).got (s.st.chans (rh c)) := hRd ▸ hR
    exact absurd hRg.2.1 (by simp [hr])

/-- A writer blocked in a write without a pending event has an open buffer, so the reader's is
closed. -/
theorem busy_open {xs ack : List Val} {c : DChan} (hW : WInv (.busy xs) ack c) (hP : c.Pos)
    (hev : c.w.ev.isSome = false) : c.r.gone = false ∧ c.rcap = none := by
  obtain ⟨-, -, -, hle, -, hb, hg⟩ := hW
  have hr : c.r.gone = false := by
    cases h : c.r.gone
    · rfl
    · rw [hg h] at hev; cases hev
  obtain ⟨hbuf, hfull⟩ := hb hr
  have hne : c.wp ≠ xs.length := fun e => by rw [hfull e] at hev; cases hev
  have hsome : c.wbuf ≠ none := by rw [hbuf]; simp [hne]
  exact ⟨hr, hP.excl.resolve_left hsome⟩

/-- **The writer of a busy reader's stream**, when the reader has nothing pending and its buffer
is open: the writer can step, or it has nothing to write and has not finished. -/
theorem en_writer (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st) {c : Nat}
    (hm : c < net.m) {o : Out} (ho : wOut s c = some o) {R : RV} {got : List Val}
    (hinv : ChanInv o.st.view o.ack R got (s.st.chans (rh c))) (hR : R = .busy)
    (hw : (s.st.chans (rh c)).w.gone = false) (hrc : (s.st.chans (rh c)).rcap ≠ none) :
    Enabled net s ∨ ¬ (s.ns (net.wr c).1).Finished := by
  have hout := hwf.wr_out c hm
  have hj : (s.ns (net.wr c).1).outs[(net.wr c).2]? = some o := ho
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    by_cases hq : q = []
    · subst hq
      by_cases hg : ∃ b, (s.ns (net.wr c).1).rd = .gone b
      · exact Or.inl (en_dropOut hwf hI _ hout hg (d := false) (Or.inl ⟨hj, rfl⟩))
      · exact Or.inr fun hf => hg hf.1
    · exact Or.inl (en_write hwf hI _ hout hj hq)
  | busy xs q =>
    by_cases hwe : (s.st.chans (rh c)).w.ev.isSome
    · exact Or.inl (en_waitOut hwf hI _ hout hj hw hwe)
    · exact absurd (busy_open hinv.1 (hP _) (by simpa using hwe)).2 hrc
  | dead => exact absurd (hinv.2.2.1 (Or.inl rfl)) (by rw [hR]; simp)
  | closed d => exact absurd hinv.1.1 (by simp [hw])

/-- **A busy input**: the node can step, its writer can, or its writer has not finished. -/
theorem en_busy (hwf : net.WF) (htopo : net.Topo) {s : Sys net} (hI : Inv net s)
    (hP : StPos s.st) (i : Fin net.k) (hrd : (s.ns i).rd = .busy) :
    Enabled net s ∨ ∃ i' : Fin net.k, i'.val < i.val ∧ ¬ (s.ns i').Finished := by
  obtain ⟨c, hinp⟩ : ∃ c, (net.node i).inp = some c := input_of_live hI i (by simp [hrd])
  obtain ⟨hm, o, ho, hinv⟩ := chan_in hwf hI hinp
  have hRb : RInv .busy (s.ns i).got (s.st.chans (rh c)) := hrd ▸ hinv.2.1
  obtain ⟨-, hr, -, -, -, -, hev1, hev2⟩ := hRb
  by_cases hev : (s.st.chans (rh c)).r.ev.isSome
  · exact Or.inl (en_waitIn hwf hI i hinp hr hev)
  · have hw : (s.st.chans (rh c)).w.gone = false := by
      cases h : (s.st.chans (rh c)).w.gone
      · rfl
      · exact absurd (hev2 h) hev
    have hrc : (s.st.chans (rh c)).rcap ≠ none := fun h => hev (hev1 hw h)
    have hlt : (net.wr c).1.val < i.val := (hwf.inp_rd i c hinp).2 ▸ htopo c hm
    rcases en_writer hwf hI hP hm ho hinv hrd hw hrc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨_, hlt, h⟩

/-- **An output that is not closed**, of a node that has dropped its input: someone can step. -/
theorem en_out (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st) (i : Fin net.k)
    (hrd : ∃ b, (s.ns i).rd = .gone b) {j : Nat} {o : Out} (hj : (s.ns i).outs[j]? = some o)
    (hnc : ∀ d, o.st ≠ .closed d) : Enabled net s := by
  have hlen : j < (net.node i).outs.length := by
    rw [← (hI.node i).len]
    exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨c, hout⟩ : ∃ c, (net.node i).outs[j]? = some c :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    by_cases hq : q = []
    · subst hq
      exact en_dropOut hwf hI i hout hrd (d := false) (Or.inl ⟨hj, rfl⟩)
    · exact en_write hwf hI i hout hj hq
  | dead => exact en_dropOut hwf hI i hout hrd (d := true) (Or.inr ⟨hj, rfl⟩)
  | closed d => exact absurd rfl (hnc d)
  | busy xs q =>
    by_cases hwe : (s.st.chans (rh c)).w.ev.isSome
    · exact en_waitOut hwf hI i hout hj hinv.1.1 hwe
    · obtain ⟨hr, hrc⟩ := busy_open hinv.1 (hP _) (by simpa using hwe)
      exact en_reader hwf hI hm hinv hr hrc

/-- A node that has dropped its input but has not finished: one of its outputs can step. -/
theorem en_gone (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hP : StPos s.st) (i : Fin net.k)
    {b : Bool} (hrd : (s.ns i).rd = .gone b) (hnf : ¬ (s.ns i).Finished) : Enabled net s := by
  have hg : ∃ b, (s.ns i).rd = .gone b := ⟨b, hrd⟩
  have hno : ¬ ∀ o ∈ (s.ns i).outs, ∃ d, o.st = .closed d := fun h => hnf ⟨hg, h⟩
  obtain ⟨o, hmem, hnc⟩ : ∃ o ∈ (s.ns i).outs, ∀ d, o.st ≠ .closed d := by simpa using hno
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  exact en_out hwf hI hP i hg hj hnc

/-- **Progress**: if some node has not finished, some node can step. -/
theorem progress (hwf : net.WF) (htopo : net.Topo) {s : Sys net} (hI : Inv net s)
    (hP : StPos s.st) : ∀ (n : Nat) (i : Fin net.k), i.val = n → ¬ (s.ns i).Finished →
      Enabled net s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hnf
    cases hrd : (s.ns i).rd with
    | idle =>
      obtain ⟨c, hinp⟩ := input_of_live hI i (by simp [hrd])
      exact en_input_idle hwf hI i hinp hrd
    | busy =>
      rcases en_busy hwf htopo hI hP i hrd with h | ⟨i', hlt, hnf'⟩
      · exact h
      · exact ih i'.val (hi ▸ hlt) i' rfl hnf'
    | ended =>
      obtain ⟨c, hinp⟩ := input_of_live hI i (by simp [hrd])
      exact en_dropIn hwf hI i hinp (Or.inl hrd)
    | gone b => exact en_gone hwf hI hP i hrd hnf

end Silmaril.Proofs.Wasm.Component.Streams.Live
