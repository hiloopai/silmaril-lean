module

public import Silmaril.Proofs.Wasm.Component.Streams.Net.Node
public import Silmaril.Proofs.Wasm.Component.Streams.Net.Store

/-!
# The network invariant

`Inv net s`: the store is coherent with the network, every stream satisfies the protocol
invariant with the views of its writer (an output of a node) and its reader (a node's input), and
every node satisfies the node invariant. It holds initially (`inv_init`) and every step of every
node preserves it (`inv_step`), so it holds in every reachable system (`reach_inv`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Net

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd blocked)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net

variable {net : Network}

/-- The writer's output of stream `c`. -/
def wOut (s : Sys net) (c : Nat) : Option Out := (s.ns (net.wr c).1).outs[(net.wr c).2]?

/-- The protocol invariant of stream `c` in the system `s`. -/
def ChanOK (s : Sys net) (c : Nat) : Prop :=
  ∃ o, wOut s c = some o ∧
    ChanInv o.st.view o.ack (s.ns (net.rd c)).rd (s.ns (net.rd c)).got (s.st.chans (rh c))

/-- **The network invariant.** -/
structure Inv (net : Network) (s : Sys net) : Prop where
  coh : Coh net s.st
  chan : ∀ c, c < net.m → ChanOK s c
  node : ∀ i, NodeInv (net.node i) (s.ns i)

/-- `ChanOK` depends only on the stream and on the views of its two ends. -/
theorem ChanOK.congr {s s' : Sys net} {c : Nat} (h : ChanOK s c)
    (hch : s'.st.chans (rh c) = s.st.chans (rh c))
    (hw : (wOut s' c).map (fun o => (o.st.view, o.ack)) = (wOut s c).map (fun o => (o.st.view, o.ack)))
    (hr : (s'.ns (net.rd c)).rd = (s.ns (net.rd c)).rd)
    (hg : (s'.ns (net.rd c)).got = (s.ns (net.rd c)).got) : ChanOK s' c := by
  obtain ⟨o, ho, hI⟩ := h
  rw [ho] at hw
  rcases ho' : wOut s' c with _ | o'
  · rw [ho'] at hw
    simp at hw
  · rw [ho'] at hw
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
    refine ⟨o', ho', ?_⟩
    rw [hw.1, hw.2, hch, hr, hg]
    exact hI

theorem view_push (ys : List Val) (o : Out) :
    ((o.push ys).st.view, (o.push ys).ack) = (o.st.view, o.ack) := by
  obtain ⟨st, a⟩ := o
  cases st <;> rfl

theorem map_view_push (ys : List Val) (os : List Out) (j : Nat) :
    (os.map (Out.push ys))[j]?.map (fun o => (o.st.view, o.ack)) =
      os[j]?.map (fun o => (o.st.view, o.ack)) := by
  rw [List.getElem?_map]
  cases os[j]? with
  | none => rfl
  | some o => simp only [Option.map_some]; rw [view_push]

theorem ns_upd_self (s : Sys net) (i : Fin net.k) (x : NSt (net.node i).σ) :
    Function.update s.ns i x i = x := by simp

theorem ns_upd_ne (s : Sys net) (i k : Fin net.k) (x : NSt (net.node i).σ) (h : k ≠ i) :
    Function.update s.ns i x k = s.ns k := by simp [h]

/-- A property of the updated node states, by cases on the node. -/
theorem upd_cases {n : Nat} {β : Fin n → Type} (f : (k : Fin n) → β k) (i : Fin n) (v : β i)
    (P : (k : Fin n) → β k → Prop) (k : Fin n) (h1 : k ≠ i → P k (f k)) (h2 : k = i → P i v) :
    P k (Function.update f i v k) := by
  by_cases h : k = i
  · subst h
    simpa using h2 rfl
  · simpa [h] using h1 h

/-- The view of an output. -/
abbrev oview (o : Out) : WV × List Val := (o.st.view, o.ack)

/-- The input stream itself, after a step on node `i`'s input side. -/
theorem input_chan_self (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) {st' : DStore} (x' : NSt (net.node i).σ)
    (hnew : ∀ o, wOut s c = some o →
      ChanInv o.st.view o.ack (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) →
      ChanInv o.st.view o.ack x'.rd x'.got (st'.chans (rh c))) :
    ChanOK (⟨st', Function.update s.ns i x'⟩ : Sys net) c := by
  obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
  have hw : (net.wr c).1 ≠ i := hrd ▸ hwf.no_loop c hm
  obtain ⟨o, ho, hinv⟩ := hI.chan c hm
  have ho' : wOut (⟨st', Function.update s.ns i x'⟩ : Sys net) c = some o := by
    simp only [wOut] at ho ⊢
    rw [ns_upd_ne s i _ x' hw]
    exact ho
  have hinv' : ChanInv o.st.view o.ack (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) :=
    hrd ▸ hinv
  refine ⟨o, ho', ?_⟩
  show ChanInv o.st.view o.ack (Function.update s.ns i x' (net.rd c)).rd
    (Function.update s.ns i x' (net.rd c)).got (st'.chans (rh c))
  rw [hrd, ns_upd_self]
  exact hnew o ho hinv'

/-- Another stream, after a step on node `i`'s input side. -/
theorem input_chan_other (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    {c c₂ : Nat} (hinp : (net.node i).inp = some c) (hc₂ : c₂ < net.m) (e : c₂ ≠ c)
    {st' : DStore} (hst : st'.chans (rh c₂) = s.st.chans (rh c₂)) (x' : NSt (net.node i).σ)
    (hout : ∀ j : Nat, x'.outs[j]?.map oview = (s.ns i).outs[j]?.map oview) :
    ChanOK (⟨st', Function.update s.ns i x'⟩ : Sys net) c₂ := by
  have hr : net.rd c₂ ≠ i := by
    intro h
    have h' : (net.node i).inp = some c₂ := h ▸ hwf.rd_inp c₂ hc₂
    rw [hinp] at h'
    exact e (Option.some.inj h').symm
  refine (hI.chan c₂ hc₂).congr hst ?_ (ns_upd_ne s i _ x' hr ▸ rfl) (ns_upd_ne s i _ x' hr ▸ rfl)
  simp only [wOut]
  exact upd_cases s.ns i x'
    (fun k y => (y.outs[(net.wr c₂).2]?).map oview = ((s.ns k).outs[(net.wr c₂).2]?).map oview)
    _ (fun _ => rfl) (fun _ => hout _)

/-- **A step on the input side** of node `i` (input stream `c`) keeps the invariant, given the
new stream's invariant. -/
theorem inv_input (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    (hinp : (net.node i).inp = some c) {st' : DStore}
    (hcoh : Coh net st') (hst : ∀ c₂, c₂ ≠ c → st'.chans (rh c₂) = s.st.chans (rh c₂))
    (x' : NSt (net.node i).σ) (hN : NodeInv (net.node i) x')
    (hout : ∀ j : Nat, x'.outs[j]?.map oview = (s.ns i).outs[j]?.map oview)
    (hnew : ∀ o, wOut s c = some o →
      ChanInv o.st.view o.ack (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) →
      ChanInv o.st.view o.ack x'.rd x'.got (st'.chans (rh c))) :
    Inv net ⟨st', Function.update s.ns i x'⟩ := by
  refine ⟨hcoh, fun c₂ hc₂ => ?_, fun k => ?_⟩
  · by_cases e : c₂ = c
    · exact e ▸ input_chan_self hwf hI i hinp x' hnew
    · exact input_chan_other hwf hI i hinp hc₂ e (hst c₂ e) x' hout
  · exact upd_cases s.ns i x' (fun k y => NodeInv (net.node k) y) k (fun _ => hI.node k)
      (fun _ => hN)

/-- **A step on output `j`** of node `i` (stream `c`) keeps the invariant, given the new
stream's invariant. -/
theorem inv_output (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) {st' : DStore}
    (hcoh : Coh net st') (hst : ∀ c₂, c₂ ≠ c → st'.chans (rh c₂) = s.st.chans (rh c₂))
    (o' : Out) (hN : NodeInv (net.node i) { s.ns i with outs := (s.ns i).outs.set j o' })
    (hnew : ∀ o, (s.ns i).outs[j]? = some o →
      ChanInv o.st.view o.ack (s.ns (net.rd c)).rd (s.ns (net.rd c)).got (s.st.chans (rh c)) →
      ChanInv o'.st.view o'.ack (s.ns (net.rd c)).rd (s.ns (net.rd c)).got (st'.chans (rh c))) :
    Inv net ⟨st', Function.update s.ns i { s.ns i with outs := (s.ns i).outs.set j o' }⟩ := by
  obtain ⟨hm, hwr⟩ := hwf.out_wr i j c hout
  have hri : net.rd c ≠ i := by
    intro h
    have := hwf.no_loop c hm
    rw [hwr, h] at this
    exact this rfl
  have hlen : j < (s.ns i).outs.length := by
    rw [(hI.node i).len]
    exact (List.getElem?_eq_some_iff.1 hout).1
  refine ⟨hcoh, fun c₂ hc₂ => ?_, fun k => ?_⟩
  · by_cases e : c₂ = c
    · subst e
      obtain ⟨o, ho, hinv⟩ := hI.chan c₂ hc₂
      simp only [wOut] at ho
      rw [hwr] at ho
      refine ⟨o', ?_, ?_⟩
      · simp only [wOut]
        rw [hwr]
        show (Function.update s.ns i _ i).outs[j]? = some o'
        simp [hlen]
      · simp only
        rw [ns_upd_ne s i _ _ hri]
        exact hnew o ho hinv
    · refine (hI.chan c₂ hc₂).congr (hst c₂ e) ?_ ?_ ?_
      · simp only [wOut]
        refine upd_cases s.ns i _
          (fun k y => (y.outs[(net.wr c₂).2]?).map oview = ((s.ns k).outs[(net.wr c₂).2]?).map oview)
          _ (fun _ => rfl) (fun hi => ?_)
        by_cases hj : (net.wr c₂).2 = j
        · exfalso
          have h1 := hwf.wr_out c₂ hc₂
          have h2 : net.wr c₂ = (i, j) := Prod.ext hi hj
          rw [h2] at h1
          have h3 : (net.node i).outs[j]? = some c₂ := h1
          rw [hout] at h3
          exact e (Option.some.inj h3).symm
        · simp [List.getElem?_set_ne (Ne.symm hj)]
      · exact upd_cases s.ns i _ (fun k y => y.rd = (s.ns k).rd) _ (fun _ => rfl) (fun _ => rfl)
      · exact upd_cases s.ns i _ (fun k y => y.got = (s.ns k).got) _ (fun _ => rfl)
          (fun _ => rfl)
  · exact upd_cases s.ns i _ (fun k y => NodeInv (net.node k) y) k (fun _ => hI.node k)
      (fun _ => hN)


/-! ## The invariant holds initially and is preserved -/

theorem chans_setChan_ne (st : DStore) (c c₂ : Nat) (c' : DChan) (h : c₂ ≠ c) :
    (st.setChan (rh c) c').chans (rh c₂) = st.chans (rh c₂) := by
  have : rh c₂ ≠ rh c := by simp only [rh]; omega
  simp [DStore.setChan, upd, this]

theorem chans_setChan_self (st : DStore) (c : Nat) (c' : DChan) :
    (st.setChan (rh c) c').chans (rh c) = c' := by
  simp [DStore.setChan, upd]

theorem init_chan (hwf : net.WF) (c : Nat) (hc : c < net.m) : ChanOK (init net) c := by
  have hw := hwf.wr_out c hc
  have hr := hwf.rd_inp c hc
  refine ⟨⟨.idle (if (net.node (net.wr c).1).inp = none then
    (net.node (net.wr c).1).T.flush (net.node (net.wr c).1).T.init else []), []⟩, ?_, ?_⟩
  · simp only [wOut, init, NSt.init, List.getElem?_map]
    rw [hw]
    rfl
  · simp only [init, NSt.init, hr, reduceCtorEq, ↓reduceIte]
    refine ⟨by simp [WInv, OS.view, initStore], by simp [RInv, initStore], fun hx => ?_,
      fun hx => ?_⟩ <;> rcases hx with hx | hx <;> cases hx

theorem init_node (i : Fin net.k) : NodeInv (net.node i) ((init net).ns i) := by
  refine ⟨rfl, by simp [init, NSt.init], fun o ho => ?_, fun hg => ?_, fun hi => ?_⟩
  · simp only [init, NSt.init, List.mem_map] at ho
    obtain ⟨_, -, rfl⟩ := ho
    by_cases hi : (net.node i).inp = none
    · simp [OInv, NSt.outSoFar, init, NSt.init, hi, NSt.flushedP, Tr.feed]
    · simp [OInv, NSt.outSoFar, init, NSt.init, hi, NSt.flushedP, Tr.feed]
  · by_cases hi : (net.node i).inp = none
    · simp [init, NSt.init, hi] at hg
    · simp [init, NSt.init, hi] at hg
  · simp [init, NSt.init, hi]

theorem inv_init (hwf : net.WF) : Inv net (init net) :=
  ⟨⟨rfl, rfl⟩, init_chan hwf, init_node⟩

theorem step_readBlk (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c n : Nat}
    {st' : DStore} (hinp : (net.node i).inp = some c) (hrd : (s.ns i).rd = .idle)
    (hds : dstep s.st (.streamRead (rh c) n) = some (st', .nat blocked)) :
    Inv net ⟨st', Function.update s.ns i { s.ns i with rd := .busy }⟩ := by
  obtain ⟨hm, c', hread, rfl⟩ := dstep_read hI.coh hds
  have hg := read_gone hread
  refine inv_input hwf hI i hinp (coh_setChan hI.coh _ _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _ (inv_readBlk _ _ (hI.node i) hrd)
    (fun _ => rfl) (fun o ho hinv => ?_)
  rw [chans_setChan_self]
  rw [hrd] at hinv
  rcases read_spec hinv hread with ⟨-, h⟩ | ⟨p, ys, hp, -⟩
  · exact h
  · cases hp

theorem step_readNow (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    {c n p : Nat} {ys : List Val} {st' : DStore} (hinp : (net.node i).inp = some c)
    (hrd : (s.ns i).rd = .idle) (hds : dstep s.st (.streamRead (rh c) n) = some (st', .read p ys)) :
    Inv net ⟨st', Function.update s.ns i ((s.ns i).onRead (net.node i).T p ys)⟩ := by
  obtain ⟨hm, c', hread, rfl⟩ := dstep_read hI.coh hds
  have hg := read_gone hread
  refine inv_input hwf hI i hinp (coh_setChan hI.coh _ _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _
    (inv_onRead _ _ _ _ (hI.node i) (Or.inl hrd))
    (fun j => by simp only [NSt.onRead]; exact map_view_push _ _ j) (fun o ho hinv => ?_)
  rw [chans_setChan_self]
  rw [hrd] at hinv
  rcases read_spec hinv hread with ⟨hp, -⟩ | ⟨p', ys', hp, h⟩
  · cases hp
  · obtain ⟨rfl, rfl⟩ := Res.read.inj hp
    simpa [NSt.onRead] using h

theorem step_waitIn (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    {e : Event} {st' : DStore} (hinp : (net.node i).inp = some c)
    (hw : DWait s.st (net.ws i) (rh c) st' e) :
    Inv net ⟨st', Function.update s.ns i ((s.ns i).onRead (net.node i).T e.payload e.items)⟩ := by
  obtain ⟨hm, c', htake, rfl⟩ := wait_rh hI.coh hw
  have hg := takeR_gone htake
  obtain ⟨-, hrd⟩ := hwf.inp_rd i c hinp
  obtain ⟨o, -, hinv⟩ := hI.chan c hm
  have hinv' : ChanInv o.st.view o.ack (s.ns i).rd (s.ns i).got (s.st.chans (rh c)) := hrd ▸ hinv
  refine inv_input hwf hI i hinp (coh_setChan hI.coh _ _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _
    (inv_onRead _ _ _ _ (hI.node i) (takeR_spec hinv' htake).1)
    (fun j => by simp only [NSt.onRead]; exact map_view_push _ _ j) (fun o ho hinv => ?_)
  rw [chans_setChan_self]
  simpa [NSt.onRead] using (takeR_spec hinv htake).2

theorem step_dropIn (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k) {c : Nat}
    {r : Res} {st' : DStore} (hinp : (net.node i).inp = some c)
    (hstop : (s.ns i).mayStop (net.node i).T) (hds : dstep s.st (.streamDropR (rh c)) = some (st', r)) :
    Inv net ⟨st', Function.update s.ns i ((s.ns i).stop (net.node i).T)⟩ := by
  obtain ⟨hm, c', hdrop, rfl⟩ := dstep_dropR hI.coh hds
  have hg := dropR_gone hdrop
  have hR0 : (s.ns i).rd = .idle ∨ (s.ns i).rd = .ended := by
    rcases hstop with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  refine inv_input hwf hI i hinp (coh_dropR hI.coh c hm _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _ (inv_stop _ _ (hI.node i) hstop)
    (fun j => by simp only [NSt.stop]; exact map_view_push _ _ j) (fun o ho hinv => ?_)
  have := dropR_spec hinv hR0 hdrop
  simpa [NSt.stop, DStore.remove, chans_setChan_self] using this

theorem step_write (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    {j c : Nat} {q a : List Val} {n r : Nat} {st' : DStore} (hout : (net.node i).outs[j]? = some c)
    (hx : (s.ns i).outs[j]? = some ⟨.idle q, a⟩)
    (hds : dstep s.st (.streamWrite (wh c) (q.take n)) = some (st', .nat r)) :
    Inv net ⟨st', Function.update s.ns i
      { s.ns i with outs := (s.ns i).outs.set j (Out.afterWrite (q.take n) (q.drop n) a r) }⟩ := by
  obtain ⟨hm, c', hwrite, rfl⟩ := dstep_write hI.coh hds
  have hg := write_gone hwrite
  refine inv_output hwf hI i hout (coh_setChan hI.coh _ _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _ (inv_write _ _ (hI.node i) j q a n r hx)
    (fun o ho hinv => ?_)
  rw [hx] at ho
  obtain rfl := Option.some.inj ho
  obtain ⟨r', hr', h⟩ := write_spec (rest := q.drop n) hinv hwrite
  obtain rfl := Res.nat.inj hr'
  rw [chans_setChan_self]
  exact h

theorem step_waitOut (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    {j c : Nat} {o : Out} {e : Event} {st' : DStore} (hout : (net.node i).outs[j]? = some c)
    (hx : (s.ns i).outs[j]? = some o) (hw : DWait s.st (net.ws i) (wh c) st' e) :
    Inv net ⟨st', Function.update s.ns i
      { s.ns i with outs := (s.ns i).outs.set j (o.onWrite e.payload) }⟩ := by
  obtain ⟨hm, c', htake, rfl⟩ := wait_wh hI.coh hw
  have hg := takeW_gone htake
  refine inv_output hwf hI i hout (coh_setChan hI.coh _ _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _ (inv_waitOut _ _ (hI.node i) j o _ hx)
    (fun o₁ ho hinv => ?_)
  rw [hx] at ho
  obtain rfl := Option.some.inj ho
  rw [chans_setChan_self]
  exact takeW_spec hinv htake

theorem step_dropOut (hwf : net.WF) {s : Sys net} (hI : Inv net s) (i : Fin net.k)
    {j c : Nat} {a : List Val} {d : Bool} {r : Res} {st' : DStore}
    (hout : (net.node i).outs[j]? = some c) (hrd : ∃ b, (s.ns i).rd = .gone b)
    (hx : (s.ns i).outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨
      (s.ns i).outs[j]? = some ⟨.dead, a⟩ ∧ d = true)
    (hds : dstep s.st (.streamDropW (wh c)) = some (st', r)) :
    Inv net ⟨st', Function.update s.ns i
      { s.ns i with outs := (s.ns i).outs.set j ⟨.closed d, a⟩ }⟩ := by
  obtain ⟨hm, c', hdrop, rfl⟩ := dstep_dropW hI.coh hds
  have hg := dropW_gone hdrop
  refine inv_output hwf hI i hout (coh_dropW hI.coh c hm _ hg.1 hg.2)
    (fun c₂ e => chans_setChan_ne _ _ _ _ e) _ (inv_dropOut _ _ (hI.node i) j a d hrd hx)
    (fun o ho hinv => ?_)
  have hWd : (o.st.view = .idle ∧ d = false ∨ o.st.view = .dead ∧ d = true) ∧ o.ack = a := by
    rcases hx with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ <;> rw [hx] at ho <;> obtain rfl := Option.some.inj ho
    · exact ⟨Or.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, rfl⟩
  have := dropW_spec hinv hWd.1 hdrop
  rw [hWd.2] at this
  simpa [DStore.remove, chans_setChan_self, OS.view] using this

/-- **Every step of every node preserves the invariant.** -/
theorem inv_step (hwf : net.WF) {s s' : Sys net} (hI : Inv net s) (h : Step net s s') :
    Inv net s' := by
  obtain ⟨i, hn⟩ := h
  cases hn with
  | readBlk hinp hrd _ _ hds => exact step_readBlk hwf hI i hinp hrd hds
  | readNow hinp hrd _ _ hds => exact step_readNow hwf hI i hinp hrd hds
  | waitIn hinp hw => exact step_waitIn hwf hI i hinp hw
  | dropIn hinp hstop hds => exact step_dropIn hwf hI i hinp hstop hds
  | write hout hx _ _ hds => exact step_write hwf hI i hout hx hds
  | waitOut hout hx hw => exact step_waitOut hwf hI i hout hx hw
  | dropOut hout hrd hx hds => exact step_dropOut hwf hI i hout hrd hx hds

/-- **The invariant holds in every reachable system.** -/
theorem reach_inv (hwf : net.WF) {s : Sys net} (h : Reach net s) : Inv net s := by
  induction h with
  | refl => exact inv_init hwf
  | tail _ hs ih => exact inv_step hwf ih hs

end Silmaril.Proofs.Wasm.Component.Streams.Net
