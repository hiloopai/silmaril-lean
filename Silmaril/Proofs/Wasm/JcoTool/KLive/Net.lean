module

public import Silmaril.Proofs.Wasm.JcoTool.KLive.Bound

/-!
# A network with generated modules has no deadlock

`mprogress`: in a reachable system of a topologically numbered network whose modules' kernels
fit, if some node has not finished (abstractly: its input dropped and its outputs closed), some
node or module can step. The argument is `Live.progress`'s, with modules:

* a node or module waiting for a read with nothing pending: its writer has a smaller index and has
  not finished (its writable end is open); the argument moves upstream (`mprog_main`);
* a module waiting for a write with nothing pending, or a node with a busy output: the reader's
  buffer is closed (`busy_open`), so the reader can act, or is itself a module waiting for a write;
  the argument moves downstream (`mprog_fwd`), to larger indices.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KLive

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event EventCode blocked)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net (Network NSt RV OS Out rh wh NStep Node Reach Sys)
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Wasm.Component.Streams.Kernel (KM KSt)
open Silmaril.Wasm.JcoTool.KCore
open Silmaril.Wasm.JcoTool.KDrop
open Silmaril.Wasm.JcoTool.KNet
open Silmaril.Wasm.JcoTool.KLive
open Silmaril.Proofs.Wasm.JcoTool.KCore
open Silmaril.Proofs.Wasm.JcoTool.KDrop
open Silmaril.Proofs.Wasm.JcoTool.KNet
open Silmaril.Proofs.Wasm.Component.Streams.Net (Coh Inv RInv WInv ChanInv wOut)
open Silmaril.Proofs.Wasm.Component.Streams.Live (StPos chan_in chan_out busy_open input_of_live
  wbuf_ne_nil read_ok write_ok dropR_ok dropW_ok dstep_read_eq dstep_write_eq dstep_dropR_eq
  dstep_dropW_eq wait_rh_ok wait_wh_ok)

/-- **The data of the progress argument**: a reachable system `m` with modules, an abstraction
`s` of it, and the network's invariants. -/
structure Ctx (M : MNet) (m : MSys M.net) (s : Sys M.net) : Prop where
  ok : M.OK
  topo : M.net.Topo
  fits : ∀ i k N, M.gen i = some (k, N) → KFits k N
  abs : Abs M m s
  inv : Inv M.net s
  pos : StPos s.st
  rb : RB M m
  good : Silmaril.Wasm.Component.Streams.Cancel.GoodS m.st

/-! ## Node steps -/

/-- Node `j` of the network can step. -/
def NEn (M : MNet) (s : Sys M.net) (j : Fin M.net.k) : Prop :=
  ∃ st' x', NStep (M.net.node j) (M.net.ws j) s.st (s.ns j) st' x'

theorem en_of_nen {M : MNet} {m : MSys M.net} {s : Sys M.net} (hA : Abs M m s) {j : Fin M.net.k}
    (hg : M.gen j = none) (h : NEn M s j) : MEnabled M m := by
  obtain ⟨st', x', hn⟩ := h
  have hn' : NStep (M.net.node j) (M.net.ws j) m.st (m.ns j) st' x' := by
    rw [← hA.1, ← (hA.2 j).1 hg]; exact hn
  exact ⟨_, MStep.node j hg hn'⟩

theorem en_of_mod {M : MNet} {m : MSys M.net} {i : Fin M.net.k} {k : KM} {N : Nat}
    (hg : M.gen i = some (k, N)) (h : CanStep k N m.st (m.ms i)) : MEnabled M m := by
  obtain ⟨st', ms', hd⟩ := h
  exact ⟨_, MStep.mod i hg hd⟩

theorem nen_input_idle {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {c : Nat} (hinp : (M.net.node i).inp = some c) (hrd : (s.ns i).rd = .idle) : NEn M s i := by
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hI hinp
  rw [hrd] at hinv
  obtain ⟨-, hr, hst, -, -, hev⟩ := hinv.2.1
  by_cases hd : (M.net.node i).T.done (s.ns i).s = true
  · obtain ⟨c', hdrop⟩ := dropR_ok hr (by rw [hst]; decide)
    exact ⟨_, _, NStep.dropIn hinp (Or.inr ⟨hrd, Or.inl hd⟩) (dstep_dropR_eq hI.coh hm hr hdrop)⟩
  · have hev' : (s.st.chans (rh c)).w.gone = true → (s.st.chans (rh c)).r.ev.isSome := by
      intro hw; rw [hev, hw]; rfl
    obtain ⟨c', res, hread, hres⟩ := read_ok (n := 1) hr hst hev' (wbuf_ne_nil hinv.1 hr) Nat.one_pos
    have hds := dstep_read_eq hI.coh hm hr hread
    have hd' : (M.net.node i).T.done (s.ns i).s = false := by simpa using hd
    rcases hres with rfl | ⟨p, ys, rfl⟩
    · exact ⟨_, _, NStep.readBlk hinp hrd hd' Nat.one_pos hds⟩
    · exact ⟨_, _, NStep.readNow hinp hrd hd' Nat.one_pos hds⟩

theorem nen_waitIn {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {c : Nat} (hinp : (M.net.node i).inp = some c) (hr : (s.st.chans (rh c)).r.gone = false)
    (hev : (s.st.chans (rh c)).r.ev.isSome) : NEn M s i := by
  obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
  obtain ⟨st', e, hw⟩ := wait_rh_ok hI.coh hm hr hev
  rw [hrd] at hw
  exact ⟨_, _, NStep.waitIn hinp hw⟩

theorem nen_ended {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {c : Nat} (hinp : (M.net.node i).inp = some c) (hrd : (s.ns i).rd = .ended) : NEn M s i := by
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hI hinp
  rw [hrd] at hinv
  obtain ⟨-, hr, hst, -⟩ := hinv.2.1
  obtain ⟨c', hdrop⟩ := dropR_ok hr (by rw [hst]; decide)
  exact ⟨_, _, NStep.dropIn hinp (Or.inl hrd) (dstep_dropR_eq hI.coh hm hr hdrop)⟩

theorem nen_write {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {j c : Nat} (hout : (M.net.node i).outs[j]? = some c) {q a : List Val}
    (hj : (s.ns i).outs[j]? = some ⟨.idle q, a⟩) (hq : q ≠ []) : NEn M s i := by
  obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
  obtain ⟨hw, hst, -, -, hev⟩ := hinv.1
  have hev' : (s.st.chans (rh c)).r.gone = true → (s.st.chans (rh c)).w.ev.isSome := by
    intro hr; rw [hev, hr]; rfl
  have hx : q.take q.length ≠ [] := by simpa using hq
  obtain ⟨c', r, hwr⟩ := write_ok hw hst hev' hx
  exact ⟨_, _, NStep.write hout hj (List.length_pos_iff.2 hq) (le_refl _)
    (dstep_write_eq hI.coh hm hw hwr)⟩

theorem nen_dropOut {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {j c : Nat} (hout : (M.net.node i).outs[j]? = some c) (hrd : ∃ b, (s.ns i).rd = .gone b)
    {a : List Val} {d : Bool} (hj : (s.ns i).outs[j]? = some ⟨.idle [], a⟩ ∧ d = false ∨
      (s.ns i).outs[j]? = some ⟨.dead, a⟩ ∧ d = true) : NEn M s i := by
  have hok : c < M.net.m ∧ (s.st.chans (rh c)).w.gone = false ∧ (s.st.chans (rh c)).w.st ≠ .copying := by
    rcases hj with ⟨hj, -⟩ | ⟨hj, -⟩
    · obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
      exact ⟨hm, hinv.1.1, by rw [hinv.1.2.1]; decide⟩
    · obtain ⟨hm, hinv⟩ := chan_out hwf hI hout hj
      exact ⟨hm, hinv.1.1, by rw [hinv.1.2.1]; decide⟩
  obtain ⟨c', hdrop⟩ := dropW_ok hok.2.1 hok.2.2
  exact ⟨_, _, NStep.dropOut hout hrd hj (dstep_dropW_eq hI.coh hok.1 hok.2.1 hdrop)⟩

theorem nen_waitOut {M : MNet} {s : Sys M.net} (hI : Inv M.net s) (hwf : M.net.WF) (i : Fin M.net.k)
    {j c : Nat} (hout : (M.net.node i).outs[j]? = some c) {o : Silmaril.Wasm.Component.Streams.Net.Out}
    (hj : (s.ns i).outs[j]? = some o)
    (hw : (s.st.chans (rh c)).w.gone = false) (hev : (s.st.chans (rh c)).w.ev.isSome) : NEn M s i := by
  obtain ⟨hm, hwr⟩ := hwf.out_wr i j c hout
  obtain ⟨st', e, hwt⟩ := wait_wh_ok hI.coh hm hw hev
  rw [hwr] at hwt
  exact ⟨_, _, NStep.waitOut hout hj hwt⟩

/-! ## Modules in the system -/

theorem cast_fields {Nd : Node} {k : KM} {c c' : Nat} (h : Nd = Silmaril.Wasm.JcoTool.KDrop.node k c c')
    (x : NSt Nd.σ) :
    (cast (congrArg (fun N : Node => NSt N.σ) h) x).rd = x.rd ∧
      (cast (congrArg (fun N : Node => NSt N.σ) h) x).got = x.got ∧
      (cast (congrArg (fun N : Node => NSt N.σ) h) x).outs = x.outs ∧
      (x.s = (Nd.T.feed Nd.T.init x.got).1 →
        (cast (congrArg (fun N : Node => NSt N.σ) h) x).s =
          ((trV k).feed (trV k).init (cast (congrArg (fun N : Node => NSt N.σ) h) x).got).1) := by
  subst h
  exact ⟨rfl, rfl, rfl, id⟩

theorem finished_of_exit {r w ws : Nat} {ms : MS} {x : NSt KSt} (hR : RelD r w ws ms x)
    (hex : ms.mode = .exited) : x.Finished := by
  unfold RelD at hR
  simp only [hex, ↓reduceIte] at hR
  obtain ⟨b, hb, d, a, ha⟩ := hR
  refine ⟨⟨b, hb⟩, fun o ho => ?_⟩
  rw [ha] at ho
  rw [List.mem_singleton.1 ho]
  exact ⟨d, rfl⟩

/-- **The environment of module `i`**, from the network's invariants. -/
theorem mod_env {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    {k : KM} {N c c' : Nat} (hg : M.gen i = some (k, N))
    (hn : M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c') {y : NSt KSt}
    (hy : y.rd = (s.ns i).rd ∧ y.got = (s.ns i).got ∧ y.outs = (s.ns i).outs) :
    Env M.net m.st c c' (M.net.ws i) N y := by
  have hwf := hC.ok.wf
  have hst : s.st = m.st := hC.abs.1
  have hinp : (M.net.node i).inp = some c := inp_of hn
  have hout : (M.net.node i).outs[0]? = some c' := by rw [hn]; rfl
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hC.inv hinp
  obtain ⟨hm', hwr⟩ := hwf.out_wr i 0 c' hout
  have hrd : M.net.rd c = i := (hwf.inp_rd i c hinp).2
  have hbig := hC.ok.ws
  refine ⟨hst ▸ hC.inv.coh, hm, hm', by rw [hrd], by rw [hwr], ws_lt hC.ok i, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [rh, wh, M32]; omega
  · rw [hy.1, hy.2.1, ← hst]; exact hinv.2.1
  · intro o' ho'
    rw [hy.2.2] at ho'
    obtain ⟨-, hinv'⟩ := chan_out hwf hC.inv hout ho'
    rw [← hst]; exact hinv'.1
  · exact (hC.good (rh c)).1
  · have hb := hC.rb i k N c c' hg hn
    simp only [cb] at hb
    omega

/-- **A module of the system**: it can step, or waits for a read, or for a write, with nothing
pending. -/
theorem mod_case {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    {k : KM} {N : Nat} (hg : M.gen i = some (k, N)) (hnf : ¬ (s.ns i).Finished) :
    ∃ c c', M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c c' ∧
      (MEnabled M m ∨ ((s.ns i).rd = .busy ∧ (m.st.chans (rh c)).r.ev = none) ∨
        (∃ xs q a, (s.ns i).outs = [⟨.busy xs q, a⟩] ∧ (m.st.chans (rh c')).w.ev = none)) := by
  obtain ⟨c, c', hn, hR⟩ := (hC.abs.2 i).2 k N hg
  obtain ⟨hy1, hy2, hy3, hy4⟩ := cast_fields hn (s.ns i)
  refine ⟨c, c', hn, ?_⟩
  have hex : (m.ms i).mode ≠ .exited := by
    intro he
    obtain ⟨⟨b, hb⟩, ho⟩ := finished_of_exit hR he
    exact hnf ⟨⟨b, hy1 ▸ hb⟩, fun o hmem => ho o (hy3 ▸ hmem)⟩
  have hE := mod_env hC hg hn ⟨hy1, hy2, hy3⟩
  have hks := hy4 (hC.inv.node i).hs
  rcases mod_progress (hC.ok.size i k N hg) (hC.fits i k N hg) hR hex hE hks with h | ⟨h1, h2⟩ | ⟨xs, q, a, h1, h2⟩
  · exact .inl (en_of_mod hg h)
  · exact .inr (.inl ⟨hy1 ▸ h1, h2⟩)
  · exact .inr (.inr ⟨xs, q, a, hy3 ▸ h1, h2⟩)

/-! ## Upstream and downstream -/

/-- The writer of a stream whose writable end is open has not finished. -/
theorem writer_unfinished {M : MNet} {s : Sys M.net} (hI : Inv M.net s) {c : Nat} (hm : c < M.net.m)
    (hw : (s.st.chans (rh c)).w.gone = false) : ¬ (s.ns (M.net.wr c).1).Finished := by
  intro hf
  obtain ⟨o, ho, hinv⟩ := hI.chan c hm
  have hmem : o ∈ (s.ns (M.net.wr c).1).outs := List.mem_of_getElem? ho
  obtain ⟨d, hd⟩ := hf.2 o hmem
  have hW := hinv.1
  rw [hd] at hW
  exact absurd hW.1 (by simp [hw])

/-- **A busy input with nothing pending**: its writer has a smaller index and has not finished. -/
theorem busy_in {M : MNet} {s : Sys M.net} (hwf : M.net.WF) (htopo : M.net.Topo) (hI : Inv M.net s)
    {i : Fin M.net.k} {c : Nat} (hinp : (M.net.node i).inp = some c) (hrd : (s.ns i).rd = .busy)
    (hev : (s.st.chans (rh c)).r.ev = none) :
    ∃ w : Fin M.net.k, w.val < i.val ∧ ¬ (s.ns w).Finished := by
  obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hI hinp
  have hR : RInv .busy (s.ns i).got (s.st.chans (rh c)) := hrd ▸ hinv.2.1
  have hw : (s.st.chans (rh c)).w.gone = false := by
    cases h : (s.st.chans (rh c)).w.gone
    · rfl
    · have := hR.2.2.2.2.2.2.2 h; rw [hev] at this; cases this
  have hlt : (M.net.wr c).1.val < i.val := (hwf.inp_rd i c hinp).2 ▸ htopo c hm
  exact ⟨_, hlt, writer_unfinished hI hm hw⟩

/-- Downstream, a node reader: it reads, drops its input, or takes its read's event. -/
theorem fwd_node {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {c : Nat}
    (hm : c < M.net.m) (hg : M.gen (M.net.rd c) = none) (hr : (m.st.chans (rh c)).r.gone = false)
    (hrc : (m.st.chans (rh c)).rcap = none) (hw : (m.st.chans (rh c)).w.gone = false) :
    MEnabled M m := by
  have hwf : M.net.WF := hC.ok.wf
  have hst : s.st = m.st := hC.abs.1
  have hinp : (M.net.node (M.net.rd c)).inp = some c := hwf.rd_inp c hm
  obtain ⟨-, o, -, hinv⟩ := chan_in hwf hC.inv hinp
  have hR : RInv (s.ns (M.net.rd c)).rd (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hinv.2.1
  cases hrd : (s.ns (M.net.rd c)).rd with
  | idle => exact en_of_nen hC.abs hg (nen_input_idle hC.inv hwf _ hinp hrd)
  | busy =>
    have hRb : RInv .busy (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hrd ▸ hR
    exact en_of_nen hC.abs hg (nen_waitIn hC.inv hwf _ hinp (hst ▸ hr)
      (hRb.2.2.2.2.2.2.1 (hst ▸ hw) (hst ▸ hrc)))
  | ended =>
    have hRe : RInv .ended (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hrd ▸ hR
    exact absurd hRe.2.2.2.1 (by rw [hst]; simp [hw])
  | gone b =>
    have hRg : RInv (.gone b) (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hrd ▸ hR
    exact absurd hRg.2.1 (by rw [hst]; simp [hr])

/-- The reader of an open stream has not dropped its input. -/
theorem reader_live {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {c : Nat}
    (hm : c < M.net.m) (hr : (m.st.chans (rh c)).r.gone = false) : ¬ (s.ns (M.net.rd c)).Finished := by
  intro hf
  obtain ⟨b, hb⟩ := hf.1
  obtain ⟨-, o, -, hinv⟩ := chan_in hC.ok.wf hC.inv (hC.ok.wf.rd_inp c hm)
  have hRg : RInv (.gone b) (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hb ▸ hinv.2.1
  exact absurd hRg.2.1 (by rw [hC.abs.1]; simp [hr])

/-- A module waiting for a write with nothing pending: the next stream downstream is open, its
reader's buffer closed. -/
theorem out_next {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    {k : KM} {c₁ c₂ : Nat} (hn : M.net.node i = Silmaril.Wasm.JcoTool.KDrop.node k c₁ c₂)
    {xs q a : List Val} (hout : (s.ns i).outs = [⟨.busy xs q, a⟩])
    (hev : (m.st.chans (rh c₂)).w.ev = none) :
    c₂ < M.net.m ∧ i.val < (M.net.rd c₂).val ∧ (m.st.chans (rh c₂)).r.gone = false ∧
      (m.st.chans (rh c₂)).rcap = none ∧ (m.st.chans (rh c₂)).w.gone = false := by
  have hst : s.st = m.st := hC.abs.1
  have hout₂ : (M.net.node i).outs[0]? = some c₂ := by rw [hn]; rfl
  have hj : (s.ns i).outs[0]? = some ⟨.busy xs q, a⟩ := by rw [hout]; rfl
  obtain ⟨hm₂, hinv₂⟩ := chan_out hC.ok.wf hC.inv hout₂ hj
  have hW : WInv (.busy xs) a (s.st.chans (rh c₂)) := hinv₂.1
  obtain ⟨hr₂, hrc₂⟩ := busy_open hW (hC.pos _) (by rw [hst, hev]; rfl)
  have htop : ((M.net.wr c₂).1).val < (M.net.rd c₂).val := hC.topo c₂ hm₂
  have hlt : i.val < (M.net.rd c₂).val := by rwa [(hC.ok.wf.out_wr _ 0 c₂ hout₂).2] at htop
  exact ⟨hm₂, hlt, hst ▸ hr₂, hst ▸ hrc₂, hst ▸ hW.1⟩

/-- Downstream, a module reader: it steps, or waits for a write, and the argument moves on. -/
theorem fwd_mod {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {c : Nat}
    (hm : c < M.net.m) {k : KM} {N : Nat} (hg : M.gen (M.net.rd c) = some (k, N))
    (hr : (m.st.chans (rh c)).r.gone = false) (hrc : (m.st.chans (rh c)).rcap = none)
    (hw : (m.st.chans (rh c)).w.gone = false)
    (ih : ∀ c₂, c₂ < M.net.m → (M.net.rd c).val < (M.net.rd c₂).val →
      (m.st.chans (rh c₂)).r.gone = false → (m.st.chans (rh c₂)).rcap = none →
      (m.st.chans (rh c₂)).w.gone = false → MEnabled M m) : MEnabled M m := by
  have hst : s.st = m.st := hC.abs.1
  have hinp : (M.net.node (M.net.rd c)).inp = some c := hC.ok.wf.rd_inp c hm
  obtain ⟨c₁, c₂, hn₁, hcase⟩ := mod_case hC hg (reader_live hC hm hr)
  have hcc : c₁ = c := Option.some.inj ((inp_of hn₁).symm.trans hinp)
  rcases hcase with h | ⟨hrd, hev⟩ | ⟨xs, q, a, hout, hev⟩
  · exact h
  · obtain ⟨-, o, -, hinv⟩ := chan_in hC.ok.wf hC.inv hinp
    have hRb : RInv .busy (s.ns (M.net.rd c)).got (s.st.chans (rh c)) := hrd ▸ hinv.2.1
    have hs : (s.st.chans (rh c)).r.ev.isSome := hRb.2.2.2.2.2.2.1 (hst ▸ hw) (hst ▸ hrc)
    rw [hst, ← hcc, hev] at hs
    cases hs
  · obtain ⟨hm₂, hlt, hr₂, hrc₂, hw₂⟩ := out_next hC hn₁ hout hev
    exact ih c₂ hm₂ hlt hr₂ hrc₂ hw₂

/-- **Downstream**: the reader of a stream whose writer waits on an open buffer, the reader's
buffer being closed, can act, or the argument moves to a larger index. -/
theorem mprog_fwd {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) :
    ∀ (n c : Nat), c < M.net.m → M.net.k - (M.net.rd c).val = n →
      (m.st.chans (rh c)).r.gone = false → (m.st.chans (rh c)).rcap = none →
      (m.st.chans (rh c)).w.gone = false → MEnabled M m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hm hn hr hrc hw
    cases hg : M.gen (M.net.rd c) with
    | none => exact fwd_node hC hm hg hr hrc hw
    | some kN =>
      exact fwd_mod hC hm hg hr hrc hw fun c₂ hm₂ hlt => ih _
        (by have := (M.net.rd c₂).isLt; omega) c₂ hm₂ rfl

/-- A busy output of node `i` with nothing pending: downstream. -/
theorem busy_out {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    {j c : Nat} (hout : (M.net.node i).outs[j]? = some c) {xs q a : List Val}
    (hj : (s.ns i).outs[j]? = some ⟨.busy xs q, a⟩) (hev : (m.st.chans (rh c)).w.ev = none) :
    MEnabled M m := by
  have hst : s.st = m.st := hC.abs.1
  obtain ⟨hm, hinv⟩ := chan_out hC.ok.wf hC.inv hout hj
  have hW : WInv (.busy xs) a (s.st.chans (rh c)) := hinv.1
  obtain ⟨hr, hrc⟩ := busy_open hW (hC.pos _) (by rw [hst, hev]; rfl)
  exact mprog_fwd hC _ c hm rfl (hst ▸ hr) (hst ▸ hrc) (hst ▸ hW.1)

/-- **A network node that has dropped its input** and not finished: one of its outputs acts. -/
theorem node_gone {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    (hg : M.gen i = none) {b : Bool} (hrd : (s.ns i).rd = .gone b) (hnf : ¬ (s.ns i).Finished) :
    MEnabled M m := by
  have hwf := hC.ok.wf
  have hst : s.st = m.st := hC.abs.1
  have hgn : ∃ b, (s.ns i).rd = .gone b := ⟨b, hrd⟩
  have hno : ¬ ∀ o ∈ (s.ns i).outs, ∃ d, o.st = .closed d := fun h => hnf ⟨hgn, h⟩
  obtain ⟨o, hmem, hnc⟩ : ∃ o ∈ (s.ns i).outs, ∀ d, o.st ≠ .closed d := by simpa using hno
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  have hlen : j < (M.net.node i).outs.length := by
    rw [← (hC.inv.node i).len]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨c, hout⟩ : ∃ c, (M.net.node i).outs[j]? = some c := ⟨_, List.getElem?_eq_getElem hlen⟩
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    by_cases hq : q = []
    · subst hq
      exact en_of_nen hC.abs hg (nen_dropOut hC.inv hwf i hout hgn (d := false) (.inl ⟨hj, rfl⟩))
    · exact en_of_nen hC.abs hg (nen_write hC.inv hwf i hout hj hq)
  | dead => exact en_of_nen hC.abs hg (nen_dropOut hC.inv hwf i hout hgn (d := true) (.inr ⟨hj, rfl⟩))
  | closed d => exact absurd rfl (hnc d)
  | busy xs q =>
    obtain ⟨hm, hinv⟩ := chan_out hwf hC.inv hout hj
    cases hev : (m.st.chans (rh c)).w.ev with
    | none => exact busy_out hC hout hj hev
    | some p =>
      exact en_of_nen hC.abs hg (nen_waitOut hC.inv hwf i hout hj hinv.1.1 (by rw [hst, hev]; rfl))

/-- Upstream, a network node. -/
theorem main_node {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    (hg : M.gen i = none) (hnf : ¬ (s.ns i).Finished)
    (ih : ∀ w : Fin M.net.k, w.val < i.val → ¬ (s.ns w).Finished → MEnabled M m) : MEnabled M m := by
  have hwf : M.net.WF := hC.ok.wf
  cases hrd : (s.ns i).rd with
  | idle =>
    obtain ⟨c, hinp⟩ := input_of_live hC.inv i (by simp [hrd])
    exact en_of_nen hC.abs hg (nen_input_idle hC.inv hwf i hinp hrd)
  | busy =>
    obtain ⟨c, hinp⟩ := input_of_live hC.inv i (by simp [hrd])
    obtain ⟨hm, o, -, hinv⟩ := chan_in hwf hC.inv hinp
    have hRb : RInv .busy (s.ns i).got (s.st.chans (rh c)) := hrd ▸ hinv.2.1
    cases hev : (s.st.chans (rh c)).r.ev with
    | some p => exact en_of_nen hC.abs hg (nen_waitIn hC.inv hwf i hinp hRb.2.1 (by rw [hev]; rfl))
    | none =>
      obtain ⟨w, hlt, hwnf⟩ := busy_in hwf hC.topo hC.inv hinp hrd hev
      exact ih w hlt hwnf
  | ended =>
    obtain ⟨c, hinp⟩ := input_of_live hC.inv i (by simp [hrd])
    exact en_of_nen hC.abs hg (nen_ended hC.inv hwf i hinp hrd)
  | gone b => exact node_gone hC hg hrd hnf

/-- Upstream, a module. -/
theorem main_mod {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) {i : Fin M.net.k}
    {k : KM} {N : Nat} (hg : M.gen i = some (k, N)) (hnf : ¬ (s.ns i).Finished)
    (ih : ∀ w : Fin M.net.k, w.val < i.val → ¬ (s.ns w).Finished → MEnabled M m) : MEnabled M m := by
  have hst : s.st = m.st := hC.abs.1
  obtain ⟨c, c', hn, hcase⟩ := mod_case hC hg hnf
  rcases hcase with h | ⟨hrd, hev⟩ | ⟨xs, q, a, hout, hev⟩
  · exact h
  · obtain ⟨w, hlt, hwnf⟩ := busy_in hC.ok.wf hC.topo hC.inv (inp_of hn) hrd (hst ▸ hev)
    exact ih w hlt hwnf
  · have hout' : (M.net.node i).outs[0]? = some c' := by rw [hn]; rfl
    exact busy_out hC hout' (by rw [hout]; rfl) hev

/-- **Upstream**: if node `i` has not finished, some node or module can step. -/
theorem mprog_main {M : MNet} {m : MSys M.net} {s : Sys M.net} (hC : Ctx M m s) :
    ∀ (n : Nat) (i : Fin M.net.k), i.val = n → ¬ (s.ns i).Finished → MEnabled M m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hnf
    have ih' : ∀ w : Fin M.net.k, w.val < i.val → ¬ (s.ns w).Finished → MEnabled M m :=
      fun w hlt hwnf => ih _ (hi ▸ hlt) w rfl hwnf
    cases hg : M.gen i with
    | none => exact main_node hC hg hnf ih'
    | some kN => exact main_mod hC hg hnf ih'

end Silmaril.Proofs.Wasm.JcoTool.KLive
