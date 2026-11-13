module

public import Silmaril.Proofs.Wasm.Component.Streams.Callback.Abs
public import Silmaril.Proofs.Wasm.Component.Streams.Live.Main
public import Silmaril.Wasm.Component.Streams.Pipes.Thms

/-!
# The driver loop refines the node program

`cb_sim`: in a pipe whose transformer is the generated module, if the system the module's state
stands for (`CSys.abs`) is a reachable system of `Pipes.pipe xs T`, every step of the module is a
step of node `1` of that pipe on the abstract state (`NStep`), or leaves the abstract state and the
store as they were. The facts about the built-ins' results that the module relies on (a read
result is `BLOCKED` or items; a write or write event acknowledges at most what was offered; an
event on an idle end is `DROPPED` with no items) come from the protocol invariant of the abstract
system.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Res Event blocked packCopy CopyResult)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Pipes
open Silmaril.Wasm.Component.Streams.Callback
open Silmaril.Proofs.Wasm.Component.Streams.Net
open Silmaril.Proofs.Wasm.Component.Streams.Live

variable {σ : Type} {T : Tr σ Val Val}

/-! ## What the built-ins report -/

/-- A write by an idle writer acknowledges at most the items offered. -/
theorem write_count_le {ack xs : List Val} {c c' : DChan} {r : Nat} (hW : WInv .idle ack c)
    (h : c.write xs = some (c', .nat r)) (hr : r ≠ blocked) : count r ≤ xs.length := by
  obtain ⟨hwg, hwst, -, -, hev⟩ := hW
  unfold DChan.write at h
  split_ifs at h with h1 h2
  · have hev' : c.w.ev = some 0 := by simpa [h2] using hev
    simp only [hev', Option.some.injEq, Prod.mk.injEq, Res.nat.injEq] at h
    rw [← h.2, count_packCopy]
    exact Nat.zero_le _
  · split at h
    · exact absurd (Res.nat.inj (Prod.mk.inj (Option.some.inj h)).2).symm hr
    · rename_i n _
      have h3 := Res.nat.inj (Prod.mk.inj (Option.some.inj h)).2
      rw [← h3, count_packCopy]
      exact Nat.min_le_right _ _

/-- A write event acknowledges at most the items offered. -/
theorem takeW_count_le {ack xs : List Val} {c c' : DChan} {p : Nat} (hW : WInv (.busy xs) ack c)
    (h : c.takeW = some (c', p)) : count p ≤ xs.length := by
  obtain ⟨q, hq, rfl⟩ := takeW_some h
  have hwp : c.wp = q := by simp [DChan.wp, hq]
  have hle : c.wp ≤ xs.length := hW.2.2.2.1
  split <;> rw [count_packCopy] <;> omega

/-- An event on an idle readable end is `DROPPED`, with no items. -/
theorem takeR_idle {got : List Val} {c c' : DChan} {p : Nat} {ys : List Val}
    (hR : RInv .idle got c) (h : c.takeR = some (c', p, ys)) : status p ≠ 0 ∧ ys = [] := by
  obtain ⟨q, hq, rfl, rfl⟩ := takeR_some h
  have hev : c.r.ev = (if c.w.gone then some 0 else none) := hR.2.2.2.2.2
  have hw : c.w.gone = true := by cases hg : c.w.gone <;> simp_all
  refine ⟨?_, hR.2.2.2.2.1⟩
  simp [hw, status_packCopy, CopyResult.toNat]

/-! ## The abstract system -/

theorem abs_ns1 (xs : List Val) (c : CSys σ) : (CSys.abs xs T c).ns 1 = c.cb.abs T := rfl

variable {xs : List Val} {batch wmax : Nat}

/-- The node of the pipe that the module implements. -/
abbrev N1 (xs : List Val) (T : Tr σ Val Val) : Node := (pipe xs T).node 1

theorem out_abs {c : CB σ} (hpc : c.pc ≠ .exit) (hd : c.dead = false) (hw : c.wpend = false) :
    (c.abs T).outs[0]? = some ⟨.idle (c.out ++ c.fl T), c.ack⟩ := by
  simp [CB.abs, CB.absOut, hpc, hd, hw]

/-! ## Steps that call a built-in on the output -/

theorem sim_write {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) {st' : DStore}
    {res : Nat} (hpc : c.cb.pc = .run) (hwp : c.cb.wpend = false) (hd : c.cb.dead = false)
    (hne : c.cb.out ≠ [])
    (hds : dstep c.st (.streamWrite (wh 1) (c.cb.out.take (writeLen wmax c.cb.out.length))) =
      some (st', .nat res)) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      ((if res = blocked then
          ({ c.cb with pc := .wait, wpend := true, wl := writeLen wmax c.cb.out.length } : CB σ)
        else c.cb.onwrite res).abs T : NSt σ) := by
  have hn : writeLen wmax c.cb.out.length ≤ c.cb.out.length := writeLen_le _ _
  have hn0 : 0 < writeLen wmax c.cb.out.length := writeLen_pos (List.length_pos_iff.2 hne)
  obtain ⟨h1, h2⟩ := take_out_fl (T := T) c.cb hn
  have hj := out_abs (T := T) (by simp [hpc]) hd hwp
  have hds' : dstep c.st (.streamWrite (wh 1)
      ((c.cb.out ++ c.cb.fl T).take (writeLen wmax c.cb.out.length))) = some (st', .nat res) := by
    rw [h1]; exact hds
  have hstep := NStep.write (N := N1 xs T) (ws := (pipe xs T).ws 1) (j := 0) (c := 1) rfl hj hn0
    (by simp; omega) hds'
  split
  · rename_i hr
    subst hr
    show NStep (N1 xs T) _ _ _ _
      ((({ c.cb with pc := .wait, wpend := true, wl := writeLen wmax c.cb.out.length } :
        CB σ)).abs T : NSt σ)
    rw [abs_write_blocked hd hn]
    exact hstep
  · rename_i hr
    have hI := reach_inv (pipe_wf xs T) hR
    obtain ⟨-, hinv⟩ := chan_out (pipe_wf xs T) hI (i := 1) (j := 0) (c := 1) rfl hj
    obtain ⟨-, c', hwr, -⟩ := dstep_write hI.coh hds'
    have hk : count res ≤ writeLen wmax c.cb.out.length := by
      have := write_count_le hinv.1 hwr hr
      rwa [h1, List.length_take, Nat.min_eq_left hn] at this
    rw [abs_write_now hpc hd hwp hn hr hk]
    exact hstep

theorem sim_dropW {c : CSys σ} {st' : DStore} {res : Res}
    (hpc : c.cb.pc = .run) (hwp : c.cb.wpend = false) (h0 : c.cb.dead = true ∨ c.cb.out = [])
    (hfd : c.cb.flushed = true ∨ c.cb.dead = true) (hrd : c.cb.rdropped = true)
    (hds : dstep c.st (.streamDropW (wh 1)) = some (st', res)) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      (({ c.cb with pc := .exit, out := [] } : CB σ).abs T : NSt σ) := by
  have hg : ∃ b, (c.cb.abs T).rd = .gone b := ⟨c.cb.ended, by simp [CB.abs, hrd]⟩
  have hx : (c.cb.abs T).outs[0]? = some ⟨.idle [], c.cb.ack⟩ ∧ c.cb.dead = false ∨
      (c.cb.abs T).outs[0]? = some ⟨.dead, c.cb.ack⟩ ∧ c.cb.dead = true := by
    cases hd : c.cb.dead
    · have hout : c.cb.out = [] := by simpa [hd] using h0
      have hf : c.cb.flushed = true := by simpa [hd] using hfd
      left
      simp [CB.abs, CB.absOut, CB.fl, hpc, hd, hwp, hout, hf]
    · right
      simp [CB.abs, CB.absOut, hpc, hd]
  show NStep (N1 xs T) _ _ _ _ ((({ c.cb with pc := .exit, out := [] } : CB σ)).abs T : NSt σ)
  rw [abs_dropW]
  exact NStep.dropOut (j := 0) (c := 1) rfl hg hx hds

theorem sim_evOut {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) (h : c.cb.Inv T)
    {st' : DStore} {e : Event} (hpc : c.cb.pc = .wait)
    (hw : DWait c.st ((pipe xs T).ws 1) (wh 1) st' e) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      ((if c.cb.wpend then ({ c.cb with pc := .run, wpend := false } : CB σ).onwrite e.payload
        else ({ c.cb with pc := .run, dead := true } : CB σ).stopReading).abs T : NSt σ) := by
  have hI := reach_inv (pipe_wf xs T) hR
  have hj : (c.cb.abs T).outs[0]? = some (c.cb.absOut T) := rfl
  obtain ⟨-, hinv⟩ := chan_out (pipe_wf xs T) hI (i := 1) (j := 0) (c := 1) rfl hj
  obtain ⟨-, c', htake, -⟩ := wait_wh hI.coh hw
  have hstep := NStep.waitOut (N := N1 xs T) (j := 0) (c := 1) rfl hj hw
  obtain ⟨hres, hres0⟩ := takeW_res (reach_pos hR _) hinv.1 htake
  have hpc' : c.cb.pc ≠ .exit := by simp [hpc]
  split
  · rename_i hwp
    obtain ⟨hl, hd, -⟩ := h.i7 hwp
    have hW : WInv (.busy (c.cb.out.take c.cb.wl)) c.cb.ack
        ((CSys.abs xs T c).st.chans (rh 1)) := by
      have := hinv.1
      simp only [CB.absOut, hpc', hd, hwp, ↓reduceIte, Bool.false_eq_true, OS.view] at this
      exact this
    have hk : count e.payload ≤ c.cb.wl := by
      have := takeW_count_le hW htake
      rwa [List.length_take, Nat.min_eq_left hl] at this
    show NStep (N1 xs T) _ _ _ _
      (((({ c.cb with pc := .run, wpend := false } : CB σ)).onwrite e.payload).abs T : NSt σ)
    rw [abs_evOut_busy hpc hwp hd hk hl]
    exact hstep
  · rename_i hwp
    have hwp' : c.cb.wpend = false := by simpa using hwp
    have hs : status e.payload ≠ 0 := by
      intro hs
      obtain ⟨ys, hy, -⟩ := hres0 hs
      by_cases hd : c.cb.dead = true
      · simp [CB.absOut, hpc', hd, OS.view] at hy
      · simp [CB.absOut, hpc', hd, hwp', OS.view] at hy
    show NStep (N1 xs T) _ _ _ _
      ((({ c.cb with pc := .run, dead := true } : CB σ)).stopReading.abs T : NSt σ)
    rw [abs_evOut_idle hpc hwp' hs]
    exact hstep

/-! ## Steps on the input -/

theorem abs_reset {c : CB σ} (h0 : c.dead = true ∨ c.out = []) (hw : c.wpend = false) :
    ({ c with out := [] } : CB σ).abs T = c.abs T := by
  simp only [CB.abs, absOut_reset h0 hw]

theorem sim_dropR {c : CSys σ} (h : c.cb.Inv T) {st' : DStore} {res : Res}
    (hpd : c.cb.pdrop = true) (hds : dstep c.st (.streamDropR (rh 0)) = some (st', res)) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      (({ c.cb with pdrop := false, rdropped := true } : CB σ).abs T : NSt σ) := by
  rw [abs_dropR h hpd]
  exact NStep.dropIn rfl (abs_mayStop h hpd) hds

theorem sim_read {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) (h : c.cb.Inv T)
    {st' : DStore} {res : Res} (hb : 0 < batch) (hpc : c.cb.pc = .run) (hwp : c.cb.wpend = false)
    (h0 : c.cb.dead = true ∨ c.cb.out = []) (he : c.cb.eof = false) (hrp : c.cb.rpend = false)
    (hds : dstep c.st (.streamRead (rh 0) batch) = some (st', res)) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      ((match res with
        | .read p ys => ({ c.cb with out := [] } : CB σ).onread T p ys
        | _ => ({ c.cb with pc := .wait, rpend := true, out := [] } : CB σ)).abs T : NSt σ) := by
  have hrd : c.cb.rdropped = false := by
    cases hr : c.cb.rdropped
    · rfl
    · rw [h.i1 hr] at he; cases he
  have hen : c.cb.ended = false := by
    cases hx : c.cb.ended
    · rfl
    · rw [h.i2 hx] at he; cases he
  have hdn : T.done c.cb.s = false := by
    cases hx : T.done c.cb.s
    · rfl
    · rw [h.i3 hx] at he; cases he
  have hrdA : (c.cb.abs T).rd = .idle := by simp [CB.abs, hrd, hrp, hen]
  have hI := reach_inv (pipe_wf xs T) hR
  obtain ⟨-, o, -, hinv⟩ := chan_in (pipe_wf xs T) hI (i := 1) (c := 0) rfl
  have hinv' : ChanInv o.st.view o.ack .idle (c.cb.abs T).got ((CSys.abs xs T c).st.chans (rh 0)) :=
    hrdA ▸ hinv
  obtain ⟨-, c', hread, -⟩ := dstep_read hI.coh hds
  rcases read_spec hinv' hread with ⟨rfl, -⟩ | ⟨p, ys, rfl, -⟩
  · show NStep (N1 xs T) _ _ _ _
      ((({ c.cb with pc := .wait, rpend := true, out := [] } : CB σ)).abs T : NSt σ)
    rw [abs_read_blocked hpc h0 hwp hrd]
    exact NStep.readBlk rfl hrdA hdn hb hds
  · show NStep (N1 xs T) _ _ _ _ (((({ c.cb with out := [] } : CB σ)).onread T p ys).abs T : NSt σ)
    rw [abs_onread (c := ({ c.cb with out := [] } : CB σ)) p ys (by simp [hpc]) hrd hrp hen
      (fun hw => by simp [hwp] at hw), abs_reset h0 hwp]
    exact NStep.readNow rfl hrdA hdn hb hds

theorem onRead_pc_rpend (c : CB σ) (p : Nat) (ys : List Val) (hpc : c.pc ≠ .exit) :
    (({ c with pc := .run, rpend := false } : CB σ).abs T).onRead T p ys =
      (c.abs T).onRead T p ys := by
  have ho : ({ c with pc := .run, rpend := false } : CB σ).absOut T = c.absOut T := by
    simp [CB.absOut, CB.fl, hpc]
  simp only [NSt.onRead, CB.abs, ho]

/-- The readable end the module waits on is live, and it has not seen the end. -/
theorem evIn_live {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) {st' : DStore}
    {e : Event} (hrp : c.cb.rpend = false)
    (hw : DWait c.st ((pipe xs T).ws 1) (rh 0) st' e) :
    (c.cb.abs T).rd = .idle ∧
      RInv (c.cb.abs T).rd (c.cb.abs T).got ((CSys.abs xs T c).st.chans (rh 0)) := by
  have hI := reach_inv (pipe_wf xs T) hR
  obtain ⟨-, o, -, hinv⟩ := chan_in (pipe_wf xs T) hI (i := 1) (c := 0) rfl
  have hlive := wait_rh_live hI.coh hw
  obtain ⟨-, c', htake, -⟩ := wait_rh hI.coh hw
  have hR' : RInv (c.cb.abs T).rd (c.cb.abs T).got ((CSys.abs xs T c).st.chans (rh 0)) := hinv.2.1
  refine ⟨?_, hR'⟩
  obtain ⟨hRi, -⟩ := takeR_res (reach_pos hR _) hR' htake
  rcases hRi with h1 | h1
  · exact h1
  · have : c.cb.rpend = true := by
      unfold CB.abs at h1
      split at h1 <;> (try split at h1) <;> (try split at h1) <;> simp_all
    rw [hrp] at this
    cases this

/-- An event on the input, when the module has no read pending, is a `DROPPED` with no items. -/
theorem evIn_idle {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) {st' : DStore}
    {e : Event} (hrp : c.cb.rpend = false)
    (hw : DWait c.st ((pipe xs T).ws 1) (rh 0) st' e) :
    c.cb.rdropped = false ∧ status e.payload ≠ 0 ∧ e.items = [] := by
  obtain ⟨hidle, hR'⟩ := evIn_live hR hrp hw
  have hI := reach_inv (pipe_wf xs T) hR
  obtain ⟨-, c', htake, -⟩ := wait_rh hI.coh hw
  have hrd : c.cb.rdropped = false := by
    cases hr : c.cb.rdropped
    · rfl
    · simp [CB.abs, hr] at hidle
  rw [hidle] at hR'
  exact ⟨hrd, takeR_idle hR' htake⟩

theorem sim_evIn {c : CSys σ} (hR : Reach (pipe xs T) (CSys.abs xs T c)) (h : c.cb.Inv T)
    {st' : DStore} {e : Event} (hpc : c.cb.pc = .wait)
    (hw : DWait c.st ((pipe xs T).ws 1) (rh 0) st' e) :
    NStep (N1 xs T) ((pipe xs T).ws 1) c.st (c.cb.abs T : NSt σ) st'
      ((if c.cb.rpend then
          ({ c.cb with pc := .run, rpend := false } : CB σ).onread T e.payload e.items
        else ({ c.cb with pc := .run, ended := true } : CB σ).stopReading).abs T : NSt σ) := by
  have hstep := NStep.waitIn (N := N1 xs T) (x := (c.cb.abs T : NSt σ)) (c := 0) rfl hw
  have hpc' : c.cb.pc ≠ .exit := by simp [hpc]
  split
  · rename_i hrp
    have hrd := h.i8 hrp
    have hen : c.cb.ended = false := by
      cases hx : c.cb.ended
      · rfl
      · rw [h.i11 hx] at hrp; cases hrp
    show NStep (N1 xs T) _ _ _ _ (((({ c.cb with pc := .run, rpend := false } :
      CB σ)).onread T e.payload e.items).abs T : NSt σ)
    rw [abs_onread (c := ({ c.cb with pc := .run, rpend := false } : CB σ)) _ _ (by simp) hrd rfl
      hen (fun hw' => (h.i7 hw').1), onRead_pc_rpend _ _ _ hpc']
    exact hstep
  · rename_i hrp
    have hrp' : c.cb.rpend = false := by simpa using hrp
    obtain ⟨hrd, hs, hy⟩ := evIn_idle hR hrp' hw
    show NStep (N1 xs T) _ _ _ _
      ((({ c.cb with pc := .run, ended := true } : CB σ)).stopReading.abs T : NSt σ)
    rw [abs_evIn_idle hpc hrd hrp' hs, ← hy]
    exact hstep

end Silmaril.Proofs.Wasm.Component.Streams.Callback
