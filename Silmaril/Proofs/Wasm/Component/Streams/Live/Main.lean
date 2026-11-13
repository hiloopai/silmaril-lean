module

public import Silmaril.Proofs.Wasm.Component.Streams.Live.Progress

/-!
# Termination and liveness of stream networks

* `reach_pos`: the positivity facts hold in every reachable system.
* `bounded_of_spec`: if every node `i` has read a prefix of `L i` (`SpecOK`), the potential's
  bounds hold with `B i = |L i|` and `Bo i = |T_i.run (L i)|`: an output acknowledges a prefix of
  its node's output so far, a prefix of `T_i.run (L i)` (`out_spec`).
* `specOK_of_consistent`: for a topologically numbered network, a consistent assignment of
  specifications (a source's is `[]`, a node's is its writer's transformer run on the writer's)
  holds in every reachable system (`net_spec`, by induction along the numbering).
* `reach_pot_lt`: every step from a reachable system decreases the potential.
* `reach_done`: from every reachable system some steps lead to a system where every node has
  finished; `exec_done`: **every** maximal execution, whatever the scheduler, reaches such a system
  within `pot (init net)` steps and stays there (`done_stuck`: no node can step any more).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Streams.Live

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Obj Res Event upd)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Drop
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Live
open Silmaril.Proofs.Wasm.Component.Streams.Net

variable {net : Network}

/-! ## Invariants -/

theorem nstep_pos {N : Node} {ws : Nat} {st st' : DStore} {x x' : NSt N.σ} (hP : StPos st)
    (h : NStep N ws st x st' x') : StPos st' := by
  cases h with
  | readBlk _ _ _ _ hds => exact dstep_pos hP hds
  | readNow _ _ _ _ hds => exact dstep_pos hP hds
  | write _ _ _ _ hds => exact dstep_pos hP hds
  | waitIn _ hw => exact wait_pos hP hw
  | waitOut _ _ hw => exact wait_pos hP hw
  | dropIn _ _ hds => exact dstep_pos hP hds
  | dropOut _ _ _ hds => exact dstep_pos hP hds

/-- **The positivity facts hold in every reachable system.** -/
theorem reach_pos {s : Sys net} (h : Reach net s) : StPos s.st := by
  induction h with
  | refl => exact fun _ => pos_empty
  | tail _ hs ih =>
    obtain ⟨i, hn⟩ := hs
    exact nstep_pos ih hn

/-- What an output has acknowledged is a prefix of its node's output so far. -/
theorem ack_prefix {L : List Val} {fl : Bool} {o : Out} (h : OInv L fl o) : o.ack <+: L := by
  obtain ⟨st, a⟩ := o
  cases st with
  | idle q =>
    have h' : a ++ q = L := h
    exact h' ▸ List.prefix_append _ _
  | busy xs q =>
    have h' : a ++ xs ++ q = L := h
    rw [← h', List.append_assoc]
    exact List.prefix_append _ _
  | dead => exact h
  | closed d =>
    cases d
    · have h' : a = L ∧ fl = true := h
      exact h'.1 ▸ List.prefix_refl _
    · exact h

/-- **The bounds of the potential**, from the specifications. -/
theorem bounded_of_spec {s : Sys net} (hI : Inv net s) {L : Fin net.k → List Val}
    (hL : ∀ i, SpecOK s i (L i)) :
    Bounded (fun i => (L i).length) (fun i => ((net.node i).T.run (L i)).length) s := by
  intro i
  have hO := out_spec _ _ (hI.node i) (L i) (hL i).1 (hL i).2
  refine ⟨(hL i).1.length_le, fun o ho => ?_⟩
  exact ((ack_prefix ((hI.node i).outs o ho)).trans hO.1).length_le

/-- A consistent assignment of specifications to the nodes. -/
def Consistent (net : Network) (L : Fin net.k → List Val) : Prop :=
  ∀ i, ((net.node i).inp = none → L i = []) ∧
    ∀ c, (net.node i).inp = some c → L i = (net.node (net.wr c).1).T.run (L (net.wr c).1)

/-- **A consistent assignment holds in every reachable system**, for a topologically numbered
network. -/
theorem specOK_of_consistent (hwf : net.WF) (htopo : net.Topo) {L : Fin net.k → List Val}
    (hL : Consistent net L) {s : Sys net} (hI : Inv net s) :
    ∀ (n : Nat) (i : Fin net.k), i.val = n → SpecOK s i (L i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    cases hinp : (net.node i).inp with
    | none =>
      rw [(hL i).1 hinp]
      exact src_spec hI i hinp
    | some c =>
      obtain ⟨hm, hrd⟩ := hwf.inp_rd i c hinp
      have hlt : (net.wr c).1.val < n := by
        have := htopo c hm
        rw [hrd] at this
        omega
      have hU : SpecOK s (net.wr c).1 (L (net.wr c).1) := ih _ hlt _ rfl
      rw [(hL i).2 c hinp]
      exact node_spec hwf hI i hinp _ hU

/-! ## Termination -/

/-- The data under which the potential decreases. -/
structure Setting (net : Network) (L : Fin net.k → List Val) : Prop where
  wf : net.WF
  topo : net.Topo
  cons : Consistent net L

/-- The bounds of a setting. -/
abbrev bB {L : Fin net.k → List Val} (_ : Setting net L) : Fin net.k → Nat := fun i => (L i).length

/-- The output bounds of a setting. -/
abbrev bBo {L : Fin net.k → List Val} (_ : Setting net L) : Fin net.k → Nat :=
  fun i => ((net.node i).T.run (L i)).length

theorem reach_bounded {L : Fin net.k → List Val} (S : Setting net L) {s : Sys net}
    (h : Reach net s) : Bounded (bB S) (bBo S) s := by
  have hI := reach_inv S.wf h
  exact bounded_of_spec hI (fun i => specOK_of_consistent S.wf S.topo S.cons hI _ i rfl)

/-- **Every step from a reachable system decreases the potential.** -/
theorem reach_pot_lt {L : Fin net.k → List Val} (S : Setting net L) {s s' : Sys net}
    (h : Reach net s) (hs : Step net s s') : pot (bB S) (bBo S) s' < pot (bB S) (bBo S) s :=
  step_pot_lt S.wf (reach_inv S.wf h) (reach_pos h) (reach_bounded S (Steps.tail h hs)) hs

/-- **Progress** from a reachable system. -/
theorem reach_progress {L : Fin net.k → List Val} (S : Setting net L) {s : Sys net}
    (h : Reach net s) (hnd : ¬ s.AllDone) : Enabled net s := by
  obtain ⟨i, hi⟩ : ∃ i, ¬ (s.ns i).Finished := by
    by_contra hc
    exact hnd (fun i => by_contra fun hn => hc ⟨i, hn⟩)
  exact progress S.wf S.topo (reach_inv S.wf h) (reach_pos h) _ i rfl hi

theorem steps_trans {s₁ s₂ s₃ : Sys net} (h₁ : Steps net s₁ s₂) (h₂ : Steps net s₂ s₃) :
    Steps net s₁ s₃ := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact Steps.tail ih hs

theorem steps_head {s₁ s₂ s₃ : Sys net} (h₁ : Step net s₁ s₂) (h₂ : Steps net s₂ s₃) :
    Steps net s₁ s₃ :=
  steps_trans (Steps.tail (Steps.refl _) h₁) h₂

/-- **From every reachable system, some steps lead to a system where every node has finished.** -/
theorem reach_done {L : Fin net.k → List Val} (S : Setting net L) :
    ∀ (n : Nat) (s : Sys net), Reach net s → pot (bB S) (bBo S) s = n →
      ∃ s', Steps net s s' ∧ s'.AllDone := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s h hn
    by_cases hd : s.AllDone
    · exact ⟨s, Steps.refl _, hd⟩
    · obtain ⟨s₁, hs⟩ := reach_progress S h hd
      have hlt := reach_pot_lt S h hs
      obtain ⟨s', h', hd'⟩ := ih _ (hn ▸ hlt) s₁ (Steps.tail h hs) rfl
      exact ⟨s', steps_head hs h', hd'⟩

/-! ## Finished systems -/

theorem tbl_rh_live {st : DStore} (hc : Coh net st) {c s : Nat}
    (h : st.tbl (rh c) = some (.streamR s)) : (st.chans (rh c)).r.gone = false := by
  rw [hc.1] at h
  exact (tblOf_rh h).2.1

theorem tbl_wh_live {st : DStore} (hc : Coh net st) {c s : Nat}
    (h : st.tbl (wh c) = some (.streamW s)) : (st.chans (rh c)).w.gone = false := by
  rw [hc.1] at h
  exact (tblOf_wh h).2.1

/-- Waiting on a readable end needs that end. -/
theorem wait_rh_live {st st' : DStore} (hc : Coh net st) {s c : Nat} {e : Event}
    (h : DWait st s (rh c) st' e) : (st.chans (rh c)).r.gone = false := by
  obtain ⟨-, -, h⟩ := h
  simp only [takeEv] at h
  split at h
  · rename_i s' ht
    exact tbl_rh_live hc ht
  · rename_i s' ht
    rw [hc.1] at ht
    unfold tblOf rh at ht
    split_ifs at ht <;> simp_all
  · simp at h

/-- Waiting on a writable end needs that end. -/
theorem wait_wh_live {st st' : DStore} (hc : Coh net st) {s c : Nat} {e : Event}
    (h : DWait st s (wh c) st' e) : (st.chans (rh c)).w.gone = false := by
  obtain ⟨-, -, h⟩ := h
  simp only [takeEv] at h
  split at h
  · rename_i s' ht
    rw [hc.1] at ht
    unfold tblOf wh at ht
    split_ifs at ht <;> simp_all
  · rename_i s' ht
    exact tbl_wh_live hc ht
  · simp at h

/-- A node that has dropped its input cannot wait on it. -/
theorem no_waitIn (hwf : net.WF) {s : Sys net} (hI : Inv net s) {i : Fin net.k} {c : Nat}
    (hinp : (net.node i).inp = some c) {b : Bool} (hb : (s.ns i).rd = .gone b) {st' : DStore}
    {e : Event} (hw : DWait s.st (net.ws i) (rh c) st' e) : False := by
  obtain ⟨-, o, -, hinv⟩ := chan_in hwf hI hinp
  have hR : RInv (.gone b) (s.ns i).got (s.st.chans (rh c)) := hb ▸ hinv.2.1
  have h1 : (s.st.chans (rh c)).r.gone = true := hR.2.1
  rw [wait_rh_live hI.coh hw] at h1
  cases h1

/-- A closed output cannot be waited on. -/
theorem no_waitOut (hwf : net.WF) {s : Sys net} (hI : Inv net s) {i : Fin net.k} {j c : Nat}
    (hout : (net.node i).outs[j]? = some c) {o : Out} {d : Bool}
    (hj : (s.ns i).outs[j]? = some o) (hd : o.st = .closed d) {st' : DStore} {e : Event}
    (hw : DWait s.st (net.ws i) (wh c) st' e) : False := by
  obtain ⟨-, hinv⟩ := chan_out hwf hI hout hj
  have hW : WInv (.closed d) o.ack (s.st.chans (rh c)) := by
    have := hinv.1
    rw [hd] at this
    exact this
  have h1 : (s.st.chans (rh c)).w.gone = true := hW.1
  rw [wait_wh_live hI.coh hw] at h1
  cases h1

/-- **A finished system cannot step.** -/
theorem done_stuck (hwf : net.WF) {s : Sys net} (hI : Inv net s) (hd : s.AllDone) :
    ¬ Enabled net s := by
  rintro ⟨s', i, hn⟩
  obtain ⟨⟨b, hb⟩, hcl⟩ := hd i
  have hno : ∀ {j : Nat} {o : Out}, (s.ns i).outs[j]? = some o → ∃ d, o.st = .closed d :=
    fun hj => hcl _ (List.mem_of_getElem? hj)
  cases hn with
  | readBlk _ hrd => exact absurd (hb ▸ hrd) (by simp)
  | readNow _ hrd => exact absurd (hb ▸ hrd) (by simp)
  | write _ hj => obtain ⟨d, hd⟩ := hno hj; cases hd
  | waitIn hinp hw => exact no_waitIn hwf hI hinp hb hw
  | waitOut hout hj hw =>
    obtain ⟨d, hd⟩ := hno hj
    exact no_waitOut hwf hI hout hj hd hw
  | dropIn _ hstop => rcases hstop with h | ⟨h, -⟩ <;> exact absurd (hb ▸ h) (by simp)
  | dropOut _ _ hj =>
    rcases hj with ⟨hj, -⟩ | ⟨hj, -⟩ <;> obtain ⟨d, hd⟩ := hno hj <;> cases hd

/-! ## Executions -/

theorem exec_reach {r : Nat → Sys net} (hr : Exec net r) : ∀ n, Reach net (r n) := by
  intro n
  induction n with
  | zero => rw [hr.1]; exact Steps.refl _
  | succ n ih =>
    rcases hr.2 n with h | ⟨-, h⟩
    · exact Steps.tail ih h
    · rw [h]; exact ih

/-- While no system is finished, an execution steps and the potential falls each time. -/
theorem exec_pot {L : Fin net.k → List Val} (S : Setting net L) {r : Nat → Sys net}
    (hr : Exec net r) (N : Nat) (hnd : ∀ n, n < N → ¬ (r n).AllDone) :
    pot (bB S) (bBo S) (r N) + N ≤ pot (bB S) (bBo S) (r 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have ih' := ih (fun n hn => hnd n (Nat.lt_succ_of_lt hn))
    have hen : Enabled net (r N) := reach_progress S (exec_reach hr N) (hnd N (Nat.lt_succ_self N))
    rcases hr.2 N with h | ⟨hne, -⟩
    · have := reach_pot_lt S (exec_reach hr N) h
      omega
    · exact absurd hen hne

/-- **Liveness under every scheduler**: every maximal execution reaches a system where every
node has finished, within `pot (init net)` steps, and stays there. -/
theorem exec_done {L : Fin net.k → List Val} (S : Setting net L) {r : Nat → Sys net}
    (hr : Exec net r) :
    ∃ n, n ≤ pot (bB S) (bBo S) (init net) ∧ ∀ m, n ≤ m → r m = r n ∧ (r m).AllDone := by
  have hex : ∃ n, (r n).AllDone := by
    by_contra hc
    have hnd : ∀ n, ¬ (r n).AllDone := fun n hn => hc ⟨n, hn⟩
    have := exec_pot S hr (pot (bB S) (bBo S) (r 0) + 1) (fun n _ => hnd n)
    omega
  classical
  let n := Nat.find hex
  have hn : (r n).AllDone := Nat.find_spec hex
  have hmin : ∀ k, k < n → ¬ (r k).AllDone := fun k hk => Nat.find_min hex hk
  have hle : n ≤ pot (bB S) (bBo S) (init net) := by
    have := exec_pot S hr n hmin
    rw [hr.1] at this
    omega
  have hstay : ∀ m, n ≤ m → r m = r n := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      have hdm : (r m).AllDone := ih ▸ hn
      have hst := done_stuck S.wf (reach_inv S.wf (exec_reach hr m)) hdm
      rcases hr.2 m with h | ⟨-, h⟩
      · exact absurd ⟨_, h⟩ hst
      · rw [h, ih]
  exact ⟨n, hle, fun m hm => ⟨hstay m hm, (hstay m hm) ▸ hn⟩⟩

end Silmaril.Proofs.Wasm.Component.Streams.Live
