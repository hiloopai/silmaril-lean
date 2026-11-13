module

public import Silmaril.Proofs.Project.WasmP3Rust.HelloDen.Write

/-!
# `hello` under `den`: the answers to `waitable-set.wait`

The wait discipline makes a `STREAM_WRITE` event the completion of the blocked write; other
events re-enter the callback, which returns `WAIT` again.
-/

@[expose] public section

namespace Silmaril.Proofs.Project.WasmP3Rust.HelloDen

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Versions.P3 Silmaril.Project.WasmP3Rust
open Silmaril.Project.WasmP3Rust.Den Silmaril.Project.WasmP3Rust.HelloDen
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult blocked)

/-- The bytes a copy result reports as written, of the pending bytes `bs`. -/
def wout (x : Option (Option (CopyResult × Nat))) (bs : List (BitVec 8)) : List (BitVec 8) :=
  match x with
  | some (some (.completed, k)) => bs.take k
  | _ => []

theorem cWait_ne₁ : cWait ≠ cStreamNew := by decide
theorem cWait_ne₂ : cWait ≠ stdoutWrite3 := by decide
theorem cWait_ne₃ : cWait ≠ cStreamWrite := by decide

theorem os_wait_quiet (q : OsSt) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv, n = some [cv, iv, pv] → natOf cv ≠ some 3) :
    osStep3 0 q (.imp cWait a n) = (q, []) := by
  unfold osStep3
  dsimp only
  simp only [cWait_ne₁, cWait_ne₂, cWait_ne₃, ite_false, ite_true]
  split
  · rename_i cv iv pv
    have h3 := h cv iv pv rfl
    split
    · rename_i hcv _ _; exact absurd hcv h3
    · rfl
  · rfl

theorem wait_quiet (q : List Nat) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv, n = some [cv, iv, pv] → natOf cv ≠ some 3) :
    waitStep q (.imp cWait a n) = some q := by
  unfold waitStep
  simp only [cWait_ne₃, ite_false, ite_true]
  split
  · rename_i cv iv pv
    simp only [h cv iv pv rfl, streamWriteCode, ite_false]
  · rfl

theorem obsStep_wait_quiet (o : Obs) (a : List Val) (n : Option (List Val))
    (h : ∀ cv iv pv, n = some [cv, iv, pv] → natOf cv ≠ some 3) :
    obsStep o (.imp cWait a n) = o := by
  rcases o with ⟨os, out, ok, wp⟩
  simp only [obsStep, os_wait_quiet os a n h, wait_quiet _ a n h, wbytes, List.filterMap_nil,
    List.append_nil, okEv, Bool.or_false]
  cases wp <;> rfl

/-- A `STREAM_WRITE` event not for a blocked write is refused by the wait discipline. -/
theorem obsStep_wait_refused {o : Obs} {q : List Nat} (a : List Val) {cv iv pv : Val}
    (hwp : o.wp = some q) (hc : natOf cv = some 3) (hi : ∀ i, natOf iv = some i → i ∉ q) :
    (obsStep o (.imp cWait a (some [cv, iv, pv]))).wp = none := by
  simp only [obsStep, hwp, Option.bind_some, waitStep,
    cWait_ne₃, ite_false, ite_true, hc, streamWriteCode]
  cases h : natOf iv with
  | none => rfl
  | some i => simp only [hi i h, ite_false]

/-- The `STREAM_WRITE` event of the blocked write. -/
theorem obsStep_wait_write {o : Obs} {w : Nat} {bs : List (BitVec 8)} (a : List Val)
    {cv iv pv : Val} (hwp : o.wp = some [w]) (hc : natOf cv = some 3) (hi : natOf iv = some w)
    (hpend : o.os.pend.find? (·.1 = w) = some (w, bs)) (hout : w ∈ o.os.outW) :
    obsStep o (.imp cWait a (some [cv, iv, pv])) =
      { o with out := o.out ++ wout ((natOf pv).bind copyOf) bs, wp := some [] } := by
  have hos : osStep3 0 o.os (.imp cWait a (some [cv, iv, pv])) =
      (o.os, (wout ((natOf pv).bind copyOf) bs).map (.writeEv 0)) := by
    unfold osStep3
    dsimp only
    simp only [cWait_ne₁, cWait_ne₂, cWait_ne₃, ite_false, ite_true, hc, hi, Option.bind_eq_bind]
    generalize (natOf pv).bind copyOf = x
    rcases x with _ | _ | ⟨_ | _ | _, k⟩ <;> simp [hpend, hout, wout]
  simp only [obsStep, hos, wbytes_map, okEv, Bool.or_false, hwp, Option.bind_some, waitStep,
    cWait_ne₃, ite_false, ite_true, hc, hi, streamWriteCode,
    List.mem_singleton, List.erase_cons_head]

/-- The driver's continuation after `waitable-set.wait` (`DCall.wait`). -/
abbrev waitCont (cb : Nat) (d : DConf helloK) (n : Option (List Val)) : DConf helloK :=
  afterWait cb d n

theorem reenter_eq {d : DConf helloK} (ev : List Nat) (hpc : d.core.pc = .waitW ∨ d.core.pc = .waitF) :
    reenter 30 d ev = { d with core := onEvent d.core ev, mode := .run } := by
  simp only [reenter, helloK, show (30 : Nat) ≠ 29 by decide, false_and, ite_false, true_and,
    hpc, ite_true]

theorem dinv_back {o : Obs} {d : DConf helloK} (c : HConf) (hok : o.ok = false)
    (hr : d.result = none) (h : PcInv o c) : DInv o { d with core := c, mode := .run } :=
  ⟨hok, .inl ⟨hr, h⟩⟩

theorem waitCont_some {d : DConf helloK} {cv iv pv : Val} {c i q : Nat} (hc : natOf cv = some c)
    (hi : natOf iv = some i) (hq : natOf pv = some q) :
    waitCont 30 d (some [cv, iv, pv]) = reenter 30 d [c, i, q] := by
  simp only [waitCont, afterWait, hc, hi, hq]

theorem waitCont_none {d : DConf helloK} {n : Option (List Val)}
    (h : ∀ cv iv pv, n = some [cv, iv, pv] →
      natOf cv = none ∨ natOf iv = none ∨ natOf pv = none) :
    waitCont 30 d n = d.trapped := by
  unfold waitCont afterWait
  split
  · rename_i cv iv pv
    rcases h cv iv pv rfl with e | e | e <;> simp [e]
  · rfl

theorem onEvent_other {c : HConf} {code i q : Nat} (hpc : c.pc = .waitW) (h : code ≠ 3) :
    onEvent c [code, i, q] = c := by
  unfold onEvent
  split
  · rename_i h'; simp_all
  · rename_i h'; simp_all
  · rfl

theorem onEvent_otherF {c : HConf} {code i q : Nat} (hpc : c.pc = .waitF)
    (h : ¬ (code = 4 ∧ i = c.f)) : onEvent c [code, i, q] = c := by
  unfold onEvent
  split
  · simp_all
  · rename_i i' p' h₁ h₂
    simp only [List.cons.injEq] at h₂
    obtain ⟨rfl, rfl, rfl, -⟩ := h₂
    simp only [true_and] at h
    simp only [h, ite_false]
  · rfl

/-- `writeEvent` keeps the invariant when the event's bytes came out. -/
theorem writeEvent_inv {o : Obs} {c : HConf} (p : Nat) (hl : Live o c) :
    PcInv { o with out := o.out ++ wout (copyOf p) (helloMsg.drop c.off), wp := some [] }
      (writeEvent c p) := by
  have hret : PcInv { o with out := o.out ++ [], wp := some [] } { c with pc := .ret 1 } :=
    ⟨⟨hl.1, hl.2.1, by rw [List.append_nil]; exact hl.2.2.1, hl.2.2.2⟩, nofun, rfl⟩
  rcases hc : copyOf p with _ | _ | ⟨_ | _ | _, k⟩ <;> simp only [writeEvent, hc, wout]
  · exact hret
  · exact hret
  · have e : ({ o with out := o.out ++ (helloMsg.drop c.off).take k, wp := some [] } : Obs) =
        { ({ o with wp := some [] } : Obs) with
          out := helloMsg.take c.off ++ (helloMsg.drop c.off).take k } := by
      rw [hl.2.2.1]
    rw [e]
    exact advance_inv k ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2⟩ rfl
  · exact hret
  · exact hret

theorem onEvent_write {c : HConf} (hpc : c.pc = .waitW) (p : Nat) :
    onEvent c [3, c.w, p] = writeEvent c p := by
  unfold onEvent
  split <;> simp_all

theorem onEvent_read {c : HConf} (hpc : c.pc = .waitF) (p : Nat) :
    onEvent c [4, c.f, p] = readEvent c p := by
  unfold onEvent
  split <;> simp_all

/-- The driver's continuation on an answer of three values: a trap, or the callback re-entered
with the event. -/
theorem waitCont_cases {d : DConf helloK} {cv iv pv : Val} {P : DConf helloK → Prop}
    (htrap : P d.trapped)
    (hev : ∀ c i q, natOf cv = some c → natOf iv = some i → natOf pv = some q →
      P (reenter 30 d [c, i, q])) :
    P (waitCont 30 d (some [cv, iv, pv])) := by
  cases hc : natOf cv with
  | none => rw [waitCont_none (by simp [hc])]; exact htrap
  | some c =>
    cases hi : natOf iv with
    | none => rw [waitCont_none (by simp [hi])]; exact htrap
    | some i =>
      cases hq : natOf pv with
      | none => rw [waitCont_none (by simp [hq])]; exact htrap
      | some q => rw [waitCont_some hc hi hq]; exact hev c i q hc hi hq

theorem prefix_wout (off : Nat) (x : Option (Option (CopyResult × Nat))) :
    helloMsg.take off ++ wout x (helloMsg.drop off) <+: helloMsg := by
  unfold wout
  split
  · rw [take_add_drop]; exact List.take_prefix _ _
  · rw [List.append_nil]; exact List.take_prefix _ _

/-- The `STREAM_WRITE` event of the blocked write. -/
theorem waitW_write {o : Obs} {d : DConf helloK} {s : Nat} {cv iv pv : Val} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitW) (hp : Blocked o d.core)
    (h3 : natOf cv = some 3) (hi : natOf iv = some d.core.w) :
    DInv (obsStep o (.imp cWait [natV s] (some [cv, iv, pv]))) (waitCont 30 d (some [cv, iv, pv])) := by
  rw [obsStep_wait_write _ hp.2.2.1 h3 hi hp.2.2.2 (by rw [hp.1.1]; simp)]
  have hpre := prefix_wout d.core.off ((natOf pv).bind copyOf)
  rw [← hp.1.2.2.1] at hpre
  refine waitCont_cases (dinv_trapped hok hpre) fun c i q hc hi' hq => ?_
  obtain rfl : c = 3 := Option.some.inj (hc.symm.trans h3)
  obtain rfl : i = d.core.w := Option.some.inj (hi'.symm.trans hi)
  rw [reenter_eq _ (.inl hpc)]
  refine dinv_back _ hok hr ?_
  rw [onEvent_write hpc, hq, Option.bind_some]
  exact writeEvent_inv q hp.1

/-- A `STREAM_WRITE` event while the write is blocked: the wait discipline makes it the
blocked write's. -/
theorem waitW_three {o : Obs} {d : DConf helloK} {s : Nat} {cv iv pv : Val} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitW) (hp : Blocked o d.core)
    (h3 : natOf cv = some 3)
    (hacc : (obsStep o (.imp cWait [natV s] (some [cv, iv, pv]))).wp.isSome) :
    DInv (obsStep o (.imp cWait [natV s] (some [cv, iv, pv]))) (waitCont 30 d (some [cv, iv, pv])) := by
  by_cases hi : natOf iv = some d.core.w
  · exact waitW_write hok hr hpc hp h3 hi
  · have e := obsStep_wait_refused [natV s] (pv := pv) hp.2.2.1 h3 (fun j hj => by
      simp only [List.mem_singleton]; rintro rfl; exact hi hj)
    rw [e] at hacc; cases hacc

/-- Other events while the write is blocked: the callback returns `WAIT` again. -/
theorem waitW_quiet {o : Obs} {d : DConf helloK} {s : Nat} {cv iv pv : Val} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitW) (hp : Blocked o d.core)
    (h3 : natOf cv ≠ some 3) :
    DInv (obsStep o (.imp cWait [natV s] (some [cv, iv, pv]))) (waitCont 30 d (some [cv, iv, pv])) := by
  rw [obsStep_wait_quiet _ _ _ (fun _ _ _ e => by cases e; exact h3)]
  refine waitCont_cases (dinv_trapped hok hp.1.prefix) fun c i q hc _ _ => ?_
  rw [reenter_eq _ (.inl hpc), onEvent_other hpc (fun e => h3 (by rw [hc, e]))]
  exact dinv_back _ hok hr (by simp only [PcInv, hpc]; exact hp)

theorem resume_waitW {o : Obs} {d : DConf helloK} {s : Nat} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitW) (hp : Blocked o d.core)
    (n : Option (List Val)) (hacc : (obsStep o (.imp cWait [natV s] n)).wp.isSome) :
    DInv (obsStep o (.imp cWait [natV s] n)) (waitCont 30 d n) := by
  rcases n with _ | ⟨_ | ⟨cv, _ | ⟨iv, _ | ⟨pv, _ | _⟩⟩⟩⟩
  rotate_left 4
  · by_cases h3 : natOf cv = some 3
    · exact waitW_three hok hr hpc hp h3 hacc
    · exact waitW_quiet hok hr hpc hp h3
  all_goals
    rw [obsStep_wait_quiet _ _ _ (fun _ _ _ e => by cases e)]
    rw [waitCont_none (fun _ _ _ e => by cases e)]
    exact dinv_trapped hok hp.1.prefix

/-- `readEvent` after all bytes are out keeps the invariant. -/
theorem readEvent_inv {o : Obs} {c : HConf} (p : Nat) (hp : Done o c) : PcInv o (readEvent c p) := by
  have hret : ∀ v, PcInv o { c with pc := .ret v } := fun _ => ⟨hp.1, fun _ => hp.2.1, hp.2.2⟩
  unfold readEvent
  split
  · exact hret _
  · exact hret _

/-- Any event after all bytes are out: the future's, or `WAIT` again. -/
theorem waitF_event {o : Obs} {c : HConf} (hpc : c.pc = .waitF) (hp : Done o c) (e i q : Nat) :
    PcInv o (onEvent c [e, i, q]) := by
  by_cases h4 : e = 4 ∧ i = c.f
  · obtain ⟨rfl, rfl⟩ := h4
    rw [onEvent_read hpc]
    exact readEvent_inv q hp
  · rw [onEvent_otherF hpc h4]
    simp only [PcInv, hpc]
    exact hp

theorem resume_waitF {o : Obs} {d : DConf helloK} {s : Nat} (hok : o.ok = false)
    (hr : d.result = none) (hpc : d.core.pc = .waitF) (hp : Done o d.core)
    (n : Option (List Val)) (hacc : (obsStep o (.imp cWait [natV s] n)).wp.isSome) :
    DInv (obsStep o (.imp cWait [natV s] n)) (waitCont 30 d n) := by
  have htrap : DInv o d.trapped := dinv_trapped hok hp.1.prefix
  have hquiet : ∀ cv iv pv, n = some [cv, iv, pv] → natOf cv ≠ some 3 := fun cv iv pv e h3 => by
    subst e
    have e := obsStep_wait_refused [natV s] (iv := iv) (pv := pv) hp.2.2 h3 (fun _ _ => by simp)
    rw [e] at hacc; cases hacc
  rw [obsStep_wait_quiet _ _ _ hquiet]
  rcases n with _ | ⟨_ | ⟨cv, _ | ⟨iv, _ | ⟨pv, _ | _⟩⟩⟩⟩
  rotate_left 4
  · refine waitCont_cases htrap fun c i q _ _ _ => ?_
    rw [reenter_eq _ (.inr hpc)]
    exact dinv_back _ hok hr (waitF_event hpc hp c i q)
  all_goals
    rw [waitCont_none (fun _ _ _ e => by cases e)]
    exact htrap

end Silmaril.Proofs.Project.WasmP3Rust.HelloDen

end
