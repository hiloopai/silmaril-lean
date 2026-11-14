module

public import Silmaril.Proofs.Wasi.Cli.Host2.Emit

/-!
# The WASI 0.2 host: what a write shows

Proofs for `Silmaril.Wasi.Cli.Host2.Thms`: `writeAll_facts` (a run of the chunked writes writes a
prefix of the chunks, all of them when it returns `true`) and `put_facts` (`PutFacts`: the
same for `api2.put ch b`, on the stream of `ch` only).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-- An event read neither as stdin, a file, a `get-stderr` handle nor an exit. -/
def Mute (e : WEv) : Prop :=
  PlainEv e ∧ handles Versions.P2.getStderr [e] = [] ∧
    endCode cliRun (some Versions.P2.cliExit) e = none

theorem mute_bwf_req (h : BitVec 32) (c : List (BitVec 8)) :
    Mute (.req streamWrite [.u32 h, bytesV c]) :=
  ⟨plainEv_req _ _, rfl, endCode_req _ (by decide)⟩

theorem mute_bwf_imp (h : BitVec 32) (c : List (BitVec 8)) (n : Option (List Val)) :
    Mute (.imp streamWrite [.u32 h, bytesV c] n) :=
  ⟨plainEv_imp _ _ (by decide), handles_imp_ne _ _ (by decide), rfl⟩

/-- **What a run of the writes shows**: mute events, the successful writes are a prefix of the
chunks on `h`, all of them (and no failure) when the run returned `true`. -/
def WFacts (h : BitVec 32) (cs : List (List (BitVec 8))) (w : List WEv) (r : Option Bool) :
    Prop :=
  (∀ e ∈ w, Mute e) ∧ ∃ j, w.filterMap write2 = (cs.take j).map (h, ·) ∧
    (r = some true → j = cs.length ∧ w.any failedWrite2 = false)

/-- Nothing written. -/
theorem wfacts_none {h : BitVec 32} {cs : List (List (BitVec 8))} {w : List WEv}
    {r : Option Bool} (hm : ∀ e ∈ w, Mute e) (hw : w.filterMap write2 = [])
    (hr : r ≠ some true) : WFacts h cs w r :=
  ⟨hm, 0, by simpa using hw, fun h' => absurd h' hr⟩

/-- One more successful write. -/
theorem wfacts_cons_ok {h : BitVec 32} {c : List (BitVec 8)} {cs : List (List (BitVec 8))}
    {w : List WEv} {r : Option Bool} (hf : WFacts h cs w r) {n : Option (List Val)}
    (hn : okUnit n = true) :
    WFacts h (c :: cs)
      (.req streamWrite [.u32 h, bytesV c] :: .imp streamWrite [.u32 h, bytesV c] n :: w) r := by
  obtain ⟨hm, j, hj, hr⟩ := hf
  have hw : write2 (.imp streamWrite [.u32 h, bytesV c] n) = some (h, c) := by
    rw [write2_bwf]; simp [hn]
  have hfw : failedWrite2 (.imp streamWrite [.u32 h, bytesV c] n) = false := failedWrite2_ok _ hn
  refine ⟨fun e he => ?_, j + 1, ?_, fun h' => ?_⟩
  · rcases List.mem_cons.1 he with rfl | he
    · exact mute_bwf_req h c
    rcases List.mem_cons.1 he with rfl | he
    · exact mute_bwf_imp h c n
    · exact hm e he
  · simp [List.filterMap_cons, write2_req, hw, hj]
  · obtain ⟨hl, ha⟩ := hr h'
    exact ⟨by simp [hl], by simp [failedWrite2_req, hfw, ha]⟩

/-- **A run of the chunked writes** (`writeAll`). -/
theorem writeAll_facts (h : BitVec 32) :
    ∀ (cs : List (List (BitVec 8))) {w : List WEv} {r : Option Bool},
      PRun (writeAll h cs) w r → WFacts h cs w r
  | [], w, r, hr => by
    have hr' : PRun (.pure true) w r := hr
    obtain ⟨rfl, -⟩ := PRun.pure_inv hr'
    exact ⟨fun e he => absurd he List.not_mem_nil, 0, rfl, fun _ => ⟨rfl, rfl⟩⟩
  | c :: cs, w, r, hr => by
    have h0 : PRun (.call (⟨streamWrite, bwf_mem⟩, [.u32 h, bytesV c]) fun n =>
        if okUnit n then writeAll h cs else .pure false) w r := hr
    rcases PRun.call_inv h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n, w', rfl, h'⟩
    · exact wfacts_none (fun e he => absurd he List.not_mem_nil) rfl (by simp)
    · exact wfacts_none (fun e he => List.mem_singleton.1 he ▸ mute_bwf_req h c) rfl (by simp)
    by_cases hn : okUnit n = true
    · have hw : PRun (writeAll h cs) w' r := by simpa [hn] using h'
      exact wfacts_cons_ok (writeAll_facts h cs hw) hn
    · have hw : PRun (I := I2) (.pure false) w' r := by simpa [hn] using h'
      obtain ⟨rfl, hr'⟩ := PRun.pure_inv hw
      have hm : ∀ e ∈ [WEv.req streamWrite [.u32 h, bytesV c],
          .imp streamWrite [.u32 h, bytesV c] n], Mute e := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro e (rfl | rfl)
        exacts [mute_bwf_req h c, mute_bwf_imp h c n]
      refine wfacts_none hm (by simp [write2_req, write2_bwf, hn]) ?_
      rcases hr' with rfl | rfl <;> simp

/-! ## A write on a channel -/

/-- **What a run of `api2.put ch` shows**: plain events, no exit, and a prefix of the chunks
written on one handle, which is the `get-stderr` handle exactly when `ch` is stderr. -/
structure PutFacts (ch : Channel) (cs : List (List (BitVec 8))) (v : List WEv)
    (r : Option Bool) : Prop where
  plain : ∀ e ∈ v, PlainEv e
  code : ∀ e ∈ v, endCode cliRun (some Versions.P2.cliExit) e = none
  written : ∃ h j, v.filterMap write2 = (cs.take j).map (h, ·) ∧
    (j = 0 ∨ handles Versions.P2.getStderr v = if ch = .stderr then [h] else []) ∧
    (r = some true → j = cs.length ∧ v.any failedWrite2 = false)

theorem stdFn_plain (ch : Channel) : Plain2 (stdFn ch) := by cases ch <;> decide
theorem stdFn_ne_exit (ch : Channel) : stdFn ch ≠ Versions.P2.cliExit := by cases ch <;> decide
theorem stdFn_ne_osWrite (ch : Channel) : stdFn ch ≠ Versions.P2.osWrite := by cases ch <;> decide
theorem stdFn_ne_bwf (ch : Channel) : stdFn ch ≠ streamWrite := by cases ch <;> decide

/-- The two events of the `get-stdout`/`get-stderr` call. -/
theorem get_events (ch : Channel) (n : Option (List Val)) :
    ∀ e ∈ [WEv.req (stdFn ch) [], .imp (stdFn ch) [] n], PlainEv e ∧
      endCode cliRun (some Versions.P2.cliExit) e = none ∧ write2 e = none ∧
      failedWrite2 e = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro e (rfl | rfl)
  · exact ⟨plainEv_req _ _, endCode_req _ (stdFn_ne_exit ch), rfl, rfl⟩
  · exact ⟨plainEv_imp _ _ (stdFn_plain ch), rfl, write2_imp _ _ (stdFn_ne_osWrite ch)
      (stdFn_ne_bwf ch), failedWrite2_imp _ _ (stdFn_ne_osWrite ch) (stdFn_ne_bwf ch)⟩

/-- The `get-stderr` handles of the `get-stdout`/`get-stderr` call. -/
theorem handles_get_std (ch : Channel) (n : Option (List Val)) :
    handles Versions.P2.getStderr [.req (stdFn ch) [], .imp (stdFn ch) [] n] =
      if ch = .stderr then (u32Of n).toList else [] := by
  rw [handles_cons, handles_req, List.nil_append]
  cases ch
  · exact handles_imp_ne _ _ (by decide)
  · exact handles_get _ _ _

/-- Nothing written: the call alone. -/
theorem putFacts_get {ch : Channel} {cs : List (List (BitVec 8))} {v : List WEv}
    {r : Option Bool} (n : Option (List Val))
    (hv : v <+: [.req (stdFn ch) [], .imp (stdFn ch) [] n]) (hr : r ≠ some true) :
    PutFacts ch cs v r := by
  have hg := get_events ch n
  have hv' : ∀ e ∈ v, e ∈ [WEv.req (stdFn ch) [], .imp (stdFn ch) [] n] := fun e he => hv.mem he
  refine ⟨fun e he => (hg e (hv' e he)).1, fun e he => (hg e (hv' e he)).2.1, 0, 0, ?_,
    .inl rfl, fun h' => absurd h' hr⟩
  exact List.filterMap_eq_nil_iff.2 fun e he => (hg e (hv' e he)).2.2.1

/-- The call, then the writes on its handle. -/
theorem putFacts_write {ch : Channel} {cs : List (List (BitVec 8))} {w : List WEv}
    {r : Option Bool} {n : Option (List Val)} {h : BitVec 32} (hu : u32Of n = some h)
    (hw : WFacts h cs w r) :
    PutFacts ch cs ([.req (stdFn ch) [], .imp (stdFn ch) [] n] ++ w) r := by
  have hg := get_events ch n
  obtain ⟨hm, j, hj, hr⟩ := hw
  have hgw : [WEv.req (stdFn ch) [], .imp (stdFn ch) [] n].filterMap write2 = [] :=
    List.filterMap_eq_nil_iff.2 fun e he => (hg e he).2.2.1
  have hgf : [WEv.req (stdFn ch) [], .imp (stdFn ch) [] n].any failedWrite2 = false :=
    List.any_eq_false.2 fun e he => by simp [(hg e he).2.2.2]
  have hwh : handles Versions.P2.getStderr w = [] :=
    List.filterMap_eq_nil_iff.2 fun e he => List.filterMap_eq_nil_iff.1 (hm e he).2.1 e (by simp)
  refine ⟨fun e he => ?_, fun e he => ?_, h, j, by rw [List.filterMap_append, hgw, hj]; rfl,
    .inr ?_, fun h' => ⟨(hr h').1, by rw [List.any_append, hgf, (hr h').2]; rfl⟩⟩
  · rcases List.mem_append.1 he with he | he
    exacts [(hg e he).1, (hm e he).1]
  · rcases List.mem_append.1 he with he | he
    exacts [(hg e he).2.1, (hm e he).2.2]
  · rw [handles_append, handles_get_std, hwh, hu, List.append_nil]
    cases ch <;> rfl

/-- **A run of `api2.put ch b`.** -/
theorem put_facts {ch : Channel} {b : Bytes} {v : List WEv} {r : Option Bool}
    (hr : PRun (api2.put ch b) v r) : PutFacts ch (chunk4096 (toWasm b)) v r := by
  have h0 : PRun (.call (⟨stdFn ch, stdFn_mem ch⟩, []) fun n => match u32Of n with
      | some h => writeAll h (chunk4096 (toWasm b))
      | none => .pure false) v r := hr
  rcases PRun.call_inv h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n, w, rfl, h'⟩
  · exact putFacts_get none List.nil_prefix (by simp)
  · exact putFacts_get none (List.prefix_cons_iff.2 (by simp)) (by simp)
  cases hu : u32Of n with
  | none =>
    have hw : PRun (I := I2) (.pure false) w r := by rw [hu] at h'; exact h'
    obtain ⟨rfl, hr'⟩ := PRun.pure_inv hw
    exact putFacts_get n (List.prefix_refl _) (by rcases hr' with rfl | rfl <;> simp)
  | some h =>
    have hw : PRun (writeAll h (chunk4096 (toWasm b))) w r := by rw [hu] at h'; exact h'
    exact putFacts_write hu (writeAll_facts h _ hw)

end Silmaril.Wasi.Cli.Host2

end
