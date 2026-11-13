module

public import Silmaril.Proofs.Wasi.Cli.Host3.Scan
public import Silmaril.Wasi.Cli.Host2.Thms

/-!
# The WASI 0.3 host: what a write shows

Proofs for `Silmaril.Wasi.Cli.Host3.Thms`. `Facts q k bs v r`: along a run `v` of a stage of
`put3` from the scan state `q`, no event ends the run, `p3CliView` sees a prefix of `bs` on the
sink `k` (and possibly a refusal), and all of `bs` when the stage returned `true`. Stage by
stage: `dropW_quiet`, `afterWait_quiet`, `waitWrite_facts`, `write_facts`, **`put3_facts`**.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host3

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3 (natOf copyOf cStreamNew cStreamWrite cStreamDropW cWsNew cJoin cWait
  stdoutWrite3)
open Silmaril.Wasi.Cli.Host2 (u32Of toWasm)

/-- **What a run of a stage of `put3` shows** from the scan state `q`. -/
structure Facts (q : Sc3) (k : Sink) (bs : List (BitVec 8)) (v : List WEv) (r : Option Bool) :
    Prop where
  code : ∀ e ∈ v, endCode3 e = none
  outs : OutOk k bs (scan3 q v)
  done : r = some true → scan3 q v = [.out k bs]

/-- Nothing shown yet. -/
theorem facts_quiet {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {v : List WEv} {r : Option Bool}
    (hv : ∀ e ∈ v, Quiet3 e) (hr : r ≠ some true) : Facts q k bs v r :=
  ⟨fun e he => (hv e he).2, .inl (scan3_quiet hv q).1, fun h => absurd h hr⟩

/-- Facts after quiet events. -/
theorem facts_after_quiet {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {u v : List WEv}
    {r : Option Bool} (hu : ∀ e ∈ u, Quiet3 e) (hv : Facts q k bs v r) :
    Facts q k bs (u ++ v) r := by
  have hs : scan3 q (u ++ v) = scan3 q v := by
    rw [scan3_append, (scan3_quiet hu q).1, (scan3_quiet hu q).2]; rfl
  refine ⟨fun e he => ?_, hs ▸ hv.outs, fun h => hs ▸ hv.done h⟩
  rcases List.mem_append.1 he with he | he
  exacts [(hu e he).2, hv.code e he]

/-- A run of a call: nothing, the request, or the request, an answer and the rest. -/
theorem call_cases {α : Type} {m : (nsig I3).Op} {k : Option (List Val) → WProg I3 α}
    {v : List WEv} {r : Option α} (h : PRun (.call m k) v r) :
    (v <+: [.req m.1.1 m.2] ∧ r = none) ∨
      ∃ n v', v = [.req m.1.1 m.2, .imp m.1.1 m.2 n] ++ v' ∧ PRun (k n) v' r := by
  rcases PRun.call_inv h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n, v', rfl, h'⟩
  · exact .inl ⟨List.nil_prefix, rfl⟩
  · exact .inl ⟨List.prefix_refl _, rfl⟩
  · exact .inr ⟨n, v', rfl, h'⟩

/-- **A quiet call** keeps the facts of its continuations. -/
theorem facts_call {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {m : (nsig I3).Op}
    {c : Option (List Val) → WProg I3 Bool} (hq : Quiet3 (.req m.1.1 m.2))
    (hi : ∀ n, Quiet3 (.imp m.1.1 m.2 n))
    (hc : ∀ n v r, PRun (c n) v r → Facts q k bs v r) {v : List WEv} {r : Option Bool}
    (h : PRun (.call m c) v r) : Facts q k bs v r := by
  rcases call_cases h with ⟨hv, rfl⟩ | ⟨n, v', rfl, h'⟩
  · exact facts_quiet (fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ hq) (by simp)
  · refine facts_after_quiet (fun e he => ?_) (hc n v' r h')
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    exacts [hq, hi n]

/-- The run of a program that returns `false` at once. -/
theorem facts_false {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {v : List WEv} {r : Option Bool}
    (h : PRun (I := I3) (.pure false) v r) : Facts q k bs v r := by
  obtain ⟨rfl, hr⟩ := PRun.pure_inv h
  exact facts_quiet (fun e he => absurd he List.not_mem_nil) (by rcases hr with rfl | rfl <;> simp)

/-! ## Quiet functions -/

theorem quiet_canon {f : FnName} (hk : k3 f = .other) (h1 : f ≠ stdoutWrite3)
    (h2 : f ≠ W3.stderrWrite) (h3 : f ≠ W3.writeVia) (h4 : f ≠ exit3) (h5 : f ≠ W3.exitCode)
    (a : List Val) : Quiet3 (.req f a) ∧ ∀ n, Quiet3 (.imp f a n) :=
  ⟨quiet3_req a h4 h5, fun n => quiet3_imp' a n hk h1 h2 h3⟩

theorem quiet_dropW (a : List Val) :
    Quiet3 (.req cStreamDropW a) ∧ ∀ n, Quiet3 (.imp cStreamDropW a n) :=
  quiet_canon (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a

theorem quiet_wsNew (a : List Val) : Quiet3 (.req cWsNew a) ∧ ∀ n, Quiet3 (.imp cWsNew a n) :=
  quiet_canon (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a

theorem quiet_join (a : List Val) : Quiet3 (.req cJoin a) ∧ ∀ n, Quiet3 (.imp cJoin a n) :=
  quiet_canon (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) a

/-- `stream.drop-writable` is quiet. -/
theorem dropW_quiet {w : BitVec 32} {v : List WEv} {r : Option Bool} (h : PRun (dropW w) v r) :
    ∀ e ∈ v, Quiet3 e := by
  have h0 : PRun (.call (⟨cStreamDropW, dropW_mem⟩, [.u32 w]) fun _ => .pure true) v r := h
  rcases call_cases h0 with ⟨hv, -⟩ | ⟨n, v', rfl, h'⟩
  · exact fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ (quiet_dropW _).1
  · have hv' : v' = [] := (PRun.pure_inv h').1
    subst hv'
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl)
    exacts [(quiet_dropW _).1, (quiet_dropW _).2 n]

/-! ## The stages -/

/-- After the wait: quiet, and `true` only when the wait reported the whole write. -/
theorem afterWait_quiet {w : BitVec 32} {len : Nat} {n : Option (List Val)} {v : List WEv}
    {r : Option Bool} (h : PRun (afterWait w len n) v r) :
    (∀ e ∈ v, Quiet3 e) ∧ (r = some true → waitOk n w len = true) := by
  unfold afterWait at h
  by_cases hn : waitOk n w len = true
  · have h' : PRun (dropW w) v r := by simpa [hn] using h
    exact ⟨dropW_quiet h', fun _ => hn⟩
  · have h' : PRun (I := I3) (.pure false) v r := by simpa [hn] using h
    obtain ⟨rfl, hr⟩ := PRun.pure_inv h'
    exact ⟨fun e he => absurd he List.not_mem_nil, fun h' => by rcases hr with rfl | rfl <;> simp_all⟩

/-- The step of a `waitable-set.wait`. -/
theorem step_wait (q : Sc3) (a : List Val) (n : Option (List Val)) :
    q.step (.imp cWait a n) = q.waited n := by
  have hk : k3 cWait = .wait := by decide
  simp only [Sc3.step, hk]

theorem quiet_wait_req (a : List Val) : Quiet3 (.req cWait a) :=
  quiet3_req a (by decide) (by decide)

/-- The wait itself, then `afterWait`. -/
theorem wait_facts {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {w : BitVec 32}
    (hp : q.pend = [(w.toNat, bs)]) (hw : q.sinks.lookup w.toNat = some k) (hk : k.Plain)
    (hi : q.ins = []) {ws : BitVec 32} {v : List WEv} {r : Option Bool}
    (h : PRun ((callI cWait wait_mem [.u32 ws]).bind (afterWait w bs.length)) v r) :
    Facts q k bs v r := by
  have h0 : PRun (.call (⟨cWait, wait_mem⟩, [.u32 ws]) (afterWait w bs.length)) v r := h
  rcases call_cases h0 with ⟨hv, rfl⟩ | ⟨n, v', rfl, h'⟩
  · exact facts_quiet (fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ quiet_wait_req _) (by simp)
  obtain ⟨hq, hdone⟩ := afterWait_quiet h'
  have hs : scan3 q ([.req cWait [.u32 ws], .imp cWait [.u32 ws] n] ++ v') = (q.waited n).2 := by
    rw [scan3_append, (scan3_quiet hq _).1, List.append_nil]
    simp [scan3, step_wait]; rfl
  refine ⟨fun e he => ?_, hs ▸ waited_out hp hw hk hi n,
    fun hr => hs ▸ waited_all hp hw hk (hdone hr)⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl) | he
  exacts [rfl, rfl, (hq e he).2]

/-- **Waiting for a blocked write** of `bs` on `w`. -/
theorem waitWrite_facts {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {w : BitVec 32}
    (hp : q.pend = [(w.toNat, bs)]) (hw : q.sinks.lookup w.toNat = some k) (hk : k.Plain)
    (hi : q.ins = []) {v : List WEv} {r : Option Bool} (h : PRun (waitWrite w bs.length) v r) :
    Facts q k bs v r := by
  have h0 : PRun (.call (⟨cWsNew, wsNew_mem⟩, []) fun n => match u32Of n with
      | some ws => (callI cJoin join_mem [.u32 w, .u32 ws]).bind fun _ =>
          (callI cWait wait_mem [.u32 ws]).bind (afterWait w bs.length)
      | none => .pure false) v r := h
  refine facts_call (quiet_wsNew []).1 (quiet_wsNew []).2 (fun n v r h₁ => ?_) h0
  cases hu : u32Of n with
  | none => rw [hu] at h₁; exact facts_false h₁
  | some ws =>
    rw [hu] at h₁
    have h₁' : PRun (.call (⟨cJoin, join_mem⟩, [.u32 w, .u32 ws]) fun _ =>
        (callI cWait wait_mem [.u32 ws]).bind (afterWait w bs.length)) v r := h₁
    exact facts_call (quiet_join _).1 (quiet_join _).2
      (fun _ v r h₂ => wait_facts hp hw hk hi h₂) h₁'

/-- The step of a `stream.write`. -/
theorem step_write (q : Sc3) (w : BitVec 32) (bs : List (BitVec 8)) (n : Option (List Val)) :
    q.step (.imp cStreamWrite [.u32 w, bytesV bs] n) = q.wrote w.toNat bs (copyAns n) := by
  have hk : k3 cStreamWrite = .write := by decide
  simp [Sc3.step, hk, natOf, Host2.bytesOf_bytesV]


/-- Two events changing the state without output, then a run with facts. -/
theorem facts_cons_step {q q' : Sc3} {k : Sink} {bs : List (BitVec 8)} {e₁ e₂ : WEv}
    {v : List WEv} {r : Option Bool} (h₁ : Quiet3 e₁) (h₂ : q.step e₂ = (q', []))
    (hc : endCode3 e₂ = none) (hv : Facts q' k bs v r) : Facts q k bs ([e₁, e₂] ++ v) r := by
  have hs : scan3 q ([e₁, e₂] ++ v) = scan3 q' v := by
    simp [scan3, h₁.1 q, h₂]
  refine ⟨fun e he => ?_, hs ▸ hv.outs, fun h => hs ▸ hv.done h⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl) | he
  exacts [h₁.2, hc, hv.code e he]

/-- Two events, the second with an output, then quiet events. -/
theorem facts_cons_out {q q' : Sc3} {k : Sink} {bs : List (BitVec 8)} {e₁ e₂ : WEv}
    {O : List Out3} {v : List WEv} {r : Option Bool} (h₁ : Quiet3 e₁) (h₂ : q.step e₂ = (q', O))
    (hc : endCode3 e₂ = none) (hv : ∀ e ∈ v, Quiet3 e) (hO : OutOk k bs O)
    (hd : r = some true → O = [.out k bs]) : Facts q k bs ([e₁, e₂] ++ v) r := by
  have hs : scan3 q ([e₁, e₂] ++ v) = O := by
    simp [scan3, h₁.1 q, h₂, (scan3_quiet hv q').1]
  refine ⟨fun e he => ?_, hs ▸ hO, fun h => hs ▸ hd h⟩
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (rfl | rfl) | he
  exacts [h₁.2, hc, (hv e he).2]

theorem quiet_write_req (a : List Val) : Quiet3 (.req cStreamWrite a) :=
  quiet3_req a (by decide) (by decide)

/-- Two events with an output, then a run that returns `false` at once. -/
theorem facts_cons_false {q q' : Sc3} {k : Sink} {bs : List (BitVec 8)} {e₁ e₂ : WEv}
    {O : List Out3} {v : List WEv} {r : Option Bool} (h₁ : Quiet3 e₁) (h₂ : q.step e₂ = (q', O))
    (hc : endCode3 e₂ = none) (hO : OutOk k bs O) (h : PRun (I := I3) (.pure false) v r) :
    Facts q k bs ([e₁, e₂] ++ v) r := by
  have hv : v = [] := (PRun.pure_inv h).1
  have hr : r ≠ some true := by rcases (PRun.pure_inv h).2 with h' | h' <;> simp [h']
  rw [hv]
  exact facts_cons_out h₁ h₂ hc (fun e he => absurd he List.not_mem_nil) hO fun h => absurd h hr

/-- The write completed with `j` items. -/
theorem write_completed {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {w : BitVec 32}
    (hw : q.sinks.lookup w.toNat = some k) (hk : k.Plain) {n : Option (List Val)} {j : Nat}
    (hc : copyAns n = some (some (.completed, j))) {v : List WEv} {r : Option Bool}
    (h : PRun (if j = bs.length then dropW w else .pure false) v r) :
    Facts q k bs ([.req cStreamWrite [.u32 w, bytesV bs], .imp cStreamWrite [.u32 w, bytesV bs] n]
      ++ v) r := by
  have hst : q.step (.imp cStreamWrite [.u32 w, bytesV bs] n) =
      ((q.wrote w.toNat bs (copyAns n)).1, (q.wrote w.toNat bs (copyAns n)).2) :=
    step_write q w bs n
  have hO : OutOk k bs (q.wrote w.toNat bs (copyAns n)).2 := wrote_out hw hk bs _
  by_cases hj : j = bs.length
  · have hq : ∀ e ∈ v, Quiet3 e := dropW_quiet (by simpa [hj] using h)
    have hall : (q.wrote w.toNat bs (copyAns n)).2 = [.out k bs] := by
      rw [hc, hj]; exact wrote_all hw hk bs
    exact facts_cons_out (quiet_write_req _) hst rfl hq hO fun _ => hall
  · exact facts_cons_false (quiet_write_req _) hst rfl hO (by simpa [hj] using h)

/-- **The write of `bs` on `w`, then `afterWrite`**, from a state where `w` is the writable
end of a plain sink and nothing is pending. -/
theorem write_facts {q : Sc3} {k : Sink} {bs : List (BitVec 8)} {w : BitVec 32}
    (hw : q.sinks.lookup w.toNat = some k) (hk : k.Plain) (hp : q.pend = []) (hi : q.ins = [])
    {v : List WEv} {r : Option Bool}
    (h : PRun ((callI cStreamWrite write_mem [.u32 w, bytesV bs]).bind
      (afterWrite w bs.length)) v r) : Facts q k bs v r := by
  have h0 : PRun (.call (⟨cStreamWrite, write_mem⟩, [.u32 w, bytesV bs])
      (afterWrite w bs.length)) v r := h
  rcases call_cases h0 with ⟨hv, rfl⟩ | ⟨n, v', rfl, h'⟩
  · exact facts_quiet (fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ quiet_write_req _)
      (by simp)
  have hst : q.step (.imp cStreamWrite [.u32 w, bytesV bs] n) =
      ((q.wrote w.toNat bs (copyAns n)).1, (q.wrote w.toNat bs (copyAns n)).2) :=
    step_write q w bs n
  unfold afterWrite at h'
  split at h'
  · next j hc => exact write_completed hw hk hc h'
  · next hc =>
    have hst' : q.step (.imp cStreamWrite [.u32 w, bytesV bs] n) =
        ({ q with pend := [(w.toNat, bs)] }, []) := by
      rw [hst, hc, wrote_blocked, hp]
    exact facts_cons_step (quiet_write_req _) hst' rfl
      (waitWrite_facts (q := { q with pend := [(w.toNat, bs)] }) rfl hw hk hi h')
  · exact facts_cons_false (quiet_write_req _) hst rfl (wrote_out hw hk bs _) h'

theorem pairOf_eq {n : Option (List Val)} {r w : BitVec 32} (h : pairOf n = some (r, w)) :
    n = some [.u32 r, .u32 w] := by
  unfold pairOf at h; split at h <;> simp_all

theorem step_new_out (q : Sc3) (a : List Val) (n : Option (List Val)) :
    (q.step (.imp cStreamNew a n)).2 = [] := by
  have hk : k3 cStreamNew = .new := by decide
  simp only [Sc3.step, hk]
  split
  · split <;> rfl
  · rfl

theorem step_new (q : Sc3) (a : List Val) (r w : BitVec 32) :
    q.step (.imp cStreamNew a (some [.u32 r, .u32 w])) =
      ({ q with pairs := (r.toNat, w.toNat) :: q.pairs }, []) := by
  have hk : k3 cStreamNew = .new := by decide
  simp [Sc3.step, hk, natOf]

theorem step_outFn (ch : Channel) (q : Sc3) {r : BitVec 32} {w : Nat}
    (hr : q.pairs.lookup r.toNat = some w) (n : Option (List Val)) :
    q.step (.imp (outFn ch) [.u32 r] n) =
      ({ q with sinks := (w, Sink.ofChannel ch) :: q.sinks }, []) := by
  have hk : k3 (outFn ch) = .other := by cases ch <;> decide
  have hs : sinkCall q.fds (outFn ch) [.u32 r] = some (r.toNat, Sink.ofChannel ch) := by
    have hne : W3.stderrWrite ≠ stdoutWrite3 := by decide
    cases ch <;> simp [sinkCall, outFn, natOf, Sink.ofChannel, hne]
  simp only [Sc3.step, hk, hs, hr]

theorem quiet_new_req (a : List Val) : Quiet3 (.req cStreamNew a) :=
  quiet3_req a (by decide) (by decide)

theorem quiet_out_req (ch : Channel) (a : List Val) : Quiet3 (.req (outFn ch) a) :=
  quiet3_req a (by cases ch <;> decide) (by cases ch <;> decide)

/-- After `stream.new` answered a pair: `write-via-stream`, then the write. -/
theorem put3_pair {ch : Channel} {b : Bytes} {r' w : BitVec 32} {v : List WEv} {r : Option Bool}
    (h : PRun ((callI (outFn ch) (outFn_mem ch) [.u32 r']).bind fun _ =>
      (callI cStreamWrite write_mem [.u32 w, bytesV (toWasm b)]).bind
        (afterWrite w (toWasm b).length)) v r) :
    Facts { pairs := [(r'.toNat, w.toNat)] } (Sink.ofChannel ch) (toWasm b) v r := by
  have h₁ : PRun (.call (⟨outFn ch, outFn_mem ch⟩, [.u32 r']) fun _ =>
      (callI cStreamWrite write_mem [.u32 w, bytesV (toWasm b)]).bind
        (afterWrite w (toWasm b).length)) v r := h
  rcases call_cases h₁ with ⟨hv, rfl⟩ | ⟨n', v'', rfl, h₂⟩
  · exact facts_quiet (fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ quiet_out_req ch _)
      (by simp)
  · exact facts_cons_step (quiet_out_req ch _) (step_outFn ch _ (w := w.toNat) (by simp) n')
      rfl (write_facts (by simp) (Sink.plain_ofChannel ch) rfl rfl h₂)

/-- **A run of `put3 ch b`** from the empty scan state. -/
theorem put3_facts {ch : Channel} {b : Bytes} {v : List WEv} {r : Option Bool}
    (h : PRun (put3 ch b) v r) : Facts {} (Sink.ofChannel ch) (toWasm b) v r := by
  have h0 : PRun (.call (⟨cStreamNew, new_mem⟩, []) fun n => match pairOf n with
      | some (r, w) => (callI (outFn ch) (outFn_mem ch) [.u32 r]).bind fun _ =>
          (callI cStreamWrite write_mem [.u32 w, bytesV (toWasm b)]).bind
            (afterWrite w (toWasm b).length)
      | none => .pure false) v r := h
  rcases call_cases h0 with ⟨hv, rfl⟩ | ⟨n, v', rfl, h'⟩
  · exact facts_quiet (fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ quiet_new_req _)
      (by simp)
  cases hp : pairOf n with
  | none =>
    exact facts_cons_false (q := {}) (e₂ := .imp cStreamNew [] n) (quiet_new_req _) rfl rfl
      (.inl (step_new_out {} [] n)) (by simpa [hp] using h')
  | some rw =>
    have hn : n = some [.u32 rw.1, .u32 rw.2] := pairOf_eq hp
    have h₁ := put3_pair (ch := ch) (b := b) (by simpa [hp] using h')
    exact hn ▸ facts_cons_step (quiet_new_req _) (step_new {} [] rw.1 rw.2) rfl h₁

end Silmaril.Wasi.Cli.Host3

end
