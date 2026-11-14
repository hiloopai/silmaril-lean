module

public import Silmaril.Wasi.Cli.Host3.Defs
public import Silmaril.Wasi.Cli.Main.Thms

/-!
# The WASI 0.3 CLI view on the traces of the host's programs

Proofs for `Silmaril.Wasi.Cli.Host3.Thms`: the scan of `p3CliView` along concatenations
(`scan3_append`), quiet events (`Quiet3`: no output, no state change, no exit), and the steps of
the events of `put3` (`step_new`, `step_out`, `step_write`, `step_wait`) with what they show
(`wrote_out`, `waited_out`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli

open Silmaril.Cli
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (CopyResult)
open Silmaril.Wasi.Versions.P3 (natOf copyOf cStreamNew cStreamWrite cStreamDropW cWsNew cJoin cWait
  stdoutWrite3)

/-! ## The scan along concatenations -/

theorem scan3_append (q : Sc3) (t u : List WEv) :
    scan3 q (t ++ u) = scan3 q t ++ scan3 (q.after t) u := by
  induction t generalizing q with
  | nil => rfl
  | cons e t ih => simp [scan3, Sc3.after, ih]

theorem scan3_cons (q : Sc3) (e : WEv) (t : List WEv) :
    scan3 q (e :: t) = (q.step e).2 ++ scan3 (q.step e).1 t := rfl

/-- **A quiet event**: no output, no change of the scan's state, no exit. -/
def Quiet3 (e : WEv) : Prop := (∀ q : Sc3, q.step e = (q, [])) ∧ endCode3 e = none

theorem scan3_quiet {t : List WEv} (ht : ∀ e ∈ t, Quiet3 e) (q : Sc3) :
    scan3 q t = [] ∧ q.after t = q := by
  induction t with
  | nil => exact ⟨rfl, rfl⟩
  | cons e t ih =>
    have he : q.step e = (q, []) := (ht e List.mem_cons_self).1 q
    have ih' := ih fun e' he' => ht e' (List.mem_cons_of_mem _ he')
    exact ⟨by rw [scan3_cons, he, ih'.1]; rfl, by rw [Sc3.after, he, ih'.2]⟩

theorem quiet3_call (f : FnName) (a : List Val) : Quiet3 (.call f a) := ⟨fun _ => rfl, rfl⟩

theorem quiet3_req {f : FnName} (a : List Val) (h1 : f ≠ exit3) (h2 : f ≠ W3.exitCode) :
    Quiet3 (.req f a) := by
  refine ⟨fun _ => rfl, ?_⟩
  unfold endCode3; split <;> simp_all

/-- No sink is made by a function other than the three `write-via-stream`s. -/
theorem sinkCall_none {f : FnName} (h1 : f ≠ stdoutWrite3) (h2 : f ≠ W3.stderrWrite)
    (h3 : f ≠ W3.writeVia) (fds : Fds) (a : List Val) : sinkCall fds f a = none := by
  unfold sinkCall; split <;> simp_all

theorem quiet3_imp {f : FnName} (a : List Val) (n : Option (List Val)) (hk : k3 f = .other)
    (hs : ∀ fds, sinkCall fds f a = none) : Quiet3 (.imp f a n) := by
  refine ⟨fun q => ?_, rfl⟩
  simp only [Sc3.step, hk, hs]

/-- A quiet call: the function is read by nothing. -/
theorem quiet3_imp' {f : FnName} (a : List Val) (n : Option (List Val)) (hk : k3 f = .other)
    (h1 : f ≠ stdoutWrite3) (h2 : f ≠ W3.stderrWrite) (h3 : f ≠ W3.writeVia) :
    Quiet3 (.imp f a n) :=
  quiet3_imp a n hk fun fds => sinkCall_none h1 h2 h3 fds a

/-! ## Delivering -/

/-- A sink other than a file. -/
def Sink.Plain : Sink → Prop
  | .file _ _ => False
  | _ => True

theorem Sink.plain_ofChannel (ch : Channel) : (Sink.ofChannel ch).Plain := by cases ch <;> trivial

theorem deliver_plain {q : Sc3} {w : Nat} {k : Sink} (hw : q.sinks.lookup w = some k)
    (hk : k.Plain) (b : List (BitVec 8)) : q.deliver w b = (q, [.out k b]) := by
  unfold Sc3.deliver
  rw [hw]
  cases k with
  | file p off => exact absurd hk id
  | stdout => rfl
  | stderr => rfl

/-- What `p3CliView` may have seen of one write of `bs` on a sink `k`. -/
def OutOk (k : Sink) (bs : List (BitVec 8)) (O : List Out3) : Prop :=
  O = [] ∨ ∃ j, O = [.out k (bs.take j)] ∨ O = [.out k (bs.take j), .refused]

/-- **A `stream.write` on a plain sink** delivers a prefix of its bytes (and a refusal when
dropped); all of them when it completes with all of them; a blocked write is pending. -/
theorem wrote_out {q : Sc3} {w : Nat} {k : Sink} (hw : q.sinks.lookup w = some k)
    (hk : k.Plain) (bs : List (BitVec 8)) (c : Option (Option (CopyResult × Nat))) :
    OutOk k bs (q.wrote w bs c).2 := by
  unfold Sc3.wrote
  split
  · next j => exact .inr ⟨j, .inl (by rw [deliver_plain hw hk])⟩
  · next j => exact .inr ⟨j, .inr (by simp only [deliver_plain hw hk]; rfl)⟩
  · exact .inl rfl
  · exact .inl rfl

theorem wrote_all {q : Sc3} {w : Nat} {k : Sink} (hw : q.sinks.lookup w = some k)
    (hk : k.Plain) (bs : List (BitVec 8)) :
    (q.wrote w bs (some (some (.completed, bs.length)))).2 = [.out k bs] := by
  simp [Sc3.wrote, deliver_plain hw hk]

theorem wrote_blocked (q : Sc3) (w : Nat) (bs : List (BitVec 8)) :
    q.wrote w bs (some none) = ({ q with pend := (w, bs) :: q.pend }, []) := rfl

/-- **A `waitable-set.wait`** with one pending write of `bs` on `w`, to a plain sink, and no
stdin: a prefix of `bs`; all of it when it reports the write completed with all of it. -/
theorem waited_out {q : Sc3} {w : Nat} {k : Sink} {bs : List (BitVec 8)}
    (hp : q.pend = [(w, bs)]) (hw : q.sinks.lookup w = some k) (hk : k.Plain) (hi : q.ins = [])
    (n : Option (List Val)) : OutOk k bs (q.waited n).2 := by
  unfold Sc3.waited
  split
  · next cv iv pv =>
    split
    · next w' _ j _ _ _ =>
      rw [hp]
      by_cases hww : w' = w
      · subst hww; exact .inr ⟨j, .inl (by simp [deliver_plain hw hk])⟩
      · have hb : (w' == w) = false := by simpa using hww
        exact .inl (by simp [List.lookup, hb])
    · exact .inl rfl
  · split
    · exact .inl (by simp [hi])
    · exact .inl rfl
  · exact .inl rfl

theorem waited_all {q : Sc3} {w : BitVec 32} {k : Sink} {bs : List (BitVec 8)}
    (hp : q.pend = [(w.toNat, bs)]) (hw : q.sinks.lookup w.toNat = some k) (hk : k.Plain)
    {n : Option (List Val)} (hn : Host3.waitOk n w bs.length = true) :
    (q.waited n).2 = [.out k bs] := by
  unfold Host3.waitOk at hn
  split at hn
  · next cv iv pv =>
    obtain ⟨hc, hi, hpv⟩ := of_decide_eq_true hn
    simp [Sc3.waited, hc, hi, hpv, hp, deliver_plain hw hk]
  · exact absurd hn (by simp)

end Silmaril.Wasi.Cli

end
