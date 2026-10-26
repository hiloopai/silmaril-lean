module

public import Silmaril.Apps.Sha256sum.IOLayer.Write

/-! # The stdin path of `sha256sum-min`, decompiled to the stream level

Status: **VERIFIED** (no `sorry`, no new axioms).

`s1Prog` is the stdin path of `sha256sum-min` (`apps/sha256sum-min/src/sha256sum.c`) with
its output layer factored out: `digest_fd(0)` reads standard input to end of file in
32768-byte requests, `output_file` emits the 68-byte record with `out_putc`, `main` closes
descriptor 0, and `close_stdout` reads the layer state (`olen != 0`, `out_error`), flushes if
anything is pending, closes 1, tests the gnulib `close_stream` condition, then closes 2.

`s1_satisfiesF`: the program **running over the concrete buffer layer `lb _ 4096`** (the
machine the binary is simulated against, call for call) satisfies the specification on the
stdin tier with a working **or full** standard output (`StdinDomF`): every exiting run,
under every read chunking and every write split, shows exactly `sha256sum w`. On a full
output the record's newline flush fails, so `close_stdout` reports "write error" with no
errno text and exits 1. `s1_satisfies` is the original S1 domain.

`program_name` is taken to be `argv[0]`, as the specification says. The binary's
`set_program_name` strips a `/.libs/` directory and an `lt-` prefix (gnulib), so for such an
`argv[0]` the binary and the specification disagree on every diagnostic (checked on the
binary: `argv[0] = "/x/.libs/lt-foo"` prints `foo: …`). The binary targets need that case
excluded from the domain, or the specification changed. The proof never sees a `write` call: it goes through `exec_to_mexec` and the
stream-level lemmas of `IOLayer.Write`, and the buffer is the Lean list `putsBuf`
computes.

Consequently the S1 binary target reduces to `S1RefinesLB`: a call-for-call simulation of
the x86 binary by `lb s1Machine 4096`, in which the memory `obuf[0, olen)` and `out_error`
are related to the layer's `buf` and `err` (`s1_of_refinesLB`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys.IOLayer

open Silmaril.Apps.Sha256sum

/-- The control points of the stdin path. -/
inductive Ph where
  | reading (acc : Bytes)
  | putting (rest : Bytes)
  | close0
  | query
  | flushing (pend prev : Bool)
  | close1 (pend prev : Bool) (fe : Option Errno)
  /-- `error_msg (0, fe, "write error")`: its `out_flush`, then the message. -/
  | report (fe : Option Errno)
  | report2 (fe : Option Errno)
  | close2
  | done
  | exit1
  /-- A path the program takes only off the domain. -/
  | failed

/-- The program's state: `program_name` and the control point. -/
structure S1 where
  pn : Bytes
  ph : Ph

/-- The "write error" diagnostic, with the errno text when there is one. -/
def writeErrorMsg (pn : Bytes) : Option Errno → Bytes
  | none => diag pn (lit "write error")
  | some e => diagE pn (lit "write error") e

def s1Step : S1 → OAction S1
  | ⟨pn, ph⟩ =>
    match ph with
    | .reading acc => .call (.read 0 32768) fun
        | .data [] => ⟨pn, .putting (stdinRecord acc)⟩
        | .data b => ⟨pn, .reading (acc ++ b)⟩
        | _ => ⟨pn, .failed⟩
    | .putting [] => .tau ⟨pn, .close0⟩
    | .putting (c :: cs) => .putc c ⟨pn, .putting cs⟩
    | .close0 => .call (.close 0) fun
        | .ok _ => ⟨pn, .query⟩
        | _ => ⟨pn, .failed⟩
    | .query => .query fun pend prev => ⟨pn, .flushing pend prev⟩
    | .flushing pend prev =>
      if pend then .flush fun fe => ⟨pn, .close1 pend prev fe⟩
      else .tau ⟨pn, .close1 pend prev none⟩
    | .close1 _ prev fe => .call (.close 1) fun
        | .ok _ => if prev || fe.isSome then ⟨pn, .report fe⟩ else ⟨pn, .close2⟩
        | _ => ⟨pn, .failed⟩
    | .report fe => .flush fun _ => ⟨pn, .report2 fe⟩
    | .report2 fe => .writeAll 2 (writeErrorMsg pn fe) fun _ => ⟨pn, .exit1⟩
    | .close2 => .call (.close 2) fun
        | .ok _ => ⟨pn, .done⟩
        | _ => ⟨pn, .failed⟩
    | .done => .exit 0
    | .exit1 => .exit 1
    | .failed => .stuck

def s1Machine : OMachine := ⟨S1, s1Step⟩

/-- The initial state: `program_name` is `argv[0]`, the program is at `digest_fd(0)`, the
buffer is empty, no error. -/
def s1Init (w : World) : (lb s1Machine 4096).State := .run ⟨w.prog, .reading []⟩ [] false

/-- The stdin tier, with a working **or full** standard output. -/
def StdinDomF (w : World) : Prop := w.argv.length = 1 ∧ ∃ b, w.stdin = .bytes b

theorem stdinRecord_ne_nil (d : Bytes) : stdinRecord d ≠ [] := by
  intro h; have := stdinRecord_length d; rw [h] at this; simp at this

theorem stdinRecord_getLast? (d : Bytes) : (stdinRecord d).getLast? = some 10 := by
  simp [stdinRecord, lit, List.getLast?_append]

/-- The specification on the stdin tier, for both kinds of standard output. -/
theorem sha256sum_stdinF (P : Bytes) (posix : Bool) (fs : Bytes → ReadResult) (b : Bytes)
    (full : Bool) :
    sha256sum { argv := [P], posix, fs, stdin := .bytes b, stdoutFull := full } =
      if full then { stdout := [], stderr := diag (progName P) (lit "write error"), status := 1 }
      else { stdout := stdinRecord b, stderr := [], status := 0 } := by
  simp only [sha256sum, World.prog, World.argv0, List.headD_cons, List.tail_cons]
  have hs : scan P posix [] = .done {} [] := rfl
  have hv : validate {} = none := rfl
  rw [hs]
  simp only [hv, runMode, operandsOrStdin, ↓reduceIte, computeAll, computeOne, readPath,
    readStdin, Bool.and_true]
  have hrec := stdinRecord_getLast? b
  have hne := stdinRecord_ne_nil b
  simp only [stdinRecord] at hrec hne
  cases full <;>
    simp [finish, St.emit, computeLine, recordBody, delim, stdinRecord, dash, problematic, lit,
      isProblemByte, World.prog, World.argv0] at hrec hne ⊢

/-- The record is one line: on a working stdout `out_putc` sends all of it, on a full one
nothing, and the buffer ends empty; the sticky flag records the failed newline flush. -/
theorem putsF_record (full : Bool) (d : Bytes) :
    putsF full 4096 [] false (stdinRecord d) = (if full then [] else stdinRecord d, [], full) := by
  have hne := stdinRecord_ne_nil d
  have hl := stdinRecord_getLast? d
  generalize stdinRecord d = r at hne hl ⊢
  cases full with
  | false =>
    rw [putsF_false]
    have h2 := putsBuf_line 4096 [] r hne ((List.getLast_eq_iff_getLast?_eq_some hne).mpr hl)
    have h := putsBuf_inv 4096 [] r
    rw [h2] at h
    simp only [List.append_nil, List.nil_append] at h
    simp [h, h2]
  | true =>
    obtain ⟨h1, h2⟩ := putsF_true 4096 [] false r
    obtain ⟨h3, h4⟩ := (h2 hne).1 hl
    show _ = ([], [], true)
    exact Prod.ext h1 (Prod.ext h3 h4)

/-- After the record: the closes, through `close_stdout`, on either kind of stdout. -/
theorem s1_tail {w : World} {pn : Bytes} {k : KState} {aevs : List AEvent} {n : Nat}
    (h0 : k.fds 0 ≠ none) (h1 : k.fds 1 = some .stdout) (h2 : k.fds 2 = some .stderr)
    (m : MExec s1Machine 4096 (WorldStep w) (.run ⟨pn, .putting []⟩ [] w.stdoutFull) k aevs n) :
    awritten 1 aevs = [] ∧
      awritten 2 aevs = (if w.stdoutFull then diag pn (lit "write error") else []) ∧
      n = (if w.stdoutFull then 1 else 0) := by
  have m := mexec_tau (s' := (⟨pn, .close0⟩ : S1)) rfl m
  obtain ⟨r, k1, aevs1, he, rfl, m⟩ := mexec_call (c := .close 0) rfl m
  obtain ⟨rfl, rfl⟩ := close_inv h0 he
  have m := mexec_query (f := fun pend prev => (⟨pn, .flushing pend prev⟩ : S1)) rfl m
  cases hf : w.stdoutFull
  · rw [hf] at m
    have m := mexec_tau (s' := (⟨pn, .close1 false false none⟩ : S1)) rfl m
    obtain ⟨r, k2, aevs2, he, rfl, m⟩ := mexec_call (c := .close 1) rfl m
    obtain ⟨rfl, rfl⟩ := close_inv (by simp [KState.set, h1]) he
    obtain ⟨r, k3, aevs3, he, rfl, m⟩ := mexec_call (c := .close 2) rfl m
    obtain ⟨rfl, rfl⟩ := close_inv (by simp [KState.set, h2]) he
    obtain ⟨rfl, rfl⟩ := mexec_exit (st := 0) rfl m
    simp [awritten, written]
  · rw [hf] at m
    have m := mexec_tau (s' := (⟨pn, .close1 false true none⟩ : S1)) rfl m
    obtain ⟨r, k2, aevs2, he, rfl, m⟩ := mexec_call (c := .close 1) rfl m
    obtain ⟨rfl, rfl⟩ := close_inv (by simp [KState.set, h1]) he
    have m : MExec s1Machine 4096 (WorldStep w) (.run ⟨pn, .report none⟩ [] true)
        ((k.set 0 none).set 1 none) aevs2 n := by
      simpa using m
    have m := mexec_run_tau (A := s1Machine) (cap := 4096)
      (t0 := flushThen [] true fun e b er => .run ⟨pn, .report2 none⟩ b er) rfl m
    simp only [flushThen, ↓reduceIte] at m
    obtain ⟨aevs3, m, hw⟩ := mexec_writeAll (A := s1Machine) (cap := 4096) (w := w)
      (fd := 2) (b := writeErrorMsg pn none) (f := fun _ => (⟨pn, .exit1⟩ : S1))
      (sink_stderr (k := (k.set 0 none).set 1 none) (by simp [KState.set, h2]))
      (s := (⟨pn, .report2 none⟩ : S1)) rfl m
    obtain ⟨rfl, rfl⟩ := mexec_exit (st := 1) rfl m
    simp [awritten, written, hw, writeErrorMsg]

theorem s1_reading {w : World} {t : LState s1Machine.State} {k : KState}
    {aevs : List AEvent} {n : Nat} (m : MExec s1Machine 4096 (WorldStep w) t k aevs n) :
    ∀ pn acc rest, t = .run ⟨pn, .reading acc⟩ [] false → k.stdin = .bytes rest →
      k.fds 0 = some .stdin → k.fds 1 = some .stdout → k.fds 2 = some .stderr →
      awritten 1 aevs = (if w.stdoutFull then [] else stdinRecord (acc ++ rest)) ∧
      awritten 2 aevs = (if w.stdoutFull then diag pn (lit "write error") else []) ∧
      n = (if w.stdoutFull then 1 else 0) := by
  induction m with
  | exit hs => intro pn acc rest e; cases e; cases hs
  | tau hs _ _ => intro pn acc rest e; subst e; simp [lbStep, s1Machine, s1Step] at hs
  | wa _ _ => intro pn acc rest e; cases e
  | @call s buf err c f k r k' aevs n hs he run ih =>
    intro pn acc rest e hin h0 h1 h2
    cases e
    simp only [s1Machine, s1Step] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨b, rfl, ⟨hpre, -, hnil⟩, rfl⟩ := read_stdin_inv h0 hin he
    cases b with
    | nil =>
      have hr : rest = [] := (hnil rfl).resolve_right (by decide)
      subst hr
      have run' : MExec s1Machine 4096 (WorldStep w)
          (.run ⟨pn, .putting (stdinRecord acc)⟩ [] false) { k with stdin := .bytes [] } aevs n := by
        simpa using run
      obtain ⟨aevs', m', hw⟩ := mexec_putsF (A := s1Machine) (cap := 4096)
        (P := fun cs => (⟨pn, .putting cs⟩ : S1)) (fun _ _ => rfl)
        (k := { k with stdin := .bytes [] }) (full := w.stdoutFull) ⟨h1, rfl⟩
        (stdinRecord acc) [] false aevs run'
      rw [putsF_record] at m' hw
      obtain ⟨o1, o2, rfl⟩ := s1_tail (k := { k with stdin := .bytes [] }) (by simp [h0]) h1 h2 m'
      refine ⟨?_, ?_, rfl⟩
      · simp only [awritten, written, hw 1, o1]; cases w.stdoutFull <;> simp
      · simp [awritten, written, hw 2, o2]
    | cons x xs =>
      obtain ⟨u, rfl⟩ := hpre
      have := ih pn (acc ++ x :: xs) u rfl (by simp) h0 h1 h2
      simpa [awritten, written, List.append_assoc] using this

/-- **S1, both kinds of standard output, for the stream program over the concrete buffer
layer.** On a full standard output the record's newline flush fails, so `close_stdout`
reports "write error" with no errno text and the status is 1, as the specification says. -/
theorem s1_satisfiesF :
    Satisfies (lb s1Machine 4096) WorldStep s1Init StdinDomF := by
  intro w ⟨hargv, ⟨b, hb⟩⟩ evs n run
  obtain ⟨P, hP⟩ : ∃ P, w.argv = [P] := by
    match h : w.argv, hargv with
    | [P], _ => exact ⟨P, rfl⟩
  have hw : w = { w with argv := [P], stdin := .bytes b } := by
    cases w; simp_all
  obtain ⟨aevs, m, hwr⟩ := exec_to_mexec run
  obtain ⟨h1, h2, hn⟩ := s1_reading m w.prog [] b rfl (by simp [KState.init, hb])
    (by simp [KState.init]) (by simp [KState.init]) (by simp [KState.init])
  have hprog : w.prog = progName P := by
    simp [World.prog, Silmaril.Apps.Sha256sum.World.argv0, hP]
  rw [hw, sha256sum_stdinF]
  simp only [observe, hwr, h1, h2, hn, ← hprog]
  cases w.stdoutFull <;> rfl

/-- The original S1 domain (working standard output) is a special case. -/
theorem s1_satisfies : Satisfies (lb s1Machine 4096) WorldStep s1Init StdinDom :=
  s1_satisfiesF.restrict fun _ ⟨ha, hb, _⟩ => ⟨ha, hb⟩

/-- The S1 binary target through the layer: the binary is simulated, call for call, by the
stream program over `sha256sum-min`'s own buffer layer. -/
def S1RefinesLB {B : Machine} (initB : World → B.State → Prop) (dom : World → Prop) : Prop :=
  TraceRefinesRel B (lb s1Machine 4096) WorldStep initB s1Init dom

theorem s1_of_refinesLB {B : Machine} {initB : World → B.State → Prop}
    (h : S1RefinesLB initB StdinDomF) : SatisfiesRel B WorldStep initB StdinDomF :=
  SatisfiesRel.of_traceRefines h s1_satisfiesF

end Silmaril.Apps.Sha256sum.Sys.IOLayer
