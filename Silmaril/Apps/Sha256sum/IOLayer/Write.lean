module

public import Silmaril.Apps.Sha256sum.StdinRef

/-! # Decompiling a userspace output buffer: the write layer

Status: **VERIFIED** (no `sorry`, no axioms beyond Lean's standard three).

A C program that prints through a stdio-like buffer (`sha256sum-min`'s `obuf`/`olen`/
`out_error` with `out_putc`, `out_flush`, `write_all`; glibc's `_IOLBF` `stdout`) issues
`write` system calls at points chosen by the buffer policy, in pieces chosen by the kernel
(partial writes). This file separates the two concerns.

* `OAction`/`OMachine`: an **abstract stream program**. Besides internal steps, raw system
  calls and exit, it has the four operations of the C output layer as primitives:
  `putc c` (`out_putc`), `flush` (`out_flush`, returning its errno), `query` (`olen != 0` and
  `out_error`, as `close_stdout` reads them) and `writeAll fd b` (`write_all`, used
  unbuffered for standard error).
* `lb A cap`: the **concrete layer**, a `Sys.Machine` that implements those primitives exactly
  as `sha256sum-min` does: a `cap`-byte buffer, flushed when full before appending and after
  every newline, discarded on a failed flush (with a sticky error flag), and `write_all` as
  a `write` loop that retries partial writes and stops at the first error. This is the
  machine the binary is simulated against, call for call (`Sys.TraceRefines`); its state
  holds the buffer contents that the binary keeps in `obuf[0, olen)`.
* `WA E fd k b k' e acc`: one **atomic** `write_all` of `b` under environment `E`:
  final kernel state `k'`, errno `e`, bytes accepted `acc`.
* `MExec A E`: the **macro-step semantics** of the layer, in which each `write_all` loop is
  one `WA` step and records one `wrote fd acc` event; all other steps are those of `lb`.

Theorems:

* `exec_to_mexec` (**loop summarisation**): every exiting run of `lb A cap` is an exiting
  run of `MExec` with the same status, and the bytes written on every descriptor agree
  (`written fd evs = awritten fd aevs`). Nothing is assumed about `E`. The proof is one
  induction; the only lemma it needs is the loop invariant `wa_exec`.
* `wa_stdout` / `wa_stderr` / `wa_full`: what `WA` is under `Sys.WorldStep`: on a working
  standard output (or standard error) every `write_all` accepts **all** its bytes and leaves
  the kernel unchanged, whatever split the kernel chose; on a full standard output it accepts
  nothing and fails with `ENOSPC` after one call.
* `putc_sent` / `putcs_sent` (**write coalescing**): on a working sink the ghost invariant
  `sent ++ buf = emitted` is preserved by `out_putc`, independently of `cap` and of where the
  newlines are. With `flush_sent` it gives: after a final flush everything emitted was sent,
  so the buffered program's output equals the unbuffered one's. `putsBuf_prefix` is the
  prefix form a per-byte trace model (LPS) needs.
* `flushF`/`putcF`/`putsF`, `mexec_flushThenF`/`mexec_putcF`/`mexec_putsF`: the same for
  either kind of standard output (working or full). `putsF_true` (**full-stdout policy**):
  nothing is sent, and after a nonempty output the last byte decides the layer state (a
  final newline leaves the buffer empty with the sticky flag set; anything else leaves bytes
  pending), which is what `close_stdout` turns into "write error" without or with `ENOSPC`.

The reusable technique: (1) give the program's I/O helpers as primitives of an abstract
machine; (2) prove once that their implementation (`lb`) macro-steps to atomic
specifications (`WA`); (3) characterise the atomic specification under the concrete kernel
(`wa_stdout`); (4) reason about the rest of the program at the stream level, where the
buffer is a Lean list and a `write` loop is an equation.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Sys.IOLayer

open Silmaril.Apps.Sha256sum

/-! ## Abstract stream programs -/

/-- The actions of a program written against the C output layer. -/
inductive OAction (S : Type) where
  | tau (s : S)
  /-- A raw system call (reads, `openat`, `close`; not writes to standard output). -/
  | call (c : Call) (k : Ret → S)
  | exit (status : Nat)
  | stuck
  /-- `out_putc c`. -/
  | putc (c : UInt8) (s : S)
  /-- `out_flush ()`: `none` on success (or nothing to flush), else the errno. -/
  | flush (k : Option Errno → S)
  /-- Read the layer state: (`olen != 0`, `out_error`). -/
  | query (k : Bool → Bool → S)
  /-- `write_all fd b`, unbuffered. -/
  | writeAll (fd : Nat) (b : Bytes) (k : Option Errno → S)

structure OMachine where
  State : Type
  step : State → OAction State

/-! ## The concrete layer -/

/-- States of `lb A cap`: running the abstract program with buffer `buf` and sticky error
flag `err`, or inside a `write_all` loop with `rest` left to write. -/
inductive LState (S : Type) where
  | run (s : S) (buf : Bytes) (err : Bool)
  | wa (fd : Nat) (rest : Bytes) (k : Option Errno → LState S)

/-- `out_flush` from buffer `buf` and flag `err`, continuing with `k errno buf' err'`. -/
def flushThen {S : Type} (buf : Bytes) (err : Bool)
    (k : Option Errno → Bytes → Bool → LState S) : LState S :=
  if buf = [] then k none [] err
  else .wa 1 buf fun e => k e [] (err || e.isSome)

/-- The second half of `out_putc c` (after the "buffer full" flush): append `c`, flush after
a newline. -/
def appendThen {S : Type} (c : UInt8) (s : S) (buf : Bytes) (err : Bool) : LState S :=
  if c = 10 then flushThen (buf ++ [c]) err fun _ b e => .run s b e
  else .run s (buf ++ [c]) err

/-- The step function of the layer. -/
def lbStep (A : OMachine) (cap : Nat) : LState A.State → Action (LState A.State)
  | .run s buf err =>
    match A.step s with
    | .tau s' => .tau (.run s' buf err)
    | .call c f => .call c fun r => .run (f r) buf err
    | .exit n => .exit n
    | .stuck => .stuck
    | .putc c s' =>
      if buf.length = cap then .tau (flushThen buf err fun _ b e => appendThen c s' b e)
      else .tau (appendThen c s' buf err)
    | .flush f => .tau (flushThen buf err fun e b er => .run (f e) b er)
    | .query f => .tau (.run (f (buf ≠ []) err) buf err)
    | .writeAll fd b f => .tau (.wa fd b fun e => .run (f e) buf err)
  | .wa fd rest k =>
    if rest = [] then .tau (k none)
    else .call (.write fd rest) fun
      | .ok n => .wa fd (rest.drop n) k
      | .err e => k (some e)
      -- `sha256sum-min` reads the reply from `rax`, which a `data` reply sets to its length
      | .data d => .wa fd (rest.drop d.length) k

/-- `sha256sum-min`'s output layer around the abstract program `A`, with a `cap`-byte buffer
(4096 in the binary). -/
def lb (A : OMachine) (cap : Nat) : Machine := ⟨LState A.State, lbStep A cap⟩

/-! ## Atomic `write_all` -/

/-- One `write_all fd b` under `E`: from kernel state `k` to `k'`, with errno `e`, the bytes
`acc` accepted by the kernel. -/
inductive WA (E : Env) (fd : Nat) : KState → Bytes → KState → Option Errno → Bytes → Prop
  | nil {k} : WA E fd k [] k none []
  | ok {k rest n k1 k2 e acc} : rest ≠ [] → E k (.write fd rest) (.ok n) k1 →
      WA E fd k1 (rest.drop n) k2 e acc → WA E fd k rest k2 e (rest.take n ++ acc)
  | err {k rest er k1} : rest ≠ [] → E k (.write fd rest) (.err er) k1 →
      WA E fd k rest k1 (some er) []
  | data {k rest d k1 k2 e acc} : rest ≠ [] → E k (.write fd rest) (.data d) k1 →
      WA E fd k1 (rest.drop d.length) k2 e acc → WA E fd k rest k2 e acc

/-- Macro-level events: raw calls, and whole `write_all`s with the bytes they got accepted. -/
inductive AEvent where
  | raw (e : Event)
  | wrote (fd : Nat) (acc : Bytes)

/-- The bytes accepted on `fd`. -/
def awritten (fd : Nat) : List AEvent → Bytes
  | [] => []
  | .raw e :: rest => written fd [e] ++ awritten fd rest
  | .wrote d acc :: rest => (if d = fd then acc else []) ++ awritten fd rest

/-- The macro-step semantics of the layer: `lb`'s steps, with each `write_all` loop atomic. -/
inductive MExec (A : OMachine) (cap : Nat) (E : Env) :
    LState A.State → KState → List AEvent → Nat → Prop
  | exit {s buf err k n} : A.step s = .exit n → MExec A cap E (.run s buf err) k [] (n % 256)
  | tau {t t' k evs n} : lbStep A cap t = .tau t' → (∀ fd rest k', t ≠ .wa fd rest k') →
      MExec A cap E t' k evs n → MExec A cap E t k evs n
  | call {s buf err c f k r k' evs n} : A.step s = .call c f → E k c r k' →
      MExec A cap E (.run (f r) buf err) k' evs n →
      MExec A cap E (.run s buf err) k (.raw (c, r) :: evs) n
  | wa {fd rest kont k k' e acc evs n} : WA E fd k rest k' e acc →
      MExec A cap E (kont e) k' evs n →
      MExec A cap E (.wa fd rest kont) k (.wrote fd acc :: evs) n

/-! ## Loop summarisation -/

theorem written_cons (fd : Nat) (e : Event) (evs : List Event) :
    written fd (e :: evs) = written fd [e] ++ written fd evs := by
  rcases e with ⟨c, r⟩
  cases c <;> cases r <;> simp [written]

/-- Inversion of a macro-step run from inside a `write_all` loop. -/
theorem mexec_wa_inv {A : OMachine} {cap : Nat} {E : Env} {fd : Nat} {rest : Bytes}
    {kont : Option Errno → LState A.State} {k : KState} {aevs : List AEvent} {n : Nat}
    (h : MExec A cap E (.wa fd rest kont) k aevs n) :
    ∃ k' e acc aevs', aevs = .wrote fd acc :: aevs' ∧ WA E fd k rest k' e acc ∧
      MExec A cap E (kont e) k' aevs' n := by
  cases h with
  | tau _ hne _ => exact absurd rfl (hne fd rest kont)
  | wa hwa m => exact ⟨_, _, _, _, rfl, hwa, m⟩

/-- **Loop summarisation.** Every exiting run of the concrete layer is a macro-step run with
the same status and the same bytes on every descriptor. Nothing is assumed about `E`. -/
theorem exec_to_mexec {A : OMachine} {cap : Nat} {E : Env} {t : (lb A cap).State} {k : KState}
    {evs : List Event} {n : Nat} (h : Exec (lb A cap) E t k evs n) :
    ∃ aevs, MExec A cap E t k aevs n ∧ ∀ fd, written fd evs = awritten fd aevs := by
  induction h with
  | @exit t k n hs =>
    rcases t with ⟨s, buf, err⟩ | ⟨fd, rest, kont⟩
    · simp only [lb, lbStep] at hs
      split at hs <;> (try split_ifs at hs) <;> simp at hs
      subst hs
      exact ⟨[], .exit (by assumption), fun _ => rfl⟩
    · simp only [lb, lbStep] at hs; split_ifs at hs
  | @tau t t' k evs n hs run ih =>
    obtain ⟨aevs, m, hw⟩ := ih
    rcases t with ⟨s, buf, err⟩ | ⟨fd, rest, kont⟩
    · exact ⟨aevs, .tau hs (by simp) m, hw⟩
    · simp only [lb, lbStep] at hs
      split_ifs at hs with hr
      cases hs; subst hr
      exact ⟨.wrote fd [] :: aevs, .wa .nil m, fun fd' => by simp [awritten, hw]⟩
  | @call t c f k r k' evs n hs he run ih =>
    obtain ⟨aevs, m, hw⟩ := ih
    rcases t with ⟨s, buf, err⟩ | ⟨fd, rest, kont⟩
    · simp only [lb, lbStep] at hs
      split at hs <;> (try split_ifs at hs) <;> (try simp at hs)
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨.raw (c, r) :: aevs, .call (by assumption) he m, fun fd => ?_⟩
      rw [written_cons, hw]; rfl
    · simp only [lb, lbStep] at hs
      split_ifs at hs with hr
      obtain ⟨rfl, rfl⟩ := hs
      rcases r with j | d | er
      · obtain ⟨k2, e, acc, aevs', rfl, hwa, m'⟩ := mexec_wa_inv m
        refine ⟨.wrote fd (rest.take j ++ acc) :: aevs', .wa (.ok hr he hwa) m', fun fd' => ?_⟩
        rw [written_cons, hw]
        by_cases h : fd = fd' <;> simp [written, awritten, h]
      · obtain ⟨k2, e, acc, aevs', rfl, hwa, m'⟩ := mexec_wa_inv m
        exact ⟨.wrote fd acc :: aevs', .wa (.data hr he hwa) m', fun fd' => by
          rw [written_cons, hw]; simp [written, awritten]⟩
      · exact ⟨.wrote fd [] :: aevs, .wa (.err hr he) m, fun fd' => by
          rw [written_cons, hw]; simp [written, awritten]⟩

/-! ## `write_all` under the world's kernel -/

theorem write_stderr_inv {w : World} {k : KState} {p : Bytes} {r : Ret} {k' : KState}
    (h2 : k.fds 2 = some .stderr) (h : WorldStep w k (.write 2 p) r k') :
    ∃ n, r = .ok n ∧ Accepts p n ∧ k' = k := by
  cases h with
  | writeErr _ ha => exact ⟨_, rfl, ha, rfl⟩
  | writeOut hs _ _ => simp_all
  | writeFull hs _ => simp_all
  | writeBad hb => rcases hb with hb | hb | ⟨_, _, hb⟩ <;> simp_all

/-- A descriptor every write to which is accepted, in part, without changing the kernel. -/
def Sink (w : World) (k : KState) (fd : Nat) : Prop :=
  ∀ p r k', WorldStep w k (.write fd p) r k' → ∃ n, r = .ok n ∧ Accepts p n ∧ k' = k

theorem sink_stdout {w : World} {k : KState} (h1 : k.fds 1 = some .stdout)
    (hf : w.stdoutFull = false) : Sink w k 1 :=
  fun _ _ _ h => write_stdout_inv h1 hf h

theorem sink_stderr {w : World} {k : KState} (h2 : k.fds 2 = some .stderr) : Sink w k 2 :=
  fun _ _ _ h => write_stderr_inv h2 h

/-- **`write_all` on a working sink** accepts all its bytes, whatever the kernel's split, and
leaves the kernel unchanged. -/
theorem wa_sink {w : World} {fd : Nat} {k : KState} {b : Bytes} {k' : KState}
    {e : Option Errno} {acc : Bytes} (h : WA (WorldStep w) fd k b k' e acc) (hs : Sink w k fd) :
    k' = k ∧ e = none ∧ acc = b := by
  induction h with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | ok _ he _ ih =>
    obtain ⟨m, hm, -, rfl⟩ := hs _ _ _ he
    cases hm
    obtain ⟨rfl, rfl, rfl⟩ := ih hs
    exact ⟨rfl, rfl, List.take_append_drop _ _⟩
  | err _ he => obtain ⟨_, hm, -⟩ := hs _ _ _ he; cases hm
  | data _ he _ _ => obtain ⟨_, hm, -⟩ := hs _ _ _ he; cases hm

/-- On a working sink the full `write_all` exists (so the layer is not vacuous). -/
theorem wa_sink_total {w : World} {fd : Nat} {k : KState}
    (hfd : (k.fds fd = some .stdout ∧ w.stdoutFull = false) ∨ k.fds fd = some .stderr) :
    ∀ b, WA (WorldStep w) fd k b k none b := by
  intro b
  induction b using List.rec with
  | nil => exact .nil
  | cons x xs _ =>
    have he : WorldStep w k (.write fd (x :: xs)) (.ok (x :: xs).length) k := by
      rcases hfd with ⟨h1, hf⟩ | h2
      · exact .writeOut h1 hf ⟨le_rfl, fun _ => by simp⟩
      · exact .writeErr h2 ⟨le_rfl, fun _ => by simp⟩
    have h0 : WA (WorldStep w) fd k ((x :: xs).drop (x :: xs).length) k none [] := by
      simpa using (WA.nil : WA (WorldStep w) fd k [] k none [])
    simpa using WA.ok (by simp) he h0

/-- **`write_all` on a full standard output** fails with `ENOSPC` and accepts nothing. -/
theorem wa_full {w : World} {k : KState} {b : Bytes} {k' : KState} {e : Option Errno}
    {acc : Bytes} (h1 : k.fds 1 = some .stdout) (hf : w.stdoutFull = true) (hb : b ≠ [])
    (h : WA (WorldStep w) 1 k b k' e acc) : k' = k ∧ e = some .ENOSPC ∧ acc = [] := by
  cases h with
  | nil => exact absurd rfl hb
  | ok _ he _ => cases he <;> simp_all
  | err _ he => cases he <;> simp_all
  | data _ he _ => cases he

/-! ## Write coalescing: the pure buffer model

On a working sink `out_putc` is a pure function of the buffer: it returns the bytes sent to
the kernel and the new buffer. The ghost invariant `sent ++ buf = emitted` is
`putcBuf_inv`. -/

/-- `out_putc c` on a working sink: (bytes sent, new buffer). -/
def putcBuf (cap : Nat) (buf : Bytes) (c : UInt8) : Bytes × Bytes :=
  let o1 := if buf.length = cap then buf else []
  let b1 := if buf.length = cap then [] else buf
  if c = 10 then (o1 ++ (b1 ++ [c]), []) else (o1, b1 ++ [c])

theorem putcBuf_inv (cap : Nat) (buf : Bytes) (c : UInt8) :
    (putcBuf cap buf c).1 ++ (putcBuf cap buf c).2 = buf ++ [c] := by
  unfold putcBuf; split_ifs <;> simp_all

/-- `out_puts`-style iteration: (bytes sent, final buffer). -/
def putsBuf (cap : Nat) : Bytes → Bytes → Bytes × Bytes
  | buf, [] => ([], buf)
  | buf, c :: cs =>
    let r := putcBuf cap buf c
    let q := putsBuf cap r.2 cs
    (r.1 ++ q.1, q.2)

/-- **Write coalescing.** Whatever the buffer size and wherever the newlines are, what was
sent plus what is still buffered is what was emitted. -/
theorem putsBuf_inv (cap : Nat) (buf cs : Bytes) :
    (putsBuf cap buf cs).1 ++ (putsBuf cap buf cs).2 = buf ++ cs := by
  induction cs generalizing buf with
  | nil => simp [putsBuf]
  | cons c cs ih =>
    simp only [putsBuf, List.append_assoc, ih]
    rw [← List.append_assoc, putcBuf_inv]; simp

/-- **Prefix form of coalescing** (what a per-byte trace model such as LPS needs for prefix
safety): what the layer has sent is always a prefix of what the program emitted, so every
observable output trace of the buffered program is a prefix of the unbuffered one's. -/
theorem putsBuf_prefix (cap : Nat) (buf cs : Bytes) : (putsBuf cap buf cs).1 <+: buf ++ cs :=
  ⟨_, putsBuf_inv cap buf cs⟩

/-- A line ending in a newline leaves the buffer empty, provided it fits. -/
theorem putsBuf_line (cap : Nat) (buf cs : Bytes) (hl : cs ≠ []) (hnl : cs.getLast hl = 10) :
    (putsBuf cap buf cs).2 = [] := by
  induction cs generalizing buf with
  | nil => exact absurd rfl hl
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [List.getLast_singleton] at hnl
      simp [putsBuf, putcBuf, hnl]
    | cons d ds =>
      simp only [putsBuf]
      exact ih _ (by simp) (by simpa using hnl)

/-! ## Stream-level steps of the macro semantics

These lemmas let a proof about a program over the layer move through `out_putc`,
`out_flush`, the layer query and `write_all` with pure list updates, never seeing a
`write` call. -/

theorem mexec_run_tau {A : OMachine} {cap : Nat} {E : Env} {s : A.State} {buf : Bytes}
    {err : Bool} {t0 : LState A.State} {k : KState} {aevs : List AEvent} {n : Nat}
    (hs : lbStep A cap (.run s buf err) = .tau t0) (h : MExec A cap E (.run s buf err) k aevs n) :
    MExec A cap E t0 k aevs n := by
  cases h with
  | exit he => simp [lbStep, he] at hs
  | tau hs' _ m => rw [hs] at hs'; cases hs'; exact m
  | call hc _ _ => simp [lbStep, hc] at hs

theorem mexec_flushThen {A : OMachine} {cap : Nat} {w : World} {buf : Bytes} {err : Bool}
    {kf : Option Errno → Bytes → Bool → LState A.State} {k : KState} {aevs : List AEvent}
    {n : Nat} (hk : Sink w k 1) (h : MExec A cap (WorldStep w) (flushThen buf err kf) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w) (kf none [] err) k aevs' n ∧
      ∀ fd, awritten fd aevs = (if fd = 1 then buf else []) ++ awritten fd aevs' := by
  unfold flushThen at h
  split_ifs at h with hb
  · subst hb; exact ⟨aevs, h, fun fd => by simp⟩
  · obtain ⟨k', e, acc, aevs', rfl, hwa, m⟩ := mexec_wa_inv h
    obtain ⟨rfl, rfl, rfl⟩ := wa_sink hwa hk
    refine ⟨aevs', by simpa using m, fun fd => ?_⟩
    by_cases h1 : 1 = fd
    · simp [awritten, h1]
    · simp [awritten, h1]; grind

theorem mexec_putc {A : OMachine} {cap : Nat} {w : World} {s s' : A.State} {c : UInt8}
    {buf : Bytes} {err : Bool} {k : KState} {aevs : List AEvent} {n : Nat}
    (hk : Sink w k 1) (hs : A.step s = .putc c s')
    (h : MExec A cap (WorldStep w) (.run s buf err) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w) (.run s' (putcBuf cap buf c).2 err) k aevs' n ∧
      ∀ fd, awritten fd aevs = (if fd = 1 then (putcBuf cap buf c).1 else []) ++
        awritten fd aevs' := by
  have happ : ∀ b aevs, MExec A cap (WorldStep w) (appendThen c s' b err) k aevs n →
      ∃ aevs', MExec A cap (WorldStep w)
        (.run s' (if c = 10 then [] else b ++ [c]) err) k aevs' n ∧
        ∀ fd, awritten fd aevs = (if fd = 1 then (if c = 10 then b ++ [c] else []) else []) ++
          awritten fd aevs' := by
    intro b aevs m
    unfold appendThen at m
    split_ifs at m with hc
    · obtain ⟨aevs', m', hw⟩ := mexec_flushThen hk m
      exact ⟨aevs', by simpa [hc] using m', by simpa [hc] using hw⟩
    · exact ⟨aevs, by simpa [hc] using m, fun fd => by simp [hc]⟩
  by_cases hcap : buf.length = cap
  · have m := mexec_run_tau (t0 := flushThen buf err fun _ b e => appendThen c s' b e)
      (by simp [lbStep, hs, hcap]) h
    obtain ⟨aevs1, m1, hw1⟩ := mexec_flushThen hk m
    obtain ⟨aevs2, m2, hw2⟩ := happ [] aevs1 m1
    refine ⟨aevs2, by by_cases hc : c = 10 <;> simpa [putcBuf, hcap, hc] using m2, fun fd => ?_⟩
    rw [hw1, hw2]
    by_cases hc : c = 10 <;> by_cases h1 : fd = 1 <;> simp [putcBuf, hcap, hc, h1]
  · have m := mexec_run_tau (t0 := appendThen c s' buf err) (by simp [lbStep, hs, hcap]) h
    obtain ⟨aevs2, m2, hw2⟩ := happ buf aevs m
    refine ⟨aevs2, by by_cases hc : c = 10 <;> simpa [putcBuf, hcap, hc] using m2, fun fd => ?_⟩
    rw [hw2]
    by_cases hc : c = 10 <;> by_cases h1 : fd = 1 <;> simp [putcBuf, hcap, hc, h1]

theorem mexec_flush {A : OMachine} {cap : Nat} {w : World} {s : A.State}
    {f : Option Errno → A.State} {buf : Bytes} {err : Bool} {k : KState} {aevs : List AEvent}
    {n : Nat} (hk : Sink w k 1) (hs : A.step s = .flush f)
    (h : MExec A cap (WorldStep w) (.run s buf err) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w) (.run (f none) [] err) k aevs' n ∧
      ∀ fd, awritten fd aevs = (if fd = 1 then buf else []) ++ awritten fd aevs' :=
  mexec_flushThen hk
    (mexec_run_tau (t0 := flushThen buf err fun e b er => .run (f e) b er) (by simp [lbStep, hs]) h)

theorem mexec_query {A : OMachine} {cap : Nat} {E : Env} {s : A.State}
    {f : Bool → Bool → A.State} {buf : Bytes} {err : Bool} {k : KState} {aevs : List AEvent}
    {n : Nat} (hs : A.step s = .query f) (h : MExec A cap E (.run s buf err) k aevs n) :
    MExec A cap E (.run (f (buf ≠ []) err) buf err) k aevs n :=
  mexec_run_tau (by simp [lbStep, hs]) h

theorem mexec_tau {A : OMachine} {cap : Nat} {E : Env} {s s' : A.State} {buf : Bytes}
    {err : Bool} {k : KState} {aevs : List AEvent} {n : Nat} (hs : A.step s = .tau s')
    (h : MExec A cap E (.run s buf err) k aevs n) : MExec A cap E (.run s' buf err) k aevs n :=
  mexec_run_tau (by simp [lbStep, hs]) h

theorem mexec_writeAll {A : OMachine} {cap : Nat} {w : World} {s : A.State} {fd : Nat}
    {b : Bytes} {f : Option Errno → A.State} {buf : Bytes} {err : Bool} {k : KState}
    {aevs : List AEvent} {n : Nat} (hk : Sink w k fd) (hs : A.step s = .writeAll fd b f)
    (h : MExec A cap (WorldStep w) (.run s buf err) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w) (.run (f none) buf err) k aevs' n ∧
      ∀ fd', awritten fd' aevs = (if fd = fd' then b else []) ++ awritten fd' aevs' := by
  obtain ⟨k', e, acc, aevs', rfl, hwa, m⟩ :=
    mexec_wa_inv (mexec_run_tau (t0 := .wa fd b fun e => .run (f e) buf err) (by simp [lbStep, hs]) h)
  obtain ⟨rfl, rfl, rfl⟩ := wa_sink hwa hk
  exact ⟨aevs', m, fun fd' => by simp [awritten]⟩

/-- A raw call: the reply is one the environment admits. -/
theorem mexec_call {A : OMachine} {cap : Nat} {E : Env} {s : A.State} {c : Call}
    {f : Ret → A.State} {buf : Bytes} {err : Bool} {k : KState} {aevs : List AEvent} {n : Nat}
    (hs : A.step s = .call c f) (h : MExec A cap E (.run s buf err) k aevs n) :
    ∃ r k' aevs', E k c r k' ∧ aevs = .raw (c, r) :: aevs' ∧
      MExec A cap E (.run (f r) buf err) k' aevs' n := by
  cases h with
  | exit he => rw [hs] at he; cases he
  | tau ht _ _ => simp [lbStep, hs] at ht
  | call hc he m => rw [hs] at hc; cases hc; exact ⟨_, _, _, he, rfl, m⟩

theorem mexec_exit {A : OMachine} {cap : Nat} {E : Env} {s : A.State} {st : Nat} {buf : Bytes}
    {err : Bool} {k : KState} {aevs : List AEvent} {n : Nat} (hs : A.step s = .exit st)
    (h : MExec A cap E (.run s buf err) k aevs n) : aevs = [] ∧ n = st % 256 := by
  cases h with
  | exit he => rw [hs] at he; cases he; exact ⟨rfl, rfl⟩
  | tau ht _ _ => simp [lbStep, hs] at ht
  | call hc _ _ => rw [hs] at hc; cases hc

/-- **`out_puts` at the stream level**: a loop of `putc`s over a list is one pure buffer
update (`putsBuf`) and one output prefix. -/
theorem mexec_puts {A : OMachine} {cap : Nat} {w : World} {P : Bytes → A.State}
    (hP : ∀ c cs, A.step (P (c :: cs)) = .putc c (P cs)) {err : Bool} {k : KState} {n : Nat}
    (hk : Sink w k 1) :
    ∀ cs buf aevs, MExec A cap (WorldStep w) (.run (P cs) buf err) k aevs n →
      ∃ aevs', MExec A cap (WorldStep w) (.run (P []) (putsBuf cap buf cs).2 err) k aevs' n ∧
        ∀ fd, awritten fd aevs = (if fd = 1 then (putsBuf cap buf cs).1 else []) ++
          awritten fd aevs' := by
  intro cs
  induction cs with
  | nil => intro buf aevs m; exact ⟨aevs, m, fun fd => by simp [putsBuf]⟩
  | cons c cs ih =>
    intro buf aevs m
    obtain ⟨aevs1, m1, hw1⟩ := mexec_putc hk (hP c cs) m
    obtain ⟨aevs2, m2, hw2⟩ := ih _ _ m1
    refine ⟨aevs2, m2, fun fd => ?_⟩
    rw [hw1, hw2]
    by_cases h1 : fd = 1 <;> simp [putsBuf, h1]

/-! ## Both kinds of standard output: the pure layer model

`flushF full` and `putcF full` are `out_flush` and `out_putc` as pure functions of the layer
state for a standard output that works (`full = false`) or is full (`full = true`): bytes
sent, errno, new buffer, new sticky flag. `mexec_putsF` moves a whole `out_puts` loop to the
stream level for either kind. -/

/-- `out_flush` on a stdout of kind `full`: (bytes sent, errno, new sticky flag). -/
def flushF (full : Bool) (buf : Bytes) (err : Bool) : Bytes × Option Errno × Bool :=
  if buf = [] then ([], none, err) else if full then ([], some .ENOSPC, true) else (buf, none, err)

/-- `out_putc c` on a stdout of kind `full`: (bytes sent, new buffer, new sticky flag). -/
def putcF (full : Bool) (cap : Nat) (buf : Bytes) (err : Bool) (c : UInt8) :
    Bytes × Bytes × Bool :=
  let f1 := if buf.length = cap then flushF full buf err else ([], none, err)
  let b1 := if buf.length = cap then [] else buf
  if c = 10 then
    let f2 := flushF full (b1 ++ [c]) f1.2.2
    (f1.1 ++ f2.1, [], f2.2.2)
  else (f1.1, b1 ++ [c], f1.2.2)

def putsF (full : Bool) (cap : Nat) : Bytes → Bool → Bytes → Bytes × Bytes × Bool
  | buf, err, [] => ([], buf, err)
  | buf, err, c :: cs =>
    let r := putcF full cap buf err c
    let q := putsF full cap r.2.1 r.2.2 cs
    (r.1 ++ q.1, q.2.1, q.2.2)

/-- A stdout of kind `full` at `k`. -/
def Out (w : World) (k : KState) (full : Bool) : Prop :=
  k.fds 1 = some .stdout ∧ w.stdoutFull = full

theorem mexec_flushThenF {A : OMachine} {cap : Nat} {w : World} {full : Bool} {buf : Bytes}
    {err : Bool} {kf : Option Errno → Bytes → Bool → LState A.State} {k : KState}
    {aevs : List AEvent} {n : Nat} (hk : Out w k full)
    (h : MExec A cap (WorldStep w) (flushThen buf err kf) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w)
      (kf (flushF full buf err).2.1 [] (flushF full buf err).2.2) k aevs' n ∧
      ∀ fd, awritten fd aevs = (if fd = 1 then (flushF full buf err).1 else []) ++
        awritten fd aevs' := by
  cases full with
  | false =>
    obtain ⟨aevs', m, hw⟩ := mexec_flushThen (sink_stdout hk.1 hk.2) h
    refine ⟨aevs', ?_, ?_⟩
    · by_cases hb : buf = [] <;> simpa [flushF, hb] using m
    · intro fd; by_cases hb : buf = [] <;> simp [flushF, hb, hw fd]
  | true =>
    unfold flushThen at h
    split_ifs at h with hb
    · subst hb; exact ⟨aevs, by simpa [flushF] using h, fun fd => by simp [flushF]⟩
    · obtain ⟨k', e, acc, aevs', rfl, hwa, m⟩ := mexec_wa_inv h
      obtain ⟨rfl, rfl, rfl⟩ := wa_full hk.1 hk.2 hb hwa
      exact ⟨aevs', by simpa [flushF, hb] using m, fun fd => by simp [awritten, flushF, hb]⟩

theorem mexec_putcF {A : OMachine} {cap : Nat} {w : World} {full : Bool} {s s' : A.State}
    {c : UInt8} {buf : Bytes} {err : Bool} {k : KState} {aevs : List AEvent} {n : Nat}
    (hk : Out w k full) (hs : A.step s = .putc c s')
    (h : MExec A cap (WorldStep w) (.run s buf err) k aevs n) :
    ∃ aevs', MExec A cap (WorldStep w)
      (.run s' (putcF full cap buf err c).2.1 (putcF full cap buf err c).2.2) k aevs' n ∧
      ∀ fd, awritten fd aevs = (if fd = 1 then (putcF full cap buf err c).1 else []) ++
        awritten fd aevs' := by
  have happ : ∀ b e aevs, MExec A cap (WorldStep w) (appendThen c s' b e) k aevs n →
      ∃ aevs', MExec A cap (WorldStep w)
        (.run s' (if c = 10 then [] else b ++ [c])
          (if c = 10 then (flushF full (b ++ [c]) e).2.2 else e)) k aevs' n ∧
        ∀ fd, awritten fd aevs =
          (if fd = 1 then (if c = 10 then (flushF full (b ++ [c]) e).1 else []) else []) ++
            awritten fd aevs' := by
    intro b e aevs m
    unfold appendThen at m
    split_ifs at m with hc
    · obtain ⟨aevs', m', hw⟩ := mexec_flushThenF hk m
      exact ⟨aevs', by simpa [hc] using m', by simpa [hc] using hw⟩
    · exact ⟨aevs, by simpa [hc] using m, fun fd => by simp [hc]⟩
  by_cases hcap : buf.length = cap
  · have m := mexec_run_tau (t0 := flushThen buf err fun _ b e => appendThen c s' b e)
      (by simp [lbStep, hs, hcap]) h
    obtain ⟨aevs1, m1, hw1⟩ := mexec_flushThenF hk m
    obtain ⟨aevs2, m2, hw2⟩ := happ [] _ aevs1 m1
    refine ⟨aevs2, by by_cases hc : c = 10 <;> simpa [putcF, hcap, hc] using m2, fun fd => ?_⟩
    rw [hw1, hw2]
    by_cases hc : c = 10 <;> by_cases h1 : fd = 1 <;> simp [putcF, hcap, hc, h1]
  · have m := mexec_run_tau (t0 := appendThen c s' buf err) (by simp [lbStep, hs, hcap]) h
    obtain ⟨aevs2, m2, hw2⟩ := happ buf err aevs m
    refine ⟨aevs2, by by_cases hc : c = 10 <;> simpa [putcF, hcap, hc] using m2, fun fd => ?_⟩
    rw [hw2]
    by_cases hc : c = 10 <;> by_cases h1 : fd = 1 <;> simp [putcF, hcap, hc, h1]

/-- **`out_puts` at the stream level, either kind of stdout.** -/
theorem mexec_putsF {A : OMachine} {cap : Nat} {w : World} {full : Bool} {P : Bytes → A.State}
    (hP : ∀ c cs, A.step (P (c :: cs)) = .putc c (P cs)) {k : KState} {n : Nat}
    (hk : Out w k full) :
    ∀ cs buf err aevs, MExec A cap (WorldStep w) (.run (P cs) buf err) k aevs n →
      ∃ aevs', MExec A cap (WorldStep w)
        (.run (P []) (putsF full cap buf err cs).2.1 (putsF full cap buf err cs).2.2) k aevs' n ∧
        ∀ fd, awritten fd aevs = (if fd = 1 then (putsF full cap buf err cs).1 else []) ++
          awritten fd aevs' := by
  intro cs
  induction cs with
  | nil => intro buf err aevs m; exact ⟨aevs, m, fun fd => by simp [putsF]⟩
  | cons c cs ih =>
    intro buf err aevs m
    obtain ⟨aevs1, m1, hw1⟩ := mexec_putcF hk (hP c cs) m
    obtain ⟨aevs2, m2, hw2⟩ := ih _ _ _ m1
    refine ⟨aevs2, m2, fun fd => ?_⟩
    rw [hw1, hw2]
    by_cases h1 : fd = 1 <;> simp [putsF, h1]

/-- On a working stdout the general model is the coalescing model. -/
theorem putsF_false (cap : Nat) (buf cs : Bytes) (err : Bool) :
    putsF false cap buf err cs = ((putsBuf cap buf cs).1, (putsBuf cap buf cs).2, err) := by
  induction cs generalizing buf with
  | nil => simp [putsF, putsBuf]
  | cons c cs ih =>
    have hc1 : putcF false cap buf err c = ((putcBuf cap buf c).1, (putcBuf cap buf c).2, err) := by
      unfold putcF putcBuf flushF; split_ifs <;> simp_all
    rw [putsF, putsBuf, hc1]
    simp only [ih]

/-- **The full-stdout policy lemma.** On a full stdout nothing is ever sent, and after a
nonempty output the layer state is decided by its last byte: a final newline leaves the
buffer empty and the sticky flag set (the last flush failed); anything else leaves bytes
pending. This is what gnulib `close_stdout` turns into "write error" without or with
`ENOSPC` (`Sha256sum.finish`). -/
theorem putsF_true (cap : Nat) (buf : Bytes) (err : Bool) (cs : Bytes) :
    (putsF true cap buf err cs).1 = [] ∧
      (cs ≠ [] → (cs.getLast? = some 10 →
          (putsF true cap buf err cs).2.1 = [] ∧ (putsF true cap buf err cs).2.2 = true) ∧
        (cs.getLast? ≠ some 10 → (putsF true cap buf err cs).2.1 ≠ [])) := by
  induction cs generalizing buf err with
  | nil => simp [putsF]
  | cons c cs ih =>
    have h1 : (putcF true cap buf err c).1 = [] := by
      clear ih; unfold putcF flushF; split_ifs <;> simp_all
    cases cs with
    | nil =>
      refine ⟨by simp [putsF, h1], fun _ => ⟨fun hl => ?_, fun hl => ?_⟩⟩
      · have hc : c = 10 := by simpa using hl
        subst hc
        clear ih h1; unfold putsF putsF putcF flushF
        split_ifs <;> simp_all
      · have hc : c ≠ 10 := by simpa using hl
        unfold putsF putsF putcF
        simp [hc]
    | cons d ds =>
      obtain ⟨ih1, ih2⟩ := ih (putcF true cap buf err c).2.1 (putcF true cap buf err c).2.2
      rw [putsF]
      refine ⟨by simp only [h1, ih1, List.append_nil], fun _ => ?_⟩
      have := ih2 (by simp)
      simpa [List.getLast?_cons_cons] using this

end Silmaril.Apps.Sha256sum.Sys.IOLayer
