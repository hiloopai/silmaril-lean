module

public import Silmaril.Wasi.Versions.HttpOver.Defs
public import Silmaril.Wasi.Versions.HttpBody3.Defs

@[expose] public section

/-!
# HTTP with response bodies across versions: 0.3 over 0.2 (buffering)

**`httpB3Over2 rounds`** imports the 0.2 HTTP functions with bodies (`httpBodyImports`) and
exports the 0.3 ones (`httpBody3Fns`).

* The outgoing slice (`set-authority`, `set-path-with-query`, `send`, `get-status-code`) runs the
  programs of `http3Over2 rounds` (`Silmaril.Wasi.Versions.HttpOver`), lifted to the larger import
  set (`liftP`).
* `consume-body(rs, _)` does the whole 0.2 body protocol within the call: `consume(rs)`,
  `stream(b)`, `blocking-read(s, 65536)` until `error(closed)` (at most `rounds` reads,
  `readAll`), `finish(b)`, polling `future-trailers.get` while it answers `none` (at most
  `rounds` times, `pollTr`) and, for trailers, `entries(t)`. It buffers the body bytes and the
  trailer outcome (`TrInfo`) under two fresh handles: a readable end `rd` and a future `fu`,
  and answers `(rd, fu)`. Any failure (an error of `consume` or `stream`, a failed read, rounds
  running out, an ill-typed answer) is a trap.
* `stream.read(rd, n)` answers from the buffer as `body3Impl` does (`read3Ans`: at most
  `min n 2^27` bytes, `DROPPED 0` at the end); `future.read(fu)` answers the buffered trailer
  outcome, handing out a fresh trailer handle `t` for trailers; `copy-all(t)` answers the
  buffered `entries` answer. No import call.

Buffering is the simplest correct strategy: all 0.2 calls of a body happen in one export call,
so no other call can reuse a 0.2 handle in between. A streaming adapter (reading 0.2 chunks on
each `stream.read`) is not covered.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.Net

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## Lifting programs along an inclusion of imports -/

/-- A program over the imports `I`, as a program over `I' ⊇ I`. -/
def liftP {I I' : Set FnName} {A : Type} (h : I ⊆ I') : Prog (nsig I) A → Prog (nsig I') A
  | .pure a => .pure a
  | .call m k => .call (⟨m.1.1, h m.1.2⟩, m.2) fun n => liftP h (k n)

/-- The outgoing 0.2 functions are among the functions with bodies. -/
theorem httpImports_sub : httpImports ⊆ httpBodyImports := Set.subset_union_left

/-- An exported function that is not a body function is an outgoing 0.3 function. -/
theorem mem_http3 {f : FnName} (hm : f ∈ httpBody3Fns) (hb : isBodyFn3 f = false) : f ∈ http3Fns := by
  rcases hm with hm | hm
  · exact hm
  · simp only [bodyFns3_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [isBodyFn3] at hb

/-! ## Imports -/

/-- `consume` as a 0.2 import. -/
def iConsume : {f // f ∈ httpBodyImports} := ⟨consume2, Or.inr (by simp [bodyFns2_eq])⟩
/-- `stream` as a 0.2 import. -/
def iBodyStream : {f // f ∈ httpBodyImports} := ⟨bodyStream2, Or.inr (by simp [bodyFns2_eq])⟩
/-- `blocking-read` as a 0.2 import. -/
def iBread : {f // f ∈ httpBodyImports} := ⟨P2.isBread, Or.inr (by simp [bodyFns2_eq])⟩
/-- `finish` as a 0.2 import. -/
def iFinish2 : {f // f ∈ httpBodyImports} := ⟨bodyFinish2, Or.inr (by simp [bodyFns2_eq])⟩
/-- `future-trailers.get` as a 0.2 import. -/
def iTrGet : {f // f ∈ httpBodyImports} := ⟨trGet2, Or.inr (by simp [bodyFns2_eq])⟩
/-- `entries` as a 0.2 import. -/
def iEntries : {f // f ∈ httpBodyImports} := ⟨entries2, Or.inr (by simp [bodyFns2_eq])⟩

/-! ## The component -/

/-- The buffered trailer outcome. -/
inductive TrInfo where
  /-- No trailers. -/
  | noTr
  /-- Trailers, with the answer of `entries`. -/
  | tr (ans : Option (List Val))
  /-- The transfer failed with this `error-code` value. -/
  | err (v : Val)

/-- The state of `httpB3Over2`. -/
structure B3St where
  /-- The remaining bytes of each readable end. -/
  bufs : List (BitVec 32 × List (BitVec 8)) := []
  /-- The trailer outcome of each future. -/
  futv : List (BitVec 32 × TrInfo) := []
  /-- The `entries` answer of each trailer handle. -/
  trv : List (BitVec 32 × Option (List Val)) := []
  /-- The next fresh handle. -/
  next : Nat := 0

/-- The program run after a body program, from the state `st`. -/
abbrev BProg3 : Type := SProg B3St httpBodyImports

/-- The read length of `readAll`. -/
def readLen2 : Nat := 65536

/-- Read the stream `s` until `error(closed)`, at most `k` times; `acc` holds the bytes so far. -/
def readAll (st : B3St) (s : BitVec 32) (kont : List (BitVec 8) → BProg3) :
    Nat → List (BitVec 8) → BProg3
  | 0, _ => .pure (st, none)
  | k + 1, acc => .call (iBread, [.u32 s, .u64 (BitVec.ofNat 64 readLen2)]) fun r =>
    match r with
    | some [.variant 0 (some (.record vs))] =>
      match u8sOf vs with
      | some bs => readAll st s kont k (acc ++ bs)
      | none => .pure (st, none)
    | some [.variant 1 (some (.variant 1 none))] => kont acc
    | _ => .pure (st, none)

/-- Poll the trailer future `ft` while it answers `none`, at most `k` times. -/
def pollTr (st : B3St) (ft : BitVec 32) (kont : TrInfo → BProg3) : Nat → BProg3
  | 0 => .pure (st, none)
  | k + 1 => .call (iTrGet, [.u32 ft]) fun r =>
    match r with
    | some [.variant 0 none] => pollTr st ft kont k
    | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 0 none))))))] => kont .noTr
    | some [.variant 1 (some (.variant 0 (some (.variant 0 (some (.variant 1 (some (.u32 t))))))))] =>
      .call (iEntries, [.u32 t]) fun r₂ => kont (.tr r₂)
    | some [.variant 1 (some (.variant 0 (some (.variant 1 (some (.variant c p))))))] =>
      kont (.err (.variant c p))
    | _ => .pure (st, none)

/-- Store a buffered body and trailer outcome under fresh handles, and answer them. -/
def storeBody (st : B3St) (bytes : List (BitVec 8)) (i : TrInfo) : B3St × Option (List Val) :=
  ({ st with bufs := (BitVec.ofNat 32 (2 * st.next), bytes) :: st.bufs,
             futv := (BitVec.ofNat 32 (2 * st.next + 1), i) :: st.futv, next := st.next + 1 },
   some [.record [P3.natV (2 * st.next), P3.natV (2 * st.next + 1)]])

/-- After reading the body: finish it and read the trailers. -/
def finishProg (rounds : Nat) (st : B3St) (b : BitVec 32) (bytes : List (BitVec 8)) : BProg3 :=
  .call (iFinish2, [.u32 b]) fun r =>
    match r with
    | some [.u32 ft] => pollTr st ft (fun i => .pure (storeBody st bytes i)) rounds
    | _ => .pure (st, none)

/-- After `consume` gave the body `b`: its stream, the body, the trailers. -/
def streamProg (rounds : Nat) (st : B3St) (b : BitVec 32) : BProg3 :=
  .call (iBodyStream, [.u32 b]) fun r₂ =>
    match okHandle r₂ with
    | some s => readAll st s (finishProg rounds st b) rounds []
    | none => .pure (st, none)

/-- The program of `consume-body(rs, _)`. -/
def consumeProg (rounds : Nat) (st : B3St) (a : List Val) : BProg3 :=
  match a with
  | .u32 rs :: _ =>
    .call (iConsume, [.u32 rs]) fun r₁ =>
      match okHandle r₁ with
      | some b => streamProg rounds st b
      | none => .pure (st, none)
  | _ => .pure (st, none)

/-- The answer `DROPPED 0` of `stream.read`. -/
def dropped0 : Option (List Val) := some [P3.natV (packCopy .dropped 0), bytesV []]

/-- The answer `error` of `future.read` for an unknown future. -/
def errFut : Option (List Val) := some [P3.natV 0, errV (some (.variant 0 none))]

/-- The result of `stream.read(rd, n)` (no import call). -/
def bufRead (st : B3St) (a : List Val) : B3St × Option (List Val) :=
  match a with
  | .u32 h :: _ =>
    match lookup h st.bufs with
    | some rest =>
      ({ st with bufs := (h, rest.drop (rest.take (min (count3 a) chunk3)).length) :: st.bufs },
       read3Ans rest (count3 a))
    | none => (st, dropped0)
  | _ => (st, dropped0)

/-- The result of `future.read(fu)` (no import call). -/
def bufFut (st : B3St) (a : List Val) : B3St × Option (List Val) :=
  match a with
  | .u32 h :: _ =>
    match lookup h st.futv with
    | some .noTr => (st, some [P3.natV 0, okV (some noneV)])
    | some (.tr ans) =>
      ({ st with trv := (BitVec.ofNat 32 (2 * st.next), ans) :: st.trv, next := st.next + 1 },
       some [P3.natV 0, okV (some (.variant 1 (some (.u32 (BitVec.ofNat 32 (2 * st.next))))))])
    | some (.err v) => (st, some [P3.natV 0, errV (some v)])
    | none => (st, errFut)
  | _ => (st, errFut)

/-- The result of `copy-all(t)` (no import call). -/
def bufCopy (st : B3St) (a : List Val) : B3St × Option (List Val) :=
  (st, (lookup (selfH a) st.trv).getD (some [fieldsV []]))

/-- The program of a body function. -/
def bodyProg3 (rounds : Nat) (st : B3St) (f : FnName) (a : List Val) : BProg3 :=
  if f = consumeBody3 then consumeProg rounds st a
  else if f = P3.cStreamRead then .pure (bufRead st a)
  else if f = P3.cFutureRead then .pure (bufFut st a)
  else .pure (bufCopy st a)

/-- **HTTP with bodies, 0.3 over 0.2.** -/
def httpB3Over2 (rounds : Nat) : SBody B3St httpBodyImports httpBody3Fns := fun st q =>
  if hb : isBodyFn3 q.1.1 = false then
    (liftP httpImports_sub (http3Over2 rounds () (⟨q.1.1, mem_http3 q.1.2 hb⟩, q.2))).bind
      fun x => .pure (st, x.2)
  else bodyProg3 rounds st q.1.1 q.2

/-- A buffered trailer outcome for a request of key `k`. -/
def InfoOk (B : BWeb) (k : Val × Val) : TrInfo → Prop
  | .noTr => B.trailers k = none
  | .tr ans => (B.trailers k).isSome ∧ entriesOk (B.trailers k) ans = true
  | .err v => ∃ c p, v = .variant c p

/-- **The invariant of `httpB3Over2`** over the body web `B`: the outgoing states agree
(`JH3`); every tracked 0.3 body stream has the rest of the body in its buffer; every tracked
trailer future and trailer resource has a buffered outcome or answer that the 0.3 theory
accepts. The 0.2 body state is not constrained. -/
def JB3 (B : BWeb) (st : B3St) (q2 : BodySt) (q3 : Body3St) : Prop :=
  JH3 () q2.base q3.base ∧
  (∀ r k n, lookup r q3.streams = some (some (k, n)) → lookup r st.bufs = some ((B.body k).drop n)) ∧
  (∀ f k, lookup f q3.futs = some (some k) → (∃ r, B k.1 k.2 = .resp r) →
    ∃ i, lookup f st.futv = some i ∧ InfoOk B k i) ∧
  (∀ t k, lookup t q3.trs = some (some k) →
    ∃ ans, lookup t st.trv = some ans ∧ entriesOk (B.trailers k) ans = true)

/-- The postcondition of the program of `consume-body` with arguments `a`, from the 0.3 state
`q3`: its answer is accepted by the 0.3 theory with bodies and `JB3` holds after it. -/
def PostC (B : BWeb) (q3 : Body3St) (a : List Val) : B3St × Option (List Val) → BodySt → Prop :=
  fun x q2' => ∃ q3', (body3Th B).step q3 (.imp consumeBody3 a x.2) = some q3' ∧ JB3 B x.1 q2' q3'

/-- The invariant of `readAll` on the stream `s` of a body of key `o`: the 0.2 theory tracks
`s` (when `o` is known), and the bytes read so far are the start of the body. -/
def RdInv (B : BWeb) (s : BitVec 32) (o : Option (Val × Val)) (acc : List (BitVec 8))
    (q2 : BodySt) : Prop :=
  ∃ m, lookup s q2.streams = some (o.map (·, m)) ∧ ∀ k, o = some k → acc = (B.body k).take m

end Silmaril.Wasi.Versions.Net
