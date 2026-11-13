module

public import Silmaril.Wasm.Wac.StreamFn.Defs
public import Silmaril.Games.LTS.Defs

/-!
# WAC: stream functions called step by step

`StreamFn.callSem` reads a stream package `tI: async func(in: stream<u8>) -> stream<u8>` as one
call: the whole input stream as one list of values, answered by the whole output (`k.run`). That
is the **batch** view. Under the Component Model the caller and the callee run concurrently: the
caller writes chunks into `in` (`stream.write`) and reads from the returned stream
(`stream.read`); the callee answers each chunk with what it has produced so far, and when the
caller drops the writable end of `in` (`stream.drop-writable`), the callee flushes and drops its
output.

This module gives that **stepwise** reading, the *chunk game* on the export of an `FCode`:

| move | Component Model reading |
|---|---|
| question `(0, vals xs)` | the caller writes the chunk `xs` into `in` and reads the output |
| answer `some (vals ys)` | the items `ys` the callee wrote since the last read (`(T.feed s xs).2`) |
| question `(0, flat [])` | the caller drops the writable end of `in` (end of input) |
| answer `some (vals ys)` | the callee's last items (`T.flush s`), then the end of its output; the next question opens a new stream (state `T.init`) |
| question `(0, flat fs)`, `fs ≠ []` | not a stream operation: traps (`none`), the state is kept |

* `TCode.St`, `TCode.tr`: the transformer of a code with its state space (`TCode.run` is the
  whole output of `tr`, `tr_run` in `Thms`);
* `CState`, `CStep`, `chunkL T`: the transition system of the chunk game of a transformer `T`;
* `stepSem`: the core semantics of `FCode`s in which a module's strategy is `chunkL (tr code)`;
* `session T s cs`: the plays of a whole stream: the chunks `cs` (ask, answer) and the end;
* `RunAgreeS`: two tables of packages agree up to stepwise behaviour (`Tr.Equiv` of the codes'
  transformers, export names kept).

Theorems in `Silmaril.Wasm.Wac.StreamStep.Thms`: the sessions are plays of `stepSem` and their
answers concatenate to `k.run` of the concatenated chunks (so the one-chunk session answers what
the batch call `callSem` answers), codes with equivalent transformers have equal strategies, and
compositions of packages that agree stepwise are equivalent in `stepSem`, from the WAC text and
the bytes.
-/

@[expose] public section

namespace Silmaril.Wasm.Wac.StreamStep

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Alg Silmaril.Wasm.Wac.StreamFn

/-- The state space of a code's transformer. -/
def St : TCode → Type
  | .id => Unit
  | .map _ => Unit
  | .filter _ => Unit
  | .take _ => Nat
  | .lines _ => (Unit × List Val) × Unit
  | .rechunk _ => (Unit × List Val) × Unit
  | .comp a b => St a × St b

/-- **The transformer of a code** (`TCode.run` is its whole output). -/
def tr : (k : TCode) → Tr (St k) Val Val
  | .id => Tr.id
  | .map f => Tr.map f
  | .filter p => Tr.filter p
  | .take n => Tr.take n
  | .lines sep => Proc.linesV sep
  | .rechunk n => Proc.rechunkV n
  | .comp a b => (tr a).comp (tr b)

/-- States of the chunk game: between questions, or answering `q`; `s` the transformer's state. -/
inductive CState (σ : Type) where
  | idle (s : σ)
  | run (s : σ) (q : (sigN 1).Op)

/-- The signature of an `FCode`'s exports (one function). -/
abbrev SigF : Sig.{0} := sigN 1

/-- Moves of the chunk game (no imports). -/
abbrev MoveF : Type := Move (sigN 0) SigF

/-- **The chunk game of `T`**. -/
inductive CStep {σ : Type} (T : Tr σ Val Val) : CState σ → Option MoveF → CState σ → Prop
  /-- Accept a question. -/
  | ask (s : σ) (q : SigF.Op) : CStep T (.idle s) (some (.inr (.ask q))) (.run s q)
  /-- A chunk written: answer what the transformer emits on it. -/
  | chunk (s : σ) (q : SigF.Op) (xs : List Val) : q.2 = .vals xs →
      CStep T (.run s q) (some (.inr (.ans q (some (.vals (T.feed s xs).2))))) (.idle (T.feed s xs).1)
  /-- The input ends: answer the flush; the next question opens a new stream. -/
  | close (s : σ) (q : SigF.Op) : q.2 = .flat [] →
      CStep T (.run s q) (some (.inr (.ans q (some (.vals (T.flush s)))))) (.idle T.init)
  /-- Anything else traps, keeping the state. -/
  | bad (s : σ) (q : SigF.Op) (fs : List Flat) : q.2 = .flat fs → fs ≠ [] →
      CStep T (.run s q) (some (.inr (.ans q none))) (.idle s)

/-- The transition system of the chunk game of `T`. -/
@[reducible] def chunkL {σ : Type} (T : Tr σ Val Val) : LTS (sigN 0) SigF :=
  ⟨CState σ, .idle T.init, CStep T⟩

/-- **The stepwise semantics** of `FCode`s: a module's strategy is the chunk game of its code's
transformer. -/
def stepSem : CoreSem FCode where
  sem m := Strategy.ofLTS (chunkL (tr m.code))

/-- The question writing the chunk `xs`. -/
def qChunk (xs : List Val) : SigF.Op := (⟨0, by decide⟩, .vals xs)

/-- The question ending the input. -/
def qEnd : SigF.Op := (⟨0, by decide⟩, .flat [])

/-- The plays of the chunks `cs` from the state `s`, and the state they end in. -/
def chunks {σ : Type} (T : Tr σ Val Val) : σ → List (List Val) → List MoveF × σ
  | s, [] => ([], s)
  | s, xs :: cs =>
    let r := chunks T (T.feed s xs).1 cs
    ([.inr (.ask (qChunk xs)), .inr (.ans (qChunk xs) (some (.vals (T.feed s xs).2)))] ++ r.1, r.2)

/-- **A whole stream**: the chunks `cs` from `s`, then the end of the input. -/
def session {σ : Type} (T : Tr σ Val Val) (s : σ) (cs : List (List Val)) : List MoveF :=
  (chunks T s cs).1 ++
    [.inr (.ask qEnd), .inr (.ans qEnd (some (.vals (T.flush (chunks T s cs).2))))]

/-- The items answered in a play (answers `some (vals ys)` at the export, concatenated). -/
def answers : List MoveF → List Val
  | [] => []
  | .inr (.ans _ (some (.vals ys))) :: r => ys ++ answers r
  | _ :: r => answers r

/-- Two tables of packages agree **stepwise**: the same names, and each pair of packages is the
same AST or two stream packages with the same export name whose codes' transformers are
equivalent (`Tr.Equiv`: the same output so far after every input, and the same whole output). -/
def RunAgreeS (κ : StreamPkg.Interp) (tbl tbl' : SpliceX.PkgTableX) : Prop :=
  ∀ n, (tbl.lookup n = tbl'.lookup n) ∨
    ∃ a a' s s' k k', tbl.lookup n = some a ∧ tbl'.lookup n = some a' ∧ fnShape a = some s ∧
      κ s.core = some k ∧ fnShape a' = some s' ∧ κ s'.core = some k' ∧ s.name = s'.name ∧
      Tr.Equiv (tr k) (tr k')

end Silmaril.Wasm.Wac.StreamStep
