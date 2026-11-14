module

public import Silmaril.X86.Litmus.Extract.Defs
public import Silmaril.X86.Weak9.Defs

/-!
# Litmus event extraction over `Weak9`: non-temporal and string stores from bytes

The extractor
(`Litmus.extract`) decodes with `Atomic9` and produces only `Flavor.plain` actions, so the
writer threads of the six loose corners with `movnti` or `rep stosb` were transcribed by hand
(`Silmaril.X86.MemoryModel.Litmus.Verdicts.Defs`). `wextract` decodes them from the bytes:

* where `Thread.fetch` decodes an `Atomic9` instruction, the step is **exactly** `stepSym` (so the
  plain litmus subset extracts as before);
* otherwise the instruction is decoded with `Weak9.decode` (`Thread.wfetch`, with the same
  exact-slice check) and run by `weakStep`/`strStep`, pure transcriptions of `Weak9.execWeak`
  and `Str9.execStr`:
  - `movnti m, r` is one store of the register's low bytes, `Flavor.nonTemporal`;
  - one step of `rep stosb`/`rep stosq` is one 1- or 8-byte store of `al`/`rax` at `rdi`
    (`Flavor.string`), or nothing when `rcx = 0`; `rip` stays on the instruction until `rcx`
    reaches zero, so a `rep` of `k` elements is `k` steps;
  - one step of `movsb`/`rep movsq` is a load at `rsi` (one branch per domain value) and a
    store of the loaded bytes at `rdi` (both `Flavor.string`);
* anything else makes the whole extraction `none`, as in the plain extractor.

The soundness statement `WReplay` is `Replay` with `Weak9.step` for `Atomic9.step`
(`wextract_sound` in `WeakExtract/Thms.lean`).
-/

@[expose] public section

namespace Silmaril.X86.Litmus

open Silmaril.X86 (State MState Word Byte Reg maxInstrLength)
open Silmaril.X86.Ext (Sz Mem leBytes)
open Silmaril.Process (Memory Region)
open MemEvent (Event Kind)

/-- Decode the instruction at `rip` with `Weak9.decode`: offset `o = rip - base`, the listing
decoder on the 15-byte window, and the same form on exactly its own slice inside the code. -/
def Thread.wfetch (t : Thread) (s : State) : Option (Weak9.Instr × Nat) :=
  let o := (s.rip - t.base).toNat
  match Weak9.decode ((t.code.drop o).take maxInstrLength) with
  | some (i, n) =>
    if o + n ≤ t.code.length ∧ Weak9.decode ((t.code.drop o).take n) = some (i, n) then
      some (i, n)
    else none
  | none => none

/-- The core after one element of a `rep` store of `k` bytes per element (`rcx ≠ 0`). -/
def repPost (k : Nat) (src : Bool) (s : State) (next : Word) : State :=
  let c := s.read .rcx - 1
  let t := ((if src then s.write .rsi (s.read .rsi + BitVec.ofNat 64 k) else s).write .rdi
    (s.read .rdi + BitVec.ofNat 64 k)).write .rcx c
  { t with rip := if c = 0 then next else s.rip }

/-- One element of a `rep` store of `v`'s low `k` bytes at `rdi` (a string store), or nothing
when `rcx = 0`. -/
def repStoreStep (R : List Region) (k : Nat) (v : Word) (s : State) (next : Word) :
    Option (List (List Act × State)) :=
  if s.read .rcx = 0 then some [([], { s with rip := next })]
  else
    let addr := (s.read .rdi).toNat
    if writeOk R addr k then
      some [([⟨⟨.store, addr, k, false⟩, .string, [], leBytes v k⟩], repPost k false s next)]
    else none

/-- One element of a string copy of `k` bytes from `rsi` to `rdi`, one branch per domain
value: the loaded bytes are stored back. `post` is the core after the element. -/
def copyStep (R : List Region) (dom : List Nat) (k : Nat) (s : State) (post : State) :
    Option (List (List Act × State)) :=
  let src := (s.read .rsi).toNat
  let dst := (s.read .rdi).toNat
  if readOk R src k && writeOk R dst k then
    some (dom.map fun v =>
      let bs := valBytes v k
      ([⟨⟨.load, src, k, false⟩, .string, bs, []⟩,
        ⟨⟨.store, dst, k, false⟩, .string, [], leBytes (ldVal bs) k⟩], post))
  else none

/-- The `Weak` forms (no read, so one branch). -/
def weakStep (R : List Region) (i : Weak9.Weak) (s : State) (n : Nat) :
    Option (List (List Act × State)) :=
  let next := s.rip + BitVec.ofNat 64 n
  match i with
  | .movnti sz dst src =>
    let addr := (dst.addr s next).toNat
    if writeOk R addr sz.bytes then
      some [([⟨⟨.store, addr, sz.bytes, false⟩, .nonTemporal, [],
        leBytes ((sz.read s src).setWidth 64) sz.bytes⟩], { s with rip := next })]
    else none
  | .repStosb => repStoreStep R 1 (s.read .rax) s next

/-- The `Str9` forms. -/
def strStep (R : List Region) (dom : List Nat) (i : Str9.Str) (s : State) (n : Nat) :
    Option (List (List Act × State)) :=
  let next := s.rip + BitVec.ofNat 64 n
  match i with
  | .repStosq => repStoreStep R 8 (s.read .rax) s next
  | .movsb =>
    copyStep R dom 1 s
      { (s.write .rsi (s.read .rsi + 1)).write .rdi (s.read .rdi + 1) with rip := next }
  | .repMovsq =>
    if s.read .rcx = 0 then some [([], { s with rip := next })]
    else copyStep R dom 8 s (repPost 8 true s next)

/-- **One symbolic step over `Weak9`**: `stepSym` where `Atomic9` decodes; otherwise a
`Weak` or `Str9` form. -/
def wstepSym (t : Thread) (dom : List Nat) (s : State) : Option (List (List Act × State)) :=
  match t.fetch s with
  | some _ => stepSym t dom s
  | none =>
    match t.wfetch s with
    | some (.weak i, n) => weakStep t.regions i s n
    | some (.str i, n) => strStep t.regions dom i s n
    | _ => none

/-- Explore every branch from a core, with `fuel` steps at most. -/
def wexplore (t : Thread) (dom : List Nat) : Nat → State → Option (List Trace)
  | fuel, s =>
    if s.rip = t.endRip then some [⟨[], s⟩]
    else
      match fuel with
      | 0 => none
      | f + 1 =>
        match wstepSym t dom s with
        | none => none
        | some outs =>
          (outs.mapM fun o => (wexplore t dom f o.2).map (consStep o.1 o.2)).map List.flatten

/-- **The candidate traces of a thread over `Weak9`**, or `none` if some branch is unsupported,
faults or needs more than `fuel` steps. -/
def wextract (t : Thread) (dom : List Nat) (fuel : Nat) : Option (List Trace) :=
  wexplore t dom fuel t.init

/-- **The trace replays on `Weak9`**: `Replay` with `Weak9.step`. -/
inductive WReplay (t : Thread) : State → List StepRec → State → Prop
  | done (s : State) (h : s.rip = t.endRip) : WReplay t s [] s
  | step (s : State) (r : StepRec) (rest : List StepRec) (s' : State)
      (h : ∀ m : Memory, m.regions = t.regions → Silmaril.X86.Ext.Loaded m t.base t.code →
        Answers m r.acts →
        ∃ m', Weak9.step ⟨s, m⟩ = some ⟨r.post, m'⟩ ∧ applyWrites m r.acts = some m')
      (tail : WReplay t r.post rest s') : WReplay t s (r :: rest) s'

end Silmaril.X86.Litmus
