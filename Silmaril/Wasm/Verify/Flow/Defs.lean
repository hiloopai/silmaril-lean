module

public import Silmaril.Wasm.Verify.Guard.Defs

@[expose] public section

/-!
# Assertion arguments through locals: a small abstract interpretation

The guarded-call analysis of `Silmaril.Wasm.Verify.Guard` accepts a call of the assertion only right
after `i32.const c`, `c ≠ 0`. This module tracks **nonzero facts through locals** along structured
code, so that, for example, `i32.const 1; local.set 1; local.get 1; call $assert` and
`local.get 0; if (then local.get 0; call $assert)` are accepted.

## Stable locals

The analysis of an activation fixes a list `K` of **stable** locals: locals whose every write
(`local.set`, `local.tee`) stores a nonzero `i32`. Once such a local is nonzero it stays nonzero
for the rest of the activation, so a fact "local `k` is nonzero" is never invalidated, whatever
code runs in between (branches, loops, nested blocks, calls). Parameters that are never written
are stable.

## The abstract state

`FSt` is a list `S` of stable locals known to be nonzero, and an abstraction `Top` of the value
on top of the stack:

* `gd`: a nonzero `i32`; `zero`: the `i32` `0`; `nonI32`: a value that is not an `i32`;
* `loc k`: the current value of the stable local `k` (`k ∉ S`); `other`: unknown;
* `ex`: the rest of the sequence is never executed (after `trap` or `throw_ref`).

`nextI st i` is the state after the source instruction `i` (`local.set k`/`local.tee k` add a
stable `k` to `S`; `local.get k` gives `gd` when `k ∈ S` and `loc k` when `k` is stable).
`reqI st i` is what `i` requires of the state: a call of a bad function (the assertion), a write
of a stable local need `gd` (calls also accept `nonI32`, since an assertion is only violated by the
argument `i32 0`). `okI`/`okL` (mutual, structural, so that the kernel reduces them) check an
instruction or a sequence, entering the bodies of `block`, `loop` and `try_table` with the current
`S`, and the bodies of `if` with `S` plus `k` for the `then` branch after `local.get k`; a branch
whose condition is known (`gd`, `zero`) or that can never be taken (`nonI32`) is skipped.

`okA` is the same check on administrative code (`okX`, `nextX`): values set the top state, labels
require their continuation to be checked, everything else is `other`.

## The runtime invariant

* `Sound f K S`: every local of `S` is stable and holds a nonzero `i32` in the frame `f`.
* `scopeSeqs code`: the nested `label`/`handler` bodies of `code` that run in the same frame;
  `frameScopes code`: the nested `frame` bodies with their frames.
* `SeqOK K f b`: some `S` sound for `f` checks `b`; `FramesOK code`: every nested frame body,
  with its frame, satisfies `SeqOK` for some `K`, and so do its nested bodies.

The preservation theorem (`Silmaril.Proofs.Wasm.Verify.Flow.Step`) is proved by induction on Core
`Step`, every rule, in the style of `Silmaril.Wasm.Verify.Guard`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Verify

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- The abstraction of the value on top of the stack. -/
inductive Top where
  | other
  | gd
  | zero
  | nonI32
  | loc (k : Nat)
  | ex
  deriving DecidableEq, Repr

/-- The abstract state: stable locals known to be nonzero, and the top of the stack. -/
structure FSt where
  S : List Nat
  top : Top
  deriving DecidableEq, Repr

section
variable (K : List Nat) (bad : Nat → Bool) (fs : List Nat)

/-- A call of a bad function. -/
def isBadCall : Instr → Bool
  | .call y => match fs[y.toNat]? with
    | some a => bad a
    | none => false
  | _ => false

/-- The top state after a value. -/
def topOfConst : Instr → Top
  | .intConst .i32 c => if c == 0 then .zero else .gd
  | _ => .nonI32

/-- Add a stable local to `S`. -/
def addK (x : Nat) (S : List Nat) : List Nat := if K.contains x then x :: S else S

/-- The state after a source instruction. -/
def nextI (st : FSt) : Instr → FSt
  | .intConst t c => ⟨st.S, topOfConst (.intConst t c)⟩
  | .floatConst _ _ => ⟨st.S, .nonI32⟩
  | .vecConst _ => ⟨st.S, .nonI32⟩
  | .localGet x => ⟨st.S, if st.S.contains x.toNat then .gd
      else if K.contains x.toNat then .loc x.toNat else .other⟩
  | .localSet x => ⟨addK K x.toNat st.S, .other⟩
  | .localTee x => ⟨addK K x.toNat st.S, .other⟩
  | .throwRef => ⟨st.S, .ex⟩
  | _ => ⟨st.S, .other⟩

/-- A write of a stable local. -/
def isSetK : Instr → Bool
  | .localSet x => K.contains x.toNat
  | .localTee x => K.contains x.toNat
  | _ => false

/-- The local requirement of a source instruction (bodies excluded): a bad call needs a nonzero
`i32` or a non-`i32` argument, a write of a stable local a nonzero `i32`. -/
def reqI (st : FSt) (i : Instr) : Bool :=
  (!isBadCall bad fs i || st.top == .gd || st.top == .nonI32) && (!isSetK K i || st.top == .gd)

/-- The facts at the start of the `then` branch of an `if`. -/
def thenS (st : FSt) : List Nat :=
  match st.top with
  | .loc k => k :: st.S
  | _ => st.S

mutual

/-- **The check of a source instruction**, bodies included. -/
def okI (st : FSt) : Instr → Bool
  | .block _ b => okL ⟨st.S, .other⟩ b
  | .loop _ b => okL ⟨st.S, .other⟩ b
  | .tryTable _ _ b => okL ⟨st.S, .other⟩ b
  | .if_ _ b₁ b₂ =>
    (st.top == .zero || st.top == .nonI32 || okL ⟨thenS st, .other⟩ b₁) &&
      (st.top == .gd || st.top == .nonI32 || okL ⟨st.S, .other⟩ b₂)
  | i => reqI K bad fs st i

/-- **The check of a source sequence.** -/
def okL : FSt → List Instr → Bool
  | _, [] => true
  | st, i :: is => st.top == .ex || (okI st i && okL (nextI K st i) is)

end

/-- The state after an administrative instruction. -/
def nextX (st : FSt) : Admin → FSt
  | .plain i => nextI K st i
  | .ref _ => ⟨st.S, .nonI32⟩
  | .trap => ⟨st.S, .ex⟩
  | _ => ⟨st.S, .other⟩

/-- The check of an administrative instruction (nested runtime bodies excluded). -/
def okX (st : FSt) : Admin → Bool
  | .plain i => okI K bad fs st i
  | .label _ cont _ => okL K bad fs ⟨st.S, .other⟩ cont
  | _ => true

/-- **The check of administrative code.** -/
def okA : FSt → List Admin → Bool
  | _, [] => true
  | st, x :: l => st.top == .ex || (okX K bad fs st x && okA (nextX K st x) l)

end

/-! ## The runtime invariant -/

/-- Every local of `S` is stable and holds a nonzero `i32` in the frame. -/
def Sound (f : Frame) (K S : List Nat) : Prop :=
  ∀ k ∈ S, k ∈ K ∧ ∃ c : BitVec 32, f.locals[k]? = some (some (Val.i32 c)) ∧ c ≠ 0

/-- The nested `label` and `handler` bodies (same frame), recursively, not entering frames. -/
def scopeSeqs : List Admin → List (List Admin)
  | [] => []
  | .label _ _ b :: rest => b :: (scopeSeqs b ++ scopeSeqs rest)
  | .handler _ _ b :: rest => b :: (scopeSeqs b ++ scopeSeqs rest)
  | _ :: rest => scopeSeqs rest

/-- The nested `frame` bodies with their frames, recursively. -/
def frameScopes : List Admin → List (Frame × List Admin)
  | [] => []
  | .label _ _ b :: rest => frameScopes b ++ frameScopes rest
  | .handler _ _ b :: rest => frameScopes b ++ frameScopes rest
  | .frame _ f b :: rest => (f, b) :: (frameScopes b ++ frameScopes rest)
  | _ :: rest => frameScopes rest

/-- A sequence of the frame `f` is checked from some sound state. -/
def SeqOK (K : List Nat) (bad : Nat → Bool) (fs : List Nat) (f : Frame) (b : List Admin) : Prop :=
  ∃ S, Sound f K S ∧ okA K bad fs ⟨S, .other⟩ b = true

/-- Every nested frame body is checked, with its nested bodies, for some list of stable
locals. -/
def FramesOK (bad : Nat → Bool) (fs : List Nat) (code : List Admin) : Prop :=
  ∀ p ∈ frameScopes code, ∃ K, SeqOK K bad fs p.1 p.2 ∧ ∀ b ∈ scopeSeqs p.2, SeqOK K bad fs p.1 b

/-- Every Wasm function in `G` has a body checked from the empty state, for some list of stable
locals. -/
def BodiesFlow {H : Type} (G : Nat → Prop) (bad : Nat → Bool) (fs : List Nat)
    (funcs : List (FuncInst H)) : Prop :=
  ∀ a fi code, G a → funcs[a]? = some fi → fi.code = .wasm code →
    ∃ K, okL K bad fs ⟨[], .other⟩ code.body = true

/-! ## The reachability predicate -/

/-- The instruction predicate of the reachability invariant for the flow analysis: the targets
of `return_call` and `ref.func` are in `G`, the targets of `call` in `G` or bad. -/
def CallPl (G : Nat → Prop) (bad : Nat → Bool) (fs : List Nat) (i : Instr) : Prop :=
  (∀ x ∈ instrRF i, ∀ a, fs[x]? = some a → G a) ∧
    ∀ x ∈ instrCalls i, ∀ a, fs[x]? = some a → G a ∨ bad a = true

end Silmaril.Wasm.Verify
