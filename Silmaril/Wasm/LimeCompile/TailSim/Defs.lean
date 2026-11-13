module

public import Silmaril.Wasm.LimeCompile.Tail.Defs
public import Silmaril.Wasm.Execution.Core.Sim.Context

/-!
# The two-way simulation of the tail-call rewrite: definitions

`Tail.tailModule` rewrites `return_call x` to `call x; return` and `return_call_indirect t y` to
`call_indirect t y; return` outside `try_table` bodies. This file defines the relation between a
source configuration (the module before the rewrite) and a target configuration (after it) used
to prove `Tail.Task.tailSim`.

The relation is not a code-relation closure with matching exit kernels: after a rewritten tail
call the source leaves its labels and frame with `return_call_ref` and runs the callee outside the
caller's frame, while the target runs the callee inside the caller's frame and labels, followed
by `return` (`TailRel`). Its parts:

* `FRel`: related function instances (same type and module; the same code, or a Wasm function
  and its rewrite `Tail.tailFunc`);
* `RCRPair c c'`: a source `RETURN_CALL_REF` and the target's `CALL_REF` with the same
  annotation;
* `PW ys B`: the target body `B` of a caller frame (a *wrapper*) whose innermost label holds `ys`
  followed by `RETURN` (`val* L[val* ys RETURN instr*] instr*` with `L` a nest of labels);
* `PT ws c B`: a pending tail call: `B` is a wrapper body whose innermost stack is `ws` followed
  by the target's `CALL_REF` for the source's `c`;
* `TA y` / `TT a y`: `y` has a trap (resp. the throw of exception `a`) at its active position
  under labels and frames, so it reduces to it;
* `Arity d k vs`: the callee type `d` returns `k` values and takes `vs.length` arguments;
* `R tl x y` (mutually with `CE k xs ys`): the code relation. `tl = true` marks code in tail
  position of a frame (not under a handler of that frame), where rewritten tail calls may occur.
  Constructors: identical non-context instructions (`same`), a rewritten instruction (`instr`),
  the target's `CALL_REF; RETURN` for the source's `RETURN_CALL_REF` (`rcr`), labels and
  handlers with related bodies, callee segments (`callee`), a pending tail call that the source
  has already bubbled out of some labels (`bub`), and traps or throws on the source side matched
  by a trap- or throw-active target (`trapC`, `throwC`);
* `CE k xs ys`: callee segments of arity `k`: related frames of arity `k`, a call redex
  (`val* REF.FUNC_ADDR a CALL_REF d`) related to itself or to the pending target frame, a callee
  wrapped by the target in a caller frame of arity `k` (`wrap`, nesting when the callee itself
  tail-calls), and `k` values (a callee that has returned inside a wrapper).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.TailSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.LimeCompile.Tail (tailI tailL tailFunc)

/-- Related function code: the same code, or a Wasm function and its tail rewrite. -/
def FCode {H : Type} : FuncCode H → FuncCode H → Prop
  | .wasm f, .wasm g => g = f ∨ g = tailFunc f
  | .host h, .host h' => h = h'
  | _, _ => False

/-- Related function instances: same defined type and module, related code. -/
def FRel {H : Type} (fi gi : FuncInst H) : Prop :=
  fi.type = gi.type ∧ fi.module = gi.module ∧ FCode fi.code gi.code

/-- A source `RETURN_CALL_REF` and the target's `CALL_REF` with the same annotation. -/
def RCRPair : Admin → Admin → Prop
  | .returnCallRefType d, c' => c' = .callRefType d
  | .plain (.returnCallRef y), c' => c' = .plain (.callRef y)
  | _, _ => False

/-- A nest of labels, each level with a value prefix and a suffix (an evaluation context made
of labels only). -/
inductive NCtx where
  | hole
  | label (V : List Val) (n : Nat) (cont : List Instr) (N : NCtx) (L : List Admin)

/-- Plug code into a nest of labels. -/
def NCtx.fill : NCtx → List Admin → List Admin
  | .hole, X => X
  | .label V n cont N L, X => vals V ++ .label n cont (N.fill X) :: L

/-- A wrapper body: `ys` followed by `RETURN` in the innermost of a nest of labels. -/
def PW (ys B : List Admin) : Prop :=
  ∃ (N : NCtx) (pre : List Val) (Y : List Admin), B = N.fill (vals pre ++ ys ++ .plain .return_ :: Y)

/-- A pending tail call: the target's wrapper body whose innermost stack is exactly `ws`,
followed by the target's `CALL_REF` for the source's `c` and `RETURN`. -/
def PT (ws : List Val) (c : Admin) (B : List Admin) : Prop :=
  ∃ (N : NCtx) (c' : Admin) (Y : List Admin), RCRPair c c' ∧
    B = N.fill (vals ws ++ c' :: .plain .return_ :: Y)

/-- A pending tail call that the source has bubbled out of at least one label: the target's
innermost stack is `ws` in a nest of at least one label. -/
def PTL (ws : List Val) (c : Admin) (B : List Admin) : Prop :=
  ∃ (V : List Val) (n : Nat) (cont : List Instr) (N : NCtx) (L : List Admin) (c' : Admin)
    (Y : List Admin), RCRPair c c' ∧
    B = vals V ++ .label n cont (N.fill (vals ws ++ c' :: .plain .return_ :: Y)) :: L

/-- A trap at the active position, under labels and frames. -/
inductive TA : List Admin → Prop where
  | base (ws : List Val) (y : List Admin) : TA (vals ws ++ .trap :: y)
  | label (ws : List Val) (n : Nat) (cont : List Instr) {b : List Admin} (y : List Admin) :
      TA b → TA (vals ws ++ .label n cont b :: y)
  | frame (ws : List Val) (n : Nat) (fi : Frame) {b : List Admin} (y : List Admin) :
      TA b → TA (vals ws ++ .frame n fi b :: y)

/-- The throw of exception `a` at the active position, under labels and frames. -/
inductive TT (a : Nat) : List Admin → Prop where
  | base (ws : List Val) (y : List Admin) : TT a (vals ws ++ throwing a ++ y)
  | label (ws : List Val) (n : Nat) (cont : List Instr) {b : List Admin} (y : List Admin) :
      TT a b → TT a (vals ws ++ .label n cont b :: y)
  | frame (ws : List Val) (n : Nat) (fi : Frame) {b : List Admin} (y : List Admin) :
      TT a b → TT a (vals ws ++ .frame n fi b :: y)

/-- The callee type `d` returns `k` values and takes `vs.length` arguments. -/
def Arity (d : DefType) (k : Nat) (vs : List Val) : Prop :=
  ∀ ps rs : Ty (.list .val), Expand d (.func ps rs) → rs.length = k ∧ vs.length = ps.length

mutual
/-- **The code relation** (source on the left, target on the right). The flag `fw` selects the
forward (`true`) or the backward (`false`) simulation: a source that has bubbled out of labels
alone (`bub`) occurs only forwards, values returned inside a wrapper (`CE.vals`) only
backwards. -/
inductive R : Bool → Bool → List Admin → List Admin → Prop where
  | nil {fw tl : Bool} : R fw tl [] []
  | same {fw tl : Bool} {a : Admin} {x y : List Admin} : ¬ a.IsCtx → R fw tl x y →
      R fw tl (a :: x) (a :: y)
  | instr {fw : Bool} {i : Instr} {x y : List Admin} : R fw true x y →
      R fw true (.plain i :: x) ((tailI i).map .plain ++ y)
  | rcr {fw : Bool} {c c' : Admin} {x y : List Admin} : RCRPair c c' → R fw true x y →
      R fw true (c :: x) (c' :: .plain .return_ :: y)
  | label {fw tl : Bool} {n : Nat} {cont cont' : List Instr} {b b' x y : List Admin} :
      (cont' = cont ∨ (tl = true ∧ cont' = tailL cont)) → R fw tl b b' → R fw tl x y →
      R fw tl (.label n cont b :: x) (.label n cont' b' :: y)
  | handler {fw tl : Bool} {n : Nat} {cs : List Catch} {b b' x y : List Admin} :
      R fw false b b' → R fw tl x y → R fw tl (.handler n cs b :: x) (.handler n cs b' :: y)
  | callee {fw tl : Bool} {k : Nat} {xs ys x y : List Admin} : CE fw k xs ys → R fw tl x y →
      R fw tl (xs ++ x) (ys ++ y)
  | bub {ws : List Val} {c : Admin} {B : List Admin} (U : List Val) (X : List Admin) :
      PTL ws c B → R true true (vals (U ++ ws) ++ c :: X) B
  | trapC {fw tl : Bool} (us : List Val) (x : List Admin) {y : List Admin} : TA y →
      R fw tl (vals us ++ .trap :: x) y
  | throwC {fw tl : Bool} {a : Nat} (us : List Val) (x : List Admin) {y : List Admin} : TT a y →
      R fw tl (vals us ++ throwing a ++ x) y

/-- **Callee segments of arity `k`.** -/
inductive CE : Bool → Nat → List Admin → List Admin → Prop where
  | frame {fw : Bool} {k : Nat} {fc : Frame} {b b' : List Admin} : R fw true b b' →
      CE fw k [.frame k fc b] [.frame k fc b']
  | call {fw : Bool} {k : Nat} {vs : List Val} {a : Nat} {d : DefType} : Arity d k vs →
      CE fw k (vals vs ++ [.ref (.func a), .callRefType d])
        (vals vs ++ [.ref (.func a), .callRefType d])
  | pend {fw : Bool} {k : Nat} {vs ws : List Val} {a : Nat} {d : DefType} {fi : Frame}
      {B : List Admin} {c : Admin} : Arity d k vs → PT ws c B → (vs ++ [.ref (.func a)]) <:+ ws →
      c.retToCallIn fi.module = .callRefType d →
      CE fw k (vals vs ++ [.ref (.func a), .callRefType d]) [.frame k fi B]
  | wrap {fw : Bool} {k : Nat} {xs ys : List Admin} {fi : Frame} {B : List Admin} :
      CE fw k xs ys → PW ys B → CE fw k xs [.frame k fi B]
  | vals {k : Nat} {ws : List Val} {fi : Frame} {B : List Admin} : ws.length = k →
      PW (vals ws) B → CE false k (vals ws) [.frame k fi B]
end

end Silmaril.Wasm.LimeCompile.TailSim
