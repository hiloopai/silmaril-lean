module

public import Silmaril.Wasm.Execution.Core.Instantiation

/-!
# A weakest-precondition calculus for Wasm Core 3.0 code: definitions

`WP P host s f code Q` says: from store `s` and frame `f`, the administrative
code `code` **can run** (in profile `P`, with host semantics `host`) to a final
form, and the outcome satisfies `Q`. The final forms (`Outcome`) are

* `normal vs`: the code fell through, leaving the values `vs`;
* `br l vs`: the code is about to branch to the enclosing label `l` with the
  values `vs` on the stack (anything after the `br` is dead code);
* `ret vs`: the code is about to `return` with the values `vs`;
* `trap`: the code trapped;
* `throw a`: the code is throwing the exception at address `a`
  (`REF.EXN_ADDR a; THROW_REF`, the form `throw` and `throw_ref` reduce to);
* `tail vs a c`: the code is about to tail-call the function at address `a`
  (`return_call`, `return_call_ref`, `return_call_indirect`), with arguments on top
  of `vs`.

This is the outcome-indexed postcondition of Wasm Logic (Watt, Maksimović,
Krishnaswami and Gardner, ECOOP 2019, Figure 9): there, the label
postconditions `L` and the return postcondition `R` live in the context; here
they are the `br` and `ret` cases of one postcondition `Q`. `blockPost` pushes a
label whose postcondition is the block's own, `loopPost` one whose
postcondition is the loop invariant, as the `[block]` and `[loop]` rules do.

`WP` is existential: it asks for **one** run (total correctness of one
execution), in every profile and for every host relation. It is the calculus
for proving that code *can* reach an outcome (completeness of a specification).
For code with a unique run (deterministic profiles and closed hosts), "some run"
and "every run" coincide.

Function specifications (`FuncSpec`) are stated on the code a call reduces to
(`callCode`), which is what `call x`, `call_ref`, `call_indirect` and the
embedder's `$invoke` produce. `exec` is a small interpreter for straight-line
code whose soundness (`exec_sound`) turns symbolic evaluation by `simp` into
runs.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Core

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

/-! ## Outcomes -/

/-- How control leaves a piece of code. -/
inductive Outcome where
  /-- Fell through with the values `vs`. -/
  | normal (vs : List Val)
  /-- About to branch to the enclosing label `l` with the values `vs`. -/
  | br (l : Nat) (vs : List Val)
  /-- About to return with the values `vs`. -/
  | ret (vs : List Val)
  /-- Trapped. -/
  | trap
  /-- Throwing the exception at address `a` (`REF.EXN_ADDR a; THROW_REF`). -/
  | throw (a : Nat)
  /-- About to tail-call the function at address `a` (`REF.FUNC_ADDR a` followed by the
  `RETURN_CALL_REF` form `c`), with the values `vs` below the reference. -/
  | tail (vs : List Val) (a : Nat) (c : Admin)

/-- The code `c` is a final form of outcome `o`. -/
def Outcome.Ends : Outcome → List Admin → Prop
  | .normal vs, c => c = vals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List Admin), x.toNat = l ∧
      c = vals vs ++ .plain (.br x) :: rest
  | .ret vs, c => ∃ rest : List Admin, c = vals vs ++ .plain .return_ :: rest
  | .trap, c => c = [.trap]
  | .throw a, c => c = throwing a
  | .tail vs a r, c => r.IsReturnCallRef ∧ ∃ rest : List Admin,
      c = vals vs ++ .ref (.func a) :: r :: rest

/-- Put the values `vs₀` below the stack of an outcome. A trap and a throw discard
them. -/
def Outcome.prepend (vs₀ : List Val) : Outcome → Outcome
  | .normal vs => .normal (vs₀ ++ vs)
  | .br l vs => .br l (vs₀ ++ vs)
  | .ret vs => .ret (vs₀ ++ vs)
  | .trap => .trap
  | .throw a => .throw a
  | .tail vs a c => .tail (vs₀ ++ vs) a c

/-- Postconditions see the store, the frame and the outcome. -/
abbrev Post (H : Type) := Store H → Frame → Outcome → Prop

variable {H : Type}

/-! ## The weakest precondition -/

/-- **The weakest precondition.** From `s` and `f`, `code` can run to a final form
whose outcome satisfies `Q`. -/
def WP (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (code : List Admin)
    (Q : Post H) : Prop :=
  ∃ (s' : Store H) (f' : Frame) (c' : List Admin) (o : Outcome),
    Steps P host ⟨s, f, code⟩ ⟨s', f', c'⟩ ∧ o.Ends c' ∧ Q s' f' o

/-- The postcondition of the first part of `c₁ ++ c₂`: on falling through, run `c₂`;
a branch, a return or a throw skips `c₂`; a trap stays a trap. -/
def seqPost (P : Profile) (host : HostSemantics H) (c₂ : List Admin) (Q : Post H) : Post H :=
  fun s f o =>
    match o with
    | .normal vs => WP P host s f (vals vs ++ c₂) Q
    | o => Q s f o

/-- What the code inside a label `label n cont` may end with, seen from outside
the label: falling through leaves the label; a branch to the label itself
(`br 0`) continues with `cont` on the top `n` values; deeper branches lose one
label; a return, a trap or a throw passes through. -/
def labelPost (P : Profile) (host : HostSemantics H) (n : Nat) (cont : List Instr)
    (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal vs)
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧
      WP P host s f (vals vs₂ ++ expression cont) Q
  | .br (l + 1) vs => Q s f (.br l vs)
  | .ret vs => Q s f (.ret vs)
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail vs a c)

/-- What the body of a block of result arity `n` may end with, seen from outside
the block: falling through or branching to the block's own label (`br 0`) both
leave the block normally with the top `n` values; deeper branches lose one label. -/
def blockPost (n : Nat) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal vs)
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧ Q s f (.normal vs₂)
  | .br (l + 1) vs => Q s f (.br l vs)
  | .ret vs => Q s f (.ret vs)
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail vs a c)

/-- What the body of a loop with parameter arity `n` may end with: a branch to the
loop's own label (`br 0`) re-enters the loop with the top `n` values, which must
satisfy the invariant at a smaller measure; everything else leaves the loop. -/
def loopPost (n : Nat) (Inv : Nat → Store H → Frame → List Val → Prop) (m : Nat)
    (Q : Post H) : Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal vs)
  | .br 0 vs =>
    ∃ vs₁ vs₂ k, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧ k < m ∧ Inv k s f vs₂
  | .br (l + 1) vs => Q s f (.br l vs)
  | .ret vs => Q s f (.ret vs)
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail vs a c)

/-- What a caught exception `a` becomes at the matching catch clause: a branch to
the clause's label with the exception's fields, its reference, both, or nothing. -/
def caughtPost (s : Store H) (f : Frame) (a : Nat) (Q : Post H) : Catch → Prop
  | .catch_ _ l => ∃ e : ExnInst, s.exns[a]? = some e ∧ Q s f (.br l.toNat e.fields)
  | .catchRef _ l => ∃ e : ExnInst, s.exns[a]? = some e ∧
      Q s f (.br l.toNat (e.fields ++ [.ref (.exn a)]))
  | .catchAll l => Q s f (.br l.toNat [])
  | .catchAllRef l => Q s f (.br l.toNat [.ref (.exn a)])

/-- An exception `a` thrown into the catch clauses `cs`: the first matching clause
catches it (`caughtPost`); if none matches, it propagates. -/
def catchPost (s : Store H) (f : Frame) (a : Nat) (Q : Post H) : List Catch → Prop
  | [] => Q s f (.throw a)
  | c :: cs => (CatchMatches s f a c ∧ caughtPost s f a Q c) ∨
      (¬ CatchMatches s f a c ∧ catchPost s f a Q cs)

/-- What the code inside an exception handler `handler n cs` may end with, seen from
outside: a throw is dispatched to the catch clauses (`catchPost`); everything else
passes through. -/
def handlerPost (cs : List Catch) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .throw a => catchPost s f a Q cs
  | o => Q s f o

/-! ## Function specifications -/

/-- The code of a call of the function at address `a` on `args`: what `call x`
reduces to in one step, and the code of `$invoke`. -/
def callCode (s : Store H) (a : Nat) (args : List Val) : List Admin :=
  vals args ++ [.ref (.func a), .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]

/-- **A function specification.** From any store and arguments satisfying `Pre`,
in any calling frame and through any `CALL_REF` form `c` (`call`, `call_ref`,
`call_indirect`, `return_call` and `$invoke` all reduce to one), a call of the
function at address `a` can return `res` leaving the store `s'`, with
`Post s args s' res`.

Deviation from the source: `Silmaril.Wasm.Verify.FuncSpec` fixes `c` to the
`CALL_REF` of `callCode`; quantifying over `c` lets one specification serve the
typed `call_ref y` of Wasm 3.0 and tail calls (`return_call`), whose `CALL_REF`
carries the annotation of the call site. -/
def FuncSpec (P : Profile) (host : HostSemantics H) (a : Nat) (Pre : Store H → List Val → Prop)
    (Post : Store H → List Val → Store H → List Val → Prop) : Prop :=
  ∀ s args, Pre s args → ∀ (f : Frame) (c : Admin), c.IsCallRef → ∃ s' res,
    Steps P host ⟨s, f, vals args ++ [.ref (.func a), c]⟩ ⟨s', f, vals res⟩ ∧
      Post s args s' res

/-- A **functional** specification: the call computes the store and results by the
Lean function `F`. -/
abbrev FuncSpecFn (P : Profile) (host : HostSemantics H) (a : Nat)
    (Pre : Store H → List Val → Prop)
    (F : Store H → List Val → Store H × List Val) : Prop :=
  FuncSpec P host a Pre fun s args s' res => (s', res) = F s args

/-- What a function body of result arity `n` may end with: falling through, a
branch to the body's own label (`br 0`), or `return`, each with the top `n`
values as results; or a tail call of a function `a` whose own call can return
results satisfying `K` from every calling frame (the callee replaces the body's
frame, so its results are the body's). A deeper branch is impossible in a valid
body; a trap or an escaping exception is excluded by this postcondition. -/
def funcPost (P : Profile) (host : HostSemantics H) (n : Nat) (K : Store H → List Val → Prop) :
    Post H := fun s F o =>
  match o with
  | .normal res => res.length = n ∧ K s res
  | .br 0 vs => ∃ vs₁ res, vs = vs₁ ++ res ∧ res.length = n ∧ K s res
  | .br (_ + 1) _ => False
  | .ret vs => ∃ vs₁ res, vs = vs₁ ++ res ∧ res.length = n ∧ K s res
  | .trap => False
  | .throw _ => False
  | .tail vs a c => ∃ (vs₁ args : List Val) (fn : FuncInst H) (ps rs : Ty (.list .val)),
      vs = vs₁ ++ args ∧ s.funcs[a]? = some fn ∧ Expand fn.type (.func ps rs) ∧
      args.length = ps.length ∧ ∀ g : Frame, ∃ s' res,
        Steps P host ⟨s, g, vals args ++ [.ref (.func a), c.retToCallIn F.module]⟩
          ⟨s', g, vals res⟩ ∧ K s' res

/-! ## Straight-line code by evaluation -/

/-- Pop an integer of type `t` (the stack is top-first). -/
def popInt : (t : IntType) → List Val → Option (BitVec t.width × List Val)
  | .i32, .num ⟨.int .i32, a⟩ :: rs => some (a, rs)
  | .i64, .num ⟨.int .i64, a⟩ :: rs => some (a, rs)
  | _, _ => none

/-- Pop any value. -/
def popV : List Val → Option (Val × List Val)
  | v :: rs => some (v, rs)
  | [] => none

/-- The value of a set local. -/
def localVal? (f : Frame) (x : LocalIdx) : Option Val :=
  match f.local? x with
  | some (some v) => some v
  | _ => none

/-- One instruction of straight-line code; the operand stack is top-first. -/
def exec1 (s : Store H) (f : Frame) (rs : List Val) :
    Instr → Option (Store H × Frame × List Val)
  | .nop => some (s, f, rs)
  | .drop => (popV rs).map fun (_, rs') => (s, f, rs')
  | .intConst t c => some (s, f, .num ⟨.int t, c⟩ :: rs)
  | .localGet x => (localVal? f x).map fun v => (s, f, v :: rs)
  | .localSet x =>
    (popV rs).bind fun (v, rs') =>
      if x.toNat < f.locals.length then some (s, f.setLocal x v, rs') else none
  | .localTee x =>
    (popV rs).bind fun (v, rs') =>
      if x.toNat < f.locals.length then some (s, f.setLocal x v, v :: rs') else none
  | .globalGet x => (s.global? f x).map fun (_, g) => (s, f, g.value :: rs)
  | .globalSet x =>
    (popV rs).bind fun (v, rs') => (s.global? f x).map fun (a, _) => (s.setGlobal a v, f, rs')
  | .intUnOp t op =>
    (popInt t rs).map fun (x, rs₁) => (s, f, .num ⟨.int t, intUnOp t op x⟩ :: rs₁)
  | .intBinOp t op =>
    (popInt t rs).bind fun (y, rs₁) => (popInt t rs₁).bind fun (x, rs₂) =>
      match intBinOp t op x y with
      | .ok z => some (s, f, .num ⟨.int t, z⟩ :: rs₂)
      | .error _ => none
  | .intTestOp t op =>
    (popInt t rs).map fun (x, rs₁) => (s, f, Val.i32 (intTestOp t op x) :: rs₁)
  | .intRelOp t op =>
    (popInt t rs).bind fun (y, rs₁) => (popInt t rs₁).map fun (x, rs₂) =>
      (s, f, Val.i32 (intRelOp t op x y) :: rs₂)
  | .intLoad t none x arg =>
    (popInt .i32 rs).bind fun (a, rs₁) => (s.mem? f x).bind fun (_, mi) =>
      (Memory.load mi.bytes (effAddr a.toNat arg) (t.width / 8)).map fun c =>
        (s, f, .num ⟨.int t, c.setWidth t.width⟩ :: rs₁)
  | .intLoad t (some (sz, sx)) x arg =>
    (popInt .i32 rs).bind fun (a, rs₁) => (s.mem? f x).bind fun (_, mi) =>
      (Memory.load mi.bytes (effAddr a.toNat arg) (sz.width / 8)).map fun c =>
        (s, f, .num ⟨.int t, match sx with
          | .signed => c.signExtend t.width
          | .unsigned => c.setWidth t.width⟩ :: rs₁)
  | .intStore t none x arg =>
    (popInt t rs).bind fun (c, rs₁) => (popInt .i32 rs₁).bind fun (a, rs₂) =>
      (s.mem? f x).bind fun (ma, mi) =>
      (Memory.store mi.bytes (effAddr a.toNat arg) (count := t.width / 8)
        (c.setWidth _)).map fun b => (s.setMem ma { mi with bytes := b }, f, rs₂)
  | .intStore t (some sz) x arg =>
    (popInt t rs).bind fun (c, rs₁) => (popInt .i32 rs₁).bind fun (a, rs₂) =>
      (s.mem? f x).bind fun (ma, mi) =>
      (Memory.store mi.bytes (effAddr a.toNat arg) (count := sz.width / 8)
        (c.setWidth _)).map fun b => (s.setMem ma { mi with bytes := b }, f, rs₂)
  | _ => none

/-- Straight-line code. -/
def exec (s : Store H) (f : Frame) (rs : List Val) :
    List Instr → Option (Store H × Frame × List Val)
  | [] => some (s, f, rs)
  | i :: is =>
    match exec1 s f rs i with
    | some (s₁, f₁, rs₁) => exec s₁ f₁ rs₁ is
    | none => none

end Silmaril.Wasm.Logic.Core
