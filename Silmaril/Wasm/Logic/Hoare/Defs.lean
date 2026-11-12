module

public import Silmaril.Wasm.Logic.Core.Defs

/-!
# An every-run program logic for Wasm Core 3.0: definitions

`Safe P host Q n c` is a step-indexed **safety** predicate on Core 3.0
configurations: for `n` steps, either the code has reached an exit (`Exits`) whose
outcome satisfies `Q`, or it can step and every successor is safe for `n - 1`
steps. `HWP P host s f code Q` (safe for every `n`) is the **every-run, partial
correctness** weakest precondition: no run from `⟨s, f, code⟩` gets stuck, and
every run that stops does so at an exit satisfying `Q` (`HWP.sound`,
`Silmaril.Wasm.Logic.Hoare.Thms`). Unlike `Silmaril.Wasm.Logic.Core.WP`, which asks for
one run, `HWP` covers every run, so nondeterminism (relaxed SIMD and float NaNs
in a nondeterministic profile, `memory.grow`/`table.grow` failing or succeeding,
host calls) is handled by quantifying over the successors.

`TSafe` is the inductive (least-fixpoint) version: **total correctness**, every
run terminates (`TSafe.not_diverges`).

Outcomes are those of the existential calculus (`Silmaril.Wasm.Logic.Core.Outcome`:
`normal`, `br`, `ret`, `trap`, `throw`, `tail`). `Exits o c` is looser than
`Outcome.Ends` for traps and exceptions: a `trap` or an exception may still have
values before it and dead code after it (the bubbling rules remove them in
further steps, without changing the store or the frame).

Postconditions see the store, the frame and the outcome. The combinators below
say how an outcome is seen from outside a sequence (`seqPostK`), a label
(`labelPostK`), an exception handler (`Silmaril.Wasm.Logic.Core.handlerPost`), a
function frame (`framePostK`) and a call (`callPost`); the `K` versions carry a
step index `k` for the continuation, which is what makes loops and recursive
calls provable by induction on the index (Löb induction).

Function specifications (`FSpec`, `FSpecAt`) are every-run, step-indexed and
quantify over the calling frame, the caller's operand stack below the arguments
and every `CALL_REF` form (so one specification serves `call`, `call_ref`,
`call_indirect`, `return_call*` and the embedder's `$invoke`). A spec context
`Ctx` assigns specifications to function addresses; `Ctx.ValidAt n Γ` says all of
them hold for `n` steps.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.Hoare

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type}

/-! ## Exits -/

/-- The code `c` has left with outcome `o`. A trap or an exception may still be
inside a sequence (values before, dead code after); everything else is exact. -/
def Exits : Outcome → List Admin → Prop
  | .normal vs, c => c = vals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List Admin), x.toNat = l ∧
      c = vals vs ++ .plain (.br x) :: rest
  | .ret vs, c => ∃ rest : List Admin, c = vals vs ++ .plain .return_ :: rest
  | .trap, c => ∃ (vs : List Val) (rest : List Admin), c = vals vs ++ .trap :: rest
  | .throw a, c => ∃ (vs : List Val) (rest : List Admin), c = vals vs ++ throwing a ++ rest
  | .tail vs a r, c => r.IsReturnCallRef ∧ ∃ rest : List Admin,
      c = vals vs ++ .ref (.func a) :: r :: rest

/-! ## Safety and the every-run weakest precondition -/

/-- **Step-indexed safety.** For `n` steps, `c` either has exited with an outcome
satisfying `Q`, or it can step and all its successors are safe for `n - 1` steps. -/
def Safe (P : Profile) (host : HostSemantics H) (Q : Post H) : Nat → Config H → Prop
  | 0, _ => True
  | n + 1, c => (∃ o, Exits o c.code ∧ Q c.store c.frame o) ∨
      ((∃ c', Step P host c c') ∧ ∀ c', Step P host c c' → Safe P host Q n c')

/-- **The every-run weakest precondition** (partial correctness): `code` is safe
from `s, f` for every number of steps. -/
def HWP (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (code : List Admin)
    (Q : Post H) : Prop :=
  ∀ n, Safe P host Q n ⟨s, f, code⟩

/-- **Total safety**: the least fixpoint. Every run terminates, at an exit
satisfying `Q`. -/
inductive TSafe (P : Profile) (host : HostSemantics H) (Q : Post H) : Config H → Prop where
  | exit {c : Config H} (o : Outcome) : Exits o c.code → Q c.store c.frame o → TSafe P host Q c
  | step {c : Config H} : (∃ c', Step P host c c') → (∀ c', Step P host c c' → TSafe P host Q c') →
      TSafe P host Q c

/-- **The total-correctness weakest precondition.** -/
def TWP (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (code : List Admin)
    (Q : Post H) : Prop :=
  TSafe P host Q ⟨s, f, code⟩

/-- A Hoare triple `{Pre} code {Q}` in the every-run reading. -/
def Triple (P : Profile) (host : HostSemantics H) (Pre : Store H → Frame → Prop)
    (code : List Admin) (Q : Post H) : Prop :=
  ∀ s f, Pre s f → HWP P host s f code Q

/-! ## Outcomes seen from outside -/

/-- The postcondition of `c₁` in `c₁ ++ c₂`, with a continuation index `k`: on
falling through, `c₂` must be safe for `k` steps; every other outcome skips
`c₂`. -/
def seqPostK (P : Profile) (host : HostSemantics H) (c₂ : List Admin) (Q : Post H) (k : Nat) :
    Post H := fun s f o =>
  match o with
  | .normal vs => Safe P host Q k ⟨s, f, vals vs ++ c₂⟩
  | o => Q s f o

/-- `seqPostK` for every index: falling through, `c₂` satisfies `HWP`. -/
def seqPost (P : Profile) (host : HostSemantics H) (c₂ : List Admin) (Q : Post H) : Post H :=
  fun s f o =>
    match o with
    | .normal vs => HWP P host s f (vals vs ++ c₂) Q
    | o => Q s f o

/-- What the body of `LABEL_n{cont}`, sitting on the values `us`, may end with,
seen from outside the label, with a continuation index `k`. A branch to the label
itself continues with `cont` on the top `n` values, which must be safe for `k`
steps; every other outcome leaves the label (one label less for a branch). -/
def labelPostK (P : Profile) (host : HostSemantics H) (n : Nat) (cont : List Instr)
    (us : List Val) (Q : Post H) (k : Nat) : Post H := fun s f o =>
  match o with
  | .normal vs => Q s f (.normal (us ++ vs))
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧
      Safe P host Q k ⟨s, f, vals us ++ vals vs₂ ++ expression cont⟩
  | .br (l + 1) vs => Q s f (.br l (us ++ vs))
  | .ret vs => Q s f (.ret (us ++ vs))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => Q s f (.tail (us ++ vs) a c)

/-- `labelPostK` for every index. -/
def labelPost (P : Profile) (host : HostSemantics H) (n : Nat) (cont : List Instr)
    (us : List Val) (Q : Post H) : Post H := fun s f o =>
  match o with
  | .br 0 vs => ∃ vs₁ vs₂, vs = vs₁ ++ vs₂ ∧ vs₂.length = n ∧
      HWP P host s f (vals us ++ vals vs₂ ++ expression cont) Q
  | o => labelPostK P host n cont us Q 0 s f o

/-- Put the values `vs₀` below an outcome's stack, as `Outcome.prepend`. -/
def prePost (vs₀ : List Val) (Q : Post H) : Post H := fun s f o => Q s f (o.prepend vs₀)

/-- What the body of a function frame `FRAME_n{F}` may end with, seen from the
caller in frame `f` with the values `vs₀` below the call: falling through with
exactly `n` results, or `return` with at least `n` values, returns the top `n`
values; a trap or an exception passes through; a tail call of the function `a`
replaces the frame by a call of `a` from the caller, which must be safe for `k`
steps. A branch out of a function body is impossible in valid code. -/
def framePostK (P : Profile) (host : HostSemantics H) (n : Nat) (f : Frame) (vs₀ : List Val)
    (Q : Post H) (k : Nat) : Post H := fun s F o =>
  match o with
  | .normal res => res.length = n ∧ Q s f (.normal (vs₀ ++ res))
  | .br _ _ => False
  | .ret vs => ∃ vs₁ res, vs = vs₁ ++ res ∧ res.length = n ∧ Q s f (.normal (vs₀ ++ res))
  | .trap => Q s f .trap
  | .throw a => Q s f (.throw a)
  | .tail vs a c => ∃ (vs₁ args : List Val) (fn : FuncInst H) (ps rs : Ty (.list .val)),
      vs = vs₁ ++ args ∧ s.funcs[a]? = some fn ∧ Expand fn.type (.func ps rs) ∧
      args.length = ps.length ∧
      Safe P host Q k ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c.retToCallIn F.module]⟩

/-- The postcondition of a function body `expression body` run inside
`FRAME_n{F} (LABEL_n{} …)`, as seen by the caller (the label of the body and the
frame combined). -/
def bodyPostK (P : Profile) (host : HostSemantics H) (n : Nat) (f : Frame) (vs₀ : List Val)
    (Q : Post H) (k : Nat) : Post H :=
  labelPostK P host n [] [] (framePostK P host n f vs₀ Q k) k

/-! ## Function specifications -/

/-- A function specification: a precondition on the store and the arguments, and
a postcondition on the initial store and arguments, the final store and the
outcome of the call (`normal res`, `trap` or `throw a`). -/
structure FSpec (H : Type) where
  /-- The precondition. -/
  pre : Store H → List Val → Prop
  /-- The postcondition. -/
  post : Store H → List Val → Store H → Outcome → Prop

/-- The outcome of a call seen by a caller in frame `f` with the values `vs₀` below
the arguments: it returns to `f`, with results `res` on top of `vs₀`, or traps, or
throws; `R` constrains the callee's outcome. -/
def callPost (f : Frame) (vs₀ : List Val) (R : Store H → Outcome → Prop) : Post H :=
  fun s f' o => f' = f ∧
    ((∃ res, o = .normal (vs₀ ++ res) ∧ R s (.normal res)) ∨ (o = .trap ∧ R s .trap) ∨
      (∃ a, o = .throw a ∧ R s (.throw a)))

/-- **A function specification holds for `n` steps** at address `a`: from any
store and arguments satisfying the precondition, in any calling frame, below any
caller stack `vs₀` and through any `CALL_REF` form, the call is safe for `n` steps
with the call postcondition. -/
def FSpecAt (P : Profile) (host : HostSemantics H) (n : Nat) (a : Nat) (S : FSpec H) : Prop :=
  ∀ s args, S.pre s args → ∀ (f : Frame) (vs₀ : List Val) (c : Admin), c.IsCallRef →
    Safe P host (callPost f vs₀ (S.post s args)) n
      ⟨s, f, vals vs₀ ++ vals args ++ [.ref (.func a), c]⟩

/-- A specification holds for every number of steps. -/
def FSpecValid (P : Profile) (host : HostSemantics H) (a : Nat) (S : FSpec H) : Prop :=
  ∀ n, FSpecAt P host n a S

/-- A **specification context**: specifications for some function addresses. -/
abbrev Ctx (H : Type) := Nat → Option (FSpec H)

/-- Every specification of the context holds for `n` steps. -/
def Ctx.ValidAt (P : Profile) (host : HostSemantics H) (n : Nat) (Γ : Ctx H) : Prop :=
  ∀ a S, Γ a = some S → FSpecAt P host n a S

/-- Every specification of the context holds. -/
def Ctx.Valid (P : Profile) (host : HostSemantics H) (Γ : Ctx H) : Prop :=
  ∀ n, Ctx.ValidAt P host n Γ

end Silmaril.Wasm.Logic.Hoare
