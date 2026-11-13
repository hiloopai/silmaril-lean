module

public import Silmaril.Wasm.Models.FXAsyncPC.Defs

/-!
# Asyncify as a family of comorphisms: the parameters

Asyncify turns code that suspends (one-shot effect handlers, WasmFX `suspend`/`resume`) into code
without continuations, by saving the suspended frames and restoring them later. There are several
ways to do this and several optimizations; this module makes both into parameters of one
transformation, so that each choice is an **instance** with its own correctness theorem.

The source of every instance is the handler kernel `FXAsync.sstep` (one-shot shallow handlers,
nesting, forwarding, first-class continuations; `Silmaril.Wasm.Models.FXAsync`). Its relation to
`StepFX'` is on main (`FXAsyncFX.kernel_in_fx`, `FXAsyncBack.beh_eq`, `FXAsyncSus.beh_eq_tight`)
and is not repeated here.

**Strategies** (`Strategy`): how the suspended state is kept and how execution re-enters it.

* `unwind`: Binaryen-style stack unwinding. A global mode (normal / unwinding / rewinding); after
  every instrumented call site a check saves the frame and returns while unwinding; rewinding
  re-enters saved frames at their resume points. Saved frames are kept abstractly (code suffix
  and operands): the target is `FXAsync.tstep`.
* `unwindDispatch`: the same, first order. Saved frames are records (function number, resume
  index, operands) and re-entry is a dispatch on the resume index (the `global.get; br_table`
  prologue of `FXDispatch`): the target is `FXAsyncPC.fstep` on the annotated program `annP`.

CPS and a whole-program state machine are further strategies (`docs/projects/wasm-binaryen-tooling.md`); they are
not defined yet, so `Strategy` lists only those with a target machine.

**Optimizations** (`Opt`): which call sites are instrumented. (The root frame of a call, `tInit`
and `fInit`, always keeps its check; it costs one step and only matters for an unhandled tag.) `Opt.instr f` says whether a call
of `f` gets its check. The whole-program instance instruments everything (`Opt.whole`); the
selective instance keeps the check only after calls that may reach a suspension, given by an
analysis `S`, and is correct on programs for which `S` is sound (`Sound`). Liveness-based save
sets and the elision of re-entry checks need locals and blocks, which the kernel does not have;
they are documented as open.

**The family** (`Scheme`, `scheme`): an instance gives a target program type, a compiler from
kernel programs, the behaviours of a call in the target, and the fragment of source programs on
which it is meant to be correct. `Scheme.Correct` says that, on the fragment, every call has the
same behaviours (returned values, trap, divergence) in the source and the target. `Scheme`'s
charts and transition (`srcChart`, `Scheme.tgtChart`) are in `Silmaril.Wasm.FX.Asyncify.Thms`: a
correct instance is a comorphism of behaviour charts (`Atlas.BTrans.ofEq`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify

open Silmaril.Wasm.Models.FXAsync
open Silmaril.Wasm.Models.FXAsyncPC (fstep annP bodies rootCode fInit)

/-! ## Parameters -/

/-- An asyncify strategy with a target machine. -/
inductive Strategy where
  /-- Stack unwinding with call-site checks; saved frames kept abstractly (`tstep`). -/
  | unwind
  /-- Stack unwinding with first-order records and `br_table` resume dispatch (`fstep`). -/
  | unwindDispatch
deriving DecidableEq, Repr

/-- Asyncify optimizations: which call sites are instrumented. -/
structure Opt where
  /-- A call of function `f` gets a check after it iff `instr f`. -/
  instr : Nat → Bool

/-- Instrument every call site (whole-program asyncify). -/
def Opt.whole : Opt := ⟨fun _ => true⟩

/-- Instrument only calls of functions in the analysis `S` (selective asyncify). -/
def Opt.selective (S : Nat → Bool) : Opt := ⟨S⟩

/-! ## The parametric lowering -/

/-- The check after a call site of `f` (or of `f` or `g`, for `cond`): present iff instrumented. -/
def chkIf {V : Type} (b : Bool) : List (TIns V) := if b then [.chk] else []

/-- **Compile kernel code under the optimization `o`.** -/
def compO {V : Type} (o : Opt) : List (Ins V) → List (TIns V)
  | [] => []
  | .push v :: c => .push v :: compO o c
  | .prim n op :: c => .prim n op :: compO o c
  | .drop :: c => .drop :: compO o c
  | .call f :: c => .call f :: (chkIf (o.instr f) ++ compO o c)
  | .cond f g :: c => .cond f g :: (chkIf (o.instr f || o.instr g) ++ compO o c)
  | .contNew f :: c => .alloc f :: compO o c
  | .resume n hs :: c => .startRewind n :: .rchk hs :: compO o c
  | .suspend t n :: c => .startUnwind t n :: compO o c

/-- Compile a function table under `o`. -/
def compPO {V : Type} (o : Opt) (P : Prog (Ins V)) : Prog (TIns V) :=
  fun f => (P f).map fun x => (x.1, compO o x.2)

/-! ## The fragment of the selective optimization -/

/-- Code that never suspends or resumes and calls only functions outside `S`. -/
def Calm {V : Type} (S : Nat → Bool) (c : List (Ins V)) : Prop :=
  ∀ i ∈ c, match i with
    | .call f => S f = false
    | .cond f g => S f = false ∧ S g = false
    | .resume _ _ => False
    | .suspend _ _ => False
    | _ => True

/-- **A sound suspension analysis**: every function outside `S` has calm code. Then a call of a
function outside `S` cannot reach a `suspend`, nor run a continuation, and needs no check. -/
def Sound {V : Type} (S : Nat → Bool) (P : Prog (Ins V)) : Prop :=
  ∀ f np body, P f = some (np, body) → S f = false → Calm S body

/-! ## The family -/

/-- An asyncify instance: a target, a compiler, target behaviours of calls, a source fragment. -/
structure Scheme (V : Type) where
  /-- Target programs. -/
  TP : Type
  /-- The compiler. -/
  compile : Prog (Ins V) → TP
  /-- The target behaviours of a call of `f` with `args`, under the branch test. -/
  run : TP → (V → Bool) → Nat → List (SV V) → Set (Obs V)
  /-- The source programs on which the instance is meant to be correct. -/
  dom : Prog (Ins V) → Prop

/-- The kernel behaviours of a call of `f` with `args`. -/
def srcRun {V : Type} (P : Prog (Ins V)) (test : V → Bool) (f : Nat) (args : List (SV V)) :
    Set (Obs V) :=
  beh (sstep P test) (sInit f args)

/-- **Correctness of an instance**: on its fragment, every call has the same behaviours. -/
def Scheme.Correct {V : Type} (A : Scheme V) : Prop :=
  ∀ P, A.dom P → ∀ test f args, A.run (A.compile P) test f args = srcRun P test f args

/-- The fragment of an optimization: every program for `whole`, sound analyses otherwise. -/
def Opt.Dom {V : Type} (o : Opt) (P : Prog (Ins V)) : Prop := Sound o.instr P

/-- **The asyncify family**, indexed by strategy and optimization. -/
def scheme (V : Type) : Strategy → Opt → Scheme V
  | .unwind, o =>
    { TP := Prog (TIns V)
      compile := compPO o
      run := fun Q test f args => beh (tstep Q test) (tInit f args)
      dom := o.Dom }
  | .unwindDispatch, o =>
    { TP := Prog (TIns V)
      compile := compPO o
      run := fun Q test f args => beh (fstep (annP Q) (bodies Q (rootCode f)) test) (fInit f args)
      dom := o.Dom }

/-! ## Relational simulations (the general theorem's hypothesis) -/

/-- Results related by `R` (configurations) or equal (outcomes). -/
def ResRel {C D V : Type} (R : C → D → Prop) : Res C V → Res D V → Prop
  | .next a, .next b => R a b
  | .stop o, .stop o' => o = o'
  | _, _ => False

/-- **A stuttering relational simulation**: every step of `s` from an `R`-related pair is matched
by a positive number of steps of `t`, landing in `R` again or stopping with the same outcome. -/
def SimRel {C D V : Type} (s : C → Res C V) (t : D → Res D V) (R : C → D → Prop) : Prop :=
  ∀ x y, R x y → ∃ n, 0 < n ∧ ResRel R (s x) (runN t n y)

end Silmaril.Wasm.FX.Asyncify
