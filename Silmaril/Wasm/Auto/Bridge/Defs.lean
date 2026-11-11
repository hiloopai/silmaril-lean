module

public import Silmaril.Wasm.Auto.Equiv.Defs
public import Silmaril.Wasm.Verify.Checker.Defs
public import Silmaril.Wasm.Auto.ESeg.Defs

/-!
# From segments to modules: function summaries

The bridge of `docs/projects/wasm-binaryen-tooling.md` between the symbolic checkers
of the other tracks (the `SState`s and `Term`s of `Silmaril.Wasm.Auto.Equiv`) and the module-level
statements of the front end (`ModRefines`, `ModEquiv`, `ModMeets` of `Silmaril.Wasm.Auto.Front`).

* `xexec`: symbolic execution of a **function body**, extending `Silmaril.Wasm.Auto.Equiv.sexec`
  (straight-line integer code) by `select` and by `block`/`if` without branches out of them
  (parameterless block types with at most one integer result). A `select` becomes the term
  `selT a b c = b + (a - b) * [c ≠ 0]`; an `if` executes both arms from the same state and
  merges every local and result slot by `selT` on the condition. Instruction-count fuel bounds
  the recursion (structural, so the kernel evaluates it).
* `fnSum? m j`: the **summary** of function export `j` of `m`'s computed instance
  (`Silmaril.Wasm.Verify.instance?`): its integer parameter and result types and the final
  symbolic state of its body, run from the locals `var 0 … var (p-1)` (the parameters) and
  `0` (the declared locals). `fnOut F vs` is the result on the arguments `vs`.
* `fnCheck m₁ m₂ j`: the two summaries have the same parameter types and equal normal forms
  of their results (`Silmaril.Wasm.Auto.Equiv.slotsEq`); `fnResiduals` lists the result slots
  whose normal forms differ, as bitvector goals.

The theorems (`Silmaril.Wasm.Auto.Bridge.Thms`) turn a summary into the exact behaviour set of
the export at **every profile** (`behaviours … = {returns (fnOut F vs)}`: it terminates, does not
trap, and returns `fnOut F vs`), from the every-run total-correctness logic; `fnCheck` then gives
`ModEquiv` and `ModRefines`, and a reference function that agrees with `fnOut` gives `ModMeets`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Game (ScalarType ScalarInstance)
open Silmaril.Wasm.Verify (instance?)

/-! ## `select` and merges -/

/-- The term of `select a b c` (`a` when `c ≠ 0`, else `b`), at any integer type:
`b + (a - b) * [c ≠ 0]`, the comparison evaluated at `i32`. -/
def selT (a b c : Term) : Term :=
  .bin .add b (.bin .mul (.bin .sub a b) (.rel .i32 .ne c (.const 0)))

/-- Merge two slots of the same type under the condition `c` (`p` when `c ≠ 0`). -/
def mergeSlot (c : Term) (p q : IntType × Term) : Option (IntType × Term) :=
  if p.1 = q.1 then some (p.1, if p.2 = q.2 then p.2 else selT p.2 q.2 c) else none

/-- Merge two slot lists slot by slot. -/
def mergeSlots (c : Term) : List (IntType × Term) → List (IntType × Term) →
    Option (List (IntType × Term))
  | [], [] => some []
  | p :: ps, q :: qs =>
    match mergeSlot c p q, mergeSlots c ps qs with
    | some r, some rs => some (r :: rs)
    | _, _ => none
  | _, _ => none

/-- The integer type of a value type. -/
def intTy? : ValType → Option IntType
  | .num (.int t) => some t
  | _ => none

/-- The integer type of a scalar type. -/
def scalarInt? : ScalarType → Option IntType
  | .num (.int t) => some t
  | _ => none

/-- The result types of a block type `xexec` accepts: no parameters, at most one integer
result. -/
def blockRes? : BlockType → Option (List IntType)
  | .empty => some []
  | .value t => (intTy? t).map ([·])
  | .typeIdx _ => none

/-- The operand types of an accepted `select`: untyped, or annotated with one integer type. -/
def selOk : Option (List ValType) → IntType → Bool
  | none, _ => true
  | some [t'], t => intTy? t' == some t
  | some _, _ => false

/-! ## Symbolic execution of function bodies -/

/-- One instruction, given the executor `rec` for nested bodies: `select`, `block` and `if`
here, everything else by `Silmaril.Wasm.Auto.Equiv.sstep`. -/
def xone (rec : SState → List Instr → Option SState) (S : SState) : Instr → Option SState
  | .select ts =>
    match S.stack with
    | (t₃, c) :: (t₂, b) :: (t₁, a) :: st =>
      if t₃ = .i32 ∧ t₂ = t₁ ∧ selOk ts t₁ = true then
        some ⟨S.locals, (t₁, selT a b c) :: st⟩
      else none
    | _ => none
  | .block bt body =>
    match blockRes? bt, rec ⟨S.locals, []⟩ body with
    | some ts, some A =>
      if A.stack.map (·.1) = ts.reverse then some ⟨A.locals, A.stack ++ S.stack⟩ else none
    | _, _ => none
  | .if_ bt b₁ b₂ =>
    match S.stack, blockRes? bt with
    | (t, c) :: st, some ts =>
      if t = .i32 then
        match rec ⟨S.locals, []⟩ b₁, rec ⟨S.locals, []⟩ b₂ with
        | some A, some B =>
          if A.stack.map (·.1) = ts.reverse ∧ B.stack.map (·.1) = ts.reverse then
            match mergeSlots c A.locals B.locals, mergeSlots c A.stack B.stack with
            | some ls, some rs => some ⟨ls, rs ++ st⟩
            | _, _ => none
          else none
        | _, _ => none
      else none
    | _, _ => none
  | i => sstep S i

/-- **Symbolic execution of a body** with fuel `n` (one unit per instruction, nested bodies
included). -/
def xexec : Nat → SState → List Instr → Option SState
  | 0, _, _ => none
  | _ + 1, S, [] => some S
  | n + 1, S, i :: is =>
    match xone (xexec n) S i with
    | some S' => xexec n S' is
    | none => none

/-! ## Function summaries -/

/-- The initial symbolic state of a function body: parameter `i` is input `i`, declared locals
are `0`; empty stack. -/
def fnInit (ps ls : List IntType) : SState :=
  ⟨ps.mapIdx (fun i t => (t, .var i)) ++ ls.map (fun t => (t, .const 0)), []⟩

/-- The summary of a function export. -/
structure FnSum where
  /-- The parameter types. -/
  params : List IntType
  /-- The result types. -/
  results : List IntType
  /-- The final symbolic state of the body; its stack holds the results, top first. -/
  final : SState
  deriving DecidableEq, Repr

/-- The fuel of `fnSum?` (instructions per body). -/
def fnFuel : Nat := 100000

/-- The summary of a function instance with scalar type `ft`, when its body is accepted. -/
def sumOf {H : Type} (ft : Silmaril.Wasm.Game.FnType) (fi : FuncInst H) : Option FnSum :=
  match fi.code with
  | .wasm code =>
    match ft.params.mapM scalarInt?, ft.results.mapM scalarInt?, code.locals.mapM intTy? with
    | some ps, some rs, some ls =>
      match xexec fnFuel (fnInit ps ls) code.body with
      | some A => if A.stack.map (·.1) = rs.reverse then some ⟨ps, rs, A⟩ else none
      | none => none
    | _, _, _ => none
  | .host _ => none

/-- The summary of function export `j` of a computed instance. -/
def fnSumI (I : ScalarInstance) (j : Nat) : Option FnSum :=
  match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
  | some ft, some fi => sumOf ft fi
  | _, _ => none

/-- **The summary of function export `j` of `m`'s computed instance.** -/
def fnSum? (m : Module) (j : Nat) : Option FnSum :=
  match instance? m with
  | some (_, I) => fnSumI I j
  | none => none

/-- The results of a summary on the arguments `vs` (bottom first). -/
def fnOut (F : FnSum) (vs : List Val) : List Val := (stackAt (envOfVals vs) F.final).reverse

/-- **The function-level check**: same parameter types, equal normal forms of the results. -/
def fnCheck (m₁ m₂ : Module) (j : Nat) : Bool :=
  match fnSum? m₁ j, fnSum? m₂ j with
  | some A, some B => A.params == B.params && slotsEq A.final.stack B.final.stack
  | _, _ => false

/-- The residual goals of the function-level check (`none`: no summary, or different parameter
types or result shapes). -/
def fnResiduals (m₁ m₂ : Module) (j : Nat) : Option (List Goal) :=
  match fnSum? m₁ j, fnSum? m₂ j with
  | some A, some B => if A.params = B.params then slotsGoals A.final.stack B.final.stack else none
  | _, _ => none

/-! ## Bodies, for certificates of other checkers -/

/-- The local types (parameters, then declared locals) and the body of function export `j` of a
computed instance, when all are integer types. -/
def fnBodyI (I : ScalarInstance) (j : Nat) : Option (List IntType × List Instr) :=
  match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
  | some ft, some fi =>
    match fi.code with
    | .wasm code =>
      match ft.params.mapM scalarInt?, code.locals.mapM intTy? with
      | some ps, some ls => some (ps ++ ls, code.body)
      | _, _ => none
    | .host _ => none
  | _, _ => none

/-- `fnBodyI` of `m`'s computed instance. -/
def fnBody? (m : Module) (j : Nat) : Option (List IntType × List Instr) :=
  match instance? m with
  | some (_, I) => fnBodyI I j
  | none => none

/-- An instruction `xexec` runs by `Silmaril.Wasm.Auto.Equiv.sstep` (not `select`, `block`, `if`). -/
def plainI : Instr → Bool
  | .select _ | .block _ _ | .if_ _ _ _ => false
  | _ => true

/-- The side conditions under which an e-graph certificate `SegEquiv Γ a b` on the bodies `a`
and `b` of export `j` proves `ModEquiv` (`Silmaril.Wasm.Auto.Bridge.modEquiv_of_egraph`): both
exports are summarised with the same parameter types, both bodies have local types `Γ` and are
plain, and `Γ` has fewer than `2^32` entries. (Instructions have no decidable equality, so that
the bodies are `a` and `b` is a separate, definitional, hypothesis.) -/
def egraphLiftOk (m₁ m₂ : Module) (j : Nat) (Γ : List IntType) : Bool :=
  match fnSum? m₁ j, fnSum? m₂ j, fnBody? m₁ j, fnBody? m₂ j with
  | some A, some B, some (Γ₁, a), some (Γ₂, b) =>
    A.params == B.params && Γ₁ == Γ && Γ₂ == Γ && a.all plainI && b.all plainI &&
      decide (Γ.length < 2 ^ 32)
  | _, _, _, _ => false

/-! ## Every export at once -/

/-- The function-level check of export `j` on two summaries: same parameter types, and equal
normal forms of the results or residual goals all in the lemma library (`lemmaGoals`, below). -/
def sumCheck (lib : List Goal → Bool) : Option FnSum → Option FnSum → Bool
  | some A, some B =>
    A.params == B.params && (slotsEq A.final.stack B.final.stack ||
      match slotsGoals A.final.stack B.final.stack with
      | some gs => lib gs
      | none => false)
  | _, _ => false

/-- The e-graph side conditions of export `j` on two computed instances (`egraphLiftOk`). -/
def liftCheckI (I₁ I₂ : ScalarInstance) (j : Nat) : Option (List IntType) :=
  match fnSumI I₁ j, fnSumI I₂ j, fnBodyI I₁ j, fnBodyI I₂ j with
  | some A, some B, some (Γ₁, a), some (Γ₂, b) =>
    if A.params == B.params && Γ₁ == Γ₂ && a.all plainI && b.all plainI &&
      decide (Γ₁.length < 2 ^ 32) then some Γ₁ else none
  | _, _, _, _ => none

/-! ## A library of proved residual goals -/

/-- The normal form of the result of the `div10` kernel (multiply-high by
`0xCCCCCCCCCCCCCCCD`, shift by 3), as the checker computes it (the regression test
`tests.wasm.auto.Equiv.Tests` pins the same term). -/
def div10Lhs : Term :=
  .bin (.shr .unsigned) (.bin .add (.bin .mul (.const 3435973836)
    (.bin (.shr .unsigned) (.var 0) (.const 32))) (.bin .add (.bin (.shr .unsigned)
    (.bin .add (.bin .and (.const 4294967295) (.bin .mul (.const 3435973836)
    (.bin .and (.var 0) (.const 4294967295)))) (.bin .add (.bin .and (.const 4294967295)
    (.bin .mul (.const 3435973837) (.bin (.shr .unsigned) (.var 0) (.const 32))))
    (.bin (.shr .unsigned) (.bin .mul (.const 3435973837) (.bin .and (.var 0)
    (.const 4294967295))) (.const 32)))) (.const 32)) (.bin .add (.bin (.shr .unsigned)
    (.bin .mul (.const 3435973836) (.bin .and (.var 0) (.const 4294967295))) (.const 32))
    (.bin (.shr .unsigned) (.bin .mul (.const 3435973837) (.bin (.shr .unsigned) (.var 0)
    (.const 32))) (.const 32))))) (.const 3)

/-- **The lemma library**: residual goals proved once (`lemmaGoals_hold`). A residual goal of
the function-level check that is literally one of these is discharged. -/
def lemmaGoals : List Goal :=
  [(.i64, div10Lhs, .bin (.div .unsigned) (.var 0) (.const 10))]

/-- Every goal is in the lemma library. -/
def discharged (gs : List Goal) : Bool := gs.all fun g => lemmaGoals.contains g

/-- **The function-level stage on every export at once**, each module instantiated once (for
certificates: one kernel evaluation of the decoder and of the instantiation per module).
Entry `j` is `true` when the proving stage proves export `j` equivalent. -/
def checkAll (m₁ m₂ : Module) : List Bool :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) =>
    (List.range I₁.exports.length).map fun j => sumCheck discharged (fnSumI I₁ j) (fnSumI I₂ j)
  | _, _ => []

/-- The e-graph side conditions of every export at once (entry `j`: the common local types). -/
def liftAll (m₁ m₂ : Module) : List (Option (List IntType)) :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) => (List.range I₁.exports.length).map (liftCheckI I₁ I₂)
  | _, _ => []

/-! ## The extended summaries: memory, globals, conversions and trap guards

The second summariser of the front end (`docs/projects/wasm-binaryen-tooling.md`). The
first one (`Silmaril.Wasm.Auto.Bridge`) runs bodies through the straight-line integer executor of
the equivalence checker; this one runs them through the **extended** executor
`Silmaril.Wasm.Auto.Equiv.xsexec`, so that a summary covers

* `i32.wrap_i64`, `i64.extend_i32_s/u`, `select`;
* division and remainder by any divisor (a trap guard unless the divisor is a safe constant);
* `global.get`/`global.set` of the instance's globals (integer globals only), started from
  their values in the instance's store;
* integer loads and stores (full and packed) on memory `0`, started from the instance's memory
  bytes (each access an in-bounds guard).

A summary (`FnSumX`) records the final symbolic state of the body, the initial global values
and the initial memory bytes. `fnOutX F vs` is the **result** of the export on the arguments
`vs`: the stack values if every guard holds, else a trap. The theorems
(`Silmaril.Wasm.Auto.Bridge.Thms`) prove that the behaviour set of every accepted invocation is
exactly `{(fnOutX F vs).toBehaviour}`, at every profile (total correctness: no divergence), and
that `sumCheckX` (equal parameters, globals, memory where it matters, the same guards up to the
simplifier, equal simplified results) proves `ModEquiv`.

`checkAmong m₁ m₂ js` evaluates the check on the exports `js` with each module instantiated
once: certificates of whole optimizer runs split the exports into chunks, one kernel evaluation
per chunk (the `-O3` run's single evaluation of all 60 exports did not fit in 53 GB).

A Silmaril addition.
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals)
open Silmaril.Wasm.Game (ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance?)

/-! ### The instance context of a body -/

/-- The integer type of a value. -/
def valInt? : Val → Option IntType
  | .num ⟨.int t, _⟩ => some t
  | _ => none

/-- The globals of a module instance in a store: their addresses, values and integer types,
when the addresses are distinct, present, and every global holds an integer. -/
def globsOf {H : Type} (s : Store H) (mi : ModuleInst) : Option (List Nat × List Val × List IntType) :=
  match mi.globals.mapM (fun a => s.globals[a]?.map (·.value)) with
  | some gv =>
    match gv.mapM valInt? with
    | some gt => if mi.globals.Nodup then some (mi.globals, gv, gt) else none
    | none => none
  | none => none

/-- The globals a summary uses: those of `globsOf`, or none (then `global.get`/`global.set`
are not summarised). -/
def globsUsed {H : Type} (s : Store H) (mi : ModuleInst) : List Nat × List Val × List IntType :=
  (globsOf s mi).getD ([], [], [])

/-- Memory `0` of a module instance in a store, with its address. -/
def memOf {H : Type} (s : Store H) (mi : ModuleInst) : Option (Nat × MemInst) :=
  s.mem? { module := mi } ⟨0⟩

/-- The initial memory bytes of a summary (empty without memory `0`). -/
def bytesOf : Option (Nat × MemInst) → ByteArray
  | some (_, m) => m.bytes
  | none => ByteArray.empty

/-- The initial symbolic state of a body: parameter `i` is input `i`, declared locals are `0`,
global `k` is input `p + k` (`p` parameters); the initial memory; no guards. -/
def fnInitX (ps ls gt : List IntType) : XState where
  locals := ps.mapIdx (fun i t => (t, .var i)) ++ ls.map (fun t => (t, .const 0))
  stack := []
  globs := gt.mapIdx fun k t => (t, .var (ps.length + k))
  mem := .minit
  guards := []

/-! ### Summaries -/

/-- The summary of a function export, with memory, globals and traps. -/
structure FnSumX where
  /-- The parameter types. -/
  params : List IntType
  /-- The result types. -/
  results : List IntType
  /-- The initial values of the globals (inputs `p, p + 1, …`). -/
  gvals : List Val
  /-- The initial bytes of memory `0` (empty without memory). -/
  bytes : ByteArray
  /-- The final symbolic state of the body; its stack holds the results, top first. -/
  final : XState

/-- The summary of a function instance with scalar type `ft` in the store `s`. -/
def sumOfX {H : Type} (s : Store H) (ft : FnType) (fi : FuncInst H) : Option FnSumX :=
  match fi.code with
  | .wasm code =>
    match ft.params.mapM scalarInt?, ft.results.mapM scalarInt?, code.locals.mapM intTy? with
    | some ps, some rs, some ls =>
      let g := globsUsed s fi.module
      let mo := memOf s fi.module
      match xsexec mo.isSome (fnInitX ps ls g.2.2) code.body with
      | some A =>
        if A.stack.map (·.1) = rs.reverse then some ⟨ps, rs, g.2.1, bytesOf mo, A⟩ else none
      | none => none
    | _, _, _ => none
  | .host _ => none

/-- The summary of function export `j` of a computed instance. -/
def fnSumXI (I : ScalarInstance) (j : Nat) : Option FnSumX :=
  match I.exports[j]?, I.store.funcs[I.addrs.getD j 0]? with
  | some ft, some fi => sumOfX I.store ft fi
  | _, _ => none

/-- **The summary of function export `j` of `m`'s computed instance.** -/
def fnSumX? (m : Module) (j : Nat) : Option FnSumX :=
  match instance? m with
  | some (_, I) => fnSumXI I j
  | none => none

/-- The environment of a summary on the arguments `vs`: the arguments, then the globals. -/
def envX (F : FnSumX) (vs : List Val) : Env := envOfVals (vs ++ F.gvals)

/-- Every guard holds. -/
def guardsOk (ρ : Env) (B0 : ByteArray) (G : List (Guard × XState)) : Bool :=
  G.all fun g => g.1.holds ρ B0

/-- The result of a final state in an environment, from the initial bytes `B0`. -/
def outAt (ρ : Env) (B0 : ByteArray) (S : XState) : Result :=
  if guardsOk ρ B0 S.guards then .values (S.stack.map (denX ρ B0)).reverse else .trap

/-- **The result of a summarised export** on the arguments `vs`. -/
def fnOutX (F : FnSumX) (vs : List Val) : Result := outAt (envX F vs) F.bytes F.final

/-! ### The check -/

/-- A value term reads no memory. -/
def noLoad : XT → Bool
  | .var _ | .const _ | .minit => true
  | .un _ a | .wrap a | .ext _ a => noLoad a
  | .bin _ a b | .rel _ _ a b => noLoad a && noLoad b
  | .sel c a b => noLoad c && noLoad a && noLoad b
  | .load .. => false
  | .mstore .. => true

/-- The result of a final state may depend on the initial memory: it has guards, or a result
reads memory. -/
def usesMem (S : XState) : Bool := !S.guards.isEmpty || !S.stack.all (noLoad ·.2)

/-- Every guard of `G`, simplified, is among the simplified guards of `G'`. -/
def guardSub (G G' : List (Guard × XState)) : Bool :=
  G.all fun g => (G'.map (·.1.canon)).contains g.1.canon

/-- **The check of two summaries**: the same parameter types and global values, the same initial
memory when either result may depend on it, the same guards up to the simplifier (as sets), and
equal simplified results. -/
def sumCheckX : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      (!(usesMem A.final || usesMem B.final) || decide (A.bytes = B.bytes)) &&
      guardSub A.final.guards B.final.guards && guardSub B.final.guards A.final.guards &&
      decide (canonSlots A.final.stack = canonSlots B.final.stack)
  | _, _ => false

/-- The check at export `j` of two modules. -/
def fnCheckX (m₁ m₂ : Module) (j : Nat) : Bool := sumCheckX (fnSumX? m₁ j) (fnSumX? m₂ j)

/-- **The check on the exports `js`**, each module instantiated once (entry `i` for export
`js[i]`). Both function-level stages: the first summariser's (`Silmaril.Wasm.Auto.Bridge.sumCheck`,
residual goals in the lemma library) or this one's. -/
def checkAmong (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) =>
    js.map fun j =>
      Bridge.sumCheck Bridge.discharged (Bridge.fnSumI I₁ j) (Bridge.fnSumI I₂ j) ||
        sumCheckX (fnSumXI I₁ j) (fnSumXI I₂ j)
  | _, _ => []

/-- The e-graph side conditions (`Silmaril.Wasm.Auto.Bridge.egraphLiftOk`) on the exports `js`,
each module instantiated once (entry `i`: the common local types of export `js[i]`). -/
def liftAmong (m₁ m₂ : Module) (js : List Nat) : List (Option (List IntType)) :=
  match instance? m₁, instance? m₂ with
  | some (_, I₁), some (_, I₂) => js.map (Bridge.liftCheckI I₁ I₂)
  | _, _ => []

end

/-! ## Summaries with locals: the e-graph certificates of `Silmaril.Wasm.Auto.ESeg`

`egraphFuncOk m₁ m₂ j Γ da db`: the side conditions under which a function-entry certificate
`Silmaril.Wasm.Auto.ESeg.FuncEquiv Γ da db a b` on the bodies `a`, `b` of export `j` proves
`Silmaril.Wasm.Auto.Front.ModEquiv` (`Silmaril.Wasm.Auto.Bridge.modEquiv_of_funcEquiv`): both exports
are summarised (`Silmaril.Wasm.Auto.Bridge.fnSum?`) with parameter types `Γ`, their bodies have
declared locals `da` and `db` and are plain (`Bridge.plainI`), and both frames have fewer than
`2^32` locals. This is the stage of `wasm-check pass --egraph-tv-seg` (certificates of
`wasm-egraph tv-seg --func`).
-/

section
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto.Bridge

/-- The side conditions of `modEquiv_of_funcEquiv`. -/
def egraphFuncOk (m₁ m₂ : Module) (j : Nat) (Γ da db : List IntType) : Bool :=
  match fnSum? m₁ j, fnSum? m₂ j, fnBody? m₁ j, fnBody? m₂ j with
  | some A, some B, some (Γ₁, a), some (Γ₂, b) =>
    A.params == Γ && B.params == Γ && Γ₁ == Γ ++ da && Γ₂ == Γ ++ db && a.all plainI &&
      b.all plainI && decide ((Γ ++ da).length < 2 ^ 32) && decide ((Γ ++ db).length < 2 ^ 32)
  | _, _, _, _ => false

/-- The parameters and declared locals of export `j` of both modules, when `egraphFuncOk` holds
for them (what `wasm-check pass --egraph-tv-seg` checks before writing a theorem). -/
def funcLift? (m₁ m₂ : Module) (j : Nat) : Option (List IntType × List IntType × List IntType) :=
  match fnSum? m₁ j, fnBody? m₁ j, fnBody? m₂ j with
  | some A, some (Γ₁, _), some (Γ₂, _) =>
    let da := Γ₁.drop A.params.length
    let db := Γ₂.drop A.params.length
    if egraphFuncOk m₁ m₂ j A.params da db then some (A.params, da, db) else none
  | _, _, _ => none

end

/-! ## Notions of the soundness statements -/

section
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `R` up to divergence (the partial-correctness reading of a relation). -/
def OrDiv (R : Behaviour Val → Behaviour Val → Prop) : Behaviour Val → Behaviour Val → Prop :=
  fun b b' => b = .diverges ∨ R b b'

/-- The outcome of a result that returns or traps. -/
def resOutcome : Result → Outcome
  | .values vs => .normal vs
  | .trap => .trap
  | .throw a => .throw a

variable {H : Type}

/-- The induction hypothesis for nested bodies. -/
def BodyOk (P : Profile) (host : HostSemantics H) (ρ : Env)
    (rec : SState → List Instr → Option SState) : Prop :=
  ∀ {S S' : SState} {a : List Instr}, rec S a = some S' →
    ∀ (s : Store H) (f : Frame) (us : List Val) (rest : List Admin) (Q : Post H),
      TWP P host s (frameAt f ρ S') (vals (us ++ (stackAt ρ S').reverse) ++ rest) Q →
      TWP P host s (frameAt f ρ S) (codeAt ρ S us a rest) Q

/-- The total specification of a summarised function: from the store `s₀`, on typed arguments,
it returns `fnOut F args`. -/
def sumSpec (F : FnSum) (s₀ : Store H) : FSpec H where
  pre s args := s = s₀ ∧ TypedVals F.params args
  post _ args _ o := o = .normal (fnOut F args)

/-- What `globsUsed` gives. -/
structure GlobsOk (s : Store H) (mi : ModuleInst) (ga : List Nat) (gv : List Val)
    (gt : List IntType) : Prop where
  nodup : ga.Nodup
  addr : ∀ (k : Nat) (hk : k < ga.length), mi.globals[k]? = some ga[k] ∧ ga[k] < s.globals.length
  vals : ga.mapM (fun a => s.globals[a]?.map (·.value)) = some gv
  typed : TypedVals gt gv

/-- The context of a call of a summarised function: the store, the call frame, the environment
of the arguments and globals, the globals and memory `0`. -/
def ctxOf (s : Store H) (mi : ModuleInst) (args : List Val) (lts : List ValType) (ρ : Env) :
    XCtx H where
  s := s
  f := Frame.forCall mi args lts
  ρ := ρ
  ga := (globsUsed s mi).1
  ma := ((memOf s mi).getD (0, noMem)).1
  mi := ((memOf s mi).getD (0, noMem)).2

/-- The total specification of a summarised function: from the store `s₀`, on typed arguments,
its outcome is that of `fnOutX F args`. -/
def sumSpecX (F : FnSumX) (s₀ : Store H) : FSpec H where
  pre s args := s = s₀ ∧ TypedVals F.params args
  post _ args _ o := o = resOutcome (fnOutX F args)

end

end Silmaril.Wasm.Auto.Bridge
