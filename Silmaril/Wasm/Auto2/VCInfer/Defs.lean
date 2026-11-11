module

public import Silmaril.Wasm.Auto2.VCEquiv.Thms
public import Silmaril.Wasm.Auto2.VCLib.Thms

/-!
# Inferred contracts for `vcequiv` (round 2, summaries, pass 3)

Stage `vcequiv` (`Silmaril.Wasm.Auto2.VCEquiv`) proves two exports equivalent when each passes a
proved contract of one functional contract `EqFun`. Its library holds one hand-written contract
(invariant, variant, proved conditions) per program shape. This module removes the need for a
library entry per shape:

* `InferFun`: a functional contract `F`, a **base contract** `base ∈ F.es`, and **invariant
  templates** for a function with one loop. A template takes two local indices `n` and `a` and
  gives an invariant and a variant, e.g. `a + f n = f n₀` and `n` for `sum`;
* `InferFun.specOf c`: the base specification with the invariant and variant of candidate `c`
  (`none`: no loop annotations). Only `inv` and `var` change, so the parameters, results,
  precondition and postcondition, and with them the reference function, are the base's;
* `inferEntry I c code h`: the contract of `code` for candidate `c`, whose conditions are
  `genFunc (I.specOf c) code fuel` and whose validity `h` is a proof given by the caller. In a
  `wasm-check` certificate that proof is `vcgen4` followed by the fixed tactic of `I`
  (`InferFun.tactic`), the same for every program;
* **the search** (untrusted, used only to pick a candidate): `cands` lists the candidates for a
  code (templates over every pair of `i32` locals, with and without `n ≠ 0`); `refutes` tests
  the conditions of a candidate on sampled environments; `infer?` returns the first candidate no
  sample refutes. Sampling solves equations of the path condition for one unknown variable
  (`a = e`, `a + e = e'`, `a - e = e'`), oldest fact first, so that the loop invariant hypothesis
  and the SSA definitions are met; a sample whose path condition is false says nothing. A rejected candidate
  has a real counterexample (if the evaluator `Fm.evalB` agrees with `Fm.den`, which is not
  proved and need not be: the certificate's proof is what counts);
* `inferFuns`: the library of `InferFun`s (`sum` with the accumulator template; `max`, `add`,
  `div10` without loops).

Soundness (`Silmaril.Wasm.Auto2.VCInfer.Thms`): `modEquiv_of_infer`: two contracts derived from
one `InferFun` (library entries of its `F`, or inferred entries) that check the two exports
(`vcEquivWith`) prove `ModEquiv` at every profile, for every reflexive relation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInfer

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.VCGen
open Silmaril.Wasm.Auto2.VCBridge
open Silmaril.Wasm.Auto2.VCEquiv

/-! ## Inferred contracts -/

/-- A candidate annotation for a function with one loop: template `t`, local indices `n` and `a`,
and whether the invariant also says `n ≠ 0`. -/
structure Cand where
  t : Nat
  n : Nat
  a : Nat
  guard : Bool
  deriving DecidableEq, Repr

/-- **A functional contract with invariant templates.** -/
structure InferFun where
  /-- The functional contract. -/
  F : EqFun
  /-- The base contract, one of `F`'s. -/
  base : VcEntry
  mem : base ∈ F.es
  /-- Invariant templates for one loop: local indices `n`, `a` to an invariant and a variant. -/
  loopT : List (Nat → Nat → Fm × Tm .i32) := []
  /-- The Lean name of this `InferFun` (for certificates). -/
  leanName : String
  /-- The Lean term of `base.F` (for certificates). -/
  fnsName : String
  /-- The fixed tactic that closes the conditions after `vcgen4` (for certificates). -/
  tactic : String

/-- The annotations of a candidate (`none`: none). -/
def InferFun.annot (I : InferFun) : Option Cand → List Fm × List (Tm .i32)
  | none => ([], [])
  | some c =>
    match I.loopT[c.t]? with
    | some T =>
      let (inv, var) := T c.n c.a
      ([if c.guard then .and inv (.nz (.loc .i32 c.n)) else inv], [var])
    | none => ([], [])

/-- **The specification of a candidate**: the base's, with the candidate's annotations. -/
def InferFun.specOf (I : InferFun) (c : Option Cand) : FnSpec :=
  { I.base.S with inv := (I.annot c).1, var := (I.annot c).2 }

/-- **The contract of `code` for candidate `c`**, from a proof of its conditions. -/
def inferEntry (I : InferFun) (c : Option Cand) (code : Func)
    (h : AllValid I.base.F (genFunc (I.specOf c) code I.base.fuel)) : VcEntry where
  name := I.base.name ++ "-inferred"
  F := I.base.F
  S := I.specOf c
  fuel := I.base.fuel
  conds := genFunc (I.specOf c) code I.base.fuel
  valid := h
  total := I.base.total
  calls := I.base.calls
  mem := I.base.mem
  globals := I.base.globals

/-- Entry `i` of `F`'s contracts (the base if there is none). -/
def libEntry (I : InferFun) (i : Nat) : VcEntry := I.F.es.getD i I.base

/-- A contract **derived** from `I`: one of `F`'s, or one with the base's functions and
interface (parameters, results, pre- and postcondition). -/
def InferFun.Derives (I : InferFun) (e : VcEntry) : Prop :=
  e ∈ I.F.es ∨
    (e.F = I.base.F ∧ e.S.params = I.base.S.params ∧ e.S.results = I.base.S.results ∧
      e.S.pre = I.base.S.pre ∧ e.S.post = I.base.S.post)

/-! ## The search (untrusted) -/

/-- A pseudo-random value for variable `k` in sample `seed`: small values, `0`, `1`, `2`,
`2 ^ w - 1`, or a large one. -/
def rnd (w seed k : Nat) : Nat :=
  let h := (seed * 2654435761 + k * 2246822519 + 3266489917) % 4294967311
  let h2 := (h * 668265263 + seed + 374761393) % 4294967291
  match h % 8 with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => h2 % 16
  | 4 => 2 ^ w - 1
  | 5 => h2 % 1000
  | _ => (h2 * 4294967311 + h) % 2 ^ w

/-- An assignment: values set by the sampler (newest first), others pseudo-random. -/
structure Asg where
  seed : Nat
  set : List (IntType × Nat × Nat) := []

/-- The environment of an assignment (memories empty). -/
def Asg.env (A : Asg) : Env where
  e32 k := match A.set.find? (fun p => p.1 == .i32 && p.2.1 == k) with
    | some p => BitVec.ofNat 32 p.2.2
    | none => BitVec.ofNat 32 (rnd 32 A.seed (2 * k))
  e64 k := match A.set.find? (fun p => p.1 == .i64 && p.2.1 == k) with
    | some p => BitVec.ofNat 64 p.2.2
    | none => BitVec.ofNat 64 (rnd 64 A.seed (2 * k + 1))
  mem _ := ByteArray.empty

/-- The variables of a term (no memory: `none` for loads and memory functions). -/
def tmVars? : {t : IntType} → Tm t → Option (List (IntType × Nat))
  | t, .var _ i => some [(t, i)]
  | t, .loc _ j => some [(t, j)]
  | _, .lit .. => some []
  | _, .un _ a => tmVars? a
  | _, .bin _ a b => do return (← tmVars? a) ++ (← tmVars? b)
  | _, .rel _ a b => do return (← tmVars? a) ++ (← tmVars? b)
  | _, .eqz a => tmVars? a
  | _, .ite c a b => do return (← tmVars? c) ++ (← tmVars? a) ++ (← tmVars? b)
  | _, .wrap a => tmVars? a
  | _, .ext _ a => tmVars? a
  | _, .fn _ a => tmVars? a
  | _, .fn2 _ a b => do return (← tmVars? a) ++ (← tmVars? b)
  | _, .load .. => none
  | _, .mfn .. => none

/-- The number of occurrences of `v` among `l`. -/
def occ (v : IntType × Nat) (l : List (IntType × Nat)) : Nat := (l.filter (· == v)).length

/-- Solve `a = x` for one variable of `a` that occurs once in the whole equation (`all`) and is
not yet fixed: through `+` and `-` only. Returns the variable and its value. -/
def solve (F : Fns) (ρ : Env) (fixed all : List (IntType × Nat)) :
    {t : IntType} → Tm t → BitVec t.width → Option (IntType × Nat × Nat)
  | t, .var _ i, x => if (t, i) ∉ fixed ∧ occ (t, i) all = 1 then some (t, i, x.toNat) else none
  | t, .loc _ i, x => if (t, i) ∉ fixed ∧ occ (t, i) all = 1 then some (t, i, x.toNat) else none
  | _, .bin .add a b, x =>
    (solve F ρ fixed all a (x - Tm.den F ρ ρ b)).or (solve F ρ fixed all b (x - Tm.den F ρ ρ a))
  | _, .bin .sub a b, x =>
    (solve F ρ fixed all a (x + Tm.den F ρ ρ b)).or (solve F ρ fixed all b (Tm.den F ρ ρ a - x))
  | _, _, _ => none

/-- A comparison as a `Bool`. -/
def relBT : (t : IntType) → IntRelOp → BitVec t.width → BitVec t.width → Bool
  | .i32 => Silmaril.Wasm.Auto.VCGen.relB 32
  | .i64 => Silmaril.Wasm.Auto.VCGen.relB 64

/-- **The value of a formula** in one environment (`none`: memory, user predicates). -/
def fmEvalB (F : Fns) (ρ : Env) : Fm → Option Bool
  | .tt => some true
  | .ff => some false
  | .rel (t := t) op a b => some (relBT t op (Tm.den F ρ ρ a) (Tm.den F ρ ρ b))
  | .nz a => some (Silmaril.Wasm.Auto.VCGen.nz32 (Tm.den F ρ ρ a))
  | .not p => (fmEvalB F ρ p).map (!·)
  | .and p q => do return (← fmEvalB F ρ p) && (← fmEvalB F ρ q)
  | .or p q => do return (← fmEvalB F ρ p) || (← fmEvalB F ρ q)
  | .imp p q => do return !(← fmEvalB F ρ p) || (← fmEvalB F ρ q)
  | _ => none

/-- The conjuncts of a formula. -/
def fmConj : Fm → List Fm
  | .and p q => fmConj p ++ fmConj q
  | .tt => []
  | p => [p]

/-- The variables of a formula (`none` for memory). -/
def fmVars? : Fm → Option (List (IntType × Nat))
  | .tt | .ff => some []
  | .rel _ a b => do return (← tmVars? a) ++ (← tmVars? b)
  | .nz a => tmVars? a
  | .not p => fmVars? p
  | .and p q | .or p q | .imp p q => do return (← fmVars? p) ++ (← fmVars? q)
  | _ => none

/-- Process the conjuncts of a path condition, oldest first (the generator adds facts at the
front): an equation fixes one unknown variable to the value that makes it hold. -/
def sampleFrom (F : Fns) : Asg → List (IntType × Nat) → List Fm → Asg
  | A, _, [] => A
  | A, fixed, φ :: r =>
    let vs := (fmVars? φ).getD []
    let A' := match φ with
      | .rel .eq a b =>
        let ρ := A.env
        match (solve F ρ fixed vs a (Tm.den F ρ ρ b)).or (solve F ρ fixed vs b (Tm.den F ρ ρ a)) with
        | some (t', k, x) => { A with set := (t', k, x) :: A.set }
        | none => A
      | _ => A
    sampleFrom F A' (vs ++ fixed) r

/-- A sample refutes a condition: its path condition holds and the condition does not. -/
def refutedAt (F : Fns) (seed : Nat) (φ : Fm) : Bool :=
  match φ with
  | .imp pc ψ =>
    let A := sampleFrom F { seed } [] (fmConj pc).reverse
    fmEvalB F A.env pc == some true && fmEvalB F A.env ψ == some false
  | ψ => fmEvalB F ({ seed } : Asg).env ψ == some false

/-- Some sample (of `samples`) refutes some condition (`.ff` always does). -/
def refutes (F : Fns) (samples : Nat) (l : List Fm) : Bool :=
  l.any fun φ => φ == .ff || (List.range samples).any fun s => refutedAt F s φ

/-- The `i32` locals of a function (parameters and declared locals) of types `ps ++ ls`. -/
def i32Locals (ps : List IntType) (code : Func) : List Nat :=
  let ls := (Silmaril.Wasm.Auto.VCGen.intTys? code.locals).getD []
  ((ps ++ ls).zipIdx).filterMap fun (t, i) => if t == .i32 then some i else none

/-- **The candidates for `code`**: no annotations (no loop), or, for one loop, every template
over every pair of distinct `i32` locals, without and then with the guard `n ≠ 0`. -/
def cands (I : InferFun) (code : Func) : List (Option Cand) :=
  match nloops 1000 code.body with
  | 0 => [none]
  | 1 =>
    let ls := i32Locals I.base.S.params code
    (List.range I.loopT.length).flatMap fun t =>
      [false, true].flatMap fun g =>
        ls.flatMap fun n => (ls.filter (· ≠ n)).map fun a => some ⟨t, n, a, g⟩
  | _ => []

/-- The number of samples per condition. -/
def nSamples : Nat := 64

/-- **The first candidate that no sample refutes** for export `j` of `m` (the types must be the
base's). -/
def infer? (I : InferFun) (m : Module) (j : Nat) : Option (Option Cand × Func) :=
  match fnCode? m j with
  | some (ft, code) =>
    if ft.params.mapM Silmaril.Wasm.Auto.Bridge.scalarInt? = some I.base.S.params ∧
        ft.results.mapM Silmaril.Wasm.Auto.Bridge.scalarInt? = some I.base.S.results then
      ((cands I code).find? fun c =>
        !refutes I.base.F nSamples (genFunc (I.specOf c) code I.base.fuel)).map (·, code)
    else none
  | none => none

/-- How export `j` of `m` meets `I`: a library contract (its index in `F.es`), or an inferred
candidate. -/
inductive Side where
  | lib (i : Nat)
  | inferred (c : Option Cand) (code : Func)

/-- Find a side for export `j` of `m`: a library contract that checks it, else an inferred one. -/
def side? (I : InferFun) (m : Module) (j : Nat) : Option Side :=
  match (List.range I.F.es.length).find? fun i => vcCheck (libEntry I i) m j with
  | some i => some (.lib i)
  | none => (infer? I m j).map fun (c, code) => .inferred c code

/-- The parameters of a side's contract are the base's: `vcEquivWith` needs equal parameters,
which the library entries of one `F` need not have. -/
def sideParams (I : InferFun) : Side → List IntType
  | .lib i => (libEntry I i).S.params
  | .inferred .. => I.base.S.params

/-- **Stage `vcinfer`** (search only): some `InferFun` with a side for both exports, with
the same parameter types, and not both library contracts (stage `vcequiv` covers those). -/
def inferPair? (L : List InferFun) (m₁ m₂ : Module) (j : Nat) :
    Option (InferFun × Side × Side) :=
  L.findSome? fun I =>
    match side? I m₁ j, side? I m₂ j with
    | some (.lib _), some (.lib _) => none
    | some s₁, some s₂ => if sideParams I s₁ == sideParams I s₂ then some (I, s₁, s₂) else none
    | _, _ => none

/-! ## The library -/

open Silmaril.Wasm.Auto2.VCLib in
/-- The accumulator template of `sum`: `a + triBV n = triBV n₀`, variant `n`. -/
def sumT (n a : Nat) : Fm × Tm .i32 :=
  (.rel .eq (.bin .add (L32 a) (.fn 0 (L32 n))) (.fn 0 (P32 0)), L32 n)

open Silmaril.Wasm.Auto2.VCLib in
/-- The counting-up template of `sum`: `a = triBV i ∧ i ≤ n₀` (unsigned), variant `n₀ - i`. -/
def upT (i a : Nat) : Fm × Tm .i32 :=
  (.and (.rel .eq (L32 a) (.fn 0 (L32 i))) (.rel (.le .unsigned) (L32 i) (P32 0)),
    .bin .sub (P32 0) (L32 i))

open Silmaril.Wasm.Auto2.VCLib in
/-- `sum`, with the accumulator and counting-up templates. -/
def sumI : InferFun where
  F := sumFun
  base := sumEntry
  mem := List.mem_cons_self
  loopT := [sumT, upT]
  leanName := "Silmaril.Wasm.Auto2.VCInfer.sumI"
  fnsName := "Silmaril.Wasm.Auto2.VCLib.sumFns"
  tactic := "vc_tri"

open Silmaril.Wasm.Auto2.VCLib in
/-- `max` (no loop). -/
def maxI : InferFun where
  F := maxFun
  base := maxEntry
  mem := List.mem_cons_self
  leanName := "Silmaril.Wasm.Auto2.VCInfer.maxI"
  fnsName := "{}"
  tactic := "vc_simp"

open Silmaril.Wasm.Auto2.VCLib in
/-- `add` (no loop). -/
def addI : InferFun where
  F := addFun
  base := addEntry
  mem := List.mem_cons_self
  leanName := "Silmaril.Wasm.Auto2.VCInfer.addI"
  fnsName := "{}"
  tactic := "vc_simp"

/-- **The library of `InferFun`s** (`wasm-check`'s stage `vcinfer`). -/
def inferFuns : List InferFun := [sumI, maxI, addI]

end Silmaril.Wasm.Auto2.VCInfer
