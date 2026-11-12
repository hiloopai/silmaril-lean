module

public import Silmaril.Wasm.SpecTec.Sim.Round7.VDecl.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.MemSimd.Thms

/-!
# Round 7, memory SIMD: `OpenRMRest.rest` off memory SIMD code, and a concrete step invariant

`Round7.VDecl` reduced `OpenRMRest.rest` (stated at `BM = withVBytes BI`) to the same obligation
at round 6's builtins `BI` (`VDecl.backwardUpToDRestS_withVBytes_iff`), and moved the whole step
across `withVBytes` under a hypothetical value invariant (`VDecl.StepInv`). The definitions below
are what this topic adds.

* `NoMSDom P host c`: `NoCastVM c`, no memory SIMD instruction in `c` (code and store, at any
  depth: `Round6.MemSimd.NoMemSimd`), and none in any Core successor of `c`. On this domain
  `configVD` is `configV`, so round 6's per-rule leaves apply.
* `RestMS hn P host`: the part of `OpenRMRest.rest` that round 6's leaves do not reach, at `BI`:
  the per-rule obligations at the `NoCastVM` configurations outside `NoMSDom`.
* `OpenRMRestMS`: `MemSimd.OpenRMRest` with `rest` replaced by `RestMS`.
* `NoAtoms A v`: no `case` of an atom of `A` occurs in `v`, at any depth. `msAtoms` lists the atoms
  of the four memory SIMD instructions at `instrToVM` (`VLOAD`, `VLOAD_LANE`, `VSTORE`,
  `VSTORE_LANE`). `LhsNoAtoms A v`: `v` is a pair whose left-hand side is `NoAtoms A`.
* `LFrag e`, `lvars e`: the expression fragment the left-hand sides of `Step` rules 1–5 are
  written in (variables, tuples, lists, `case`s of atoms outside `A`, concatenations, subtype
  injections and single-domain list iterations of a variable), and its variables.
* `ctxLhsOk A rules`: the kernel fact behind the concrete invariant: in `Step` rules 1–5 the
  conclusion's left-hand side and every `Step`/`Step_read` premise's left-hand side are in the
  fragment, and the premise's variables are among the conclusion's.
* `StepInvB Q`: `VDecl.StepInv` for the backend reading `DDerivesB` (rules 43 and 23 silent under
  `RuleBodyB`, the context rules read through `conclAlts`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.VInv

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Round7.MemSimd (NoCastVM BackwardUpToDRestS)

variable {H : Type}

/-! ## The memory-SIMD-free part of `rest` -/

/-- **The memory-SIMD-free domain**: `NoCastVM c`, no memory SIMD instruction in `c` (code and
store), and none in any Core successor. -/
def NoMSDom (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  NoCastVM c ∧ Round6.MemSimd.NoMemSimd c ∧ ∀ c₁, Step P host c c₁ → Round6.MemSimd.NoMemSimd c₁

/-- **What is left of `OpenRMRest.rest`**, at round 6's builtins: the per-rule obligations at the
`NoCastVM` configurations outside `NoMSDom`, those where memory SIMD code occurs in the
configuration or in a Core successor. -/
def RestMS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  BackwardUpToDRestS (fun c => NoCastVM c ∧ ¬ NoMSDom P host c) (simEnv (Prims.builtins P hn host))
    hn P host

/-- **`OpenRMRest` with `rest` cut down to `RestMS`**: the forward half and the cast leaf as in
`OpenRMRest`, and the per-rule backward obligations only where memory SIMD code occurs. -/
structure OpenRMRestMS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `OpenRMRest.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts →
    Round7.MemSimd.BoundedSelM c → (∀ c₁, Step P host c c₁ → Round7.MemSimd.BoundedSelM c₁) →
    ¬ Round6.Target.CastRedex c.code → Step P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (Round7.MemSimd.BM P hn host))
        (Round7.MemSimd.configVD hn c) (Round7.MemSimd.configVD hn d')
  /-- What is left of `OpenRMRest.rest`. -/
  restMS : RestMS hn P host
  /-- As `OpenRMRest.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts →
    Round7.MemSimd.BoundedSelM c → (∀ c₁, Step P host c c₁ → Round7.MemSimd.BoundedSelM c₁) →
    Round6.Target.CastRedex c.code → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.MemSimd.BM P hn host) (Round7.MemSimd.configVD hn c)
        (Round7.MemSimd.configVD hn d')
  /-- As `OpenRMRest.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value),
    ConfigOk c ts → Round7.MemSimd.BoundedSelM c → Round6.Target.CastRedex c.code →
    Round6.Int.backend.step (Round7.MemSimd.BM P hn host) (Round7.MemSimd.configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = Round7.MemSimd.configVD hn d' ∧ Step P host c c'

/-! ## Values without given atoms -/

mutual
/-- **No `case` of an atom of `A` occurs in `v`**, at any depth. -/
def NoAtoms (A : List MixopS) : Value → Prop
  | .bool _ => True
  | .num _ => True
  | .text _ => True
  | .tuple vs => NoAtomsL A vs
  | .case a w => a ∉ A ∧ NoAtoms A w
  | .struct gs => NoAtomsF A gs
  | .list vs => NoAtomsL A vs
  | .opt none => True
  | .opt (some w) => NoAtoms A w

/-- `NoAtoms` on a list of values. -/
def NoAtomsL (A : List MixopS) : List Value → Prop
  | [] => True
  | v :: vs => NoAtoms A v ∧ NoAtomsL A vs

/-- `NoAtoms` on the fields of a record. -/
def NoAtomsF (A : List MixopS) : List (AtomS × Value) → Prop
  | [] => True
  | (_, v) :: gs => NoAtoms A v ∧ NoAtomsF A gs
end

/-- The atoms of the four memory SIMD instructions at `Round6.MemSimd.instrToVM`. -/
def msAtoms : List MixopS := ["VLOAD", "VLOAD_LANE", "VSTORE", "VSTORE_LANE"]

/-- `v` is a pair whose left-hand side has no `case` of an atom of `A`. -/
def LhsNoAtoms (A : List MixopS) (v : Value) : Prop :=
  ∃ l r, v = .tuple [l, r] ∧ NoAtoms A l

/-! ## The left-hand-side fragment of the context rules -/

/-- A single-domain list iteration of a variable, `x*` over the domain `xs`, possibly through a
subtype injection: the variable `xs` it reads. The bound variable is not `_`, which
`VarEnv.bindVals` does not bind. -/
def iterVar : Exp → IterExp → Option IL.Id
  | .varE x, .mk .list [.mk y (.varE xs)] => if x = y ∧ x ≠ "_" then some xs else none
  | .subE (.varE x) _ _, .mk .list [.mk y (.varE xs)] =>
      if x = y ∧ x ≠ "_" then some xs else none
  | _, _ => none

mutual
/-- **The fragment of the context rules' left-hand sides**: variables, tuples and lists of
fragment expressions, `case`s of atoms outside `A`, concatenations, subtype injections and
`iterVar` iterations. -/
def LFrag (A : List MixopS) : Exp → Bool
  | .varE _ => true
  | .tupE es => LFragL A es
  | .listE es => LFragL A es
  | .caseE a e => !A.contains a && LFrag A e
  | .catE e₁ e₂ => LFrag A e₁ && LFrag A e₂
  | .subE e _ _ => LFrag A e
  | .iterE e it => (iterVar e it).isSome
  | _ => false

/-- `LFrag` on a list. -/
def LFragL (A : List MixopS) : List Exp → Bool
  | [] => true
  | e :: es => LFrag A e && LFragL A es
end

mutual
/-- The variables a fragment expression reads (an iteration reads its domain variable). -/
def lvars : Exp → List IL.Id
  | .varE x => [x]
  | .tupE es => lvarsL es
  | .listE es => lvarsL es
  | .caseE _ e => lvars e
  | .catE e₁ e₂ => lvars e₁ ++ lvars e₂
  | .subE e _ _ => lvars e
  | .iterE e it => (iterVar e it).toList
  | _ => []

/-- `lvars` on a list. -/
def lvarsL : List Exp → List IL.Id
  | [] => []
  | e :: es => lvars e ++ lvarsL es
end

/-- The left-hand side `l` of a pair expression `(l, r)`. -/
def lhsExp : Exp → Option Exp
  | .tupE [l, _] => some l
  | _ => none

/-- A premise of a context rule against the conclusion's left-hand side `l`: a `Step`/`Step_read`
premise has a fragment left-hand side whose variables are among `l`'s; any other premise passes. -/
def ctxPremLhsOk (A : List MixopS) (l : Exp) : Prem → Bool
  | .rulePr y _ _ e =>
      !(y == "Step" || y == "Step_read") ||
        match lhsExp e with
        | some l' => LFrag A l' && (lvars l').all fun x => (lvars l).contains x
        | none => false
  | _ => true

/-- **The kernel fact behind the concrete invariant**: every conclusion alternative of `Step` rules
1–5 has a fragment left-hand side, and every `Step`/`Step_read` premise's left-hand side is a
fragment expression on its variables. -/
def ctxLhsOk (A : List MixopS) (rules : List Rule) : Bool :=
  [1, 2, 3, 4, 5].all fun j => match (rules[j]? : Option Rule) with
    | some (.ruleD _ _ _ e prems) =>
        (Round6.Reading.conclAlts e).all fun e' => match lhsExp e' with
          | some l => LFrag A l && prems.all (ctxPremLhsOk A l)
          | none => false
    | none => false

/-! ## The invariant for the backend reading -/

/-- **`VDecl.StepInv` for `DDerivesB`**: rules 43 and 23 derive no `Q` value under `RuleBodyB`,
and `Q` passes from a conclusion alternative of a context rule to its `Step` and `Step_read`
premises. -/
structure StepInvB (Q : Value → Prop) : Prop where
  /-- Rule 43 of `Step_read` derives no `Q` value. -/
  read43 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step_read" = some (ps, op, t, rules) → rules[43]? = some r →
    ¬ Round6.Reading.RuleBodyB (simEnv B) D els ps args op' r w
  /-- Rule 23 of `Step` derives no `Q` value. -/
  step23 : ∀ (B : Builtins) (D : Interp) (els : Prop) (ps : List Param) (op : MixopS) (t : Typ)
    (rules : List Rule) (r : Rule) (args : List ArgV) (op' : MixopS) (w : Value), Q w →
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → rules[23]? = some r →
    ¬ Round6.Reading.RuleBodyB (simEnv B) D els ps args op' r w
  /-- `Q` passes from a context rule's conclusion alternative to its `Step`/`Step_read`
  premises. -/
  ctx : ∀ (B : Builtins) (ps : List Param) (op : MixopS) (t : Typ) (rules : List Rule) (j : Nat)
    (nm : IL.Id) (qs : List Param) (op' : MixopS) (e e₁ : Exp) (prems : List Prem) (ρ : VarEnv)
    (v : Value) (y : IL.Id) (args : List Arg) (op'' : MixopS) (e' : Exp) (w : Value),
    (simEnv B).findRel? "Step" = some (ps, op, t, rules) → j ∈ [1, 2, 3, 4, 5] →
    rules[j]? = some (.ruleD nm qs op' e prems) → e₁ ∈ Round6.Reading.conclAlts e →
    EvalExp (simEnv B) ρ e₁ v → Q v →
    Prem.rulePr y args op'' e' ∈ prems → (y = "Step" ∨ y = "Step_read") →
    EvalExp (simEnv B) ρ e' w → Q w

end Silmaril.Wasm.SpecTec.Sim.Round7.VInv
