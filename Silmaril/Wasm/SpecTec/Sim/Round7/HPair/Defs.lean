module

public import Silmaril.Wasm.SpecTec.Sim.Round7.MSAtoms.Thms

/-!
# Round 7, `BD`: a position-sensitive invariant for the host-call rules (definitions)

`HStep.stepInvH_h` keeps `Step` rules 8 and 9 (the host calls through `call_ref`) silent by
excluding every `CALL_REF` from the source. Those rules fire only on code ending in
`REF.FUNC_ADDR a` followed by `CALL_REF yy`. The invariant below excludes only that adjacent pair,
in every list of the value, and keeps `CALL_REF` everywhere else.

* `pairAt a b`: `a` is a `case` of `REF.FUNC_ADDR` and `b` a `case` of `CALL_REF`.
* `PairFreeL cs`: no two adjacent elements of `cs` form `pairAt`.
* `NoPair v`: every list occurring in `v`, at any depth, is `PairFreeL`.
* `LhsNoPair v`: `v` is a pair whose left-hand side is `NoPair`.
* `LFragP e`: the fragment of `VInv.LFrag` without concatenations and without list expressions of
  two or more elements, the shapes that can create a new adjacent pair.
* `lastPair e`: the mixops of the last two instructions of a code expression (a list, or a
  concatenation ending in one).
* `stepPairOk rules`: the kernel fact: the `Step`/`Step_read` premises of rules 1–5 have `LFragP`
  left-hand sides, and every conclusion alternative of rules 8 and 9 ends in
  `REF.FUNC_ADDR`, `CALL_REF`.
* `EasyP hn P host c`: `RMRed.Easy` with `NoPair` for the absence of `CALL_REF`: no memory SIMD
  code in `c` or in a Core successor, and no `CALL_REF` right after a `REF.FUNC_ADDR` in the image.
* `OpenRMRestDP`: `RMRed.OpenRMRestDR` with `forward`, `castsFwd` and `castsBwd` asked only at
  sources that are not `EasyP`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.HPair

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-- `a` is a `case` of `REF.FUNC_ADDR` and `b` a `case` of `CALL_REF`. -/
def pairAt : Value → Value → Bool
  | .case a _, .case b _ => a == "REF.FUNC_ADDR" && b == "CALL_REF"
  | _, _ => false

/-- No two adjacent elements form `pairAt`. -/
def PairFreeL : List Value → Prop
  | a :: b :: rest => pairAt a b = false ∧ PairFreeL (b :: rest)
  | _ => True

mutual
/-- **Every list occurring in `v` is `PairFreeL`.** -/
def NoPair : Value → Prop
  | .bool _ => True
  | .num _ => True
  | .text _ => True
  | .tuple vs => NoPairL vs
  | .case _ w => NoPair w
  | .struct gs => NoPairF gs
  | .list vs => PairFreeL vs ∧ NoPairL vs
  | .opt none => True
  | .opt (some w) => NoPair w

/-- `NoPair` on every element. -/
def NoPairL : List Value → Prop
  | [] => True
  | v :: vs => NoPair v ∧ NoPairL vs

/-- `NoPair` on every field. -/
def NoPairF : List (AtomS × Value) → Prop
  | [] => True
  | (_, v) :: gs => NoPair v ∧ NoPairF gs
end

/-- `v` is a pair whose left-hand side is `NoPair`. -/
def LhsNoPair (v : Value) : Prop :=
  ∃ l r, v = .tuple [l, r] ∧ NoPair l

mutual
/-- **The premise fragment**: variables, tuples, lists of at most one element, `case`s, subtype
injections and `iterVar` iterations. -/
def LFragP : Exp → Bool
  | .varE _ => true
  | .tupE es => LFragPL es
  | .listE [] => true
  | .listE [e] => LFragP e
  | .caseE _ e => LFragP e
  | .subE e _ _ => LFragP e
  | .iterE e it => (VInv.iterVar e it).isSome
  | _ => false

/-- `LFragP` on a list. -/
def LFragPL : List Exp → Bool
  | [] => true
  | e :: es => LFragP e && LFragPL es
end

/-- The mixops of the last two elements of a code expression. -/
def lastPair : Exp → Option (MixopS × MixopS)
  | .listE es => match es.reverse with
    | .caseE b _ :: .caseE a _ :: _ => some (a, b)
    | _ => none
  | .catE _ e₂ => lastPair e₂
  | _ => none

/-- Every conclusion alternative of `r` ends in the instructions `a`, `b`. -/
def altPairOk (r : Rule) (a b : MixopS) : Bool :=
  match r with
  | .ruleD nm qs op e prems =>
      (Round6.Reading.conclAlts e).all fun e' =>
        (VElse.readCode (.ruleD nm qs op e' prems)).bind lastPair == some (a, b)

/-- A premise of a context rule: a `Step`/`Step_read` premise has an `LFragP` left-hand side. -/
def premPOk : Prem → Bool
  | .rulePr y _ _ e =>
      !(y == "Step" || y == "Step_read") ||
        match VInv.lhsExp e with
        | some l' => LFragP l'
        | none => false
  | _ => true

/-- **The kernel fact behind `LhsNoPair`.** -/
def stepPairOk (rules : List Rule) : Bool :=
  [1, 2, 3, 4, 5].all (fun j => match (rules[j]? : Option Rule) with
    | some (.ruleD _ _ _ _ prems) => prems.all premPOk
    | none => false) &&
  (match rules[8]? with
    | some r => altPairOk r "REF.FUNC_ADDR" "CALL_REF"
    | none => false) &&
  match rules[9]? with
  | some r => altPairOk r "REF.FUNC_ADDR" "CALL_REF"
  | none => false

section Reduction

open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (NoMemSimd)
open Round6.Target (CastRedex)
open Round7.MemSimd (BoundedSelM configVD)
open Round7.HostD (BD)

variable {H : Type}

/-- **The sources the `NoPair` transfer covers.** -/
def EasyP (hn : H → String) (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  NoMemSimd c ∧ (∀ c₁, Step P host c c₁ → NoMemSimd c₁) ∧ NoPair (Sim.configV hn c)

/-- **`RMRed.OpenRMRestDR` with `EasyP` for `Easy`.** -/
structure OpenRMRestDP (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `forward`, at sources that are not `EasyP`, for steps that are not `call_ref` steps on a
  reference under contexts. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ CastRedex c.code → ¬ EasyP hn P host c →
    Step P host c c' → ¬ HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧ SStep (simEnv (BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule backward obligations at configurations holding memory SIMD code. -/
  restMSHC : NullHost.RestMSHC hn P host
  /-- `castsFwd`, at sources that are not `EasyP`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → CastRedex c.code → ¬ EasyP hn P host c →
    Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (BD P hn host) (configVD hn c) (configVD hn d')
  /-- `castsBwd`, at sources that are not `EasyP`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → CastRedex c.code → ¬ EasyP hn P host c →
    Round6.Int.backend.step (BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end Reduction

end Silmaril.Wasm.SpecTec.Sim.Round7.HPair
