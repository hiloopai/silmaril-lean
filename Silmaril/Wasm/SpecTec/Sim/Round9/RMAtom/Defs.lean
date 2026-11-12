module

public import Silmaril.Wasm.SpecTec.Sim.Round9.RMCall.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.VInv.Defs

/-!
# Round 9, rm: rules whose left-hand code is flat (definitions)

`RestMSHCG` asks for the backward obligations of `Step_pure`, `Step_read` and `Step` at
configurations whose code holds a memory SIMD instruction (`¬ AdminsMS c.code`). Most rules cannot
fire there: their left-hand code is a list of values and of instructions without bodies, so a
configuration it matches has no memory SIMD instruction at any depth.

* `badHead op`: `op` is the head of a memory SIMD instruction (`VInv.msAtoms`) or of an
  instruction or administrative instruction with a body (`structHeads`).
* `atomCode qs e`: the left-hand code expression `e` is a concatenation of literal lists whose
  elements are `case`s with a head that is not `badHead`, or quantifiers of type `val` or `ref`,
  and of iterations over one quantifier of type `val*` whose body reads its variable back.
* `atomCfg r` (for `Step_read` and `Step`, conclusion `z; ce ~> _`) and `atomPure r` (for
  `Step_pure`, conclusion `ce ~> _`): the rule's left-hand code is `atomCode`.
* `structPure`, `structRead`: the rules of `Step_pure` (15) and `Step_read` off the memory SIMD
  rules 42–51 (16) that are not flat. Every rule of `Step` from 6 on other than 22–25 is flat.
* `RestMSHCH`, `OpenRMRestDPH`: `RMCall.RestMSHCG` and `OpenRMRestDPG` with `pure` asked only at
  `structPure`, `read` only at `structRead`, and no `step` field.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem

/-! ## The flat left-hand codes -/

/-- The heads of the instructions and administrative instructions with a body. -/
def structHeads : List MixopS :=
  ["BLOCK", "LOOP", "IF%%ELSE%", "TRY_TABLE", "LABEL_%{%}%", "HANDLER_%{%}%", "FRAME_%{%}%"]

/-- The heads that may hold or be a memory SIMD instruction. -/
def badHead (op : MixopS) : Bool := structHeads.contains op || Round7.VInv.msAtoms.contains op

/-- `y : val*`. -/
def isValSeq (y : IL.Id) : Param → Bool
  | .expP z (.iterT (.varT "val" []) .list) => z == y
  | _ => false

/-- `y : val` or `y : ref`. -/
def isValQ (y : IL.Id) : Param → Bool
  | .expP z (.varT t []) => z == y && (t == "val" || t == "ref")
  | _ => false

/-- An element of a literal left-hand code list: a `case` whose head is not `badHead`, or a
quantifier of type `val` or `ref`, possibly through a subtype injection. -/
def elemOk (qs : List Param) : Exp → Bool
  | .caseE n _ => !badHead n
  | .varE y => qs.any (isValQ y)
  | .subE (.varE y) _ _ => qs.any (isValQ y)
  | _ => false

/-- The body of an iteration reads its variable `x` back: `x`, or `x <: _`. -/
def bodyVar (x : IL.Id) : Exp → Bool
  | .varE y => y == x
  | .subE (.varE y) _ _ => y == x
  | _ => false

/-- An iteration `x*` or `x^n` over one quantifier `y : val*` whose body reads `x` back. -/
def iterAtomOk (qs : List Param) (b : Exp) : IterExp → Bool
  | .mk .list [.mk x (.varE y)] => bodyVar x b && x != "_" && qs.any (isValSeq y)
  | .mk (.listN (.varE _) none) [.mk x (.varE y)] => bodyVar x b && x != "_" && qs.any (isValSeq y)
  | _ => false

/-- **A flat left-hand code expression.** -/
def atomCode (qs : List Param) : Exp → Bool
  | .iterE b ie => iterAtomOk qs b ie
  | .catE a b => atomCode qs a && atomCode qs b
  | .listE es => es.all (elemOk qs)
  | _ => false

/-- A rule `z; ce ~> _` (of `Step_read` or `Step`) whose left-hand code is flat. -/
def atomCfg : Rule → Bool
  | .ruleD _ qs _ (.tupE [.caseE "%;%" (.tupE [_, ce]), _]) _ => atomCode qs ce
  | _ => false

/-- A rule `ce ~> _` (of `Step_pure`) whose left-hand code is flat. -/
def atomPure : Rule → Bool
  | .ruleD _ qs _ (.tupE [ce, _]) _ => atomCode qs ce
  | _ => false

/-- **The rules of `Step_pure` that are not flat** (15): `if`, the label, handler and frame
exits, `br` out of labels and handlers, `return` and the trap propagation rules. -/
def structPure : List Nat := [5, 6, 7, 8, 9, 10, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- **The rules of `Step_read` that are not flat, off the memory SIMD rules 42–51** (16):
`block`, `loop`, `return_call_ref` out of labels, handlers and frames, the `throw_ref`
propagation and catch rules, and `try_table`. -/
def structRead : List Nat := [0, 1, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

/-! ## The obligations left -/

section
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round6.MemSimd (AdminsMS)
open Round7.MemSimd (configVD adminsToVD TypedD BoundedSelM)

variable {H : Type}

/-- **`RMCall.RestMSHCG` at the rules that are not flat**: `pure` at `structPure`, `read` at
`structRead`; the `step` field is gone. -/
structure RestMSHCH (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- `RestMSHCG.pure`, at the 15 rules of `structPure`. -/
  pure : ∀ i ∈ structPure, ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    ¬ AdminsMS is → Round7.MSRest.VMS ⟨s, f, is⟩ →
    TypedD (simEnv (Prims.builtins P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (Prims.builtins P hn host)) "Step_pure" i (.tuple [.list (adminsToVD is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩
  /-- `RestMSHCG.read`, at the 16 rules of `structRead`. -/
  read : ∀ i ∈ structRead, ∀ (c : Config H) (w : Value), ¬ AdminsMS c.code →
    Round7.MSRest.VMS c → TypedD (simEnv (Prims.builtins P hn host)) hn c →
    Fires (simEnv (Prims.builtins P hn host)) "Step_read" i (.tuple [configVD hn c, w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToVD js) ∧
      Step P host c ⟨c.store, c.frame, is'⟩
  /-- As `RestMSHCG.firesRead`. -/
  firesRead : ∀ i ∈ Round8.FiresC.elseRead,
    Round8.RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i

/-- **`RMCall.OpenRMRestDPG` with `RestMSHCH` for `RestMSHCG`.** -/
structure OpenRMRestDPH (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- As `RMCall.OpenRMRestDPG.forward`. -/
  forward : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → ¬ Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' → ¬ Round7.HCtx.CallCtxStep P host c c' →
    ∃ c'', Step P host c c'' ∧ ((∀ c₃, Step P host c c₃ → c₃ = c') → c'' = c') ∧
      ∃ d', Bwd.ConfigEq c'' d' ∧
        SStep (simEnv (Round7.HostD.BD P hn host)) (configVD hn c) (configVD hn d')
  /-- The per-rule obligations left. -/
  restMSHC : RestMSHCH hn P host
  /-- As `RMCall.OpenRMRestDPG.castsFwd`. -/
  castsFwd : ∀ (c c' : Config H) (ts : List CValType), ConfigOk c ts → BoundedSelM c →
    (∀ c₁, Step P host c c₁ → BoundedSelM c₁) → Round6.Target.CastRedex c.code →
    ¬ Round7.HPair.EasyP hn P host c → Step P host c c' →
    ∃ d', Bwd.ConfigEq c' d' ∧
      Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) (configVD hn d')
  /-- As `RMCall.OpenRMRestDPG.castsBwd`. -/
  castsBwd : ∀ (c : Config H) (ts : List CValType) (w : Value), ConfigOk c ts →
    BoundedSelM c → Round6.Target.CastRedex c.code → ¬ Round7.HPair.EasyP hn P host c →
    Round6.Int.backend.step (Round7.HostD.BD P hn host) (configVD hn c) w →
    ∃ c' d', Bwd.ConfigEq c' d' ∧ w = configVD hn d' ∧ Step P host c c'

end

end Silmaril.Wasm.SpecTec.Sim.Round9.RMAtom
