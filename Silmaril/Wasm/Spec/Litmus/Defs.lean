module

public import Silmaril.Wasm.Spec.Basic.Defs
public import Silmaril.Wasm.Spec.Temporal.Defs
public import Silmaril.Wasm.Spec.Env.Defs
public import Silmaril.Wasm.Behaviour.Adapters.Core

@[expose] public section

/-!
# Litmus programs

Concrete interfaces and trace sets on which the specification logics are tested
(`Silmaril.Wasm.Spec.Litmus.Thms`). Payloads are Core values and behaviours; the programs are good
trace sets of the loose semantics `Semantics.ofSets` (the prefixes of one trace).

* `X₀`: imports `0 = assert`, `1 = log`; exports `0 = main`.
* `X₁`: imports as `X₀`; exports `0 = main`, `1 = debug`. `X₀ ⟶ X₁` keeps `main` (`ι₀₁`).
* `okRun`: `main` calls `assert(1)`, which returns, then returns `5`.
* `badRun`: `main` calls `assert(0)`.
* `debugRun` (at `X₁`): `main` returns `5`; then `debug` calls `log(7)` and returns.
-/

namespace Silmaril.Wasm.Spec.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- Litmus events. -/
abbrev Ev (X : Iface Unit) : Type := Event (List Val) (Behaviour Val) X

/-- Imports `assert`, `log`; export `main`. -/
def X₀ : Iface Unit := ⟨[(), ()], [()]⟩

/-- Imports `assert`, `log`; exports `main`, `debug`. -/
def X₁ : Iface Unit := ⟨[(), ()], [(), ()]⟩

/-- The import `assert`. -/
def assertI : X₀.Imp := ⟨0, by decide⟩
/-- The import `log`. -/
def logI : X₀.Imp := ⟨1, by decide⟩
/-- The export `main`. -/
def mainE : X₀.Exp := ⟨0, by decide⟩

/-- `X₀` sits in `X₁` (export `main` kept, `debug` hidden). -/
def ι₀₁ : X₀ ⟶ X₁ where
  exp _ := ⟨0, by decide⟩
  exp_inj a b _ := Fin.ext (by have := a.2; have := b.2; simp [X₀] at *; omega)
  exp_ty _ := rfl
  imp i := ⟨i.1, i.2⟩
  imp_inj a b h := Fin.ext (Fin.mk.inj_iff.1 h)
  imp_ty _ := rfl

/-- `main` asserts `1` and returns `5`. -/
def okRun : List (Ev X₀) :=
  [.call mainE [], .icall assertI [Val.i32 1], .iret assertI (.returns []),
    .ret mainE (.returns [Val.i32 5])]

/-- `main` asserts `0`. -/
def badRun : List (Ev X₀) := [.call mainE [], .icall assertI [Val.i32 0]]

/-- At `X₁`: `main` returns `5`, then `debug` logs `7`. -/
def debugRun : List (Ev X₁) :=
  [.call ⟨0, by decide⟩ [], .ret ⟨0, by decide⟩ (.returns [Val.i32 5]), .call ⟨1, by decide⟩ [],
    .icall ⟨1, by decide⟩ [Val.i32 7], .iret ⟨1, by decide⟩ (.returns []),
    .ret ⟨1, by decide⟩ (.returns [])]

/-- The program whose traces are the prefixes of `l`. -/
def progOf {X : Iface Unit} (l : List (Ev X)) : (Semantics.ofSets Unit (List Val) (Behaviour Val)).Prog X :=
  ⟨prefixesOf l, prefixesOf_good l⟩

end Silmaril.Wasm.Spec.Litmus

namespace Silmaril.Wasm.Spec.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- A litmus program satisfies a formula iff the prefixes of its trace do. -/
theorem models_progOf_iff (L : Logic Unit (List Val) (Behaviour Val)) {X : Iface Unit}
    (l : List (Ev X)) (φ : L.Fm X) :
    Models L (Semantics.ofSets Unit (List Val) (Behaviour Val)) (progOf l) φ ↔
      L.Sat (prefixesOf l) φ :=
  models_iff _ _ _ _

end Silmaril.Wasm.Spec.Litmus

namespace Silmaril.Wasm.Spec.Litmus

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- An atom: the event is a call of `main`. -/
def callMain : PosPred (List Val) (Behaviour Val) X₀ := fun _ e => ∃ a, e = Event.call mainE a

/-- An atom: the event is a return of `main`. -/
def retMain : PosPred (List Val) (Behaviour Val) X₀ := fun _ e => ∃ r, e = Event.ret mainE r

/-- Liveness: every call of `main` is eventually followed by a return of `main`. -/
def mainReturns : LTLFm (List Val) (Behaviour Val) X₀ :=
  LTL.alw (LTL.imp (LTL.atom callMain) (LTL.ev (LTL.atom retMain)))

/-- The environment answering `assert(1)` with no values. -/
def assertEnv : EnvSpec (List Val) (Behaviour Val) X₀ :=
  ⟨prefixesOf [.ask assertI [Val.i32 1], .ans assertI (.returns [])], prefixesOf_good _⟩

end Silmaril.Wasm.Spec.Litmus
