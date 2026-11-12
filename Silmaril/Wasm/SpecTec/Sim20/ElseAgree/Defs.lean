module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Sem.Type

/-!
# Typing off a set of type names, and the `otherwise` pairs (definitions)

`simEnv20S` and `simEnv20T` differ only in the `STORE` cases of `instr` and `admininstr`. A type
whose unfolding never reaches those two types is typed alike in both. This header names that
syntax:

* `tyEvB bad`: an event (`Round7.Script.Ev`) that is not a reference to a type in `bad`;
* `GoodT bad l`: every event of `l` is such;
* `TypsOkT bad ρ`, `ArgTyOkT bad w`: type variables and type arguments are bound to such types;
* `TypOff bad e₁ e₂`: the type tables of `e₁` and `e₂` agree outside `bad`, and every type of `e₁`
  outside `bad` unfolds to types outside `bad`;
* `typsOffB bad m`: the closure half of `TypOff`, as a check on a table;
* `tbad20`: the fifteen types of the wasm-2.0 script that reach `instr` or `admininstr`, computed
  by a reference closure over the script's type table and checked by the kernel
  (`Sim20.ElseAgree.typsOffB_fixedS20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.ElseAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (Ev evTyp evInst)

/-- An event that is not a reference to a type in `bad`. -/
def tyEvB (bad : List String) : Ev → Bool
  | .ref 2 x => !bad.contains x
  | _ => true

/-- Every event of `l` avoids the types in `bad`. -/
def GoodT (bad : List String) (l : List Ev) : Prop := ∀ e ∈ l, tyEvB bad e = true

/-- Every type variable of `ρ` is bound to a type that avoids `bad`. -/
def TypsOkT (bad : List String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, GoodT bad (evTyp p.2)

/-- A type argument avoids `bad`. -/
def ArgTyOkT (bad : List String) : ArgV → Prop
  | .typ t => GoodT bad (evTyp t)
  | _ => True

/-- **The type tables of `e₁` and `e₂` agree outside `bad`, which is closed in `e₁`.** -/
structure TypOff (bad : List String) (e₁ e₂ : Env) : Prop where
  find : ∀ x, bad.contains x = false → e₂.findTyp? x = e₁.findTyp? x
  closed : ∀ x td, bad.contains x = false → e₁.findTyp? x = some td →
    ∀ i ∈ td.2, GoodT bad (evInst i)

/-- The closure half of `TypOff`, on a table. -/
def typsOffB (bad : List String) (m : Map TypDef) : Bool :=
  m.all fun p => bad.contains p.1 || p.2.2.all fun i => (evInst i).all (tyEvB bad)

/-- The types of the wasm-2.0 script that reach `instr` or `admininstr`. -/
def tbad20 : List String :=
  ["instr", "admininstr", "config", "expr", "code", "elem", "global", "func", "datamode",
    "elemmode", "funcinst", "module", "data", "store", "state"]

end Silmaril.Wasm.SpecTec.Sim20.ElseAgree
