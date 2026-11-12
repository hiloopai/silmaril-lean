module

public import Silmaril.Compiler.C.Sem.C2Rules.Defs
/-!
# Finite C2 execution between internal cutpoints

Each edge is a successful original `C2.step` with a running result. Unlike a
contextual equality between two `loop` evaluations, a prefix directly witnesses
the steps reaching its endpoint, independently of failure or termination in the
remaining continuation. Fuel is retained at both endpoints so prefix composition
matches the interpreter's nested evaluation budgets exactly. These are source
interpreter traces, not compilation or native execution certificates.
-/

@[expose] public section

namespace Silmaril.Compile.C.Sem.C2

open Silmaril.Cerberus Silmaril.Cerberus.Ail

/-- An internal control location and its complete activation environment. -/
structure Configuration where
  focus : Option TypedStatement
  kont : C0.Kont
  env : C1.Env

/-- A finite path that neither crosses a function return nor assumes anything
about execution after its final cutpoint. The step may itself execute calls. -/
inductive Prefix (P : Prog) (fd : C1.FunDef) :
    Nat → Configuration → Nat → Configuration → Prop where
  | refl (fuel : Nat) (state : Configuration) : Prefix P fd fuel state fuel state
  | cons {fuel finalFuel : Nat} {before middle after : Configuration}
      (step : C2.step P fuel fd before.focus before.kont before.env =
        .ok (.running middle.focus middle.kont, middle.env))
      (tail : Prefix P fd fuel middle finalFuel after) :
      Prefix P fd (fuel + 1) before finalFuel after

namespace Prefix

variable {P : Prog} {fd : C1.FunDef}

theorem fuel_le {fuel finalFuel : Nat} {before after : Configuration}
    (path : Prefix P fd fuel before finalFuel after) : finalFuel ≤ fuel := by
  induction path with
  | refl => exact Nat.le_refl _
  | cons _ _ ih => omega

/-- Compose adjacent source paths without imposing a public-return boundary. -/
theorem trans {fuel middleFuel finalFuel : Nat} {before middle after : Configuration}
    (first : Prefix P fd fuel before middleFuel middle)
    (second : Prefix P fd middleFuel middle finalFuel after) :
    Prefix P fd fuel before finalFuel after := by
  induction first with
  | refl => exact second
  | cons step _ ih => exact .cons step (ih second)

/-- Finite progress gives the corresponding contextual evaluation equality,
including any error or fuel exhaustion in the unexecuted source continuation. -/
theorem loop_eq {fuel finalFuel : Nat} {before after : Configuration}
    (path : Prefix P fd fuel before finalFuel after) :
    C2.loop P fuel fd before.focus before.kont before.env =
      C2.loop P finalFuel fd after.focus after.kont after.env := by
  induction path with
  | refl => rfl
  | cons step _ ih =>
    rw [C2.loop, step]
    exact ih

/-- Every successful suffix run can be preceded by the proved source path. -/
theorem append_success {fuel finalFuel : Nat} {before after : Configuration}
    (path : Prefix P fd fuel before finalFuel after) (value : Option Val) (env : C1.Env)
    (suffix : C2.loop P finalFuel fd after.focus after.kont after.env = .ok (value, env)) :
    C2.loop P fuel fd before.focus before.kont before.env = .ok (value, env) :=
  path.loop_eq.trans suffix

/-- A single running source step is a prefix in its own right. -/
theorem single {fuel : Nat} {before after : Configuration}
    (step : C2.step P fuel fd before.focus before.kont before.env =
      .ok (.running after.focus after.kont, after.env)) :
    Prefix P fd (fuel + 1) before fuel after :=
  .cons step (.refl fuel after)

end Prefix

end Silmaril.Compile.C.Sem.C2
