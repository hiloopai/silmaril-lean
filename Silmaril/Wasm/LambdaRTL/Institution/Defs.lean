module

public import Silmaril.Wasm.LambdaRTL.Thms
public import Silmaril.Wasm.FnInst.IR.Bodies.Defs

/-!
# Loop-free fragment → λRTL as a translation of function-body languages (track `ir`)

The function-body institutions of `Silmaril.Wasm.FnInst.IR` (`Lang.inst F L`: sentences are
refinements `b ⊑ b'`, equivalences `b ≐ b'` and conjunctions of candidate bodies of a focus
hole; satisfaction compares the bodies' terminating outcomes) get two more body languages and
two translations:

| language | bodies at a hole `h` | denotation |
| --- | --- | --- |
| `fragLF E` | fragment functions of type `h` with no `loop` | `FragFunc.Run` |
| `rtl E` | λRTL functions `RFunc` of type `h` | `RFunc.Run`: the λRTL observation in `model` |

| translation | direction | body map | exactness from |
| --- | --- | --- | --- |
| `toRTL E` | `fragLF → rtl` | `RFunc.ofFrag` (`trBody`) | `trFunc_run_iff`, `trFunc_stuck_iff` |
| `lfIncl E` | `fragLF → frag` | inclusion | `rfl` |

Each `Lang.Tr` gives a comorphism of the body institutions (`Lang.Tr.comorphism`), here with
the identity environment map, so it is model-expansive and validity is borrowed
(`Silmaril.Wasm.LambdaRTL.Institution.Thms`).

Scope: the source is restricted to loop-free bodies; the λRTL language is read in the fixed
model `model` of `Silmaril.Wasm.LambdaRTL` (traps and stuckness in `Except WErr`). `rtl` does not
claim anything about λRTL bodies that are not translations.
-/

@[expose] public section

namespace Silmaril.Wasm.LambdaRTL

open Silmaril.Wasm.SSA (WVal FragFunc FOut)
open Silmaril.Wasm.FnInst.IR (Hole HasType Lang frag)
open Silmaril.Wasm (IntType)

/-- A λRTL function: parameter, declared-local and result types and a λRTL body. -/
structure RFunc where
  params : List IntType
  locals : List IntType
  result : Option IntType
  body : WRegion

/-- The λRTL store of a call: the arguments, then the zero-initialised declared locals. -/
def RFunc.store (g : RFunc) (args : List WVal) : Store :=
  initStore ⟨g.params, g.locals, g.result, []⟩ args

/-- Terminating runs of a λRTL function (outcomes in the model `model`). -/
def RFunc.Run (g : RFunc) (args : List WVal) (o : FOut) : Prop :=
  args.map WVal.type = g.params ∧ g.body.evalObs model (g.store args) = obsOf o

/-- The λRTL function of a fragment function. -/
def RFunc.ofFrag (f : FragFunc) : RFunc := ⟨f.params, f.locals, f.result, trBody f⟩

theorem RFunc.ofFrag_run_iff {f : FragFunc} (hlf : loopFreeL f.body = true) (args : List WVal)
    (o : FOut) : (RFunc.ofFrag f).Run args o ↔ f.Run args o := by
  have hf : trFunc f = some (trBody f) := by simp [trFunc, hlf]
  constructor
  · rintro ⟨hargs, he⟩
    exact (trFunc_run_iff hf hargs (initStore_spec f args) o).2 he
  · intro hr
    exact ⟨hr.1, (trFunc_run_iff hf hr.1 (initStore_spec f args) o).1 hr⟩

/-- Loop-free fragment functions, with any environment type. -/
def fragLF (E : Type) : Lang where
  Body h := {f : FragFunc // HasType f h ∧ loopFreeL f.body = true}
  Env := E
  den _ _ b := b.1.Run

/-- λRTL functions read in `model`, with any environment type. -/
def rtl (E : Type) : Lang where
  Body h := {g : RFunc // g.params = h.params ∧ g.result = h.result}
  Env := E
  den _ _ b := b.1.Run

/-- **Loop-free fragment → λRTL**, exact on denotations. -/
def toRTL (E : Type) : Lang.Tr (fragLF E) (rtl E) where
  body _ b := ⟨RFunc.ofFrag b.1, b.2.1.1, b.2.1.2⟩
  env e := e
  den_body _ _ b := by
    funext args o
    exact propext (RFunc.ofFrag_run_iff b.2.2 args o)

/-- The inclusion of loop-free functions into the fragment. -/
def lfIncl (E : Type) : Lang.Tr (fragLF E) (frag E) where
  body _ b := ⟨b.1, b.2.1⟩
  env e := e
  den_body _ _ _ := rfl

end Silmaril.Wasm.LambdaRTL
