module

public import Silmaril.Wasm.Atlas.Core.Defs

/-!
# Variants of Core and loose models

A generic pattern for implementations that deviate from Core 3.0 at a few redexes
(`docs/projects/spectec/README.md` §4.2):

* a **base** step relation `R` on Core configurations (Core `Step P host`);
* a **quirk** relation `Q` on redexes, the deviation;
* a **variant**, which overrides `R` at `Q`-redexes. Here it is given by a translation
  of the store's function code, followed by the base semantics (an implementation that
  first translates the program into its own IR and then executes it);
* the **loose** relation `loose R Q := R ∪ Ctx Q`, where `Ctx Q` closes `Q` under the
  evaluation contexts of Core: value prefixes and suffixes, `LABEL`, `HANDLER` and
  `FRAME`. Both the base semantics and the variant refine the loose one.

Observations of an arbitrary step relation are given by `behavioursR`, which has the
shape of silmaril-lean's `behavioursOf`: finite runs to a result, and infinite runs.
`behavioursOf P host = behavioursR (Step P host)` holds by definition
(`Silmaril.Wasm.Atlas.Variant.behavioursOf_eq` in `Thms`).

* `behavioursR R c`, `obsR R x c`: the observations of a configuration and of a call;
* `Ctx Q`, `loose R Q`: the context closure and the loose relation;
* `chartR R dom`: the behaviour chart of a step-relation family, with the points and calls
  of the Core chart.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Variant

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The observations of a configuration under an arbitrary step relation `R`: finite runs to a
result (values, a trap or an escaping exception) and infinite runs. -/
def behavioursR (R : Config H → Config H → Prop) (c : Config H) : Set (Behaviour Val) :=
  {b | ∃ (c' : Config H) (r : Result),
        Relation.ReflTransGen R c c' ∧ c'.code = r.toAdmin ∧ b = r.toBehaviour} ∪
  {b | b = .diverges ∧ InfiniteTrace R c}

/-- The observations of a call `(a, vs)` at a Core point `(s, host)` under the step-relation
family `R` (indexed by the host). -/
def obsR (R : HostSemantics H → Config H → Config H → Prop) (x : Core.Pt H) (c : Core.Call) :
    Set (Behaviour Val) :=
  behavioursR (R x.2) (invoke x.1 c.1 c.2)

/-- The closure of a quirk relation `Q` under the evaluation contexts of Core 3.0: value
prefixes and code suffixes, `LABEL_n{cont}`, `HANDLER_n{catch*}` and `FRAME_n{f}`. -/
inductive Ctx (Q : Config H → Config H → Prop) : Config H → Config H → Prop where
  /-- A quirk step at the redex. -/
  | base {c c' : Config H} (h : Q c c') : Ctx Q c c'
  /-- Under a value prefix and a code suffix (`ctxt-instrs`). -/
  | instrs {s s' : Store H} {f f' : Frame} {vs : List Val} {is is' rest : List Admin}
      (h : Ctx Q ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Ctx Q ⟨s, f, vals vs ++ is ++ rest⟩ ⟨s', f', vals vs ++ is' ++ rest⟩
  /-- Under a label (`ctxt-label`). -/
  | label {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
      (h : Ctx Q ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Ctx Q ⟨s, f, [.label n cont is]⟩ ⟨s', f', [.label n cont is']⟩
  /-- Under an exception handler (`ctxt-handler`). -/
  | handler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
      (h : Ctx Q ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Ctx Q ⟨s, f, [.handler n cs is]⟩ ⟨s', f', [.handler n cs is']⟩
  /-- Under a frame (`ctxt-frame`): the inner frame changes, the outer one does not. -/
  | frame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Ctx Q ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Ctx Q ⟨s, f, [.frame n fi is]⟩ ⟨s', f, [.frame n fi' is']⟩

/-- **The loose relation**: a base step, or a quirk step in an evaluation context. -/
def loose (R Q : Config H → Config H → Prop) (c c' : Config H) : Prop :=
  R c c' ∨ Ctx Q c c'

/-- The behaviour chart of a step-relation family: Core points and calls, the given domain,
observations `obsR R`. -/
def chartR (R : HostSemantics H → Config H → Config H → Prop) (dom : Core.Pt H → Prop) :
    Chart :=
  BChart (Core.Pt H) Core.Call (Behaviour Val) dom (obsR R)

end Silmaril.Wasm.Atlas.Variant
