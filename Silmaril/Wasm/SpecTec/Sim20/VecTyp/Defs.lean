module

public import Silmaril.Wasm.SpecTec.Sim20.RelFree.Thms
public import Silmaril.Wasm.SpecTec.Sim20.StoreFix.Defs

/-!
# State typing does not depend on the vector builtins (definitions)

Round 7's vector `Step` lifts, and round 8's at `VecNum.vecNB P`, take the state typed in
`simEnv20T B` at the new builtins as a hypothesis, while the forward invariant `Good20B` types it
at `Whole.storeB P`. The two builtins differ only at `$lanes_`, `$inv_lanes_`, `$vunop_`,
`$vbinop_` and `$vrelop_`. Where `storeB P` gives no answer and the clauses definitely fail, the
call is `undef`; at `vecNB P` it can be a value. That is not a `Res.Le` growth, so round 7's
`EnvExt` transfer does not apply. This topic shows instead that **typing never reaches those
names**.

* `BAgree bad B₁ B₂`: `B₂` answers as `B₁` at every name outside `bad`.
* `badV20`: the five names, `$instantiate` (the one definition that refers to a relation), and the
  two definitions that call one of the five (`$vextunop__`, `$vextbinop__`).
* `defsTypsOkB bad s`: every definition of `s` outside `bad`, and every type, refers to no
  relation and to no definition in `bad`. The kernel checks it on `fixedT20` with `badV20`
  (`VecTyp.defsTypsOkB_fixedT20`).

Under `BAgree`, harmless syntax evaluates and types alike in `env.withBuiltins B₁` and
`env.withBuiltins B₂` (`VecTyp.bagreeAt`, `tbagreeAt`, unrefined copies of `RelFree.agreeAt` and
`RelFree.tAgreeAt`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.RelFree (GoodName rfEvB)
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (items)

/-- **`B₂` answers as `B₁` at every name outside `bad`.** -/
def BAgree (bad : List String) (B₁ B₂ : Builtins) : Prop :=
  ∀ x, GoodName bad x → ∀ ws, B₂.call x ws = B₁.call x ws

/-- The names typing must avoid for the vector builtins: the five names where `storeB P` and
`vecNB P` differ, the relation user `$instantiate`, and the definitions that call one of the
five. -/
def badV20 : List String :=
  ["instantiate", "lanes_", "inv_lanes_", "vunop_", "vbinop_", "vrelop_", "vextunop__",
    "vextbinop__"]

/-- Every definition of `s` outside `bad`, and every type of `s`, is harmless (relations and
grammars are not checked). -/
def defsTypsOkB (bad : List String) (s : Script) : Bool :=
  (items s).all fun it =>
    it.1 == 0 || it.1 == 3 || (it.1 == 1 && bad.contains it.2.1) || it.2.2.all (rfEvB bad)

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
