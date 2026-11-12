module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.FwdB30DDeep

/-!
# `Step_read` facts at `Wasm30.builtins` at labels and handlers, exactly

`FwdB30X.readX_two_sided` gives, at every `FwdX30.ReadHeadX` redex on `DomDet`, a `Step_read`
fact of `stepModel builtins` to Core's successor up to `CfgRel`, and says every such fact to
typed code is that successor up to `CfgRel`. `FwdB30S.readX_exact` dropped `CfgRel` when the
successor has no label, handler, frame or `CALL_REF` at the top. With `cfgRel_exact_deep` the
successor may have labels, handlers and frames at any depth, as long as none of their bodies
has a `CALL_REF` at the top (`deepRigidL`).

* `readX_exact_deep`: at a `ReadHeadX` redex with a deeply rigid successor, the fact to
  `adminsToV is'` exists and is the only one to typed code.
* `block_exact`, `loop_exact`, `tryTable_exact`: at `block`, `loop` and `try_table`, when the
  body has no `call_ref` at the top (`callFree`).
* `throwRefHandlerNext_exact`: at `throw_ref-handler-next`, unconditionally.
* `ctrlRead_deep_cases`: every `CtrlRead` successor is deeply rigid, except at `call` (whose
  successor is `[ref, CALL_REF]`) and at a block, loop or `try_table` whose body has a
  `call_ref` at the top.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30D

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics (Profile RelaxedChoice)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim
open Silmaril.Wasm.SpecTec.Institution.Wasm30 (stepModel DomDet)
open Silmaril.Wasm.SpecTec.Institution.FwdX30 (ReadHeadX CtrlRead)

variable {H : Type}

/-- A `RETURN_CALL_REF` is deeply rigid. -/
theorem deepRigid_returnCallRef {c : Admin} (h : c.IsReturnCallRef) : deepRigid c = true := by
  unfold Admin.IsReturnCallRef at h
  split at h
  · rfl
  · rfl
  · exact h.elim

/-- `throwing a` is deeply rigid. -/
theorem deepRigidL_throwing (a : Nat) : deepRigidL (throwing a) = true := rfl

/-- **Every `CtrlRead` successor is deeply rigid**, except at `call` and at a block, loop or
`try_table` whose body has a `call_ref` at the top. -/
theorem ctrlRead_deep_cases {c : Config H} {is' : List Admin} (h : CtrlRead c is') :
    deepRigidL is' = true ∨ (∃ x, c.code = [.plain (.call x)]) ∨
      ∃ body, callFree body = false ∧ ∃ vs bt,
        c.code = vals vs ++ [.plain (.block bt body)] ∨
          c.code = vals vs ++ [.plain (.loop bt body)] ∨
          ∃ cs, c.code = vals vs ++ [.plain (.tryTable bt cs body)] := by
  cases h with
  | call => exact .inr (.inl ⟨_, rfl⟩)
  | @block _ _ bt body vs _ _ _ _ =>
    cases hb : callFree body
    · exact .inr (.inr ⟨body, hb, vs, bt, .inl rfl⟩)
    · exact .inl (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hb])
  | @loop _ _ bt body vs _ _ _ _ =>
    cases hb : callFree body
    · exact .inr (.inr ⟨body, hb, vs, bt, .inr (.inl rfl)⟩)
    · exact .inl (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hb])
  | @tryTable _ _ bt cs body vs _ _ _ _ =>
    cases hb : callFree body
    · exact .inr (.inr ⟨body, hb, vs, bt, .inr (.inr ⟨cs, rfl⟩)⟩)
    · exact .inl (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hb])
  | returnCallRefLabel hc | returnCallRefHandler hc =>
    exact .inl (by simp [deepRigidL_append, deepRigidL_vals, deepRigid_returnCallRef hc])
  | throwRefHandlerCatch | throwRefHandlerCatchRef =>
    exact .inl (by simp [deepRigidL_append, deepRigidL_vals, deepRigid])
  | _ => exact .inl rfl

section Builtins

variable {hn : H → String} {hinj : Function.Injective hn} {host : HostSemantics H}
  {hf : HostFinite host} {hh : HostOk host} {nd : Bool} {r : RelaxedChoice}

/-- The step model of `Wasm30.toModel`, at the choice-made primitives. -/
local notation "SB" => stepModel (Wasm30.builtins hn hinj host hf hh nd r)

/-- Its evaluator. -/
local notation "EB" => simEnv (Wasm30.builtins hn hinj host hf hh nd r)

/-- **At a `ReadHeadX` redex with a deeply rigid successor, the `Step_read` fact at `builtins`
is exact**: the fact to the image of Core's successor exists, and it is the only fact to typed
code. -/
theorem readX_exact_deep {c : Config H} (hc : DomDet (Profile.spec nd r) host c)
    {is' : List Admin} (hr : ReadHeadX (Profile.spec nd r) c is') (hrig : deepRigidL is' = true) :
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js]) → js = adminsToV is' := by
  obtain ⟨hex, hall⟩ := FwdB30X.readX_two_sided (hinj := hinj) (hf := hf) (hh := hh) hc hr
  exact ⟨exact_of_cfgRel_deep
      (Q := fun js => (SB).D "Step_read" "%~>%" [] (.tuple [configV hn c, .list js])) hex hrig,
    fun js hjs hq => eq_of_cfgRel_deep (hall js hjs hq) hrig⟩

/-- **`block`, exactly**, when its body has no `call_ref` at the top. -/
theorem block_exact {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) (hcf : callFree body = true)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩) :
    let is' := [Admin.label t₂.length [] (vals vs ++ expression body)]
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩,
        .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" []
          (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.block bt body)]⟩, .list js]) →
        js = adminsToV is' :=
  readX_exact_deep (hinj := hinj) (hf := hf) (hh := hh) hc (.ctrl (.block hbt hm))
    (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hcf])

/-- **`loop`, exactly**, when its body has no `call_ref` at the top. -/
theorem loop_exact {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {vs : List Val}
    {t₁ t₂ : List Silmaril.Wasm.Validation.CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
    (hm : vs.length = t₁.length) (hcf : callFree body = true)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩) :
    let is' := [Admin.label t₁.length [.loop bt body] (vals vs ++ expression body)]
    (SB).D "Step_read" "%~>%" [] (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩,
        .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" []
          (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.loop bt body)]⟩, .list js]) →
        js = adminsToV is' :=
  readX_exact_deep (hinj := hinj) (hf := hf) (hh := hh) hc (.ctrl (.loop hbt hm))
    (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hcf])

/-- **`try_table`, exactly**, when its body has no `call_ref` at the top. -/
theorem tryTable_exact {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch}
    {body : List Instr} {vs : List Val} {t₁ t₂ : List Silmaril.Wasm.Validation.CValType}
    (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : vs.length = t₁.length)
    (hcf : callFree body = true)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩) :
    let is' := [Admin.handler t₂.length cs [.label t₂.length [] (vals vs ++ expression body)]]
    (SB).D "Step_read" "%~>%" []
        (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩,
          .list (adminsToV is')]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" []
          (.tuple [configV hn ⟨s, f, vals vs ++ [.plain (.tryTable bt cs body)]⟩, .list js]) →
        js = adminsToV is' :=
  readX_exact_deep (hinj := hinj) (hf := hf) (hh := hh) hc (.ctrl (.tryTable hbt hm))
    (by simp [deepRigidL_append, deepRigidL_vals, deepRigidL_expression, hcf])

/-- **`throw_ref-handler-next`, exactly.** -/
theorem throwRefHandlerNext_exact {s : Store H} {f : Frame} {n : Nat} {c : Catch}
    {cs : List Catch} {a : Nat} (hm : ¬ CatchMatches s f a c)
    (hc : DomDet (Profile.spec nd r) host ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩) :
    (SB).D "Step_read" "%~>%" []
        (.tuple [configV hn ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩,
          .list (adminsToV [.handler n cs (throwing a)])]) ∧
      ∀ js, TypedV EB instrsT (.list js) →
        (SB).D "Step_read" "%~>%" []
          (.tuple [configV hn ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩, .list js]) →
        js = adminsToV [.handler n cs (throwing a)] :=
  readX_exact_deep (hinj := hinj) (hf := hf) (hh := hh) hc (.ctrl (.throwRefHandlerNext hm)) rfl

end Builtins

end Silmaril.Wasm.SpecTec.Institution.FwdB30D
