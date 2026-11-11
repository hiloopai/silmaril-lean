module

public import Silmaril.Wasm.Examples.Common.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms

@[expose] public section

/-!
# Sessions from call specifications

`FSpecValid.result_post`: a Core run of `$invoke` ending in a result satisfies the
postcondition for the outcome of that result. `session_allGood`: if every export call meets
`callSpec I R next Good` under the session's host, every session from a store representing
`a` is `AllGood`. `allGood_append`: the call after a prefix is `Good` in the state the prefix
reaches.
-/

namespace Silmaril.Wasm.Examples.Common

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.Logic.Hoare (FSpec FSpecValid Exits callPost not_step_vals not_step_trap
  not_step_throwing exits_vals_inv exits_trap_inv exits_throw_inv)
open Silmaril.Wasm.Spec.Multi (Call Session)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A result is final: it cannot step. -/
theorem result_final {s : Store H} {f : Frame} {r : Result} {c' : Config H} :
    ¬ Step P host ⟨s, f, r.toAdmin⟩ c' := by
  cases r with
  | values vs => exact not_step_vals
  | trap => exact not_step_trap
  | throw a => exact not_step_throwing

/-- The outcome a result exits with. -/
theorem exits_result {o : Outcome} {r : Result} (h : Exits o r.toAdmin) : outcomeResult? o = some r := by
  cases r with
  | values vs => rw [exits_vals_inv h]; rfl
  | trap =>
    have h' : Exits o (vals [] ++ .trap :: []) := h
    rw [exits_trap_inv h']; rfl
  | throw a =>
    have h' : Exits o (vals [] ++ throwing a ++ []) := h
    rw [exits_throw_inv h']; rfl

/-- The callee's outcome inside a `callPost` of an empty caller stack. -/
theorem callPost_inner {R : Store H → Outcome → Prop} {s : Store H} {f : Frame} {o : Outcome}
    {r : Result} (hr : outcomeResult? o = some r) (h : callPost {} [] R s f o) :
    outcomeResult? o = some r ∧ R s o := by
  rcases h.2 with ⟨res, rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨a, rfl, hp⟩
  · exact ⟨hr, by simpa using hp⟩
  · exact ⟨hr, hp⟩
  · exact ⟨hr, hp⟩

/-- **A run of `$invoke` ending in a result** satisfies the postcondition at the outcome of
that result. -/
theorem FSpecValid.result_post {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    {c' : Config H} {r : Result} (h : FSpecValid P host a S) (hpre : S.pre s args)
    (hs : Steps P host (invoke s a args) c') (hc : c'.code = r.toAdmin) :
    ∃ o, outcomeResult? o = some r ∧ S.post s args c'.store o := by
  rcases Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_safe h hpre hs with ⟨c'', hst⟩ | ⟨o, he, hp⟩
  · obtain ⟨cs, cf, cc⟩ := c'
    have hc' : cc = r.toAdmin := hc
    subst hc'
    exact (result_final hst).elim
  · have hr : outcomeResult? o = some r := exits_result (hc ▸ he)
    exact ⟨o, callPost_inner hr hp⟩

/-- `bodyPost` gives the step-indexed body postcondition of a call, at every index. -/
theorem bodyPost_bodyPostK {n k : Nat} {R : Store H → Outcome → Prop} {f : Frame} {vs₀ : List Val}
    {s : Store H} {F : Frame} {o : Outcome} (h : bodyPost n R s F o) :
    Silmaril.Wasm.Logic.Hoare.bodyPostK P host n f vs₀ (callPost f vs₀ R) k s F o := by
  rcases o with res | _ | _ | _ | _ | _
  · exact ⟨by simpa using h.1, rfl, .inl ⟨res, rfl, h.2⟩⟩
  all_goals first | exact h.elim | exact ⟨rfl, .inr (.inl ⟨rfl, h⟩)⟩

/-- **A function specification from an every-run proof of the body** that returns or traps. -/
theorem FSpecValid.of_body_hwp {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {S : FSpec H}
    (hfi : ∀ s args, S.pre s args → s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hlen : ∀ s args, S.pre s args → args.length = ps.length)
    (hbody : ∀ s args, S.pre s args → Silmaril.Wasm.Logic.Hoare.HWP P host s
      (Frame.forCall fi.module args code.locals) (expression code.body)
      (bodyPost rs.length (S.post s args))) :
    FSpecValid P host a S := by
  intro n
  cases n with
  | zero => intro _ _ _ _ _ _ _; trivial
  | succ n =>
    exact Silmaril.Wasm.Logic.Hoare.FSpecAt.of_body hfi hcode he hlen fun s args hpre f vs₀ =>
      (hbody s args hpre n).post_mono fun _ _ _ h => bodyPost_bodyPostK h

variable {σ : Type}

/-- **Sessions are good**: valid call specifications under the session's host make every
call of every session `Good` in the abstract state reached before it. -/
theorem session_allGood {I : ScalarInstance} {K : Env I.E} {R : σ → Store Nat → Prop}
    {next : σ → Call I → σ} {Good : σ → Call I → Prop}
    (hspec : ∀ f : I.F.Op, FSpecValid P (hostOf I.imports K) (I.addr f.1) (callSpec I R next Good f)) :
    ∀ {s : Store Nat} {a : σ} {l : List (Call I)}, R a s → Session P I K s l → AllGood next Good a l := by
  intro s a l hR hS
  induction hS generalizing a with
  | nil => trivial
  | @cons s f w rest c' r run final ans next' ih =>
    obtain ⟨o, hr, hp⟩ := FSpecValid.result_post (hspec f) ⟨rfl, a, hR⟩ run final
    obtain ⟨hg, hR'⟩ := hp a hR r hr w ans
    exact ⟨hg, ih hR'⟩

/-- The call after a prefix is good in the state the prefix reaches. -/
theorem allGood_append {I : ScalarInstance} {next : σ → Call I → σ} {Good : σ → Call I → Prop} :
    ∀ {a : σ} {l₁ : List (Call I)} {c : Call I} {l₂ : List (Call I)},
      AllGood next Good a (l₁ ++ c :: l₂) → Good (after next a l₁) c
  | _, [], _, _, h => h.1
  | _, _ :: l₁, _, _, h => allGood_append (l₁ := l₁) h.2

end Silmaril.Wasm.Examples.Common
