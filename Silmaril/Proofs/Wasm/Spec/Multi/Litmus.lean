module

public import Silmaril.Proofs.Wasm.Spec.Multi.Basic
public import Silmaril.Wasm.Spec.Litmus.Thms
public import Silmaril.Wasm.Spec.Check.Thms

@[expose] public section

/-!
# Multi-call litmus tests

* Loose semantics (`Silmaril.Wasm.Spec.Litmus`, interface `X₁` with exports `main`, `debug`):
  `debugRun_mainFirst`: in `debugRun` (`main` returns, then `debug` logs) `debug` is only called
  after `main` has returned, an export-history property of the two-call session;
  `earlyDebug_not_mainFirst`: a session calling `debug` first refutes it.
* Real Core 3.0 code (the increment function `local.get 0; i32.const 1; i32.add`, every profile):
  `incProvider_session`: in every closed-world Core session of export calls against any
  environment, every call returns a single `i32` (from `incProvider_retPost` through
  `retPost_session`).
-/

namespace Silmaril.Wasm.Spec.Multi

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Spec.Litmus
open Silmaril.Wasm.Numerics (Profile)

/-- Whether `debug` (export `1`) is only called after `main` (export `0`) has returned. -/
def mainBeforeDebug : List (SideEv (List Val) (Behaviour Val) 2) → Bool → Bool
  | [], _ => true
  | .ans i _ :: h, seen => mainBeforeDebug h (seen || i.val == 0)
  | .ask i _ :: h, seen => (i.val != 1 || seen) && mainBeforeDebug h seen

/-- The export-history formula: `debug` only after `main` has returned. -/
def mainFirst : Hist (List Val) (Behaviour Val) X₁ → Prop := fun h => mainBeforeDebug h false = true

/-- `debug` is called first. -/
def earlyDebug : List (Litmus.Ev X₁) := [.call ⟨1, by decide⟩ [], .ret ⟨1, by decide⟩ (.returns [])]

/-- A per-trace sentence about the prefixes of a list is decided by its prefixes. -/
theorem sat_prefixesOf_of_inits {X : Iface Unit} (l : List (Litmus.Ev X)) (Φ : Hist (List Val) (Behaviour Val) X → Prop)
    (h : ∀ t ∈ l.inits, Φ (exportEvents t)) :
    Models (exportHist Unit _ _) Litmus.S (progOf l) Φ := by
  rw [models_progOf_iff]
  intro t ht
  exact h t (List.mem_inits t l |>.2 ht)

theorem debugRun_mainFirst : Models (exportHist Unit _ _) Litmus.S (progOf debugRun) mainFirst := by
  refine sat_prefixesOf_of_inits debugRun mainFirst fun t ht => ?_
  have hall : debugRun.inits.all (fun t => mainBeforeDebug (exportEvents t) false) = true := rfl
  exact List.all_eq_true.1 hall t ht

theorem earlyDebug_not_mainFirst :
    ¬ Models (exportHist Unit _ _) Litmus.S (progOf earlyDebug) mainFirst := by
  rw [models_progOf_iff]
  intro h
  have hbad : mainBeforeDebug (exportEvents earlyDebug) false = false := rfl
  have hgood : mainFirst (exportEvents earlyDebug) := h earlyDebug (List.prefix_refl _)
  exact absurd (hgood.symm.trans hbad) (by decide)

open Silmaril.Wasm.Logic.GameLink.Examples (i32T)
open Silmaril.Wasm.Logic.OpenExamples (incBody)

/-- **Every call of every Core session of the increment provider returns a single `i32`**
(real Core 3.0 code, every profile, every environment). -/
theorem incProvider_session {P : Profile} {X : WIface} (p : WasmProg X) {a₁ : Nat}
    {fi₁ : FuncInst Nat} {code : Func} {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)}
    (haddr : ∀ j, p.inst.addr j = a₁) (hcode : fi₁.code = .wasm code)
    (hbody : code.body = incBody) (he : Silmaril.Wasm.Validation.Expand fi₁.type (.func ps rs))
    (hps : ps.length = 1) (hrs : rs.length = 1) (hfi : p.store.funcs[a₁]? = some fi₁)
    (hparams : ∀ j, (X.exports.get j).params = [i32T]) {K : Env (ifaceSig X.imports)}
    {l : List (Call p.inst)} (h : Session P p.inst K p.store l)
    {f : (ifaceSig X.exports).Op} {w : (ifaceSig X.exports).Ar f} (hm : ⟨f, w⟩ ∈ l) :
    ∃ m : BitVec 32, Answer.toBehaviour (ft := X.exports.get f.1) w = .returns [Val.i32 m] :=
  retPost_session p (incProvider_retPost p haddr hcode hbody he hps hrs hfi hparams f.1) h hm rfl

end Silmaril.Wasm.Spec.Multi
