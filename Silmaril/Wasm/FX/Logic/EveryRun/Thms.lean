module

public import Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Partial

/-!
# An every-run program logic for WasmFX: rules and soundness

The logic (`Silmaril.Wasm.FX.Logic.EveryRun.Defs`) has a step-indexed every-run safety predicate
`Safe` (partial correctness, `HWP`) and its inductive version `TSafe` (total correctness, `TWP`)
over `StepFX'` without host calls, for every profile and FX function table.

**Inversions of `StepFX'`** (`Silmaril.Proofs.Wasm.FX.Logic.EveryRun.{Split,Root,Stop}`):
`step_split` (a step of `V; a; R` at the first non-value `a` is a step of `V₂; a`, or a trap or an
exception cutting into `R`), `step_last` (a step of `V; a` is a root step, `Root`, under some of
the values), `no_step_blocked` (a branch or `return` at the top does not step),
`step_trapish`/`step_throwish`; values (`no_step_fvals'`) and unhandled effects
(`tsafe_suspend`) do not step.

**Rules** (total correctness; `Silmaril.Proofs.Wasm.FX.Logic.EveryRun.{Total,Derived}`):
`tsafe_seq`, `tsafe_label`, `tsafe_frame`, **`tsafe_handler`** (the handler rule),
`tsafe_inert`, `tsafe_block`, `tsafe_contNew`, **`tsafe_resume`**, `tsafe_invoke`,
`tsafe_suspend`, `tsafe_dropCont`, the terminal rules `tsafe_vals`, `tsafe_br`, `tsafe_ret`,
`tsafe_trap`, `tsafe_throw`, and the derived rules for an instruction followed by code
(`tsafe_nop`, `tsafe_refFunc`, `tsafe_i32Add`, `tsafe_call`, `tsafe_block_seq`,
`tsafe_label_seq`, `tsafe_handler_seq`, `tsafe_contNew_seq`, `tsafe_resume_seq`,
`tsafe_invoke_seq`, `tsafe_dropCont_seq`, `tsafe_suspend_seq`, `tsafe_switch_seq`).

**Step-indexed rules** (partial correctness; `Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Partial`):
`safe_mono`, `safe_post_mono`, `safe_seq`, `safe_label`, `safe_frame`, **`safe_handler`**,
`hwp_seq`, `hwp_frame`, the terminal rules `safe_vals`, `safe_br`, `safe_ret`, `safe_trap`,
`safe_throw`, and `tsafe_hwp` (total implies partial).

**Adequacy** (`Silmaril.Proofs.Wasm.FX.Logic.EveryRun.Adequacy`): `tsafe_result`/`hwp_result`
(every finished run satisfies the postcondition), `tsafe_not_infinite` (no infinite run), and
`tsafe_behaviours_eq` (exact behaviour sets).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Logic.EveryRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H}

/-- **Partial correctness**: every finished run of code with an every-run weakest precondition
satisfies the postcondition. -/
theorem HWP.result {s : Store H} {K : Conts} {f : Frame} {code : List AdminFX} {d : ConfigFX H}
    {r : Result} (h : HWP P fx s K f code Q) (hr : StepsFX' P noHost fx ⟨s, K, f, code⟩ d)
    (hd : d.code = r.toAdmin.map .core) :
    Q d.store d.conts d.frame (OutcomeFX.ofResult r) :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.hwp_result h hr hd

/-- **Total correctness**: totally safe code has no infinite run. -/
theorem TSafe.not_infinite {c : ConfigFX H} (h : TSafe P fx Q c) :
    ¬ Silmaril.InfiniteTrace (StepFX' P noHost fx) c :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_not_infinite h

/-- Total safety gives partial correctness. -/
theorem TSafe.hwp {s : Store H} {K : Conts} {f : Frame} {code : List AdminFX}
    (h : TWP P fx s K f code Q) : HWP P fx s K f code Q :=
  fun n => Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_hwp h n

/-- **Exact behaviours** from total safety and one run. -/
theorem TSafe.behaviours_eq {c : ConfigFX H} {vs₀ : List Val} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = .normal (liftV vs₀))
    (hm : Behaviour.returns vs₀ ∈ behavioursFX' P noHost fx c) :
    behavioursFX' P noHost fx c = {.returns vs₀} :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_behaviours_eq h hQ hm

/-- **The handler rule** (total correctness). -/
theorem TSafe.handler (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {hs : List HClause}
    {us : List FVal} {b : List AdminFX}
    (h : TSafe P fx (handlerPost (totJ P fx Q) hs us Q) ⟨s, K, f, b⟩) :
    TSafe P fx Q ⟨s, K, f, fvals us ++ [.handler hs b]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_handler hQ h

/-- **`resume`** (total correctness), for every payload split. -/
theorem TSafe.resume {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {k : Nat} {C : ContFX}
    {ct : TypeIdx} {hos : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs →
      TSafe P fx Q ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    TSafe P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_resume hk hr h

/-- **The handler rule** (step-indexed partial correctness): safe for `n ≤ k + 1` steps when
the code under the handler is, with the handler's postcondition continuing for `k` steps. -/
theorem Safe.handler (hQ : Inv Q) {k n : Nat} {s : Store H} {K : Conts} {f : Frame}
    {hs : List HClause} {us : List FVal} {b : List AdminFX} (hn : n ≤ k + 1)
    (h : Safe P fx (handlerPost (safeJ P fx Q k) hs us Q) n ⟨s, K, f, b⟩) :
    Safe P fx Q n ⟨s, K, f, fvals us ++ [.handler hs b]⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_handler hQ hn h

/-- **Sequencing** (step-indexed partial correctness). -/
theorem Safe.seq (hQ : Inv Q) {k n : Nat} {s : Store H} {K : Conts} {f : Frame}
    {c₁ c₂ : List AdminFX} (hn : n ≤ k) (h : Safe P fx (seqPost (safeJ P fx Q k) c₂ Q) n ⟨s, K, f, c₁⟩) :
    Safe P fx Q n ⟨s, K, f, c₁ ++ c₂⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.safe_seq hQ hn h

/-- **Sequencing** (total correctness). -/
theorem TSafe.seq (hQ : Inv Q) {s : Store H} {K : Conts} {f : Frame} {c₁ c₂ : List AdminFX}
    (h : TSafe P fx (seqPost (totJ P fx Q) c₂ Q) ⟨s, K, f, c₁⟩) :
    TSafe P fx Q ⟨s, K, f, c₁ ++ c₂⟩ :=
  Silmaril.Proofs.Wasm.FX.Logic.EveryRun.tsafe_seq' hQ h

end Silmaril.Wasm.FX.Logic.EveryRun
