module

public import Silmaril.Wasm.FX.Logic.Typed.Defs
public import Silmaril.Wasm.FX.Logic.EveryRun.Instr.Thms
public import Silmaril.Wasm.Models.FXResumeT.Thms

/-!
# The every-run WasmFX logic for typed `resume`: transfer, typed rules, adequacy

* **Transfer** (`safe_toR`, `tsafe_toR`): every `StepFXR` step is a `StepFX'` step
  (`stepFXR_incl`, `stepFXT_incl`), so code safe under `StepFX'` is safe under `StepFXR`: every
  rule of `Silmaril.Wasm.FX.Logic.EveryRun` holds for typed `resume` through it.
* **The typed `resume` rules** (`tsafeR_resume`, `safeR_resume`): under `StepFXR` a `resume` asks
  only for the split whose arguments have the continuation type's arity (`ResumeArity`), through
  `step_resumeR`; under `StepFX'` (`tsafe_resume`) every split.
* **Adequacy** (`tsafeR_result`, `hwpR_result`, `tsafeR_not_infinite`, `tsafeR_behaviours_eq`)
  for `behavioursFXR`, and `tsafe_behavioursR_eq`: a `StepFX'` proof with a typed run gives the
  exact `StepFXR` behaviour set.

Open: the context rules (sequence, label, frame, handler) for `TSafeR`/`SafeR` directly; they need
the `StepFXR` versions of the inversions `step_split` and `step_last`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Logic.Typed

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXResumeT (StepFXR StepsFXR behavioursFXR)
open Silmaril.Wasm.Models.FXResume (ResumeArity)
open Silmaril.Wasm.FX.Logic (OutcomeFX PostFX Conts)
open Silmaril.Wasm.FX.Logic.EveryRun (Stops Safe TSafe)
open Silmaril.Wasm.FX.Logic.Typed
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun (stops_notStop NotStop stops_ofResult ofResult_inj
  ofResult_normal)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX} {Q : PostFX H}

/-- Every typed step is a `StepFX'` step. -/
theorem stepR_toV {c c' : ConfigFX H} (h : StepFXR P noHost fx c c') : StepFX' P noHost fx c c' :=
  Silmaril.Proofs.Wasm.Models.FXBindT.stepFXT_incl (Silmaril.Proofs.Wasm.Models.FXResumeT.stepFXR_incl h)

/-! ## Transfer -/

/-- **Safety under `StepFX'` gives safety under typed `resume`.** -/
theorem safe_toR : ∀ {n : Nat} {c : ConfigFX H}, Safe P fx Q n c → SafeR P fx Q n c
  | 0, _, _ => trivial
  | _ + 1, _, h => ⟨h.1, fun c' hs => safe_toR (h.2 c' (stepR_toV hs))⟩

/-- **Total safety under `StepFX'` gives total safety under typed `resume`.** -/
theorem tsafe_toR {c : ConfigFX H} (h : TSafe P fx Q c) : TSafeR P fx Q c := by
  induction h with
  | intro hq _ ih => exact .intro hq fun c' hs => ih c' (stepR_toV hs)

/-! ## Typed `resume` -/

theorem notStop_resume {ct : TypeIdx} {hos : List OnClause} : NotStop (.fx (.resume ct hos)) :=
  ⟨rfl, id, by simp, by simp, by simp, by simp, by simp, by simp⟩

theorem resume_code {V : List FVal} {k : Nat} {ct : TypeIdx} {hos : List OnClause} :
    fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)] =
      fvals V ++ .contRef k :: .fx (.resume ct hos) :: [] := by
  simp [fvals, FVal.toAdmin]

/-- The successors of a typed `resume` of a live continuation. -/
theorem resumeR_succ {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {k : Nat} {C : ContFX}
    {ct : TypeIdx} {hos : List OnClause} {hs' : List HClause} (hk : K[k]? = some (some C))
    (hr : hos.mapM (resolve s f) = some hs') {y : ConfigFX H}
    (hy : StepFXR P noHost fx ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ y) :
    ∃ V₁ vs, V = V₁ ++ vs ∧ ResumeArity f.module ct vs.length ∧
      y = ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩ := by
  obtain ⟨V₁, V₂, hV, hA, hres⟩ :=
    Silmaril.Proofs.Wasm.Models.FXResumeT.step_resumeR hy V k ct hos [] resume_code
  rcases hres with ⟨C', hs'', hk', hr', hy'⟩ | ⟨hk', -⟩
  · obtain rfl : C' = C := by simpa [hk] using hk'.symm
    obtain rfl : hs'' = hs' := by simpa [hr] using hr'.symm
    exact ⟨V₁, V₂, hV, hA, hy'⟩
  · simp [hk] at hk'

/-- **Typed `resume`** (total correctness): only the typed split. -/
theorem tsafeR_resume {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {hos : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs → ResumeArity f.module ct vs.length →
      TSafeR P fx Q ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    TSafeR P fx Q ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ := by
  refine .intro (fun o ho => ?_) fun y hy => ?_
  · exact stops_notStop (Q := Q) (K := K) (V := V ++ [.cont k]) (R := []) notStop_resume o ho
  · obtain ⟨V₁, vs, hV, hA, rfl⟩ := resumeR_succ hk hr hy
    exact h V₁ vs hV hA

/-- **Typed `resume`** (step-indexed): only the typed split. -/
theorem safeR_resume {n : Nat} {s : Store H} {K : Conts} {f : Frame} {V : List FVal} {k : Nat}
    {C : ContFX} {ct : TypeIdx} {hos : List OnClause} {hs' : List HClause}
    (hk : K[k]? = some (some C)) (hr : hos.mapM (resolve s f) = some hs')
    (h : ∀ V₁ vs, V = V₁ ++ vs → ResumeArity f.module ct vs.length →
      SafeR P fx Q n ⟨s, K.set k none, f, fvals V₁ ++ [.handler hs' (C.plug (fvals vs))]⟩) :
    SafeR P fx Q (n + 1) ⟨s, K, f, fvals (V ++ [.cont k]) ++ [.fx (.resume ct hos)]⟩ := by
  refine ⟨fun o ho => ?_, fun y hy => ?_⟩
  · exact stops_notStop (Q := Q) (K := K) (V := V ++ [.cont k]) (R := []) notStop_resume o ho
  · obtain ⟨V₁, vs, hV, hA, rfl⟩ := resumeR_succ hk hr hy
    exact h V₁ vs hV hA

/-! ## Adequacy -/

theorem TSafeR.steps' {c d : ConfigFX H} (h : TSafeR P fx Q c) (hr : StepsFXR P noHost fx c d) :
    TSafeR P fx Q d := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => cases ih with | intro _ hs' => exact hs' _ hs

theorem safeR_steps {c d : ConfigFX H} (h : ∀ n, SafeR P fx Q n c)
    (hr : StepsFXR P noHost fx c d) : ∀ n, SafeR P fx Q n d := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact fun n => (ih (n + 1)).2 _ hs

/-- **Total correctness**: every finished typed run satisfies the postcondition. -/
theorem tsafeR_result {c d : ConfigFX H} {r : Result} (h : TSafeR P fx Q c)
    (hr : StepsFXR P noHost fx c d) (hd : d.code = r.toAdmin.map .core) :
    Q d.store d.conts d.frame (OutcomeFX.ofResult r) := by
  cases TSafeR.steps' h hr with
  | intro hq _ => exact hq _ (hd ▸ stops_ofResult d.store d.frame r)

/-- **Partial correctness**: every finished typed run satisfies the postcondition. -/
theorem hwpR_result {s : Store H} {K : Conts} {f : Frame} {code : List AdminFX} {d : ConfigFX H}
    {r : Result} (h : HWPR P fx s K f code Q) (hr : StepsFXR P noHost fx ⟨s, K, f, code⟩ d)
    (hd : d.code = r.toAdmin.map .core) : Q d.store d.conts d.frame (OutcomeFX.ofResult r) :=
  (safeR_steps h hr 1).1 _ (hd ▸ stops_ofResult d.store d.frame r)

/-- **No infinite typed run.** -/
theorem tsafeR_not_infinite {c : ConfigFX H} (h : TSafeR P fx Q c) :
    ¬ Silmaril.InfiniteTrace (StepFXR P noHost fx) c := by
  induction h with
  | intro _ _ ih =>
    intro hi
    obtain ⟨b, hb, hi'⟩ := hi.unfold
    exact ih b hb hi'

/-- **Exact typed behaviours** from total safety and one typed run. -/
theorem tsafeR_behaviours_eq {c : ConfigFX H} {r₀ : Result} (h : TSafeR P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFXR P noHost fx c) :
    behavioursFXR P noHost fx c = {r₀.toBehaviour} := by
  ext b
  refine ⟨fun hb => ?_, fun hb => (Set.mem_singleton_iff.mp hb) ▸ hm⟩
  rcases hb with ⟨d, r, hr, hd, rfl⟩ | ⟨-, hi⟩
  · rw [ofResult_inj (hQ _ _ _ _ (tsafeR_result h hr hd))]
    rfl
  · exact (tsafeR_not_infinite h hi).elim

/-- **Every typed behaviour is the intended one**, from total safety under `StepFX'` alone. -/
theorem tsafe_behavioursR_sub {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀) :
    behavioursFXR P noHost fx c ⊆ {r₀.toBehaviour} := by
  intro b hb
  rcases hb with ⟨d, r, hr, hd, rfl⟩ | ⟨-, hi⟩
  · rw [ofResult_inj (hQ _ _ _ _ (tsafeR_result (tsafe_toR h) hr hd))]
    rfl
  · exact (tsafeR_not_infinite (tsafe_toR h) hi).elim

/-- **Exact typed behaviours from an untyped proof**: total safety under `StepFX'` and one
typed run. -/
theorem tsafe_behavioursR_eq {c : ConfigFX H} {r₀ : Result} (h : TSafe P fx Q c)
    (hQ : ∀ s K f o, Q s K f o → o = OutcomeFX.ofResult r₀)
    (hm : r₀.toBehaviour ∈ behavioursFXR P noHost fx c) :
    behavioursFXR P noHost fx c = {r₀.toBehaviour} :=
  tsafeR_behaviours_eq (tsafe_toR h) hQ hm

end Silmaril.Proofs.Wasm.FX.Logic.Typed
