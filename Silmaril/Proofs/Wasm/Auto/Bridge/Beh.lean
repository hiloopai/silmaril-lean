module

public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Behaviour.Refinement.Interpreter
public import Silmaril.Wasm.Auto.Front.Defs

/-!
# From total specifications to behaviour sets

`behaviours_eq_of_tfspec`: a total specification (`TFSpecAt`, the every-run total-correctness
logic of `docs/projects/wasm-binaryen-tooling.md`) whose postcondition pins the outcome to returning `rs` makes the
behaviour set of `$invoke` exactly `{returns rs}`: no divergence (`TFSpecAt.invoke_terminates`),
no other result (adequacy), and one run that returns (the inductive `TSafe`). The relations of
the front end follow from such singletons (`exportRefines_of_singleton`, `meets_of_singleton`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- A totally safe configuration has a run to an exit satisfying the postcondition. -/
theorem TSafe.exists_exit {Q : Post H} {c : Config H} (h : TSafe P host Q c) :
    ∃ c' o, Steps P host c c' ∧ Exits o c'.code ∧ Q c'.store c'.frame o := by
  induction h with
  | exit o he hq => exact ⟨_, o, .refl, he, hq⟩
  | step hp _ ih =>
    obtain ⟨c₁, h₁⟩ := hp
    obtain ⟨c', o, hs, he, hq⟩ := ih c₁ h₁
    exact ⟨c', o, Relation.ReflTransGen.head h₁ hs, he, hq⟩

/-- A result whose code is `vals rs` returns `rs`. -/
theorem result_eq_of_vals {r : Result} {rs : List Val} (h : r.toAdmin = vals rs) :
    r = .values rs := by
  have h₁ := SingleThreaded.Exec.BehaviourRefinement.codeOutcome?_toAdmin r
  have h₂ := SingleThreaded.Exec.BehaviourRefinement.codeOutcome?_toAdmin (.values rs)
  rw [h] at h₁
  exact Option.some.inj (h₁.symm.trans h₂)

/-- An outcome of the call postcondition at the top level, under a postcondition that only
allows returning `rs`. -/
theorem callPost_ret {R : Store H → Outcome → Prop} {rs : List Val}
    (hR : ∀ s o, R s o → o = .normal rs) {s : Store H} {f : Frame} {o : Outcome}
    (h : callPost {} [] R s f o) : o = .normal rs := by
  obtain ⟨-, ⟨res, rfl, hr⟩ | ⟨rfl, hr⟩ | ⟨a, rfl, hr⟩⟩ := h
  · simpa using hR _ _ hr
  · exact Outcome.noConfusion (hR _ _ hr)
  · exact Outcome.noConfusion (hR _ _ hr)

/-- A finite run of `$invoke` to a result, under a valid specification pinning the result,
returns `rs`. -/
theorem returns_of_run {a : Nat} {S : FSpec H} {s : Store H} {args rs : List Val}
    (h : FSpecValid P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal rs) {c' : Config H} {r : Result}
    (hs : Steps P SingleThreaded.Det.noHost (invoke s a args) c') (hfin : c'.code = r.toAdmin) :
    r = .values rs := by
  have hw : HWP P SingleThreaded.Det.noHost s {} (invoke s a args).code
      (callPost {} [] (S.post s args)) := h.hwp_invoke hpre
  have hs' : Steps P SingleThreaded.Det.noHost ⟨s, {}, (invoke s a args).code⟩ c' := by
    rw [invoke_code] at hs ⊢
    exact hs
  have hex : ∃ o, Exits o c'.code ∧ callPost {} [] (S.post s args) c'.store c'.frame o := by
    rcases hw.sound hs' with ⟨c'', hc⟩ | hex
    · exact absurd hc (SingleThreaded.Exec.BehaviourRefinement.not_step_of_terminal ⟨r, hfin⟩)
    · exact hex
  obtain ⟨o, he, hq⟩ := hex
  have ho : o = .normal rs := callPost_ret hpost hq
  have he' : Exits (.normal rs) c'.code := ho ▸ he
  have hv : r.toAdmin = vals rs := hfin.symm.trans he'
  exact result_eq_of_vals hv

/-- Under a total specification pinning the result, every behaviour returns `rs`. -/
theorem behaviours_sub_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args rs : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal rs) :
    behaviours P SingleThreaded.Det.noHost s a args ⊆ {.returns rs} := by
  intro b hb
  by_cases hd : b = .diverges
  · have hdiv : Diverges P SingleThreaded.Det.noHost (invoke s a args) :=
      diverges_mem_behavioursOf_iff.mp (hd ▸ hb)
    exact absurd hdiv (h.invoke_terminates hpre)
  · obtain ⟨c', r, hs, hfin, hbr⟩ : ∃ (c' : Config H) (r : Result),
        Steps P SingleThreaded.Det.noHost (invoke s a args) c' ∧ c'.code = r.toAdmin ∧
          b = r.toBehaviour := exists_result_of_mem hb hd
    have hr : r = .values rs := returns_of_run h.valid hpre hpost hs hfin
    show b = .returns rs
    rw [hbr, hr]
    rfl

/-- Under a total specification pinning the result, `$invoke` has a run that returns `rs`. -/
theorem returns_mem_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args rs : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal rs) :
    Behaviour.returns rs ∈ behaviours P SingleThreaded.Det.noHost s a args := by
  have ht : TSafe P SingleThreaded.Det.noHost (callPost {} [] (S.post s args))
      ⟨s, {}, vals [] ++ vals args ++
        [.ref (.func a), .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]⟩ :=
    h s args hpre {} [] _ trivial
  obtain ⟨c', o, hs, he, hq⟩ := TSafe.exists_exit ht
  have ho : o = .normal rs := callPost_ret hpost hq
  have he' : Exits (.normal rs) c'.code := ho ▸ he
  exact returns_mem_behavioursOf (by rw [invoke_code]; exact hs) he'

/-- **The behaviour set of a function with a total specification that pins the result**
(host-free). -/
theorem behaviours_eq_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args rs : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal rs) :
    behaviours P SingleThreaded.Det.noHost s a args = {.returns rs} :=
  Set.Subset.antisymm (behaviours_sub_of_tfspec h hpre hpost)
    (Set.singleton_subset_iff.mpr (returns_mem_of_tfspec h hpre hpost))

/-! ## Relations from singletons -/

open Silmaril.Wasm.Auto.Front (ExportRefines)

/-- Two singleton behaviour sets, equal on every accepted argument list, give refinement for
any reflexive relation. -/
theorem exportRefines_of_singleton {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b) {s₁ s₂ : Store Nat} {a₁ a₂ : Nat} (g : List Val → List Val)
    (h₁ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₁ a₁ vs =
      {.returns (g vs)})
    (h₂ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₂ a₂ vs =
      {.returns (g vs)}) :
    ExportRefines R P s₁ a₁ s₂ a₂ := by
  intro vs hvs b hb
  rw [h₁ vs hvs] at hb
  refine ⟨b, ?_, hR b⟩
  rw [h₂ vs hvs]
  exact hb

end Silmaril.Proofs.Wasm.Auto.Bridge