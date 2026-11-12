module

public import Silmaril.Proofs.Wasm.Auto.Bridge.All
public import Silmaril.Proofs.Wasm.Auto.Bridge.Partial

/-!
# Total specifications that pin a trap

`behaviours_eq_trap_of_tfspec`: a total specification (`TFSpecAt`) whose postcondition pins the
outcome to a trap makes the host-free behaviour set of `$invoke` exactly `{traps}` (the companion
of `Silmaril.Proofs.Wasm.Auto.Bridge.behaviours_eq_of_tfspec` for returning functions);
`behaviours_eq_res_of_tfspec`: both, for a result that returns or traps.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {H : Type} {P : Profile}

theorem trap_not_mem_vals (vs : List Val) : Admin.trap ∉ vals vs := by
  simp only [vals, List.mem_map, not_exists, not_and]
  intro v _ h
  rcases v with ⟨_ | _, _⟩ | _ | _ <;> simp [Val.toAdmin] at h

/-- A result whose code exits with a trap is the trap. -/
theorem result_eq_trap {r : Result} {vs : List Val} {rest : List Admin}
    (h : r.toAdmin = vals vs ++ .trap :: rest) : r = .trap := by
  rcases r with rs | a | _
  · have hm : Admin.trap ∈ vals rs := by
      rw [show (Result.values rs).toAdmin = vals rs from rfl] at h
      rw [h]
      simp
    exact absurd hm (trap_not_mem_vals rs)
  · exfalso
    have hm : Admin.trap ∈ Result.toAdmin (.throw a) := by rw [h]; simp
    simp [Result.toAdmin] at hm
  · rfl

/-- An outcome of the call postcondition at the top level, under a postcondition that only
allows a trap. -/
theorem callPost_trap {R : Store H → Outcome → Prop} (hR : ∀ s o, R s o → o = .trap)
    {s : Store H} {f : Frame} {o : Outcome} (h : callPost {} [] R s f o) : o = .trap := by
  obtain ⟨-, ⟨res, rfl, hr⟩ | ⟨rfl, -⟩ | ⟨a, rfl, hr⟩⟩ := h
  · exact Outcome.noConfusion (hR _ _ hr)
  · rfl
  · exact Outcome.noConfusion (hR _ _ hr)

/-- A finite run of `$invoke` to a result, under a valid specification pinning a trap, traps. -/
theorem trap_of_run {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : FSpecValid P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .trap) {c' : Config H} {r : Result}
    (hs : Steps P SingleThreaded.Det.noHost (invoke s a args) c') (hfin : c'.code = r.toAdmin) :
    r = .trap := by
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
  have ho : o = .trap := callPost_trap hpost hq
  subst ho
  obtain ⟨vs, rest, hc⟩ := he
  exact result_eq_trap (hfin.symm.trans hc)

/-- Under a total specification pinning a trap, every behaviour traps. -/
theorem behaviours_sub_trap_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .trap) :
    behaviours P SingleThreaded.Det.noHost s a args ⊆ {.traps} := by
  intro b hb
  by_cases hd : b = .diverges
  · have hdiv : Diverges P SingleThreaded.Det.noHost (invoke s a args) :=
      diverges_mem_behavioursOf_iff.mp (hd ▸ hb)
    exact absurd hdiv (h.invoke_terminates hpre)
  · obtain ⟨c', r, hs, hfin, hbr⟩ : ∃ (c' : Config H) (r : Result),
        Steps P SingleThreaded.Det.noHost (invoke s a args) c' ∧ c'.code = r.toAdmin ∧
          b = r.toBehaviour := exists_result_of_mem hb hd
    have hr : r = .trap := trap_of_run h.valid hpre hpost hs hfin
    show b = .traps
    rw [hbr, hr]
    rfl

/-- A configuration that exits with a trap reaches the trapped configuration. -/
theorem steps_trap {c : Config H} {vs : List Val} {rest : List Admin}
    (hc : c.code = vals vs ++ .trap :: rest) :
    ∃ c' : Config H, Steps P SingleThreaded.Det.noHost c c' ∧ c'.code = [.trap] := by
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · refine ⟨⟨c.store, c.frame, [.trap]⟩, Relation.ReflTransGen.single ?_, rfl⟩
    have e : c = ⟨c.store, c.frame, vals vs ++ [.trap] ++ rest⟩ := by
      rcases c with ⟨s, f, code⟩
      simp only at hc
      simp [hc]
    rw [e]
    exact Step.trapInstrs hne
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨rfl, rfl⟩ := hne
    exact ⟨c, .refl, by simpa [vals] using hc⟩

/-- Under a total specification pinning a trap, `$invoke` has a run that traps. -/
theorem traps_mem_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .trap) :
    Behaviour.traps ∈ behaviours P SingleThreaded.Det.noHost s a args := by
  have ht : TSafe P SingleThreaded.Det.noHost (callPost {} [] (S.post s args))
      ⟨s, {}, vals [] ++ vals args ++
        [.ref (.func a), .callRefType ((s.funcs[a]?.map FuncInst.type).getD default)]⟩ :=
    h s args hpre {} [] _ trivial
  obtain ⟨c', o, hs, he, hq⟩ := TSafe.exists_exit ht
  have ho : o = .trap := callPost_trap hpost hq
  subst ho
  obtain ⟨vs, rest, hc⟩ := he
  obtain ⟨c'', hs'', hc''⟩ := steps_trap (P := P) hc
  exact traps_mem_behavioursOf (by rw [invoke_code]; exact hs.trans hs'') hc''

/-- **The behaviour set of a function with a total specification that pins a trap**
(host-free). -/
theorem behaviours_eq_trap_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    (h : TFSpecAt P SingleThreaded.Det.noHost a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .trap) :
    behaviours P SingleThreaded.Det.noHost s a args = {.traps} :=
  Set.Subset.antisymm (behaviours_sub_trap_of_tfspec h hpre hpost)
    (Set.singleton_subset_iff.mpr (traps_mem_of_tfspec h hpre hpost))

/-- **The behaviour set of a function whose total specification pins a result** that returns
or traps. -/
theorem behaviours_eq_res_of_tfspec {a : Nat} {S : FSpec H} {s : Store H} {args : List Val}
    {r : Result} (hr : ∀ x, r ≠ .throw x) (h : TFSpecAt P SingleThreaded.Det.noHost a S)
    (hpre : S.pre s args) (hpost : ∀ s' o, S.post s args s' o → o = resOutcome r) :
    behaviours P SingleThreaded.Det.noHost s a args = {r.toBehaviour} := by
  rcases r with rs | x | _
  · exact behaviours_eq_of_tfspec h hpre hpost
  · exact absurd rfl (hr x)
  · exact behaviours_eq_trap_of_tfspec h hpre hpost

end Silmaril.Proofs.Wasm.Auto.Bridge