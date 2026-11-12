module

public import Silmaril.Proofs.Wasm.Interp.Lag
public import Silmaril.Proofs.Wasm.Interp.Obligations

@[expose] public section

/-!
# Weak normalisation implies strong normalisation for typed invocations (proofs)

`no_infinite_of_lag` (abstract): for a subcommutative relation (`Det.Join` of any two
successors) with an executable step `g` that every successor reaches in at most one step and
that every other successor undercuts in a measure `μ`, a state that reaches a normal form has no
infinite trace. The measure decreasing along every step is the pair (shortest distance to a
normal form, `μ`) in the lexicographic order: the distance never grows along a step
(subcommutativity), drops along `g`, and other steps shrink `μ`.

`noDivOfTerm_typed`: for silmaril-lean's host-free Core reduction in the deterministic profile
(`Det.DStep.join'`, `stepI_maximal`, `stepI_lag_typed` with `μ` the size of the code), a typed
invocation that reaches a result has no infinite trace — silmaril-lean's `NoDivOfTerm`, at every
deterministic profile, for every typed invocation (any instructions). `noDivOfTerm_native`: at
**every** profile on native-profile stores, by profile independence. New proofs. Summary in
`Silmaril.Wasm.Interp.Thms`.
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Exec

/-! ## The abstract argument -/

section Abstract

variable {α : Type _} {R : α → α → Prop}

/-- `a` reaches a normal form in exactly `k` steps along some path. -/
inductive ReachNF (R : α → α → Prop) : Nat → α → Prop where
  | zero {a : α} (h : ∀ x, ¬ R a x) : ReachNF R 0 a
  | succ {a b : α} {k : Nat} (h : R a b) (hb : ReachNF R k b) : ReachNF R (k + 1) a

theorem reachNF_of_steps {a b : α} (h : Relation.ReflTransGen R a b) (hb : ∀ x, ¬ R b x) :
    ∃ k, ReachNF R k a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .zero hb⟩
  | head hab _ ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, .succ hab hk⟩

variable (hjoin : ∀ a b c, R a b → R a c → Det.Join R b c)
include hjoin

/-- The distance to a normal form never grows along a step. -/
theorem ReachNF.step_le {k : Nat} {a : α} (h : ReachNF R k a) :
    ∀ {b}, R a b → ∃ j ≤ k, ReachNF R j b := by
  induction h with
  | zero h => exact fun hab => absurd hab (h _)
  | @succ a a₁ k ha₁ _ ih =>
    intro b hab
    obtain ⟨x, h₁, h₂⟩ := hjoin a a₁ b ha₁ hab
    obtain ⟨j', hj', hx⟩ : ∃ j' ≤ k, ReachNF R j' x := by
      cases h₁ with
      | refl => exact ⟨k, le_rfl, ‹_›⟩
      | single h => exact ih h
    cases h₂ with
    | refl => exact ⟨j', by omega, hx⟩
    | single h => exact ⟨j' + 1, by omega, .succ h hx⟩

theorem ReachNF.reflGen_le {k : Nat} {a b : α} (h : ReachNF R k a)
    (hab : Relation.ReflGen R a b) : ∃ j ≤ k, ReachNF R j b := by
  cases hab with
  | refl => exact ⟨k, le_rfl, h⟩
  | single hab => exact h.step_le hjoin hab

omit hjoin in
/-- The executable step of a state that reaches a normal form is closer to one. -/
theorem ReachNF.of_max (hjoin : ∀ a b c, R a b → R a c → Det.Join R b c) {k : Nat} {a d : α}
    (h : ReachNF R (k + 1) a) (hmax : ∀ b, R a b → Relation.ReflGen R b d) :
    ∃ j ≤ k, ReachNF R j d := by
  cases h with
  | succ ha₁ h₁ => exact h₁.reflGen_le hjoin (hmax _ ha₁)

end Abstract

section Lex

variable {α : Type _} {R : α → α → Prop} (I : α → Prop) (g : α → Option α) (μ : α → Nat)
  (hjoin : ∀ a b c, R a b → R a c → Det.Join R b c) (hI : ∀ a b, I a → R a b → I b)
  (hcomp : ∀ a b, I a → R a b → ∃ d, g a = some d)
  (hmax : ∀ a b d, I a → R a b → g a = some d → Relation.ReflGen R b d)
  (hlag : ∀ a b d, I a → R a b → g a = some d → b = d ∨ μ b < μ a)
include hjoin hI hcomp hmax hlag

/-- One step of the lexicographic descent, at a fixed distance `k`. -/
theorem no_infinite_at {k : Nat}
    (ihk : ∀ j < k, ∀ a, I a → ReachNF R j a → ¬ Silmaril.InfiniteTrace R a) :
    ∀ m a, μ a = m → I a → ReachNF R k a → ¬ Silmaril.InfiniteTrace R a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro a hm ha hr hinf
  obtain ⟨b, hab, hinfb⟩ := hinf.unfold
  obtain ⟨d, hd⟩ := hcomp a b ha hab
  have hb : I b := hI a b ha hab
  obtain ⟨j, hj, hrb⟩ := hr.step_le hjoin hab
  rcases hlag a b d ha hab hd with rfl | hlt
  · cases hr with
    | zero h => exact h _ hab
    | @succ _ a₁ k' ha₁ h₁ =>
      obtain ⟨j', hj', hr'⟩ := (ReachNF.succ ha₁ h₁).of_max hjoin
        (fun b' hb' => hmax a b' b ha hb' hd)
      exact ihk j' (by omega) b hb hr' hinfb
  · rcases Nat.lt_or_eq_of_le hj with hjk | rfl
    · exact ihk j hjk b hb hrb hinfb
    · exact ihm (μ b) (hm ▸ hlt) b rfl hb hrb hinfb

/-- **Weak normalisation implies strong normalisation**, abstractly. -/
theorem no_infinite_of_lag : ∀ k a, I a → ReachNF R k a → ¬ Silmaril.InfiniteTrace R a := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro a ha hr
  exact no_infinite_at I g μ hjoin hI hcomp hmax hlag ihk (μ a) a rfl ha hr

end Lex

/-! ## Typed invocations -/

variable {H : Type}

/-- **No divergence after termination**, for typed configurations, deterministic profiles. -/
theorem not_diverges_typed {o : GrowOracle} {ts : List Validation.CValType} {c c' : Config H}
    (hc : ConfigOk c ts) (hst : Steps (profile o) Det.noHost c c')
    (hnf : ∀ x, ¬ Step (profile o) Det.noHost c' x) : ¬ Diverges (profile o) Det.noHost c := by
  obtain ⟨k, hk⟩ := reachNF_of_steps hst hnf
  refine no_infinite_of_lag (fun c : Config H => ConfigOk c ts) (stepI o)
    (fun c : Config H => sizeOf c.code) (fun _ _ _ h₁ h₂ => Det.DStep.join' h₁ h₂)
    (fun _ _ ha hab => typedInv'.pres _ _ ha hab) ?_ ?_ ?_ k c hc hk
  · intro a b ha hab
    have := stepI_complete_typed (o := o) ha hab
    exact Option.isSome_iff_exists.mp this
  · intro a b d ha hab hd
    exact stepI_maximal (ConfigOk.storeOk ha) (ConfigOk.deepAll_iHeadInv ha) hab hd
  · intro a b d ha hab hd
    exact (stepI_lag_typed ha hab hd).imp_right (·.1)

/-- **`NoDivOfTerm` for typed invocations**, every deterministic profile. -/
theorem noDivOfTerm_typed {o : GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hok : InvokeOk s a vs) :
    Binaryen.NoDivOfTerm (profile o) s a vs := by
  rintro ⟨c, hst, r, hr⟩
  obtain ⟨-, -, rs, -, -, hc⟩ := invoke_ok hs hok
  exact not_diverges_typed hc hst
    (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨r, hr⟩ hx)

/-- **`NoDivOfTerm` at every profile** on typed invocations of native-profile stores. -/
theorem noDivOfTerm_native {P : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs) (hok : InvokeOk s a vs) :
    Binaryen.NoDivOfTerm P s a vs :=
  (noDivOfTerm_profile_iff hF).mp (noDivOfTerm_typed (o := fun _ _ _ _ => false) hs hok)

/-- `BwdSim` at every profile from `DivSim` alone. -/
theorem bwdSim_of_divSim {P P' : Profile} {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (div : Binaryen.DivSim P' s a vs) : Binaryen.BwdSim P s a vs :=
  bwdSim_of_storeChk hF hS hok div (noDivOfTerm_native (P := P') hs hF hok)

/-- Native behaviours are Core behaviours at every profile, from `DivSim` alone. -/
theorem behaviours_eq_nbeh_of_divSim {P P' : Profile} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hF : Binaryen.NativeFuncsOk s.funcs) (hS : StoreChk s.funcs)
    (hok : InvokeOk s a vs) (div : Binaryen.DivSim P' s a vs) :
    behaviours P Binaryen.closedHost s a vs = Binaryen.nbeh s a vs :=
  behaviours_eq_nbeh hs hF hS hok div (noDivOfTerm_native (P := P') hs hF hok)

end Silmaril.Wasm.Interp
