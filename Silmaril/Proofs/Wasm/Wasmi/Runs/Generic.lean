module

public import Silmaril.Wasm.Atlas.Variant.Defs

/-!
# Behaviour sets read off the successors (proofs)

Generic facts about `Silmaril.Wasm.Atlas.Variant.behavioursR`, for any step relation:

* `behavioursR_succ`: at a configuration that is not a result, the behaviours are the union of
  the behaviours of its successors (given as a predicate `Q`, `R c c' ↔ Q c'`);
* `behavioursR_vals`: a stuck configuration of values `vs` has exactly the behaviour
  `returns vs`;
* `not_mem_vals`, `vals_ne_toAdmin`, `frame_ne_toAdmin`: list facts used to show that a code
  is not a result.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Runs

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas.Variant

variable {H : Type}

/-- A non-value is not among the values. -/
theorem not_mem_vals {a : Admin} (ha : a.val? = none) (vs : List Val) : a ∉ vals vs := by
  intro h
  simp only [vals, List.mem_map] at h
  obtain ⟨v, -, rfl⟩ := h
  simp at ha

/-- `vals` is injective. -/
theorem vals_inj : ∀ {vs ws : List Val}, vals vs = vals ws → vs = ws
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [vals] at h
  | _ :: _, [], h => by simp [vals] at h
  | v :: vs, w :: ws, h => by
    simp only [vals, List.map_cons, List.cons.injEq] at h
    have hv : v = w := by
      have := congrArg Admin.val? h.1
      simpa using this
    rw [hv, vals_inj h.2]

/-- A code containing a non-value is not a result of values. -/
theorem vals_ne_of_mem {a : Admin} {code : List Admin} (ha : a.val? = none) (hm : a ∈ code)
    (vs : List Val) : code ≠ vals vs := by
  rintro rfl
  exact not_mem_vals ha vs hm

/-- The code of a configuration with a value result determines the result. -/
theorem toAdmin_vals {vs : List Val} {r : Result} (h : vals vs = r.toAdmin) :
    r = .values vs := by
  cases r with
  | values ws => exact congrArg Result.values (vals_inj h).symm
  | throw a =>
    exact absurd (h ▸ (by simp [Result.toAdmin]) : Admin.plain .throwRef ∈ vals vs)
      (not_mem_vals (by simp [Admin.val?]) vs)
  | trap =>
    exact absurd (h ▸ (by simp [Result.toAdmin]) : Admin.trap ∈ vals vs)
      (not_mem_vals (by simp [Admin.val?]) vs)

/-- A single frame is not a result. -/
theorem frame_ne_toAdmin (n : Nat) (F : Frame) (b : List Admin) (r : Result) :
    [Admin.frame n F b] ≠ r.toAdmin := by
  cases r with
  | values vs =>
    exact vals_ne_of_mem (a := .frame n F b) (by simp [Admin.val?]) (by simp) vs
  | throw a => simp [Result.toAdmin]
  | trap => simp [Result.toAdmin]

/-- **The behaviours at a non-result are those of its successors.** -/
theorem behavioursR_succ {R : Config H → Config H → Prop} {c : Config H} (Q : Config H → Prop)
    (hnt : ∀ r : Result, c.code ≠ r.toAdmin) (hs : ∀ c', R c c' ↔ Q c') :
    behavioursR R c = {b | ∃ c', Q c' ∧ b ∈ behavioursR R c'} := by
  ext b
  constructor
  · rintro (⟨d, r, hrt, hc, rfl⟩ | ⟨rfl, hinf⟩)
    · rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c', h, hrest⟩
      · exact absurd hc (hnt r)
      · exact ⟨c', (hs c').1 h, .inl ⟨d, r, hrest, hc, rfl⟩⟩
    · obtain ⟨c', h, hinf'⟩ := hinf.unfold
      exact ⟨c', (hs c').1 h, .inr ⟨rfl, hinf'⟩⟩
  · rintro ⟨c', hq, hb⟩
    have h := (hs c').2 hq
    rcases hb with ⟨d, r, hrt, hc, rfl⟩ | ⟨rfl, hinf⟩
    · exact .inl ⟨d, r, .head h hrt, hc, rfl⟩
    · exact .inr ⟨rfl, hinf.fold h⟩

/-- At a non-result with exactly one successor, the behaviours are the successor's. -/
theorem behavioursR_det {R : Config H → Config H → Prop} {c c₁ : Config H}
    (hnt : ∀ r : Result, c.code ≠ r.toAdmin) (hs : ∀ c', R c c' ↔ c' = c₁) :
    behavioursR R c = behavioursR R c₁ := by
  rw [behavioursR_succ (· = c₁) hnt hs]
  ext b
  constructor
  · rintro ⟨c', rfl, hb⟩
    exact hb
  · exact fun hb => ⟨c₁, rfl, hb⟩

/-- **A stuck configuration of values returns them, and does nothing else.** -/
theorem behavioursR_vals {R : Config H → Config H → Prop} {s : Store H} {f : Frame}
    {vs : List Val} (hst : ∀ c', ¬ R ⟨s, f, vals vs⟩ c') :
    behavioursR R ⟨s, f, vals vs⟩ = {.returns vs} := by
  ext b
  constructor
  · rintro (⟨d, r, hrt, hc, rfl⟩ | ⟨rfl, hinf⟩)
    · rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c', h, -⟩
      · rw [toAdmin_vals hc]
        rfl
      · exact (hst c' h).elim
    · obtain ⟨c', h, -⟩ := hinf.unfold
      exact (hst c' h).elim
  · rintro rfl
    exact .inl ⟨_, .values vs, .refl, rfl, rfl⟩

end Silmaril.Proofs.Wasm.Wasmi.Runs
