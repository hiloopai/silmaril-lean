module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
import Mathlib.Tactic.IntervalCases

/-!
# System V scalar fragment: the planner's closed form

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`: `plan_scalarPlan`, the ABI model's
`plan` returns `scalarPlan` on every fragment prototype, for every vector profile.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV.Scalar

theorem next_gp (c : Used) (k : Kind) (h : c.gp ≤ 6) : (c.next k).gp ≤ 6 := by
  unfold Used.next; split <;> split <;> simp <;> omega

theorem next_vec (c : Used) (k : Kind) (h : c.vec ≤ 8) : (c.next k).vec ≤ 8 := by
  unfold Used.next; split <;> split <;> simp <;> omega

theorem loop (F : Object × Nat → Nat × Nat × Nat × Nat × List Argument →
      Except String (ForInStep (Nat × Nat × Nat × Nat × List Argument)))
    (rest : List Kind)
    (hF : ∀ k ∈ rest, ∀ j (c : Used) args, c.gp ≤ 6 → c.vec ≤ 8 →
      F (k.object, j) (c.gp, c.vec, 8 * c.st, 16, args) =
        .ok (.yield ((c.next k).gp, (c.next k).vec, 8 * (c.next k).st, 16,
          args ++ [scalarArg k c])))
    (i : Nat) (c : Used) (args : List Argument) (hg : c.gp ≤ 6) (hv : c.vec ≤ 8) :
    forIn ((rest.map Kind.object).zipIdx i) (c.gp, c.vec, 8 * c.st, 16, args) F =
      .ok ((Used.final rest c).gp, (Used.final rest c).vec, 8 * (Used.final rest c).st, 16,
        args ++ scalarArgs rest c) := by
  induction rest generalizing i c args with
  | nil => simp [scalarArgs, Used.final]; rfl
  | cons k rest ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.forIn_cons]
    rw [hF k (by simp) i c args hg hv]
    have := ih (fun k' h => hF k' (by simp [h])) (i + 1) (c.next k) (args ++ [scalarArg k c])
      (next_gp c k hg) (next_vec c k hv)
    simp only [bind, Except.bind]
    rw [this]
    simp [scalarArgs, Used.final]

theorem planReturn_scalar (r : Option Kind) :
    planReturn (r.map Kind.object) = .ok (scalarReturn r) := by
  rcases r with _ | k
  · rfl
  · cases k <;> rfl

theorem scalarReturn_not_indirect (r : Option Kind) :
    ∀ size align, scalarReturn r ≠ .indirect size align := by
  intro size align h
  rcases r with _ | k <;> cases h

theorem chunks_sse (k : Kind) (hk : k.sse = true) (g v : Nat) :
    chunks k.object gpArguments g v = .ok [⟨0, k.bytes, .vector v 0⟩] := by
  cases k <;> first | rfl | exact absurd hk (by decide)

theorem chunks_int (k : Kind) (hk : k.sse = false) (g v : Nat) (h : g < 6) :
    chunks k.object gpArguments g v =
      .ok [⟨0, k.bytes, .gp (gpArguments[g]'(by simp [gpArguments]; omega))⟩] := by
  cases k <;> first | exact absurd hk (by decide) | (interval_cases g <;> rfl)

/-- The ABI model's planner computes `scalarPlan` on the fragment, under every profile. -/
theorem plan_scalarPlan (profile : Profile) : Planned profile := by
  intro p
  obtain ⟨args, res, arity⟩ := p
  unfold Proto.plan Silmaril.Machine.SystemV.Abi.plan
  have hlen : (args.map Kind.object).length = args.length := by simp
  have hres : (Option.map Kind.object res).any (fun object =>
      decide (object.size > profile.vectorBytes) && object.classes.head? == some Class.sse &&
        (List.drop 1 object.classes).all fun x => x == Class.sseUp) = false := by
    rcases res with _ | k
    · rfl
    · have hb : k.object.size ≤ 8 := by cases k <;> decide
      have hp : 16 ≤ profile.vectorBytes := by
        unfold Profile.vectorBytes; split <;> omega
      simp only [Option.any, Option.map_some]
      have : decide (k.object.size > profile.vectorBytes) = false := by
        simp only [decide_eq_false_iff_not]; omega
      simp [this]
  simp only [planReturn_scalar, hlen, hres]
  simp only [gt_iff_lt, Nat.lt_irrefl, ite_false, Bool.not_false, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, Bool.false_and, Bool.or_false]
  simp only [bind, Except.bind, pure, Except.pure]
  have hni := scalarReturn_not_indirect res
  generalize hr : scalarReturn res = r at hni ⊢
  rcases r with _ | cs | ⟨size, align⟩
  rotate_left 2
  · exact absurd rfl (hni size align)
  all_goals
    dsimp only
    rw [show ((0 : Nat), (0 : Nat), (0 : Nat), (16 : Nat), ([] : List Argument)) =
      ((⟨0, 0, 0⟩ : Used).gp, (⟨0, 0, 0⟩ : Used).vec, 8 * (⟨0, 0, 0⟩ : Used).st, 16, []) from rfl]
    rw [show (args.map Kind.object).zipIdx = (args.map Kind.object).zipIdx 0 from rfl]
    rw [loop _ args ?_ 0 ⟨0, 0, 0⟩ [] (by decide) (by decide)]
    · simp [scalarPlan, hr, alignUp]
    · intro k mem j c acc hg hv
      have hval : k.object.valid = true := Kind.object_valid k
      have hw : needsWideVector k.object = false := by cases k <;> rfl
      have hm : memoryClass k.object = false := by cases k <;> rfl
      have ha : k.object.align ≤ 8 := by cases k <;> decide
      have hs : alignUp k.object.size 8 = 8 := by cases k <;> rfl
      have hmax : max 8 k.object.align = 8 := by omega
      have h8 : alignUp (8 * c.st) 8 = 8 * c.st := by
        simp only [alignUp, show (8 : Nat) ≠ 0 by omega, ite_false]; omega
      simp only [hval, hw, hm, Bool.false_and, Bool.false_eq_true, ite_false,
        Bool.false_or, hmax, h8, hs]
      cases hk : k.sse
      · have hg1 : gpCount k.object = 1 := by cases k <;> first | rfl | exact absurd hk (by decide)
        have hc0 : vectorCount k.object = 0 := by cases k <;> first | rfl | exact absurd hk (by decide)
        simp only [hg1, hc0, Nat.add_zero]
        by_cases hgc : c.gp < 6
        · have h1 : ¬ (6 < c.gp + 1) := by omega
          have h2 : ¬ (8 < c.vec) := by omega
          simp only [h1, h2, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
            chunks_int k hk c.gp c.vec hgc]
          simp [Used.next, scalarArg, hk, hgc]
        · have h1 : 6 < c.gp + 1 := by omega
          simp only [h1, decide_true, Bool.true_or, ite_true]
          have hst : 8 * c.st + 8 = 8 * (c.st + 1) := by omega
          simp [Used.next, scalarArg, hk, hgc, hst]
      · have hg0 : gpCount k.object = 0 := by cases k <;> first | rfl | exact absurd hk (by decide)
        have hc1 : vectorCount k.object = 1 := by cases k <;> first | rfl | exact absurd hk (by decide)
        simp only [hg0, hc1, Nat.add_zero]
        by_cases hvc : c.vec < 8
        · have h1 : ¬ (6 < c.gp) := by omega
          have h2 : ¬ (8 < c.vec + 1) := by omega
          simp only [h1, h2, decide_false, Bool.or_false, Bool.false_eq_true, ite_false,
            chunks_sse k hk c.gp c.vec]
          simp [Used.next, scalarArg, hk, hvc]
        · have h2 : 8 < c.vec + 1 := by omega
          simp only [h2, decide_true, Bool.or_true, ite_true]
          have hst : 8 * c.st + 8 = 8 * (c.st + 1) := by omega
          simp [Used.next, scalarArg, hk, hvc, hst]

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
