module

public import Silmaril.Machine.Abi.SystemV.Scalar.Defs
import Mathlib.Tactic.IntervalCases

/-!
# System V scalar fragment: the planner's closed form

Proofs for `Silmaril.Machine.Abi.SystemV.Scalar.Thms`: `plan_scalarPlan`, the ABI model's
`plan` returns `scalarPlan` on every fragment prototype, for every vector profile. The
register chunks of an argument or result (`chunks`) are computed on each of the six
register class lists of the fragment (`chunks_args`, `chunks_returns`); the loop over the
arguments is `loop`.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV.Scalar

open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV.Scalar

theorem chunks_args (n al : Nat) (e : Eights) (he : e ≠ .memory) (g v : Nat)
    (hg : g + gpCount ⟨n, al, e.classes⟩ ≤ 6) :
    chunks ⟨n, al, e.classes⟩ gpArguments g v = .ok (eightChunks n gpArguments e.classes 0 g v) := by
  rcases e with _ | s | ⟨s, t⟩
  · exact absurd rfl he
  · cases s
    · have : g ≤ 5 := by change g + 1 ≤ 6 at hg; omega
      interval_cases g <;> rfl
    · have : g ≤ 6 := by change g + 0 ≤ 6 at hg; omega
      interval_cases g <;> rfl
  · cases s <;> cases t
    · have : g ≤ 4 := by change g + 2 ≤ 6 at hg; omega
      interval_cases g <;> rfl
    · have : g ≤ 5 := by change g + 1 ≤ 6 at hg; omega
      interval_cases g <;> rfl
    · have : g ≤ 5 := by change g + 1 ≤ 6 at hg; omega
      interval_cases g <;> rfl
    · have : g ≤ 6 := by change g + 0 ≤ 6 at hg; omega
      interval_cases g <;> rfl

theorem chunks_returns (n al : Nat) (e : Eights) (he : e ≠ .memory) :
    chunks ⟨n, al, e.classes⟩ gpReturns 0 0 = .ok (eightChunks n gpReturns e.classes 0 0 0) := by
  rcases e with _ | s | ⟨s, t⟩
  · exact absurd rfl he
  · cases s <;> rfl
  · cases s <;> cases t <;> rfl

theorem beq_facts : (Class.sse == Class.memory) = false ∧ (Class.integer == Class.memory) = false ∧
    (Class.sse == Class.complexX87) = false ∧ (Class.integer == Class.complexX87) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem memory_beq_sse : (Class.memory == Class.sse) = false := rfl

theorem valid_len (n al : Nat) (e : Eights) (he : e ≠ .memory)
    (h : Object.valid ⟨n, al, e.classes⟩ = true) : eightbytes n = e.classes.length := by
  rcases e with _ | s | ⟨s, t⟩
  · exact absurd rfl he
  all_goals
    cases s <;> (try cases t) <;>
    simp [Object.valid, Eights.classes, eightClass, beq_facts] at h ⊢ <;> omega

theorem len_le (e : Eights) : e.classes.length ≤ 2 := by
  rcases e with _ | s | ⟨s, t⟩ <;> simp [Eights.classes]

theorem arg_valid (a : Arg) : a.object.valid = true := by
  cases a with
  | scalar k => exact Kind.object_valid k
  | agg x h => exact Agg.valid_of_ok h

theorem align_le (a : Arg) : a.align ≤ 8 := by
  cases a with
  | scalar k => cases k <;> decide
  | agg x h => simp only [Agg.ok, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2

theorem size_le (a : Arg) : a.size ≤ maxAggBytes := by
  cases a with
  | scalar k => cases k <;> decide
  | agg x h => simp only [Agg.ok, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem size_le_16 (a : Arg) (he : a.eights ≠ .memory) : a.size ≤ 16 := by
  have hv := arg_valid a
  rw [Arg.object_eq] at hv
  have h1 := valid_len _ _ _ he hv
  have h2 := len_le a.eights
  unfold eightbytes at h1
  omega

theorem memoryClass_eq (a : Arg) : memoryClass a.object = (a.eights == .memory) := by
  rw [Arg.object_eq]
  generalize a.eights = e
  rcases e with _ | s | ⟨s, t⟩ <;> (try cases s) <;> (try cases t) <;> rfl

theorem gpCount_le (e : Eights) (n al : Nat) : gpCount ⟨n, al, e.classes⟩ ≤ 2 := by
  rcases e with _ | s | ⟨s, t⟩ <;> (try cases s) <;> (try cases t) <;> exact Nat.le_of_ble_eq_true rfl

theorem vectorCount_le (e : Eights) (n al : Nat) : vectorCount ⟨n, al, e.classes⟩ ≤ 2 := by
  rcases e with _ | s | ⟨s, t⟩ <;> (try cases s) <;> (try cases t) <;> exact Nat.le_of_ble_eq_true rfl

theorem planReturn_eq (r : Option Arg) : planReturn (r.map Arg.object) = .ok (placeReturn r) := by
  rcases r with _ | a
  · rfl
  have hv := arg_valid a
  simp only [Option.map_some, placeReturn]
  rw [Arg.object_eq] at hv ⊢
  generalize a.size = n, a.align = al at *
  generalize a.eights = e at *
  rcases e with _ | s | ⟨s, t⟩
  all_goals
    (try cases s) <;> (try cases t) <;>
    (simp only [planReturn, hv]; rfl)

theorem chunks_fit (a : Arg) (c : Used) (hf : a.fits c = true) :
    chunks a.object gpArguments c.gp c.vec =
      .ok (eightChunks a.size gpArguments a.object.classes 0 c.gp c.vec) := by
  simp only [Arg.fits, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hf
  have he : a.eights ≠ .memory := by
    intro h; rw [memoryClass_eq, h] at hf; exact absurd hf.1.1 (by decide)
  rw [Arg.object_eq] at hf ⊢
  exact chunks_args _ _ _ he _ _ hf.1.2

theorem next_gp (c : Used) (a : Arg) (h : c.gp ≤ 6) : (c.next a).gp ≤ 6 := by
  unfold Used.next Arg.fits; split <;> simp_all

theorem next_vec (c : Used) (a : Arg) (h : c.vec ≤ 8) : (c.next a).vec ≤ 8 := by
  unfold Used.next Arg.fits; split <;> simp_all

theorem loop (F : Object × Nat → Nat × Nat × Nat × Nat × List Argument →
      Except String (ForInStep (Nat × Nat × Nat × Nat × List Argument)))
    (rest : List Arg)
    (hF : ∀ a ∈ rest, ∀ j (c : Used) args, c.gp ≤ 6 → c.vec ≤ 8 →
      F (a.object, j) (c.gp, c.vec, 8 * c.st, 16, args) =
        .ok (.yield ((c.next a).gp, (c.next a).vec, 8 * (c.next a).st, 16,
          args ++ [a.place c])))
    (i : Nat) (c : Used) (args : List Argument) (hg : c.gp ≤ 6) (hv : c.vec ≤ 8) :
    forIn ((rest.map Arg.object).zipIdx i) (c.gp, c.vec, 8 * c.st, 16, args) F =
      .ok ((Used.final rest c).gp, (Used.final rest c).vec, 8 * (Used.final rest c).st, 16,
        args ++ placeArgs rest c) := by
  induction rest generalizing i c args with
  | nil => simp [placeArgs, Used.final]; rfl
  | cons k rest ih =>
    simp only [List.map_cons, List.zipIdx_cons, List.forIn_cons]
    rw [hF k (by simp) i c args hg hv]
    have := ih (fun k' h => hF k' (by simp [h])) (i + 1) (c.next k) (args ++ [k.place c])
      (next_gp c k hg) (next_vec c k hv)
    simp only [bind, Except.bind]
    rw [this]
    simp [placeArgs, Used.final]

theorem plan_scalarPlan (profile : Profile) : Planned profile := by
  intro p
  obtain ⟨args, res, arity⟩ := p
  unfold Proto.plan Silmaril.Machine.SystemV.Abi.plan
  have hlen : (args.map Arg.object).length = args.length := by simp
  have hres : (Option.map Arg.object res).any (fun object =>
      decide (object.size > profile.vectorBytes) && object.classes.head? == some Class.sse &&
        (List.drop 1 object.classes).all fun x => x == Class.sseUp) = false := by
    rcases res with _ | a
    · rfl
    · have hp : 16 ≤ profile.vectorBytes := by
        unfold Profile.vectorBytes; split <;> omega
      simp only [Option.any, Option.map_some]
      by_cases he : a.eights = .memory
      · rw [Arg.object_eq, he]; simp [Eights.classes, memory_beq_sse]
      · have := size_le_16 a he
        have : decide (a.object.size > profile.vectorBytes) = false := by
          rw [Arg.object_eq]; simp only [decide_eq_false_iff_not]; omega
        simp [this]
  simp only [planReturn_eq, hlen, hres]
  simp only [gt_iff_lt, Nat.lt_irrefl, ite_false, Bool.not_false, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, Bool.false_and, Bool.or_false]
  simp only [bind, Except.bind, pure, Except.pure]
  generalize hr : placeReturn res = r
  rcases r with _ | cs | ⟨size, align⟩
  all_goals
    dsimp only
    first
    | rw [show ((0 : Nat), (0 : Nat), (0 : Nat), (16 : Nat), ([] : List Argument)) =
        ((⟨0, 0, 0⟩ : Used).gp, (⟨0, 0, 0⟩ : Used).vec, 8 * (⟨0, 0, 0⟩ : Used).st, 16, []) from rfl]
    | rw [show ((1 : Nat), (0 : Nat), (0 : Nat), (16 : Nat), ([] : List Argument)) =
        ((⟨1, 0, 0⟩ : Used).gp, (⟨1, 0, 0⟩ : Used).vec, 8 * (⟨1, 0, 0⟩ : Used).st, 16, []) from rfl]
    rw [show (args.map Arg.object).zipIdx = (args.map Arg.object).zipIdx 0 from rfl]
    rw [loop _ args ?_ 0 _ [] ?_ ?_]
    · simp [scalarPlan, hr, start, gpStart, alignUp]
    all_goals try decide
    intro a mem j c acc hg hv
    have hval := arg_valid a
    have hw : needsWideVector a.object = false := by
      by_cases he : a.eights = .memory
      · rw [Arg.object_eq, he]; simp [needsWideVector, Eights.classes, memory_beq_sse]
      · have := size_le_16 a he
        rw [Arg.object_eq]; simp only [needsWideVector]; simp; omega
    have ha : a.object.align ≤ 8 := by rw [Arg.object_eq]; exact align_le a
    have hmax : max 8 a.object.align = 8 := by omega
    have h8 : alignUp (8 * c.st) 8 = 8 * c.st := by
      simp only [alignUp, show (8 : Nat) ≠ 0 by omega, ite_false]; omega
    have hs : alignUp a.object.size 8 = 8 * eightbytes a.size := by
      rw [Arg.object_eq]; simp only [alignUp, eightbytes, show (8 : Nat) ≠ 0 by omega, ite_false]
      omega
    simp only [hval, hw, Bool.false_and, Bool.false_eq_true, ite_false, ite_true,
      hmax, h8, hs]
    by_cases hf : a.fits c
    · have hc : (memoryClass a.object || decide (6 < c.gp + gpCount a.object) ||
          decide (8 < c.vec + vectorCount a.object)) = false := by
        simp only [Arg.fits, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hf
        simp only [hf.1.1, Bool.false_or, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp only [hc, Bool.false_eq_true, ite_false, chunks_fit a c hf]
      simp [Used.next, Arg.place, hf]
    · have hc : (memoryClass a.object || decide (6 < c.gp + gpCount a.object) ||
          decide (8 < c.vec + vectorCount a.object)) = true := by
        simp only [Arg.fits, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          not_and_or] at hf
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        rcases hf with (hf | hf) | hf
        · left; left; simpa using hf
        · left; right; omega
        · right; omega
      have hst : 8 * c.st + 8 * eightbytes a.size = 8 * (c.st + eightbytes a.size) := by omega
      simp only [hc, ite_true]
      simp [Used.next, Arg.place, hf, hst]

end Silmaril.Proofs.Machine.Abi.SystemV.Scalar
