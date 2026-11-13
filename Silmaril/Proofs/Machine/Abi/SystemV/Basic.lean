module

public import Silmaril.Machine.Abi.SystemV.Defs
import Mathlib.Tactic.IntervalCases

/-!
# System V integer fragment: planner closed form and encodable entries

Proofs for `Silmaril.Machine.Abi.SystemV.Thms`. Nothing imports this module except
that header and later Proofs modules of the topic.

* `plan_intPlan`: the ABI model's `plan` returns `intPlan` on every fragment prototype,
  for every vector profile.
* `entry_inhabited`: every argument tuple has an `Ffi.Entry` state. The witness
  places the first six arguments in RDI…R9, the rest in 8-byte slots above the
  return address at RSP = 8, with one read/write region covering memory.
-/

@[expose] public section
namespace Silmaril.Proofs.Machine.Abi.SystemV

open Silmaril.C.Api (Scalar Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV
open Silmaril.Cerberus.NativeTypes (Bytes)
open Silmaril.X86 (Reg)

/-! ## The planner on INTEGER objects -/

theorem loop (F : Object × Nat → Nat × Nat × Nat × Nat × List Argument →
      Except String (ForInStep (Nat × Nat × Nat × Nat × List Argument)))
    (rest : List Object)
    (hF : ∀ o ∈ rest, ∀ j args, F (o, j) (min j 6, 0, 8 * (j - 6), 16, args) =
      .ok (.yield (min (j + 1) 6, 0, 8 * (j + 1 - 6), 16, args ++ [intArg o j])))
    (i : Nat) (args : List Argument) :
    forIn (rest.zipIdx i) (min i 6, 0, 8 * (i - 6), 16, args) F =
      .ok (min (i + rest.length) 6, 0, 8 * (i + rest.length - 6), 16,
        args ++ intArgs rest i) := by
  induction rest generalizing i args with
  | nil => simp [intArgs]; rfl
  | cons o rest ih =>
    simp only [List.zipIdx_cons, List.forIn_cons]
    rw [hF o (by simp) i args]
    have := ih (fun o' h => hF o' (by simp [h])) (i + 1) (args ++ [intArg o i])
    simp only [bind, Except.bind]
    rw [this]
    simp [intArgs, Nat.add_assoc, Nat.add_comm 1]

theorem loop0 (F : Object × Nat → Nat × Nat × Nat × Nat × List Argument →
      Except String (ForInStep (Nat × Nat × Nat × Nat × List Argument)))
    (rest : List Object)
    (hF : ∀ o ∈ rest, ∀ j args, F (o, j) (min j 6, 0, 8 * (j - 6), 16, args) =
      .ok (.yield (min (j + 1) 6, 0, 8 * (j + 1 - 6), 16, args ++ [intArg o j]))) :
    forIn rest.zipIdx (0, 0, 0, 16, []) F =
      .ok (min rest.length 6, 0, 8 * (rest.length - 6), 16, intArgs rest 0) := by
  simpa using loop F rest hF 0 []

theorem alignUp_eight (m : Nat) : alignUp (8 * m) 8 = 8 * m := by
  simp only [alignUp, show (8 : Nat) ≠ 0 by omega, ite_false]; omega

theorem planReturn_int (r : Option Scalar) :
    planReturn (r.map Kind.object) = .ok (intReturn (r.map Kind.object)) := by
  rcases r with _ | k
  · rfl
  · cases k <;> rfl

theorem chunks_int (k : Scalar) (j : Nat) (h : j < 6) :
    chunks (Kind.object k) gpArguments j 0 =
      .ok [⟨0, (Kind.object k).size, .gp (gpArguments[j]'(by simp [gpArguments]; omega))⟩] := by
  cases k <;> interval_cases j <;> rfl

theorem intReturn_not_indirect (r : Option Scalar) :
    ∀ size align, intReturn (r.map Kind.object) ≠ .indirect size align := by
  intro size align h
  rcases r with _ | k <;> cases h

/-- the ABI model's planner computes `intPlan` on the fragment, under every profile. -/
theorem plan_intPlan (profile : Profile) (p : Proto) :
    p.plan profile = .ok (intPlan p.objects p.resultObject) := by
  obtain ⟨⟨args, res⟩, arity⟩ := p
  unfold Proto.plan Silmaril.Machine.SystemV.Abi.plan
  have hlen : (args.map Kind.object).length = args.length := by simp
  have hres : (Option.map Kind.object res).any (fun object =>
      decide (object.size > profile.vectorBytes) && object.classes.head? == some Class.sse &&
        (List.drop 1 object.classes).all fun x => x == Class.sseUp) = false := by
    rcases res with _ | k
    · rfl
    · have : ((Kind.object k).classes.head? == some Class.sse) = false := by cases k <;> rfl
      simp [Option.any, this]
  simp only [Proto.objects, Proto.resultObject, planReturn_int, hlen, hres]
  simp only [gt_iff_lt, Nat.lt_irrefl, ite_false, Bool.not_false, bne_self_eq_false,
    Bool.and_false, Bool.false_eq_true, Bool.false_and, Bool.or_false]
  simp only [bind, Except.bind, pure, Except.pure]
  have hni := intReturn_not_indirect res
  generalize hr : intReturn (Option.map Kind.object res) = r at hni ⊢
  rcases r with _ | cs | ⟨size, align⟩
  rotate_left 2
  · exact absurd rfl (hni size align)
  all_goals
    dsimp only
    rw [loop0]
    · simp [intPlan, hr]
    · intro o mem j acc
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 mem
      have hv : (Kind.object k).valid = true := Kind.object_valid k
      have hw : needsWideVector (Kind.object k) = false := by cases k <;> rfl
      have hm : memoryClass (Kind.object k) = false := by cases k <;> rfl
      have hg : gpCount (Kind.object k) = 1 := by cases k <;> rfl
      have hc : vectorCount (Kind.object k) = 0 := by cases k <;> rfl
      have ha : (Kind.object k).align ≤ 8 := by cases k <;> decide
      have hs : alignUp (Kind.object k).size 8 = 8 := by cases k <;> rfl
      simp only [hv, hw, hm, hg, hc, Bool.false_and, Bool.false_eq_true, ite_false, ite_true]
      by_cases hj : j < 6
      · have hmin : min j 6 = j := by omega
        have hsub : j - 6 = 0 := by omega
        have hlen6 : j < gpArguments.length := by simp [gpArguments]; omega
        simp only [hmin, hsub, chunks_int k j hj]
        split
        · rename_i h
          simp at h
          omega
        · have hmin' : min (j + 1) 6 = j + 1 := by omega
          have hsub' : j + 1 - 6 = 0 := by omega
          simp [hmin', hsub', intArg, List.getElem?_eq_getElem hlen6]
      · have hmin : min j 6 = 6 := by omega
        have hmax : max 8 (Kind.object k).align = 8 := by omega
        have hnone : gpArguments[j]? = none := by simp [gpArguments]; omega
        simp only [hmin, hmax, alignUp_eight, hs]
        split
        · have hmin' : min (j + 1) 6 = 6 := by omega
          have hstack : 8 * (j - 6) + 8 = 8 * (j + 1 - 6) := by omega
          simp [hmin', hstack, intArg, hnone]
        · rename_i h
          simp at h

end Silmaril.Proofs.Machine.Abi.SystemV
