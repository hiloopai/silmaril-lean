module

public import Silmaril.Proofs.Wasm.FnInst.Ground.Rules

@[expose] public section

/-! # Refuted: equal runs give `BaseSim` for every straight-line pair

The pair

  `i32.const 1; local.set 0; i32.const 2; local.set 0`  against  `i32.const 2; local.set 0`

has equal runs from every frame and stack (`runRef_twoSets`), and the matching pair of the opt
track's fragment is equivalent there too. Yet **no** runtime relation `B` and **no** rank make
it a silmaril `BaseSim` pair (`not_baseSim_twoSets`), at any profile, for any function
relation: `BaseSim.step` matches each left step by a right run that ends in *the same frame*,
and after its first `local.set` the left frame holds `1` in local `0`, a frame the right side
never reaches (it only passes through the initial frame and the frame holding `2`).

So the restriction of `Good` to left sides that do not write the frame is necessary for a
bridge into `BaseSim` with this left side, not an artefact of the proof.
-/

namespace Silmaril.Wasm.FnInst.Ground

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

/-- Local `0`. -/
def l0 : LocalIdx := ⟨0⟩

/-- Two writes of local `0`. -/
def twoSets : List GInstr := [.const 1, .localSet l0, .const 2, .localSet l0]

/-- One write of local `0`. -/
def oneSet : List GInstr := [.const 2, .localSet l0]

theorem setLocal_setLocal (f : Frame) (x : LocalIdx) (v w : Val) :
    (f.setLocal x v).setLocal x w = f.setLocal x w := by
  simp [Frame.setLocal, List.set_set]

theorem setLocal_length (f : Frame) (x : LocalIdx) (v : Val) :
    (f.setLocal x v).locals.length = f.locals.length := by
  simp [Frame.setLocal]

/-- A write of a constant. -/
theorem run_constSet {x : LocalIdx} {k : BitVec 32} {f : Frame} {st : List Val}
    {r : Frame × List Val} (c : List GInstr)
    (h : run (.const k :: .localSet x :: c) f st = some r) :
    x.toNat < f.locals.length ∧ run c (f.setLocal x (Val.i32 k)) st = some r := by
  have h' : (if x.toNat < f.locals.length then some (f.setLocal x (Val.i32 k), st) else none).bind
      (fun r => run c r.1 r.2) = some r := h
  split at h'
  · exact ⟨by assumption, h'⟩
  · cases h'

theorem runRef_twoSets : RunRef twoSets oneSet := by
  intro f st r h
  obtain ⟨hx, h₁⟩ := run_constSet _ h
  obtain ⟨-, h₂⟩ := run_constSet [] h₁
  rw [setLocal_setLocal] at h₂
  have e : run oneSet f st = (if l0.toNat < f.locals.length then
      some (f.setLocal l0 (Val.i32 2), st) else none).bind (fun r => run [] r.1 r.2) := rfl
  rw [e]
  simp only [hx, ↓reduceIte]
  exact h₂

/-- `local.set` pops its operand and writes the local. -/
theorem head_set {s : Store H} {f : Frame} {args : List Val} {x : LocalIdx} {c₀ : Config H}
    (h : SingleThreaded.Det.Head P s f args (.plain (.localSet x)) c₀) :
    ∃ v, args = [v] ∧ c₀ = ⟨s, f.setLocal x v, []⟩ := by
  have hv := h.fam_inv (by simp [SingleThreaded.Det.famOf])
  simp only [SingleThreaded.Det.famOf, SingleThreaded.Det.FamRel] at hv
  generalize hc : (⟨s, f, vals args ++ [.plain (.localSet x)]⟩ : Config H) = c at hv
  cases hv with
  | @localSet s' f' x' v hl =>
    obtain ⟨rfl, rfl, hc'⟩ := Config.mk.inj hc
    obtain ⟨h1, h2⟩ := (SingleThreaded.Det.append_singleton_inj (l₂ := [v.toAdmin])).mp hc'
    obtain rfl : x = x' := by simpa using h2
    exact ⟨v, SingleThreaded.vals_injective h1, rfl⟩
  | _ =>
    have := congrArg List.getLast? (Config.mk.inj hc).2.2
    simp at this

/-- From `i32.const 2; local.set 0` the machine only reaches the frame holding `2`. -/
theorem oneSet_reach {s : Store H} {f : Frame} {c : Config H}
    (h : Relation.TransGen (Step P closedHost)
      ⟨s, f, vals [] ++ expression (lower oneSet) ++ []⟩ c) :
    c.frame = f.setLocal l0 (Val.i32 2) := by
  obtain ⟨c₁, h₁, h₂⟩ := Relation.TransGen.head'_iff.mp h
  have e : vals [] ++ expression (lower oneSet) ++ [] =
      vals [Val.i32 2] ++ Admin.plain (.localSet l0) :: [] := rfl
  rw [e] at h₁
  obtain ⟨vs, args, c₀, hW, hh, rfl⟩ := GuardSim.head_inv (by rfl) (by simp) (by simp) h₁
  obtain ⟨v, rfl, rfl⟩ := head_set hh
  have hW' : [] ++ [Val.i32 2] = vs ++ [v] := hW
  obtain ⟨rfl, rfl⟩ := SingleThreaded.Det.append_singleton_inj.mp hW'
  rcases Relation.ReflTransGen.cases_head h₂ with rfl | ⟨c₂, h₃, -⟩
  · rfl
  · exact absurd h₃ (Sim.Step.not_vals (vs := []))

/-- The frame with local `0` holding `0`. -/
def f0 : Frame := ⟨[some (Val.i32 0)], {}⟩

theorem local_set0 (k : BitVec 32) :
    (f0.setLocal l0 (Val.i32 k)).local? l0 = some (some (Val.i32 k)) := rfl

theorem i32_inj {a b : BitVec 32} (h : some (some (Val.i32 a)) = some (some (Val.i32 b))) :
    a = b :=
  Option.some.inj (congrArg asI32 (Option.some.inj (Option.some.inj h)) : some a = some b)

theorem f0_ne (k : BitVec 32) (hk : k ≠ 0) : f0.setLocal l0 (Val.i32 k) ≠ f0 := by
  intro h
  have h₁ := local_set0 k
  rw [h] at h₁
  exact hk (i32_inj (h₁.symm.trans rfl))

theorem setLocal_ne : f0.setLocal l0 (Val.i32 2) ≠ f0.setLocal l0 (Val.i32 1) := by
  intro h
  have h₁ := local_set0 2
  rw [h, local_set0] at h₁
  exact absurd (i32_inj h₁) (by decide)

/-- **Refuted**: the equal-run pair `twoSets`/`oneSet` is not a `BaseSim` pair, for any runtime
relation, rank and function relation, at any profile. -/
theorem not_baseSim_twoSets {F : FuncInst H → FuncInst H → Prop} :
    ¬ ∃ (B : List Admin → List Admin → Prop) (rank : List Admin → Nat),
      BaseSim P closedHost F (fun x y => x = lower twoSets ∧ y = lower oneSet) B rank := by
  rintro ⟨B, rank, hB⟩
  have hsrc := hB.src ⟨rfl, rfl⟩
  let s : Store H := {}
  have hst : StoreRel F s s := ⟨rfl, rfl, .nil⟩
  have hx : l0.toNat < f0.locals.length := by decide
  have h₁ : Step P closedHost ⟨s, f0, vals [Val.i32 1] ++ [.plain (.localSet l0)]⟩
      ⟨s, f0.setLocal l0 (Val.i32 1), vals []⟩ :=
    Step.variable (VariableStep.localSet hx)
  have e : vals [] ++ expression (lower twoSets) ++ [] =
      vals [Val.i32 1] ++ [.plain (.localSet l0)] ++ expression (lower oneSet) := rfl
  have hstep : Step P closedHost ⟨s, f0, vals [] ++ expression (lower twoSets) ++ []⟩
      ⟨s, f0.setLocal l0 (Val.i32 1), expression (lower oneSet)⟩ := by
    rw [e]
    exact Step.append_right h₁ (expression (lower oneSet))
  obtain ⟨t', es'', hm, -, -⟩ := hB.step hst hsrc AdminsRel.nil hstep
  rcases hm with ht | ⟨-, hf, -⟩
  · exact setLocal_ne (oneSet_reach ht).symm
  · exact f0_ne 1 (by decide) hf

end Silmaril.Wasm.FnInst.Ground
