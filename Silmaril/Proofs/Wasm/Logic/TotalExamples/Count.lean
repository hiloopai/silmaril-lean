module

public import Silmaril.Wasm.Logic.Total.Thms
public import Silmaril.Wasm.Logic.TotalExamples.Defs

/-!
# A worked example for total correctness: the count-down loop

`countLoop_twp`: from a frame whose only local is a nonzero `i32`, every run of
`countLoop bt` terminates, falling through with local `0` equal to `0`, in every
profile and for every host relation. The invariant is "the only local is a
nonzero `i32`", the variant its value (`count`); the body is proved with the
instruction rules of `Silmaril.Wasm.Logic.Instr.Thms` at `Wp .total`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Logic.TotalExamples

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.HoareExamples (l0 x0)

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- The loop invariant: no loop values, and the only local is a nonzero `i32`;
the module is that of the starting frame. -/
def CountInv (mi : ModuleInst) (_ : Store H) (f : Frame) (vs : List Val) : Prop :=
  vs = [] ∧ f.module = mi ∧ ∃ n : BitVec 32, n ≠ 0 ∧ f.locals = [some (.i32 n)]

/-- The postcondition: falling through with local `0` equal to `0`. -/
def countPost (mi : ModuleInst) : Post H := fun _ f o =>
  o = .normal [] ∧ f.module = mi ∧ f.locals = [some (.i32 0)]

theorem x0_toNat : x0.toNat = 0 := rfl

theorem count_set {f : Frame} {n : BitVec 32} (h : f.locals = [some (.i32 n)]) :
    count f = n.toNat ∧ (f.setLocal x0 (.i32 (n - 1))).locals = [some (.i32 (n - 1))] := by
  constructor
  · simp only [count, h, Val.i32]
    rfl
  · simp [Frame.setLocal, h, x0_toNat]

theorem count_sub_lt {n : BitVec 32} (hn : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have h₀ : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hn
    · exact h
  rw [BitVec.toNat_sub_of_le (by simp [BitVec.le_def]; omega)]
  simp
  omega

/-- The end of an iteration: `br_if 0` on the decremented local. -/
theorem count_brIf {mi : ModuleInst} {s : Store H} {f : Frame} {n : BitVec 32}
    (hm : f.module = mi) (hl : f.locals = [some (.i32 n)]) (hn : n ≠ 0) :
    TWP P host s (f.setLocal x0 (.i32 (n - 1))) (vals ([] ++ [.i32 (n - 1)]) ++ [.plain (.brIf l0)])
      (loopPostT 0 [] (CountInv mi) (fun _ f _ => count f) (count f) (countPost mi)) := by
  obtain ⟨hc, hl'⟩ := count_set (n := n) hl
  refine TWP.brIf (rest := []) (fun hne => ?_) (fun heq => ?_)
  · show ∃ vs₁ vs₂, ([] : List Val) = vs₁ ++ vs₂ ∧ vs₂.length = 0 ∧
      CountInv mi s (f.setLocal x0 (.i32 (n - 1))) vs₂ ∧ count (f.setLocal x0 (.i32 (n - 1))) < count f
    have hlt : count (f.setLocal x0 (.i32 (n - 1))) < count f := by
      rw [hc, (count_set hl').1]
      exact count_sub_lt hn
    exact ⟨[], [], rfl, rfl, ⟨rfl, hm, n - 1, hne, hl'⟩, hlt⟩
  · have hq : countPost mi s (f.setLocal x0 (.i32 (n - 1))) (.normal []) :=
      ⟨rfl, hm, by rw [hl', heq]⟩
    exact .exit (.normal []) rfl hq

/-- One iteration of the body. -/
theorem count_body {mi : ModuleInst} {s : Store H} {f : Frame} {vs : List Val}
    (hi : CountInv mi s f vs) :
    TWP P host s f (vals vs ++ expression [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub,
        .localTee x0, .brIf l0])
      (loopPostT 0 [] (CountInv mi) (fun _ f _ => count f) (count f) (countPost mi)) := by
  obtain ⟨rfl, hm, n, hn, hl⟩ := hi
  have hv : f.local? x0 = some (some (.i32 n)) := by simp [Frame.local?, hl, x0_toNat]
  have hx : x0.toNat < f.locals.length := by simp [hl, x0_toNat]
  have hsub : Numerics.intBinOp .i32 .sub n 1 = .ok (n - 1 : BitVec 32) := rfl
  have h₅ := count_brIf (P := P) (host := host) (s := s) hm hl hn
  have h₄ : TWP P host s f (vals [.i32 (n - 1), .i32 (n - 1)] ++ [.plain (.localSet x0), .plain (.brIf l0)])
      (loopPostT 0 [] (CountInv mi) (fun _ f _ => count f) (count f) (countPost mi)) :=
    Wp.localSet (m := .total) (us := [.i32 (n - 1)]) hx h₅
  have h₃ : TWP P host s f (vals [.i32 (n - 1)] ++ [.plain (.localTee x0), .plain (.brIf l0)])
      (loopPostT 0 [] (CountInv mi) (fun _ f _ => count f) (count f) (countPost mi)) :=
    Wp.localTee (m := .total) (us := []) h₄
  have h₂ : TWP P host s f (vals [.i32 n, .i32 1] ++
      [.plain (.intBinOp .i32 .sub), .plain (.localTee x0), .plain (.brIf l0)])
      (loopPostT 0 [] (CountInv mi) (fun _ f _ => count f) (count f) (countPost mi)) :=
    Wp.intBinOp (m := .total) (us := []) hsub h₃
  exact Wp.localGet (m := .total) (us := []) hv h₂

/-- **Total correctness of the count-down loop.** -/
theorem countLoop_twp {bt : BlockType} {s : Store H} {f : Frame} {n : BitVec 32}
    (hbt : f.module.blockType? bt = some ([], [])) (hn : n ≠ 0) (hl : f.locals = [some (.i32 n)]) :
    TWP P host s f (expression (countLoop bt)) (countPost f.module) := by
  have hloop := TWP.loop (P := P) (host := host) (us := []) (Inv := CountInv f.module)
    (V := fun _ f _ => count f) (Q := countPost f.module) (bt := bt) (t₂ := [])
    (body := [.localGet x0, .intConst .i32 1, .intBinOp .i32 .sub, .localTee x0, .brIf l0])
    (fun _ _ _ hi => hi.2.1 ▸ hbt) (fun _ _ _ hi => by simp [hi.1]) (fun _ _ _ hi => count_body hi)
    (s := s) (f := f) (vs := []) ⟨rfl, rfl, n, hn, hl⟩
  simpa [countLoop, expression] using hloop

end Silmaril.Wasm.Logic.TotalExamples
