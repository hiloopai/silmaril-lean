module

public import Silmaril.Proofs.Wasm.Examples.CAdder.Spec
public import Silmaril.Wasm.Logic.Total.Thms

@[expose] public section

/-!
# The compiled C adder: Euclid's loop, totally correct

clang compiles the C `gcd` to

```wat
block                       ;; if b = 0 return a
  local.get 1  br_if 0
  local.get 0  return
end
loop                        ;; do { t = b; b = a % b; a = t } while (b != 0)
  local.get 0  local.get 1  local.tee 2  i32.rem_u  local.set 1
  local.get 2  local.set 0  local.get 1  br_if 0
end
local.get 2
```

`gcd_twp`: from the call frame on `a, b` (local `2` starts at `0`), every run of the body
terminates and ends, normally or by `return`, with `[i32 (Src.gcd a b)]`, store unchanged
(total correctness, `TWP`, every profile and host relation). The loop invariant is
"`b ≠ 0` and `gcd a b` is the original gcd"; the variant is `b`, which `a % b < b` decreases.
`i32.rem_u` never traps here because the divisor is the loop's non-zero `b`.
-/

namespace Silmaril.Wasm.Examples.CAdder

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Game
open Silmaril.Wasm.Logic.Core (Post Outcome exec)
open Silmaril.Wasm.Logic.Hoare (TWP TSafe Wp Exits loopPostT labelPostT seqPostT)
open Silmaril.Wasm.Examples.Common (Wp.exec_eq)

/-- The `block` of the compiled `gcd`: return `a` when `b = 0`. -/
def gcdBlock : List Instr := [.localGet ⟨1⟩, .brIf ⟨0⟩, .localGet ⟨0⟩, .return_]

/-- The first three instructions of the loop body. -/
def gcdLoopA : List Instr := [.localGet ⟨0⟩, .localGet ⟨1⟩, .localTee ⟨2⟩]

/-- The four instructions after `i32.rem_u` (before `br_if 0`). -/
def gcdLoopB : List Instr := [.localSet ⟨1⟩, .localGet ⟨2⟩, .localSet ⟨0⟩, .localGet ⟨1⟩]

/-- The body of the `loop`. -/
def gcdLoop : List Instr := gcdLoopA ++ .intBinOp .i32 (.rem .unsigned) :: gcdLoopB ++ [.brIf ⟨0⟩]

theorem body5_eq : body5 = [.block .empty gcdBlock, .loop .empty gcdLoop, .localGet ⟨2⟩] := rfl

/-- The frame of `gcd`: the arguments `a`, `b` and the declared local `t`. -/
def frame3 (a b t : BitVec 32) : Frame :=
  ⟨[some (.i32 a), some (.i32 b), some (.i32 t)], adderMI⟩

theorem forCall_gcd (a b : BitVec 32) :
    Frame.forCall adderMI [.i32 a, .i32 b] locals5 = frame3 a b 0 := rfl

/-- The variant: the value of local `1` (`b`). -/
def bOf (f : Frame) : Nat :=
  match f.locals with
  | [_, some (.num ⟨.int .i32, b⟩), _] => b.toNat
  | _ => 0

theorem bOf_frame3 (a b t : BitVec 32) : bOf (frame3 a b t) = b.toNat := rfl

/-! ## Arithmetic -/

theorem gcd_zero_right (a : BitVec 32) : Src.gcd a 0 = a := by
  show BitVec.ofNat 32 (Nat.gcd a.toNat 0) = a
  rw [Nat.gcd_zero_right, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem remU_ok (a b : BitVec 32) (hb : b ≠ 0) :
    Numerics.intBinOp .i32 (.rem .unsigned) a b = .ok (a % b) := by
  unfold Numerics.intBinOp
  exact ite_eq_right_of_eq_false _ _ (eq_false hb)

theorem umod_lt (a b : BitVec 32) (hb : b ≠ 0) : (a % b).toNat < b.toNat := by
  have hpos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hb
    · exact h
  rw [BitVec.toNat_umod]
  exact Nat.mod_lt _ hpos

/-- One Euclid step keeps the gcd. -/
theorem gcd_step (a b : BitVec 32) : Nat.gcd b.toNat (a % b).toNat = Nat.gcd a.toNat b.toNat := by
  rw [BitVec.toNat_umod, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]

/-- When `a % b = 0` the gcd is `b`. -/
theorem gcd_of_umod_zero (a b : BitVec 32) (h : a % b = 0) :
    BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat) = b := by
  have hm : a.toNat % b.toNat = 0 := by rw [← BitVec.toNat_umod, h]; rfl
  rw [Nat.gcd_eq_right (Nat.dvd_of_mod_eq_zero hm), BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The loop -/

variable {P : Profile} {host : HostSemantics Nat}

/-- The loop invariant, for the original arguments with gcd `g`: no loop values, the store is
`s`, and the frame holds `a', b' ≠ 0` with `gcd a' b' = g`. -/
def GcdInv (s : Store Nat) (g : Nat) (s' : Store Nat) (f : Frame) (vs : List Val) : Prop :=
  vs = [] ∧ s' = s ∧ ∃ a b t : BitVec 32, f = frame3 a b t ∧ b ≠ 0 ∧ Nat.gcd a.toNat b.toNat = g

/-- What follows the loop: `local.get 2`, then the function's postcondition. -/
abbrev afterLoop (P : Profile) (host : HostSemantics Nat) (Q : Post Nat) : Post Nat :=
  seqPostT P host [.plain (.localGet ⟨2⟩)] Q

theorem exec_loopA (s : Store Nat) (a b t : BitVec 32) :
    exec s (frame3 a b t) [] gcdLoopA = some (s, frame3 a b b, [.i32 b, .i32 a]) := rfl

theorem exec_loopB (s : Store Nat) (a b r : BitVec 32) :
    exec s (frame3 a b b) [.i32 r] gcdLoopB = some (s, frame3 b r b, [.i32 r]) := rfl

/-- The loop exits with `b'` once the remainder is `0`; `b'` is then the gcd. -/
theorem loop_exit {s : Store Nat} {g : Nat} {Q : Post Nat} (a b : BitVec 32)
    (hg : Nat.gcd a.toNat b.toNat = g) (hr : a % b = 0)
    (hQ : ∀ F, Q s F (.normal [.i32 (BitVec.ofNat 32 g)])) :
    TWP P host s (frame3 b (a % b) b) (vals [] ++ [.plain (.localGet ⟨2⟩)]) Q := by
  have hb : BitVec.ofNat 32 g = b := hg ▸ gcd_of_umod_zero a b hr
  have hv : (frame3 b (a % b) b).local? ⟨2⟩ = some (some (.i32 b)) := rfl
  refine Wp.localGet (m := .total) (us := []) (rest := []) hv ?_
  exact Wp.of_vals (m := .total) (by simpa [hb] using hQ (frame3 b (a % b) b))

/-- The end of an iteration: `br_if 0` on the new remainder. -/
theorem loop_brIf {s : Store Nat} {g : Nat} {Q : Post Nat} (a b t : BitVec 32) (hb : b ≠ 0)
    (hg : Nat.gcd a.toNat b.toNat = g) (hQ : ∀ F, Q s F (.normal [.i32 (BitVec.ofNat 32 g)])) :
    TWP P host s (frame3 b (a % b) b) (vals ([] ++ [.i32 (a % b)]) ++ [.plain (.brIf ⟨0⟩)])
      (loopPostT 0 [] (GcdInv s g) (fun _ f _ => bOf f) (bOf (frame3 a b t))
        (afterLoop P host Q)) := by
  refine Silmaril.Wasm.Logic.Hoare.TWP.brIf (rest := []) (fun hne => ?_) (fun heq => ?_)
  · show ∃ vs₁ vs₂, ([] : List Val) = vs₁ ++ vs₂ ∧ vs₂.length = 0 ∧
      GcdInv s g s (frame3 b (a % b) b) vs₂ ∧ bOf (frame3 b (a % b) b) < bOf (frame3 a b t)
    have hinv : GcdInv s g s (frame3 b (a % b) b) [] :=
      ⟨rfl, rfl, b, a % b, b, rfl, hne, (gcd_step a b).trans hg⟩
    exact ⟨[], [], rfl, rfl, hinv, umod_lt a b hb⟩
  · show TSafe P host _ ⟨s, frame3 b (a % b) b, vals [] ++ []⟩
    exact TSafe.exit (.normal []) rfl (loop_exit a b hg heq hQ)

/-- One iteration of the loop body. -/
theorem loop_body {s s' : Store Nat} {g : Nat} {Q : Post Nat} {f : Frame} {vs : List Val}
    (hi : GcdInv s g s' f vs) (hQ : ∀ F, Q s F (.normal [.i32 (BitVec.ofNat 32 g)])) :
    TWP P host s' f (vals vs ++ expression gcdLoop)
      (loopPostT 0 [] (GcdInv s g) (fun _ f _ => bOf f) (bOf f) (afterLoop P host Q)) := by
  obtain ⟨rfl, rfl, a, b, t, rfl, hb, hg⟩ := hi
  have hsplit : vals [] ++ expression gcdLoop = vals [] ++ expression gcdLoopA ++
      (.plain (.intBinOp .i32 (.rem .unsigned)) :: expression gcdLoopB ++
        [.plain (.brIf ⟨0⟩)]) := rfl
  rw [hsplit]
  refine Wp.exec_eq (m := .total) (vs := []) (exec_loopA _ a b t) ?_
  refine Wp.intBinOp (m := .total) (us := []) (remU_ok a b hb) ?_
  have hB := Wp.exec_eq (m := .total) (P := P) (host := host) (vs := [.i32 (a % b)])
    (rest := [.plain (.brIf ⟨0⟩)]) (exec_loopB _ a b (a % b)) (loop_brIf a b t hb hg hQ)
  exact hB

/-- The `loop`, entered with `b ≠ 0`, followed by `local.get 2`. -/
theorem loop_twp {s : Store Nat} {Q : Post Nat} (a b : BitVec 32) (hb : b ≠ 0)
    (hQ : ∀ F, Q s F (.normal [.i32 (Src.gcd a b)])) :
    TWP P host s (frame3 a b 0) (vals [] ++ [.plain (.loop .empty gcdLoop), .plain (.localGet ⟨2⟩)])
      Q := by
  have hloop := Silmaril.Wasm.Logic.Hoare.TWP.loop (P := P) (host := host) (us := [])
    (Inv := GcdInv s (Nat.gcd a.toNat b.toNat)) (V := fun _ f _ => bOf f) (Q := afterLoop P host Q)
    (bt := .empty) (t₁ := []) (t₂ := []) (body := gcdLoop) (fun _ _ _ _ => rfl)
    (fun _ _ _ hi => by simp [hi.1]) (fun _ _ _ hi => loop_body hi hQ)
    (s := s) (f := frame3 a b 0) (vs := []) ⟨rfl, rfl, a, b, 0, rfl, hb, rfl⟩
  exact Silmaril.Wasm.Logic.Hoare.TWP.seq (c₁ := [.plain (.loop .empty gcdLoop)])
    (by simpa using hloop)

/-- The `block`: return `a` when `b = 0`, otherwise go on to the loop. -/
theorem block_twp {s : Store Nat} {Q : Post Nat} (a b : BitVec 32)
    (hN : ∀ F, Q s F (.normal [.i32 (Src.gcd a b)])) (hR : ∀ F, Q s F (.ret [.i32 (Src.gcd a b)])) :
    TWP P host s (frame3 a b 0) (vals [] ++ expression gcdBlock)
      (labelPostT P host 0 [] [] (seqPostT P host
        [.plain (.loop .empty gcdLoop), .plain (.localGet ⟨2⟩)] Q)) := by
  have hv1 : (frame3 a b 0).local? ⟨1⟩ = some (some (.i32 b)) := rfl
  have hv0 : (frame3 a b 0).local? ⟨0⟩ = some (some (.i32 a)) := rfl
  refine Wp.localGet (m := .total) (us := []) hv1 ?_
  refine Silmaril.Wasm.Logic.Hoare.TWP.brIf (fun hne => ?_) (fun heq => ?_)
  · refine ⟨[], [], rfl, rfl, TSafe.exit (.normal []) rfl ?_⟩
    exact loop_twp a b hne hN
  · refine Wp.localGet (m := .total) (us := []) hv0 ?_
    refine Wp.of_exits (m := .total) (o := .ret [.i32 a]) ⟨[], rfl⟩ ?_
    have hg : Src.gcd a b = a := by rw [heq, gcd_zero_right]
    show Q s (frame3 a b 0) (.ret ([] ++ [.i32 a]))
    exact hg ▸ hR _

/-- **Euclid's loop, compiled by clang, is totally correct**: every run of the body of `gcd`
from the call frame on `a, b` terminates with `[i32 (Src.gcd a b)]` (by falling through or by
`return`), store unchanged. -/
theorem gcd_twp (s : Store Nat) (a b : BitVec 32) {Q : Post Nat}
    (hN : ∀ F, Q s F (.normal [.i32 (Src.gcd a b)])) (hR : ∀ F, Q s F (.ret [.i32 (Src.gcd a b)])) :
    TWP P host s (frame3 a b 0) (expression body5) Q := by
  have hb := Silmaril.Wasm.Logic.Hoare.TWP.block (P := P) (host := host) (us := []) (vs := [])
    (bt := .empty) (t₁ := []) (t₂ := []) (rest := [.plain (.loop .empty gcdLoop),
      .plain (.localGet ⟨2⟩)]) (Q := Q) (s := s) (f := frame3 a b 0) rfl rfl (block_twp a b hN hR)
  simpa [body5_eq, expression] using hb

end Silmaril.Wasm.Examples.CAdder
