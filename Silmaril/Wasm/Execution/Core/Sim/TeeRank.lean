module

public import Silmaril.Wasm.Execution.Core.Sim.Rank

@[expose] public section

/-! # A payload-independent rank that decreases on local tee expansion -/

namespace Silmaril.Wasm.Execution.Core.Sim

mutual
  /-- Tee has enough weight to pay for its duplicated value and store. -/
  def teeAdminRank : Admin → Nat
    | .plain (.localTee _) => 4
    | .label _ _ b | .handler _ _ b | .frame _ _ b => 1 + teeCodeRank b
    | _ => 1

  /-- Values and indices have bounded weight regardless of their payloads. -/
  def teeCodeRank : List Admin → Nat
    | [] => 0
    | a :: l => teeAdminRank a + teeCodeRank l
end

@[simp] theorem teeCodeRank_nil : teeCodeRank [] = 0 := rfl
@[simp] theorem teeCodeRank_cons (a : Admin) (l : List Admin) :
    teeCodeRank (a :: l) = teeAdminRank a + teeCodeRank l := rfl

@[simp] theorem teeCodeRank_append (a b : List Admin) :
    teeCodeRank (a ++ b) = teeCodeRank a + teeCodeRank b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Nat.add_assoc]

theorem teeAdminRank_pos (a : Admin) : 0 < teeAdminRank a := by
  cases a with
  | plain i => cases i <;> simp [teeAdminRank]
  | _ => simp [teeAdminRank] <;> omega

theorem teeCodeRank_pos {a : List Admin} (ha : a ≠ []) : 0 < teeCodeRank a := by
  cases a with
  | nil => simp at ha
  | cons x a => have := teeAdminRank_pos x; simp; omega

@[simp] theorem teeAdminRank_val (v : Val) : teeAdminRank v.toAdmin = 1 := by
  cases v with
  | num n => cases n with | mk t x => cases t <;> rfl
  | _ => rfl

@[simp] theorem teeCodeRank_vals (vs : List Val) : teeCodeRank (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change teeAdminRank v.toAdmin + teeCodeRank (vals vs) = vs.length + 1
    rw [teeAdminRank_val, ih]
    omega

instance : LawfulCodeRank teeCodeRank where
  context_lt := by intros; simp only [teeCodeRank_append]; omega
  infix_lt := by
    intro p m q hm
    have := teeCodeRank_pos hm
    simp only [teeCodeRank_append]
    omega
  label_body_lt := by intros; simp [teeAdminRank]; omega
  label_lt := by intros; simp_all [teeAdminRank]
  handler_body_lt := by intros; simp [teeAdminRank]; omega
  handler_lt := by intros; simp_all [teeAdminRank]
  frame_body_lt := by intros; simp [teeAdminRank]; omega
  frame_lt := by intros; simp_all [teeAdminRank]

/-- The first tee administrative step strictly decreases this rank for every value. -/
theorem teeCodeRank_expand (v : Val) (x : LocalIdx) :
    teeCodeRank [v.toAdmin, v.toAdmin, .plain (.localSet x)] <
      teeCodeRank [v.toAdmin, .plain (.localTee x)] := by
  simp [teeAdminRank]

end Silmaril.Wasm.Execution.Core.Sim
