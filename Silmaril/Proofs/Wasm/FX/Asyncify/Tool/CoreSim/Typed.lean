module

public import Silmaril.Wasm.FX.Asyncify.Tool.CoreSim.Defs
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Rel
public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Macro

/-!
# The asyncified program passes the checker

`envOk_asyncify`: for a well-formed source, every body of `asyncifyProg P` checks (`EnvOk`):
operands never underflow inside an arm, locals are below the frame size `F`, only globals `0`
and `1` are used, `sp` (global 1) is only set to sums and differences of itself and multiples of
4, and every access is at `sp` or `0` plus a multiple of 4. Built from the pieces of the pass
(`run_restore`, `run_saveCode`, `run_chk`, `run_pushAns`, …) composed by `ck_seq`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim

open Silmaril.Wasm
open Silmaril.Wasm.FX.Asyncify.Tool

variable {X : CkCtx}

/-- Straight-line code from abstract stack `a` to `b`. -/
abbrev Run (X : CkCtx) (c : List Instr) (a b : List Bool) : Prop := Ck X (· = b) c a

theorem ck_append {Q₁ : List Bool → Prop} {c₁ : List Instr} {a : List Bool}
    (h : Ck X Q₁ c₁ a) : ∀ {Q : List Bool → Prop} {c₂ : List Instr},
      (∀ b, Q₁ b → Ck X Q c₂ b) → Ck X Q (c₁ ++ c₂) a := by
  induction h with
  | nil hq => exact fun h2 => h2 _ hq
  | ret hn => exact fun _ => .ret hn
  | ins hi _ ih => exact fun h2 => .ins hi (ih h2)
  | ifE ht he _ _ _ ih => exact fun h2 => .ifE ht he (ih h2)

theorem ck_seq {Q : List Bool → Prop} {c₁ c₂ : List Instr} {a b : List Bool}
    (h1 : Run X c₁ a b) (h2 : Ck X Q c₂ b) : Ck X Q (c₁ ++ c₂) a :=
  ck_append h1 fun _ hb => hb ▸ h2

theorem ins1 {i : Instr} {a b : List Bool} (h : InsOk X i a b) : Run X [i] a b := .ins h (.nil rfl)

theorem ck_mono {Q Q' : List Bool → Prop} {c : List Instr} {a : List Bool} (h : Ck X Q c a)
    (hq : ∀ b, Q b → Q' b) : Ck X Q' c a := by
  have h' := ck_append (c₂ := []) h fun b hb => .nil (hq b hb)
  rwa [List.append_nil] at h'

/-! ## Instructions of the pass -/

theorem c32_al {n : Nat} (h : n % 4 = 0) : decide ((BitVec.ofNat 32 n).toNat % 4 = 0) = true := by
  rw [BitVec.toNat_ofNat]
  exact decide_eq_true (by omega)

theorem run_c32 (n : Nat) (a : List Bool) :
    Run X [c32 n] a (decide ((BitVec.ofNat 32 n).toNat % 4 = 0) :: a) := ins1 .const

theorem run_c32_al {n : Nat} (h : n % 4 = 0) (a : List Bool) : Run X [c32 n] a (true :: a) := by
  have h1 := run_c32 (X := X) n a
  rwa [c32_al h] at h1

theorem run_gState (a : List Bool) : Run X [gState] a (false :: a) := ins1 (.gget (by decide))

theorem run_gSp (a : List Bool) : Run X [gSp] a (true :: a) := ins1 (.gget (by decide))

theorem run_sState (b : Bool) (a : List Bool) : Run X [sState] (b :: a) a :=
  ins1 (.gset (by decide) fun h => absurd h (by decide))

theorem run_sSp (a : List Bool) : Run X [sSp] (true :: a) a :=
  ins1 (.gset (by decide) fun _ => rfl)

theorem run_rel {op : IntRelOp} (y x : Bool) (a : List Bool) :
    Run X [.intRelOp .i32 op] (y :: x :: a) (false :: a) := ins1 .rel

theorem marg_al {o : Nat} (ho : o % 4 = 0) (h : o < 2 ^ 64) : (marg o).offset.val % 4 = 0 := by
  rw [marg_off h]; exact ho

theorem run_ld {o : Nat} (ho : o % 4 = 0) (h : o < 2 ^ 64) (a : List Bool) :
    Run X [ld o] (true :: a) (false :: a) := ins1 (.load (marg_al ho h))

theorem run_st {o : Nat} (ho : o % 4 = 0) (h : o < 2 ^ 64) (b : Bool) (a : List Bool) :
    Run X [st o] (b :: true :: a) a := ins1 (.store (marg_al ho h))

theorem lidx_lt {i : Nat} (hi : i < X.L) (hL : X.L < 2 ^ 32) : (lidx i).value.val < X.L := by
  rw [lidx_val (by omega)]; exact hi

/-! ## Saving and restoring frames -/

theorem run_loadLocals (hL : X.L < 2 ^ 30) :
    ∀ (i n : Nat) (a : List Bool), i + n ≤ X.L → Run X (loadLocals i n) a a
  | _, 0, a, _ => .nil rfl
  | i, n + 1, a, h => by
    have h1 : Run X [gSp, ld (4 * i), .localSet (lidx i)] a a :=
      ck_seq (run_gSp a) (ck_seq (run_ld (by omega) (by omega) a)
        (ins1 (.set (lidx_lt (by omega) (by omega)))))
    exact ck_seq h1 (run_loadLocals hL (i + 1) n a (by omega))

theorem run_saveLocals (hL : X.L < 2 ^ 30) :
    ∀ (i n : Nat) (a : List Bool), i + n ≤ X.L → Run X (saveLocals i n) a a
  | _, 0, a, _ => .nil rfl
  | i, n + 1, a, h => by
    have h1 : Run X [gSp, .localGet (lidx i), st (4 * i)] a a :=
      ck_seq (run_gSp a) (ck_seq (ins1 (.get (lidx_lt (by omega) (by omega))))
        (run_st (by omega) (by omega) false a))
    exact ck_seq h1 (run_saveLocals hL (i + 1) n a (by omega))

theorem run_restore {F : Nat} (hF : F = X.L) (hL : X.L < 2 ^ 26) :
    Run X (restoreCode F) [] [] := by
  have h1 : Run X [gSp, c32 (4 * F), subI, sSp] [] [] :=
    ck_seq (run_gSp []) (ck_seq (run_c32_al (by omega) _) (ck_seq (ins1 .bin) (run_sSp [])))
  exact ck_seq h1 (run_loadLocals (by omega) 0 F [] (by omega))

theorem run_saveCode {F : Nat} (k : Nat) (hF : F = X.L) (hL : X.L < 2 ^ 26) (hF1 : 1 ≤ F)
    (a : List Bool) : Run X (saveCode F k) a a := by
  have h1 : Run X [gSp, c32 k, st (4 * (F - 1)), gSp, c32 (4 * F), addI, sSp] a a :=
    ck_seq (run_gSp a) (ck_seq (run_c32 k _) (ck_seq (run_st (by omega) (by omega) _ a)
      (ck_seq (run_gSp a) (ck_seq (run_c32_al (by omega) _) (ck_seq (ins1 .bin) (run_sSp a))))))
  exact ck_seq (run_saveLocals (by omega) 0 (F - 1) a (by omega)) h1

theorem run_prologue {F : Nat} (hF : F = X.L) (hL : X.L < 2 ^ 26) (a : List Bool) :
    Run X (prologue F) a a :=
  ck_seq (run_gState a) (ck_seq (run_c32 2 _) (ck_seq (run_rel _ _ a)
    (.ifE (run_restore hF hL) (.nil rfl) (.nil rfl))))

theorem run_dummies (n : Nat) (a : List Bool) :
    Run X (dummies n) a (List.replicate n true ++ a) := by
  induction n generalizing a with
  | zero => exact .nil rfl
  | succ n ih =>
    have h := ck_seq (run_c32_al (X := X) (n := 0) rfl a) (ih (true :: a))
    have e : List.replicate (n + 1) true ++ a = List.replicate n true ++ true :: a := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    rw [e]; exact h

/-- The arm after a call: save the frame, dummy results, `return`. -/
theorem ck_saveRet {F : Nat} (k : Nat) (hF : F = X.L) (hL : X.L < 2 ^ 26) (hF1 : 1 ≤ F) :
    Ck X (· = []) (saveCode F k ++ dummies X.nres ++ [.return_]) [] := by
  rw [List.append_assoc]
  exact ck_seq (run_saveCode k hF hL hF1 []) (ck_seq (run_dummies X.nres [])
    (.ret (by simp only [List.length_append, List.length_replicate, List.length_nil]; omega)))

theorem run_chk {F : Nat} (k : Nat) (hF : F = X.L) (hL : X.L < 2 ^ 26) (hF1 : 1 ≤ F)
    (a : List Bool) : Run X (chk F k X.nres) a a :=
  ck_seq (run_gState a) (ck_seq (run_c32 1 _) (ck_seq (run_rel _ _ a)
    (.ifE (ck_saveRet k hF hL hF1) (.nil rfl) (.nil rfl))))

/-! ## Requests and answers -/

theorem run_pushAns :
    ∀ (j m : Nat) (a : List Bool), j + m < 2 ^ 60 →
      Run X (pushAns j m) a (List.replicate m false ++ a)
  | _, 0, a, _ => .nil rfl
  | j, m + 1, a, hj => by
    have h1 : Run X [c32 0, ld (4 * j)] a (false :: a) :=
      ck_seq (run_c32_al (n := 0) rfl a) (run_ld (by omega) (by omega) a)
    have h := ck_seq h1 (run_pushAns (j + 1) m (false :: a) (by omega))
    have e : List.replicate (m + 1) false ++ a = List.replicate m false ++ false :: a := by
      rw [List.replicate_succ', List.append_assoc]; rfl
    rw [e]; exact h

theorem run_sets (hL : X.L < 2 ^ 32) :
    ∀ (l : List LocalIdx) (p a : List Bool), p.length = l.length → (∀ r ∈ l, r.value.val < X.L) →
      Run X (l.map .localSet) (p ++ a) a
  | [], [], a, _, _ => .nil rfl
  | r :: l, b :: p, a, hp, hr =>
    ck_seq (ins1 (.set (hr r (List.mem_cons_self ..))))
      (run_sets hL l p a (by simpa using hp) fun r' h => hr r' (List.mem_cons_of_mem _ h))

theorem run_setsCode (hL : X.L < 2 ^ 32) {rs : List LocalIdx} {p : List Bool} (a : List Bool)
    (hp : p.length = rs.length) (hr : ∀ r ∈ rs, r.value.val < X.L) :
    Run X (setsCode rs) (p ++ a) a :=
  run_sets hL rs.reverse p a (by rw [List.length_reverse]; exact hp)
    fun r h => hr r (List.mem_reverse.1 h)

theorem run_getsCode : ∀ {as : List LocalIdx} (a : List Bool), (∀ x ∈ as, x.value.val < X.L) →
    Run X (getsCode as) a (List.replicate as.length false ++ a)
  | [], a, _ => .nil rfl
  | x :: as, a, h => by
    have h1 := ck_seq (ins1 (X := X) (.get (h x (List.mem_cons_self ..))) : Run X _ a (false :: a))
      (run_getsCode (false :: a) fun y hy => h y (List.mem_cons_of_mem _ hy))
    have e : List.replicate (x :: as).length false ++ a =
        List.replicate as.length false ++ false :: a := by
      rw [List.length_cons, List.replicate_succ', List.append_assoc]; rfl
    rw [e]; exact h1

theorem run_reqArgs :
    ∀ (j : Nat) (as : List LocalIdx) (a : List Bool), j + as.length < 2 ^ 60 →
      (∀ x ∈ as, x.value.val < X.L) → Run X (reqArgs j as) a a
  | _, [], a, _, _ => .nil rfl
  | j, x :: as, a, hj, h => by
    have h1 : Run X [c32 0, .localGet x, st (4 * j)] a a :=
      ck_seq (run_c32_al (n := 0) rfl a) (ck_seq (ins1 (.get (h x (List.mem_cons_self ..))))
        (run_st (by omega) (by simp only [List.length_cons] at hj; omega) false a))
    exact ck_seq h1 (run_reqArgs (j + 1) as a (by simp only [List.length_cons] at hj; omega)
      fun y hy => h y (List.mem_cons_of_mem _ hy))

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.CoreSim
