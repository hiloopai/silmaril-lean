module

public import Silmaril.Proofs.Wasm.SSA.Translate.BackCons

/-!
# The translation reflects SSA runs: structured control, operands and bodies
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

theorem TgtL_pushLabel_eq_ldepth {c : Ctx} {B : Nat} (hwfb : WFB c B) (hB : B ≤ c.ldepth)
    {o : Out (Option WVal)} {x : SVal} (h : TgtL c.pushLabel o = some (c.ldepth, x)) :
    ∃ ls r, o = .brk 0 ls r ∧ x = packV ls r := by
  cases o with
  | ok => simp [TgtL] at h
  | brk l ls r =>
      cases l with
      | zero => rw [TgtL_pushLabel_zero] at h; simp at h; exact ⟨ls, r, rfl, h.symm⟩
      | succ l =>
          rw [TgtL_pushLabel_succ] at h
          have := hwfb.tgt h; omega
  | ret r => rw [TgtL_pushLabel_ret] at h; have := hwfb.tgt h; omega
  | trap => rw [TgtL_pushLabel_trap] at h; have := hwfb.tgt h; omega

/-- A construct's CFG entered at its join block: the continuation runs and leaves through a
label of the context. -/
private theorem construct_join {B : Nat} {c : Ctx} {env : Env WVal} {ty : Option IntType}
    {k : Ctx → Option Nat → Region Prim} {ls' : List WVal} {r : Option WVal} {first L : Nat}
    {x v : SVal} (hB : B ≤ c.ldepth) (hk : KB B c env k) (hl : ls'.length = c.locals.length)
    (hf : Follow1 env (fun _ => joinBlock c.enter ty k) first x L v) (h0 : first = 0)
    (hx : x = packV ls' r) :
    BlockOk ty r ∧ ∃ m, m < B ∧ L = c.lbl m ∧ BPost c env k m v (.ok ls' (blockRes ty r)) := by
  rcases follow1_inv hf with ⟨h1, -, -⟩ | ⟨-, next, y, hb, hf'⟩
  · omega
  · obtain ⟨hok, c', env', rl, hext, hld, hag', hres, hk'⟩ := join_inv hl (hx ▸ hb)
    obtain ⟨m, hm, hnext⟩ := hk c' env' rl ls' _ _ _ hext hag' hres hk'
    have hlbl : next = c.ldepth - m := by rw [hnext]; simp only [Ctx.lbl, hld]; omega
    rcases follow1_inv hf' with ⟨-, hL, hv⟩ | ⟨h0', -⟩
    · have hL' : L = c.lbl m := by simp only [Ctx.lbl]; omega
      exact ⟨hok, m, hm, hL', c', env', rl, hext, hag', hres, hv ▸ hnext ▸ hk'⟩
    · omega

/-- A construct's CFG left before its join block: the exit is a label of the context. -/
private theorem construct_exit {B : Nat} {c : Ctx} {env : Env WVal} {ty : Option IntType}
    {k : Ctx → Option Nat → Region Prim} {bs : Fin 1 → Region Prim} {o₁ o : Out (Option WVal)}
    {m₁ first L : Nat} {x v : SVal} (hwfb : WFB c B) (hB : B ≤ c.ldepth)
    (hf : Follow1 env bs first x L v) (hfirst : first = c.ldepth + 1 - 1 - m₁)
    (ht : TgtL c o = some (m₁, x)) (hbx : BlockExit ty o₁ o) :
    m₁ < B ∧ L = c.lbl m₁ ∧ BPost c env k m₁ v o := by
  have hm : m₁ < B := hwfb.tgt ht
  rcases follow1_inv hf with ⟨-, hL, hv⟩ | ⟨h0, -⟩
  · have hpost : BPost c env k m₁ v o := by
      cases hbx <;> first | exact hv ▸ ht | simp [TgtL] at ht
    exact ⟨hm, by simp only [Ctx.lbl]; omega, hpost⟩
  · omega

/-- A structured construct: its CFG runs the entry to the join, or leaves. -/
theorem construct_inv {B : Nat} {c : Ctx} {env : Env WVal} {ty : Option IntType}
    {k : Ctx → Option Nat → Region Prim} {entry : Region Prim} {L : Nat} {v : SVal}
    {ls₀ : List WVal} {P : Out (Option WVal) → Prop}
    (hwfb : WFB c B) (hB : B ≤ c.ldepth) (hk : KB B c env k)
    (hl0 : ls₀.length = c.locals.length)
    (hentry : ∀ L' x, REval env entry L' x → ∃ m₁ o₁, m₁ < c.ldepth + 1 ∧ L' = c.ldepth - m₁ ∧
      P o₁ ∧ LenOK ls₀ o₁ ∧
      Post o₁ (fun ls' r => m₁ = c.ldepth ∧ x = packV ls' r) (TgtL c.pushLabel o₁ = some (m₁, x)))
    (h : REval env (.cfg entry 1 fun _ => joinBlock c.enter ty k) L v) :
    ∃ m o₁ o, m < B ∧ L = c.lbl m ∧ P o₁ ∧ BlockExit ty o₁ o ∧ BPost c env k m v o := by
  obtain ⟨first, x, he, hf⟩ := cfg1_inv h
  obtain ⟨m₁, o₁, hm₁, hfirst, hP, hlen, hpo⟩ := hentry _ _ he
  have exit : ∀ o, TgtL c o = some (m₁, x) → BlockExit ty o₁ o →
      ∃ m o₁ o, m < B ∧ L = c.lbl m ∧ P o₁ ∧ BlockExit ty o₁ o ∧ BPost c env k m v o := by
    intro o ht hbx
    obtain ⟨hm, hL, hpost⟩ := construct_exit (k := k) hwfb hB hf (by omega) ht hbx
    exact ⟨m₁, o₁, o, hm, hL, hP, hbx, hpost⟩
  cases o₁ with
  | ok ls' r =>
      have hl : ls'.length = c.locals.length := by simp only [LenOK] at hlen; omega
      obtain ⟨hm₁', hx⟩ : m₁ = c.ldepth ∧ x = packV ls' r := hpo
      obtain ⟨hok, m, hm, hL, hpost⟩ := construct_join hB hk hl hf (by omega) hx
      exact ⟨m, _, _, hm, hL, hP, .ok hok, hpost⟩
  | brk l ls' r =>
      show ∃ m o₁ o, m < B ∧ L = c.lbl m ∧ P o₁ ∧ BlockExit ty o₁ o ∧ BPost c env k m v o
      cases l with
      | zero =>
          have hpo' : some (c.ldepth, packV ls' r) = some (m₁, x) :=
            (TgtL_pushLabel_zero c ls' r).symm.trans hpo
          have hl : ls'.length = c.locals.length := by simp only [LenOK] at hlen; omega
          obtain ⟨hm₁', hx⟩ : c.ldepth = m₁ ∧ packV ls' r = x := by
            simpa only [Option.some.injEq, Prod.mk.injEq] using hpo'
          obtain ⟨hok, m, hm, hL, hpost⟩ := construct_join hB hk hl hf (by omega) hx.symm
          exact ⟨m, _, _, hm, hL, hP, .brk0 hok, hpost⟩
      | succ l =>
          exact exit _ ((TgtL_pushLabel_succ c _ _ _).symm.trans hpo) .brk
  | ret r => exact exit _ ((TgtL_pushLabel_ret c _).symm.trans hpo) .ret
  | trap => exact exit _ ((TgtL_pushLabel_trap c).symm.trans hpo) .trap

/-- The entry of a block or an `if` arm: the body leaves to the join or out. -/
theorem body_entry {body : List Expr} (hs : BackSeq body) {c₁ : Ctx} {env₁ : Env WVal}
    {ls : List WVal} {jl : Nat} (hwf : WF c₁) (hag : Agree c₁ env₁ ls) (hjl : jl < c₁.ldepth)
    {L' : Nat} {x : SVal}
    (h : REval env₁ (cSeq body c₁ none fun c' r => .br (c'.lbl jl) (c'.pack r)) L' x) :
    ∃ m₁ o₁, m₁ < c₁.ldepth ∧ L' = c₁.lbl m₁ ∧ Seq ls none body o₁ ∧
      Post o₁ (fun ls' r => m₁ = jl ∧ x = packV ls' r) (TgtL c₁ o₁ = some (m₁, x)) := by
  have hK : KB c₁.ldepth c₁ env₁ fun c' r => .br (c'.lbl jl) (c'.pack r) := by
    intro c' env' rl ls' r L v hext hag' hres h'
    obtain ⟨rfl, -⟩ := br_inv h'
    exact ⟨jl, hjl, rfl⟩
  obtain ⟨m₁, o₁, hm₁, rfl, hseq, hpo⟩ :=
    hs c₁.ldepth ls none c₁ env₁ _ none L' x hwf hwf.wfb (le_refl _) hag trivial hK h
  refine ⟨m₁, o₁, hm₁, rfl, hseq, ?_⟩
  cases o₁ with
  | ok ls' r =>
      obtain ⟨c', env', rl, hext, hag', hres, h'⟩ := hpo
      obtain ⟨hL, hv⟩ := br_inv h'
      exact ⟨lbl_inj' (lt_of_lt_of_le hm₁ hext.ldepth) (lt_of_lt_of_le hjl hext.ldepth) hL.symm,
        teval_det hv (eval_pack hag' hres)⟩
  | _ => exact hpo

theorem back_block {ty : Option IntType} {body : List Expr} (hs : BackSeq body) :
    BackE (.block ty body) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  have hentry : ∀ L' x, REval env (cSeq body c.pushLabel none fun c' r =>
      .br (c'.lbl c.ldepth) (c'.pack r)) L' x → ∃ m₁ o₁, m₁ < c.ldepth + 1 ∧ L' = c.ldepth - m₁ ∧
      Seq ls none body o₁ ∧ LenOK ls o₁ ∧
      Post o₁ (fun ls' r => m₁ = c.ldepth ∧ x = packV ls' r) (TgtL c.pushLabel o₁ = some (m₁, x)) := by
    intro L' x he
    obtain ⟨m₁, o₁, hm₁, rfl, hseq, hpo⟩ :=
      body_entry hs hwf.pushLabel hag (show c.ldepth < c.pushLabel.ldepth by simp [Ctx.pushLabel]) he
    exact ⟨m₁, o₁, hm₁, lbl_pushLabel c m₁, hseq, seq_len hseq, hpo⟩
  obtain ⟨m, o₁, o, hm, rfl, hseq, hbx, hpost⟩ :=
    construct_inv (P := fun o₁ => Seq ls none body o₁) hwfb hB hk hag.length.symm hentry h
  exact ⟨m, o, hm, rfl, .block hseq hbx, hpost⟩

/-- The `if` dispatch on a condition level: a truthy test selects the arm that runs. -/
private theorem truthy_case_inv {c : Ctx} {env : Env WVal} {l : Nat} {cv : WVal}
    {A B : Region Prim} {L : Nat} {v : SVal} (hv : VarOK c env l cv)
    (h : REval env (.case (.op .truthy (c.var l)) A B) L v) :
    ∃ b va, cv.truthy = some b ∧ REval (extend env va) (if b then A else B) L v := by
  have hT : TEval env (c.var l) (.atom cv) := eval_var hv
  rcases case_inv h with ⟨va, hta, hb⟩ | ⟨va, hta, hb⟩
  · obtain ⟨vx, hvx, hr⟩ := op_inv hta
    obtain ⟨b, hb', hif⟩ := run_truthy_inv (teval_det hvx hT ▸ hr)
    cases b with
    | false => cases hif
    | true => exact ⟨true, va, hb', hb⟩
  · obtain ⟨vx, hvx, hr⟩ := op_inv hta
    obtain ⟨b, hb', hif⟩ := run_truthy_inv (teval_det hvx hT ▸ hr)
    cases b with
    | true => cases hif
    | false => exact ⟨false, va, hb', hb⟩

/-- An `if` arm, entered after the condition, leaves to the join or out. -/
private theorem if_arm_entry {body : List Expr} (hs : BackSeq body) {c : Ctx} {env : Env WVal}
    {ls : List WVal} {va : SVal} {L : Nat} {x : SVal} (hwf : WF c) (hag : Agree c env ls)
    (h : REval (extend env va)
      (cSeq body c.pushLabel.bind none fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) L x) :
    ∃ m₁ o₁, m₁ < c.ldepth + 1 ∧ L = c.ldepth - m₁ ∧ Seq ls none body o₁ ∧ LenOK ls o₁ ∧
      Post o₁ (fun ls' r => m₁ = c.ldepth ∧ x = packV ls' r)
        (TgtL c.pushLabel o₁ = some (m₁, x)) := by
  obtain ⟨m₁, o₁, hm₁, hL, hseq, hpo⟩ :=
    body_entry hs (c₁ := c.pushLabel.bind) hwf.pushLabel (hag.bind _)
      (show c.ldepth < c.pushLabel.bind.ldepth by simp [Ctx.pushLabel, Ctx.bind]) h
  have hL' : L = c.ldepth - m₁ := by rw [hL]; simp [Ctx.lbl, Ctx.pushLabel, Ctx.bind]
  exact ⟨m₁, o₁, hm₁, hL', hseq, seq_len hseq, hpo⟩

theorem back_if {ty : Option IntType} {cnd : Expr} {t e : List Expr} (hc : BackE cnd)
    (ht : BackSeq t) (he : BackSeq e) : BackE (.if_ ty cnd t e) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cE] at h
  -- the construct after the condition
  have core : ∀ c' env' l ls₁ cv L' v', Ext c env c' env' → Agree c' env' ls₁ →
      VarOK c' env' l cv →
      REval env' (.cfg (.case (.op .truthy (c'.var l))
          (cSeq t c'.pushLabel.bind none fun c'' r => .br (c''.lbl c'.ldepth) (c''.pack r))
          (cSeq e c'.pushLabel.bind none fun c'' r => .br (c''.lbl c'.ldepth) (c''.pack r)))
        1 fun _ => joinBlock c'.enter ty k) L' v' →
      ∃ m o₁ o, m < B ∧ L' = c'.lbl m ∧
        (∃ b, cv.truthy = some b ∧ Seq ls₁ none (if b then t else e) o₁) ∧
        BlockExit ty o₁ o ∧ BPost c' env' k m v' o := by
    intro c' env' l ls₁ cv L' v' hext hag' hv h'
    refine construct_inv (hwfb.ext hext) (le_trans hB hext.ldepth) (hk.ext hext)
      hag'.length.symm ?_ h'
    intro L'' x hent
    obtain ⟨b, va, hb', hbody⟩ := truthy_case_inv hv hent
    have hs : BackSeq (if b then t else e) := by cases b <;> assumption
    have hbody' : REval (extend env' va) (cSeq (if b then t else e) c'.pushLabel.bind none
        fun c'' r => .br (c''.lbl c'.ldepth) (c''.pack r)) L'' x := by
      cases b <;> exact hbody
    obtain ⟨m₁, o₁, hm₁, hL, hseq, hlen, hpo⟩ := if_arm_entry hs (hwf.ext hext) hag' hbody'
    exact ⟨m₁, o₁, hm₁, hL, ⟨b, hb', hseq⟩, hlen, hpo⟩
  have hK : KB B c env (fun c r =>
      match r with
      | some l =>
          .cfg (.case (.op .truthy (c.var l))
              (cSeq t c.pushLabel.bind none fun c' r => .br (c'.lbl c.ldepth) (c'.pack r))
              (cSeq e c.pushLabel.bind none fun c' r => .br (c'.lbl c.ldepth) (c'.pack r)))
            1 fun _ => joinBlock c.enter ty k
      | none => stuck) := by
    intro c' env' rl ls' r L' v' hext hag' hres h'
    match rl, r, hres with
    | some l, some cv, hv =>
        obtain ⟨m, -, -, hm, hL, -⟩ := core c' env' l ls' cv L' v' hext hag' hv h'
        exact ⟨m, hm, hL⟩
    | none, _, _ => exact (stuck_inv h').elim
    | some _, none, hres => exact hres.elim
  obtain ⟨m, oc, hm, hL, hex, hpost⟩ := hc B ls c env _ L v hwf hwfb hB hag hK h
  cases oc with
  | ok ls₁ r =>
      show ∃ m o, m < B ∧ L = c.lbl m ∧ Exec ls (.if_ ty cnd t e) o ∧ BPost c env k m v o
      obtain ⟨c', env', rl, hext, hag', hres, h'⟩ := hpost
      match rl, r, hres with
      | some l, some cv, hv =>
          obtain ⟨m', o₁, o, hm', hL', ⟨b, hb, hseq⟩, hbx, hpo⟩ :=
            core c' env' l ls₁ cv _ v hext hag' hv h'
          have hmm : m = m' := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
            (lt_of_lt_of_le (lt_of_lt_of_le hm' hB) hext.ldepth) hL'.symm
          exact ⟨m, o, hm, hL, .if_ hex hb hseq hbx, bpost_ext hext (hmm ▸ hpo)⟩
      | none, _, _ => exact (stuck_inv h').elim
      | some _, none, hres => exact hres.elim
  | _ => exact ⟨m, _, hm, hL, .if_abrupt hex trivial, bpost_abrupt hpost trivial⟩

end Silmaril.Proofs.Wasm.SSA.Translate
