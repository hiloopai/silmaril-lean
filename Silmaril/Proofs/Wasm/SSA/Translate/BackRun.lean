module

public import Silmaril.Proofs.Wasm.SSA.Translate.BackCtl
public import Silmaril.Proofs.Wasm.SSA.Translate.Run

/-!
# The translation reflects SSA runs: `br_if`, operands, bodies, loops

`backE`/`backArgs`/`backSeq` are the structural induction over the
fragment's syntax; loops use an induction on the header's CFG execution
(`loop_follow`). `compileFunc_complete`: every terminating run of the
translation is a run of the source.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.SSA.Translate

open Silmaril.Wasm (IntType)
open Silmaril.Wasm.SSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

/-! ## `br_if` -/

/-- The operand continuation of `br_if l` in context `c`: test the last operand, then jump
to label `l` or continue with `k`. -/
private def brIfK (c : Ctx) (l : Nat) (k : Ctx → Option Nat → Region Prim) :
    Ctx → List Nat → Region Prim := fun c' vs =>
  match vs.getLast? with
  | some cl =>
      .case (.op .truthy (c'.var cl))
        (match c.labels[l]? with
          | some lk => jump c'.bind lk vs.dropLast.head?
          | none => stuck)
        (k c'.bind vs.dropLast.head?)
  | none => stuck

/-- A run of `brIfK`: the test on the last operand either jumps or continues. -/
private theorem brIfK_inv {c c' : Ctx} {l : Nat} {k : Ctx → Option Nat → Region Prim}
    {env : Env WVal} {lvls : List Nat} {L : Nat} {v : SVal}
    (h : REval env (brIfK c l k c' lvls) L v) :
    ∃ cl va, lvls.getLast? = some cl ∧
      ((TEval env (.op .truthy (c'.var cl)) (.inl va) ∧ ∃ lk, c.labels[l]? = some lk ∧
          REval (extend env va) (jump c'.bind lk lvls.dropLast.head?) L v) ∨
        (TEval env (.op .truthy (c'.var cl)) (.inr va) ∧
          REval (extend env va) (k c'.bind lvls.dropLast.head?) L v)) := by
  cases hcl : lvls.getLast? with
  | none => exact (stuck_inv (by simpa only [brIfK, hcl] using h)).elim
  | some cl =>
      simp only [brIfK, hcl] at h
      rcases case_inv h with ⟨va, hta, hb⟩ | ⟨va, hta, hb⟩
      · cases hlab : c.labels[l]? with
        | none => exact (stuck_inv (by simpa only [hlab] using hb)).elim
        | some lk => exact ⟨cl, va, rfl, .inl ⟨hta, lk, rfl, by simpa only [hlab] using hb⟩⟩
      · exact ⟨cl, va, rfl, .inr ⟨hta, hb⟩⟩

/-- A truthiness test of a level holding `cv`. -/
private theorem truthy_eval_inv {c : Ctx} {env : Env WVal} {l : Nat} {cv : WVal} {x : SVal}
    (hv : VarOK c env l cv) (h : TEval env (.op .truthy (c.var l)) x) :
    ∃ b, cv.truthy = some b ∧ x = if b then .inl .unit else .inr .unit := by
  obtain ⟨vx, hvx, hr⟩ := op_inv h
  exact run_truthy_inv (eval_var_inv hv hvx ▸ hr)

private theorem truthy_inl_inv {c : Ctx} {env : Env WVal} {l : Nat} {cv : WVal} {va : SVal}
    (hv : VarOK c env l cv) (h : TEval env (.op .truthy (c.var l)) (.inl va)) :
    cv.truthy = some true := by
  obtain ⟨b, hb, hif⟩ := truthy_eval_inv hv h
  cases b with
  | false => cases hif
  | true => exact hb

private theorem truthy_inr_inv {c : Ctx} {env : Env WVal} {l : Nat} {cv : WVal} {va : SVal}
    (hv : VarOK c env l cv) (h : TEval env (.op .truthy (c.var l)) (.inr va)) :
    cv.truthy = some false := by
  obtain ⟨b, hb, hif⟩ := truthy_eval_inv hv h
  cases b with
  | false => exact hb
  | true => cases hif

theorem back_brIf {l : Nat} {args : List Expr} (ha : BackArgs args) : BackE (.brIf l args) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  have h' : REval env (cArgs args c (brIfK c l k)) L v := h
  have hres : ∀ {c' env' lvls vs} va, List.Forall₂ (VarOK c' env') lvls vs →
      ResOK c'.bind (extend env' va) lvls.dropLast.head? vs.dropLast.head? :=
    fun va hl => ResOK.ext (Ext.bind _ _ va) (resOK_head? (forall₂_dropLast hl))
  have hK : KBs B c env (brIfK c l k) := by
    intro c' env' lvls ls' vs L' v' hext hag' hl h'
    obtain ⟨cl, va, -, ⟨-, lk, hlab, hb⟩ | ⟨-, hb⟩⟩ := brIfK_inv h'
    · obtain ⟨m, hm, hL, -⟩ :=
        jump_inv hwfb (hext.trans (Ext.bind _ _ va)) (hag'.bind _) (hres va hl) hlab hb
      exact ⟨m, hm, hL⟩
    · exact hk c'.bind (extend env' va) _ ls' vs.dropLast.head? L' v'
        (hext.trans (Ext.bind _ _ va)) (hag'.bind _) (hres va hl) hb
  obtain ⟨m, oa, hm, hLm, hargs, hpost⟩ := ha B ls c env _ L v hwf hwfb hB hag hK h'
  cases oa with
  | ok ls' vs =>
      show ∃ m o, m < B ∧ L = c.lbl m ∧ Exec ls (.brIf l args) o ∧ BPost c env k m v o
      obtain ⟨c', env', lvls, hext, hag', hl, h'⟩ := hpost
      obtain ⟨cl, va, hcl, hbr⟩ := brIfK_inv h'
      obtain ⟨cv, hcv, hvcl⟩ := forall₂_getLast?_left hl hcl
      rcases hbr with ⟨hta, lk, hlab, hb⟩ | ⟨hta, hb⟩
      · have hb' : cv.truthy = some true := truthy_inl_inv hvcl hta
        obtain ⟨m', hm', hL, ht⟩ :=
          jump_inv hwfb (hext.trans (Ext.bind _ _ _)) (hag'.bind _) (hres va hl) hlab hb
        have hmm : m = m' := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
          (lt_of_lt_of_le (lt_of_lt_of_le hm' hB) hext.ldepth) hL.symm
        have hx : Exec ls (.brIf l args) (.brk l ls' vs.dropLast.head?) :=
          Exec.brIf (l := l) hargs hcv hb'
        exact ⟨m, _, hm, hLm, hx, hmm ▸ (TgtL_brk_any _ _ _).trans ht⟩
      · have hb' : cv.truthy = some false := truthy_inr_inv hvcl hta
        have hx : Exec ls (.brIf l args) (.ok ls' vs.dropLast.head?) :=
          Exec.brIf (l := l) hargs hcv hb'
        exact ⟨m, _, hm, hLm, hx, c'.bind, _, _, hext.trans (Ext.bind _ _ _), hag'.bind _,
          hres va hl, hb⟩
  | _ => exact ⟨m, _, hm, hLm, .brIf_abrupt hargs trivial, bposts_cast hpost trivial⟩

theorem bpost_cast_s {c : Ctx} {env : Env WVal} {k : Ctx → Option Nat → Region Prim}
    {k' : Ctx → List Nat → Region Prim} {m : Nat} {v : SVal} {o : Out (Option WVal)}
    (h : BPost c env k m v o) (hab : o.Abrupt) : BPostS c env k' m v o.cast := by
  unfold BPost BPostS at *
  rw [post_abrupt (Out.cast_abrupt _ hab), TgtL_cast hab]
  rw [post_abrupt hab] at h; exact h

/-! ## Operands and bodies -/

theorem back_args_nil : BackArgs [] := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  rw [cArgs] at h
  obtain ⟨m, hm, rfl⟩ := hk c env [] ls [] L v (Ext.refl _ _) hag .nil h
  exact ⟨m, _, hm, rfl, .nil, c, env, [], Ext.refl _ _, hag, .nil, h⟩

/-- An abrupt operand outcome's postcondition moves to an outer context and any
continuation. -/
private theorem bpostS_abrupt_ext {c c' : Ctx} {env env' : Env WVal}
    {k₁ k₂ : Ctx → List Nat → Region Prim} {m : Nat} {v : SVal} {o : Out (List WVal)}
    (h : Ext c env c' env') (hp : BPostS c' env' k₁ m v o) (hab : o.Abrupt) :
    BPostS c env k₂ m v o := by
  have hq : TgtL c' o = some (m, v) := by simpa only [BPostS, post_abrupt hab] using hp
  show Post o _ (TgtL c o = some (m, v))
  rw [post_abrupt hab, ← TgtL_ext h]
  exact hq

/-- The operands after a head operand `w` at level `l`: their outcome is that of the list. -/
private theorem args_tail {ls ls₁ : List WVal} {e : Expr} {es : List Expr} {w : WVal}
    {c c' : Ctx} {env env' : Env WVal} {l m : Nat} {v : SVal} {k : Ctx → List Nat → Region Prim}
    {o' : Out (List WVal)} (hex : Exec ls e (.ok ls₁ (some w))) (hext : Ext c env c' env')
    (hv : VarOK c' env' l w) (hargs : Args ls₁ es o')
    (hpost : BPostS c' env' (fun c ls => k c (l :: ls)) m v o') :
    ∃ o, Args ls (e :: es) o ∧ BPostS c env k m v o := by
  cases o' with
  | ok ls₂ vs =>
      obtain ⟨c'', env'', lvls, hext', hag'', hl, h''⟩ := hpost
      exact ⟨_, .cons hex hargs, c'', env'', l :: lvls, hext.trans hext', hag'',
        .cons (VarOK.ext hext' hv) hl, h''⟩
  | _ => exact ⟨_, .tail_abrupt hex hargs trivial, bpostS_abrupt_ext hext hpost trivial⟩

theorem back_args_cons {e : Expr} {es : List Expr} (he : BackE e) (hes : BackArgs es) :
    BackArgs (e :: es) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  have inner : ∀ c' env' l w, Ext c env c' env' → VarOK c' env' l w →
      KBs B c' env' (fun c ls => k c (l :: ls)) := by
    intro c' env' l w hext hv c'' env'' lvls ls'' vs L'' v'' hext' hag'' hl h''
    exact hk c'' env'' (l :: lvls) ls'' (w :: vs) L'' v'' (hext.trans hext') hag''
      (.cons (VarOK.ext hext' hv) hl) h''
  let K : Ctx → Option Nat → Region Prim := fun c r =>
    match r with
    | some l => cArgs es c fun c ls => k c (l :: ls)
    | none => stuck
  have h' : REval env (cE e c K) L v := h
  have hK : KB B c env K := by
    intro c' env' rl ls' r L' v' hext hag' hres h'
    match rl, r, hres with
    | some l, some w, hv =>
        obtain ⟨m, -, hm, hL, -⟩ := hes B ls' c' env' _ L' v' (hwf.ext hext) (hwfb.ext hext)
          (le_trans hB hext.ldepth) hag' (inner c' env' l w hext hv) h'
        exact ⟨m, hm, hL⟩
    | none, _, _ => exact (stuck_inv h').elim
    | some _, none, hres => exact hres.elim
  obtain ⟨m, o, hm, hLm, hex, hpost⟩ := he B ls c env _ L v hwf hwfb hB hag hK h'
  cases o with
  | ok ls₁ r =>
      show ∃ m o, m < B ∧ L = c.lbl m ∧ Args ls (e :: es) o ∧ BPostS c env k m v o
      obtain ⟨c', env', rl, hext, hag', hres, h'⟩ := hpost
      match rl, r, hres with
      | some l, some w, hv =>
          obtain ⟨m', o', hm', hL, hargs, hpost'⟩ := hes B ls₁ c' env' _ _ v (hwf.ext hext)
            (hwfb.ext hext) (le_trans hB hext.ldepth) hag' (inner c' env' l w hext hv) h'
          have hmm : m' = m := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm' hB) hext.ldepth)
            (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth) hL
          obtain ⟨o, hargs', hpost''⟩ := args_tail hex hext hv hargs (hmm ▸ hpost')
          exact ⟨m, o, hm, hLm, hargs', hpost''⟩
      | none, _, _ => exact (stuck_inv h').elim
      | some _, none, hres => exact hres.elim
  | _ =>
      exact ⟨m, _, hm, hLm, .head_abrupt hex trivial, bpost_cast_s hpost trivial⟩

theorem back_seq_nil : BackSeq [] := by
  intro B ls r c env k rl L v hwf hwfb hB hag hres hk h
  rw [cSeq] at h
  obtain ⟨m, hm, rfl⟩ := hk c env rl ls r L v (Ext.refl _ _) hag hres h
  exact ⟨m, _, hm, rfl, .nil, c, env, rl, Ext.refl _ _, hag, hres, h⟩

theorem back_seq_cons {e : Expr} {es : List Expr} (he : BackE e) (hes : BackSeq es) :
    BackSeq (e :: es) := by
  intro B ls r c env k rl L v hwf hwfb hB hag hres hk h
  rw [cSeq] at h
  have hK : KB B c env (fun c r => cSeq es c r k) := by
    intro c' env' rl' ls' r' L' v' hext hag' hres' h'
    obtain ⟨m, -, hm, hL, -⟩ := hes B ls' r' c' env' k rl' L' v' (hwf.ext hext) (hwfb.ext hext)
      (le_trans hB hext.ldepth) hag' hres' (hk.ext hext) h'
    exact ⟨m, hm, hL⟩
  obtain ⟨m, o, hm, rfl, hex, hpost⟩ := he B ls c env _ L v hwf hwfb hB hag hK h
  cases o with
  | ok ls₁ r₁ =>
      obtain ⟨c', env', rl', hext, hag', hres', h'⟩ := hpost
      obtain ⟨m', o', hm', hL, hseq, hpost'⟩ := hes B ls₁ r₁ c' env' k rl' _ v (hwf.ext hext)
        (hwfb.ext hext) (le_trans hB hext.ldepth) hag' hres' (hk.ext hext) h'
      have : m = m' := lbl_inj' (lt_of_lt_of_le (lt_of_lt_of_le hm hB) hext.ldepth)
        (lt_of_lt_of_le (lt_of_lt_of_le hm' hB) hext.ldepth) hL.symm
      subst this
      exact ⟨m, o', hm, rfl, .cons hex hseq, bpost_ext hext hpost'⟩
  | _ => exact ⟨m, _, hm, rfl, .abrupt hex trivial, bpost_abrupt hpost trivial⟩

/-! ## Loops -/

/-- How the loop header's CFG run started on the locals `ls` ends: falling out normally
(exit `0`) or leaving through a label of `c`. -/
private def LoopRes (B : Nat) (c : Ctx) (ty : Option IntType) (body : List Expr)
    (ls : List WVal) (L : Nat) (v : SVal) : Prop :=
  (∃ ls' r, L = 0 ∧ v = packV ls' r ∧ ls'.length = ls.length ∧
    (BlockOk ty r → Exec ls (.loop ty body) (.ok ls' (blockRes ty r)))) ∨
  (∃ m o, m < B ∧ L = c.ldepth - m ∧ Exec ls (.loop ty body) o ∧ TgtL c o = some (m, v))

/-- One pass through the loop header: the body runs from the passed locals. -/
private theorem loop_header_entry {c : Ctx} {body : List Expr} (hs : BackSeq body) (hwf : WF c)
    {env : Env WVal} {ls : List WVal} {r₀ : Option WVal} {next : Nat} {middle : SVal}
    (hl : ls.length = c.locals.length)
    (hblock : REval (extend env (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩) next middle) :
    ∃ m₁ o₁, next = c.ldepth + 1 - m₁ ∧ Seq ls none body o₁ ∧
      Post o₁ (fun ls' r => m₁ = c.ldepth ∧ middle = packV ls' r)
        (TgtL (headerCtx c) o₁ = some (m₁, middle)) := by
  have hblock' : REval (extend env (packV ls r₀)) (unpack ls.length (headerCtx c) c.depth
      fun c' ls' _ => cSeq body { c' with locals := ls' } none
        fun c'' r => .br (c''.lbl c.ldepth) (c''.pack r)) next middle := by
    simpa only [loopBlocks, ← hl] using hblock
  obtain ⟨lvls, tl, env', hlv, -, -, -, hk⟩ :=
    unpack_inv ls (headerCtx c) c.depth _ (resV r₀) _ (c.depth + 1 + 2 * ls.length) _ _ rfl
      (Nat.lt_succ_self _) (by show extend _ _ (c.depth + 1 - 1 - c.depth) = _; simp [packV])
      hblock'
  let cb : Ctx := { headerCtx c with depth := c.depth + 1 + 2 * ls.length, locals := lvls }
  obtain ⟨m₁, o₁, -, hnext, hseq, hpo⟩ :=
    body_entry hs (c₁ := cb) hwf.headerCtx hlv (jl := c.ldepth)
      (by show c.ldepth < c.ldepth + 2; omega) hk
  have hnext' : next = c.ldepth + 1 - m₁ := by rw [hnext]; simp [cb, Ctx.lbl, headerCtx]
  exact ⟨m₁, o₁, hnext', hseq, hpo⟩

/-- A branch back to the loop header continues the loop. -/
private theorem loopRes_back {B : Nat} {c : Ctx} {ty : Option IntType} {body : List Expr}
    {ls ls' : List WVal} {r : Option WVal} {L : Nat} {v : SVal}
    (hseq : Seq ls none body (.brk 0 ls' r)) (hl' : ls'.length = ls.length)
    (h : LoopRes B c ty body ls' L v) : LoopRes B c ty body ls L v := by
  rcases h with ⟨ls'', r', h1, h2, h3, h4⟩ | ⟨m, o, hm, h1, hex, ht⟩
  · exact .inl ⟨ls'', r', h1, h2, h3.trans hl', fun hok => .loop_back hseq (h4 hok)⟩
  · exact .inr ⟨m, o, hm, h1, .loop_back hseq hex, ht⟩

/-- One step of the loop header's CFG run, given the rest of the run. -/
private theorem loop_follow_step {B : Nat} {c : Ctx} {ty : Option IntType} {body : List Expr}
    (hs : BackSeq body) (hwf : WF c) (hwfb : WFB c B) (hB : B ≤ c.ldepth) {env : Env WVal}
    {ls : List WVal} {r₀ : Option WVal} {next out : Nat} {middle value : SVal}
    (hl : ls.length = c.locals.length)
    (hblock : REval (extend env (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩) next middle)
    (hfollow : Follow1 env (loopBlocks c body) next middle out value)
    (ih : next = 0 → ∀ ls r₀, middle = packV ls r₀ → ls.length = c.locals.length →
      LoopRes B c ty body ls out value) :
    LoopRes B c ty body ls out value := by
  obtain ⟨m₁, o₁, hnext, hseq, hpo⟩ := loop_header_entry hs hwf hl hblock
  have hexit : ∀ o, TgtL c o = some (m₁, middle) → LoopExit ty o₁ o →
      LoopRes B c ty body ls out value := by
    intro o ht hx
    have hmB : m₁ < B := hwfb.tgt ht
    rcases follow1_inv hfollow with ⟨-, hout, hv⟩ | ⟨h0, -⟩
    · exact .inr ⟨m₁, o, hmB, by omega, .loop hseq hx, hv ▸ ht⟩
    · omega
  cases o₁ with
  | ok ls' r =>
      obtain ⟨hm₁, hx⟩ : m₁ = c.ldepth ∧ middle = packV ls' r := hpo
      have hl' : ls'.length = ls.length := by simpa [LenOK] using seq_len hseq
      rcases follow1_inv hfollow with ⟨-, hout, hv⟩ | ⟨h0, -⟩
      · exact .inl ⟨ls', r, by omega, hv.trans hx, hl', fun hok => .loop hseq (.ok hok)⟩
      · omega
  | brk l ls' r =>
      show LoopRes B c ty body ls out value
      cases l with
      | zero =>
          obtain ⟨hm₁, hx⟩ : c.ldepth + 1 = m₁ ∧ packV ls' r = middle := by
            simpa [Post, TgtL, headerCtx] using hpo
          have hl' : ls'.length = ls.length := by simpa [LenOK] using seq_len hseq
          exact loopRes_back hseq hl' (ih (by omega) ls' r hx.symm (hl'.trans hl))
      | succ l =>
          have ht : TgtL c (Out.brk (α := Option WVal) l ls' r) = some (m₁, middle) := hpo
          exact hexit _ ht .brk
  | ret r =>
      have ht : TgtL c (Out.ret (α := Option WVal) r) = some (m₁, middle) := hpo
      exact hexit _ ht .ret
  | trap =>
      have ht : TgtL c (Out.trap (α := Option WVal)) = some (m₁, middle) := hpo
      exact hexit _ ht .trap

/-- The loop header's CFG execution comes from a fragment loop. -/
theorem loop_follow {B : Nat} {c : Ctx} {ty : Option IntType} {body : List Expr}
    (hs : BackSeq body) (hwf : WF c) (hwfb : WFB c B) (hB : B ≤ c.ldepth) {env : Env WVal}
    {first : Nat} {x : SVal} {L : Nat} {v : SVal} (hf : Follow1 env (loopBlocks c body) first x L v) :
    first = 0 → ∀ ls r₀, x = packV ls r₀ → ls.length = c.locals.length →
      (∃ ls' r, L = 0 ∧ v = packV ls' r ∧ ls'.length = ls.length ∧
        (BlockOk ty r → Exec ls (.loop ty body) (.ok ls' (blockRes ty r)))) ∨
      (∃ m o, m < B ∧ L = c.ldepth - m ∧ Exec ls (.loop ty body) o ∧ TgtL c o = some (m, v)) := by
  refine Silmaril.Isotope.LambdaSSA.Semantics.Region.Follow.rec
    (motive_1 := fun _ _ _ _ _ _ _ => True)
    (motive_2 := fun env' n bs first x _ L v _ _ => ∀ (hn : n = 1), HEq bs (loopBlocks c body) →
      env' = env → first = 0 → ∀ ls r₀, x = packV ls r₀ → ls.length = c.locals.length →
      LoopRes B c ty body ls L v)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial) ?_ ?_ hf rfl HEq.rfl rfl
  · intro env' n label blocks value s hle hn _ _ h0
    omega
  · intro env' n label next out blocks current middle value s s₁ s₂ inside hblock hfollow _ ih hn hbs
      henv h0 ls r₀ hx hl
    subst hn
    cases hbs
    have hblock' : REval (extend env' (packV ls r₀)) (loopBlocks c body ⟨0, Nat.one_pos⟩)
        next middle := hx ▸ hblock
    exact loop_follow_step hs hwf hwfb hB hl hblock' hfollow (fun hn0 => ih rfl HEq.rfl henv hn0)

/-- A loop's outer CFG entered at its join block (as for `construct_inv`). -/
private theorem loop_join {B : Nat} {c : Ctx} {env : Env WVal} {ty : Option IntType}
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

theorem back_loop {ty : Option IntType} {body : List Expr} (hs : BackSeq body) :
    BackE (.loop ty body) := by
  intro B ls c env k L v hwf hwfb hB hag hk h
  have h' : REval env (.cfg (.cfg (.br 0 (c.pack none)) 1 (loopBlocks c body)) 1
      fun _ => joinBlock c.enter ty k) L v := h
  obtain ⟨first, x, he, hf⟩ := cfg1_inv h'
  obtain ⟨f0, x0, hbr, hfi⟩ := cfg1_inv he
  obtain ⟨hf0, hv0⟩ := br_inv hbr
  have hx0 : x0 = packV ls none := teval_det hv0 (eval_pack hag (rl := none) (r := none) trivial)
  rcases loop_follow (ty := ty) hs hwf hwfb hB hfi hf0 ls none hx0 hag.length.symm with
    ⟨ls', r, hfirst, hx, hl', hexec⟩ | ⟨m, o, hm, hfirst, hex, ht⟩
  · obtain ⟨hok, m, hm, hL, hpost⟩ := loop_join hB hk (hl'.trans hag.length.symm) hf hfirst hx
    exact ⟨m, _, hm, hL, hexec hok, hpost⟩
  · rcases follow1_inv hf with ⟨-, hL, hv⟩ | ⟨h0, -⟩
    · have hpost : BPost c env k m v o := by
        cases o <;> first | exact hv ▸ ht | simp [TgtL] at ht
      exact ⟨m, o, hm, by simp only [Ctx.lbl]; omega, hex, hpost⟩
    · omega

/-! ## The induction -/

mutual

theorem backE : ∀ e : Expr, BackE e
  | .op _ args => back_op (backArgs args)
  | .localGet _ => back_localGet
  | .localSet _ e => back_localSet (backE e)
  | .localTee _ e => back_localTee (backE e)
  | .drop e => back_drop (backE e)
  | .nop => back_nop
  | .unreachable => back_unreachable
  | .block _ body => back_block (backSeq body)
  | .loop _ body => back_loop (backSeq body)
  | .if_ _ c t e => back_if (backE c) (backSeq t) (backSeq e)
  | .br _ args => back_br (backArgs args)
  | .brIf _ args => back_brIf (backArgs args)
  | .return_ args => back_return (backArgs args)

theorem backArgs : ∀ es : List Expr, BackArgs es
  | [] => back_args_nil
  | e :: es => back_args_cons (backE e) (backArgs es)

theorem backSeq : ∀ es : List Expr, BackSeq es
  | [] => back_seq_nil
  | e :: es => back_seq_cons (backE e) (backSeq es)

end

/-! ## Functions -/

theorem initZeros_inv : ∀ (ts : List IntType) (c : Ctx) (env : Env WVal) (ls : List WVal)
    (K : Ctx → Region Prim) (L : Nat) (v : SVal), Agree c env ls →
    REval env (initZeros ts c K) L v →
    ∃ c' env', c'.ldepth = c.ldepth ∧ c'.labels = c.labels ∧ c'.ret = c.ret ∧
      c'.trap = c.trap ∧ c'.fty = c.fty ∧ Agree c' env' (ls ++ ts.map WVal.zero) ∧ REval env' (K c') L v
  | [], c, env, ls, K, L, v, ha, h => ⟨c, env, rfl, rfl, rfl, rfl, rfl, by simpa using ha, h⟩
  | t :: ts, c, env, ls, K, L, v, ha, h => by
      simp only [initZeros] at h
      obtain ⟨va, hva, hb⟩ := let₁_inv h
      obtain ⟨vx, hvx, hr⟩ := op_inv hva
      rw [unit_inv hvx] at hr
      have hva' : va = .atom (WVal.zero t) := by
        simp [Prim.run, decodeList, Op.eval] at hr; exact hr.symm
      subst hva'
      obtain ⟨c', env', h1, h2, h3, h4, h5, hag, hk⟩ := initZeros_inv ts _ _ (ls ++ [WVal.zero t]) K L v
        (show Agree { c.bind with locals := c.locals ++ [c.depth] }
            (extend env (.atom (WVal.zero t))) (ls ++ [WVal.zero t]) from
          List.rel_append (ha.imp fun _ _ hv => VarOK.ext (Ext.bind c env _) hv)
            (.cons (varOK_new c env _) .nil)) hb
      exact ⟨c', env', h1, h2, h3, h4, h5, by simpa using hag, hk⟩

/-- **The translation reflects terminating runs.** -/
theorem compileFunc_complete {f : FragFunc} {args : List WVal} {o : FOut}
    (h : (compileFunc f).Run args o) : f.Run args o := by
  obtain ⟨hty, L, v, hev, hdec⟩ := h
  have hty : args.map WVal.type = f.params := hty
  have hlen : args.length = f.params.length := by rw [← hty]; simp
  refine ⟨hty, ?_⟩
  have hag₀ : Agree (Ctx.initial f.params.length f.result) (argEnv args) args :=
    hlen ▸ agree_initial args f.result
  obtain ⟨c', env', h1, h2, h3, h4, h5, hag', hk'⟩ :=
    initZeros_inv f.locals _ (argEnv args) args _ L v hag₀ hev
  have htgt : ∀ {α : Type} (o : Out α),
      TgtL c' o = TgtL (Ctx.initial f.params.length f.result) o :=
    TgtL_fields h2 h3 h4 h5
  have hwf : WF c' := ⟨fun m hm => by rw [h1]; exact (wf_initial _ _).1 m (h2 ▸ hm),
    by rw [h1, h3]; exact (wf_initial _ _).2.1, by rw [h1, h4]; exact (wf_initial _ _).2.2⟩
  have hKB : KB 2 c' env' (fun c r => jump c .ret r) := by
    intro c'' env'' rl ls'' r L' v' hext _ _ h''
    obtain ⟨hL, -⟩ := br_inv h''
    exact ⟨1, by omega, by rw [hL, hext.ret, h3]; rfl⟩
  have h2le : 2 ≤ c'.ldepth := by rw [h1]; simp [Ctx.initial]
  have hwfb : WFB c' 2 := ⟨fun m hm => by simpa [h1, Ctx.initial] using hwf.1 m hm,
    by rw [h3]; simp [Ctx.initial], by rw [h4]; simp [Ctx.initial]⟩
  obtain ⟨m, out, hm, hLm, hseq, hpost⟩ :=
    backSeq f.body 2 (f.initLocals args) none c' env' _ none _ v hwf hwfb h2le hag' trivial hKB hk'
  refine ⟨out, hseq, ?_⟩
  have hdec' : decodeOut (1 - m) v = some o := by
    rw [← hdec, hLm]; simp only [Ctx.lbl, h1, Ctx.initial]
  have hret : ∀ r, TgtL c' (Out.ret (α := Unit) r) = some (m, v) →
      funcExit f.result (.ret r) = some o := by
    intro r ht
    obtain ⟨hm1, hv⟩ : 1 = m ∧ resV (blockRes f.result r) = v :=
      Prod.mk.inj (Option.some.inj ((htgt _).symm.trans ht))
    have ho : FOut.ret (blockRes f.result r) = o := by
      simpa only [← hm1, ← hv, show 1 - 1 = 0 from rfl, decodeOut_resV, Option.some.injEq]
        using hdec'
    rw [← ho]; rfl
  cases out with
  | ok ls' r =>
      show funcExit f.result (.ok ls' r) = some o
      obtain ⟨c'', env'', rl, hext, -, hres, h''⟩ := hpost
      have ht : TgtL c' (Out.ret (α := Unit) r) = some (1, resV (blockRes f.result r)) :=
        (htgt _).trans rfl
      have hj : REval env'' (jump c'' .ret rl) (c''.lbl 1) (resV (blockRes f.result r)) :=
        eval_ret hext hres ht
      have hm1 : m = 1 := by
        obtain ⟨hL, -⟩ := br_inv h''
        obtain ⟨hL', -⟩ := br_inv hj
        have hd : 2 ≤ c''.ldepth := h2le.trans hext.ldepth
        exact lbl_inj' (c := c'') (m := m) (m' := 1) (by omega) (by omega) (hL'.trans hL.symm)
      have hv : resV (blockRes f.result r) = v := teval_det (br_inv hj).2 (br_inv h'').2
      exact hret r (by rw [hm1, ← hv]; exact ht)
  | brk l ls' r =>
      show funcExit f.result (.brk l ls' r) = some o
      cases l with
      | zero =>
          have hb : TgtL c' (Out.brk (α := Option WVal) 0 ls' r) = some (m, v) := hpost
          have ht : TgtL c' (Out.ret (α := Unit) r) = some (m, v) := by
            rw [htgt]; simpa [TgtL, Ctx.initial] using (htgt _).symm.trans hb
          exact hret r ht
      | succ l =>
          have hb : TgtL c' (Out.brk (α := Option WVal) (l + 1) ls' r) = some (m, v) := hpost
          exact absurd ((htgt _).symm.trans hb) (by simp [TgtL, Ctx.initial])
  | ret r => exact hret r hpost
  | trap =>
      have ht : TgtL c' (Out.trap (α := Option WVal)) = some (m, v) := hpost
      obtain ⟨hm0, hv⟩ : 0 = m ∧ (.unit : SVal) = v :=
        Prod.mk.inj (Option.some.inj ((htgt _).symm.trans ht))
      have ho : FOut.trap = o := by simpa [← hm0, ← hv, decodeOut] using hdec'
      rw [← ho]; rfl

end Silmaril.Proofs.Wasm.SSA.Translate
