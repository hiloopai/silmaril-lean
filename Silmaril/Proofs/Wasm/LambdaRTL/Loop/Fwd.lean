module

public import Silmaril.Proofs.Wasm.LambdaRTL.Loop.Basic

/-!
# Wasm fragment → λRTL with loops: forward simulation of terminating runs (proofs)

`fwd n`: whenever the fragment's fuel interpreter returns a result at fuel `n` (`evalE n ls e`
is `some`), the translated region computes it in the sense of `SimRL`/`SimAL` — a terminating
λRTL result in `LM`, never divergence. The loop case follows the interpreter: a body that
branches to the loop's own label (`brk 0`) re-enters the λRTL loop (`iterL_cont`) and the
induction hypothesis at fuel `n` applies to the same loop from the new store; any other body
outcome leaves the λRTL loop (`iterL_ret`, `iterL_err`) as `loopExit` does.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL (Val Op Model upd)
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-! ## The statements -/

/-- Forward simulation of expressions at fuel `n`. -/
def PEL (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (e : Expr) (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion),
    (evalE n ls e).isSome = true → CtxOkL ks sd → Agree nloc ls σ →
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd e k).evalRTL modelL σ) (evalE n ls e)

/-- Forward simulation of operand lists at fuel `n`. -/
def PAL (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion),
    (evalArgs n ls es).isSome = true → CtxOkL ks sd → Agree nloc ls σ →
    SimAL nloc res ks sd k σ ((trArgsL nloc res ks sd es k).evalRTL modelL σ) (evalArgs n ls es)

/-- Forward simulation of bodies at fuel `n`. -/
def PSL (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion)
    (r : Option WVal),
    (evalSeq n ls r es).isSome = true → CtxOkL ks sd → Agree nloc ls σ → SlotRes sd r σ →
    SimRL nloc res ks sd k σ ((trSeqL nloc res ks sd es k).evalRTL modelL σ) (evalSeq n ls r es)

section

variable {nloc : Nat} {res : Option IntType}

/-! ## Building blocks -/

theorem evalL_retRL {sd : Nat} {r : Option WVal} {σ : Store} (hs : SlotRes sd r σ) :
    (retRL res sd r.isSome).evalRTL modelL σ = okL (.ret, encR (blockRes res r), σ) := by
  cases r with
  | none => cases res <;> rfl
  | some v =>
    cases res with
    | none => rfl
    | some t =>
      show okL (LLab.ret, σ (.tmp sd), σ) = _
      rw [hs v rfl]
      rfl

@[simp] theorem needValL_true (k : LRegion) : needValL true k = k := rfl

@[simp] theorem needValL_false (k : LRegion) : needValL false k = stuckRL := rfl

theorem eval_pack_L {σ : Store} {sd : Nat} {vs : List WVal} (h : SlotsRes sd vs σ) :
    (pack sd vs.length).eval modelL σ = RVal.ofList vs := by
  rw [valEval_L, eval_pack h]

theorem simAbrL_jumpTo {ks : List TgtL} {sd l : Nat} {ls' : List WVal} {r : Option WVal}
    {σ σ' : Store} {α : Type} (hctx : CtxOkL ks sd) (ha : Agree nloc ls' σ')
    (hb : Below sd σ σ') (hs : SlotRes sd r σ') :
    SimAbrL nloc res ks σ ((jumpToL ks res l sd r.isSome).evalRTL modelL σ')
      (Out.brk (α := α) l ls' r) := by
  cases hk : ks[l]? with
  | none =>
    have hj : jumpToL ks res l sd r.isSome =
        if l = ks.length then retRL res sd r.isSome else stuckRL := by
      simp [jumpToL, hk]
    simp only [SimAbrL, hk, hj]
    by_cases hl : l = ks.length
    · rw [ite_eq_left hl, ite_eq_left hl]
      exact ⟨σ', evalL_retRL hs⟩
    · rw [ite_eq_right hl, ite_eq_right hl]
      exact evalL_stuckRL σ'
  | some t =>
    have hslot := (hctx t (List.mem_of_getElem? hk)).1
    cases t with
    | lp d slot =>
      have hj : jumpToL ks res l sd r.isSome = .br (.cont d) .unit := by
        simp [jumpToL, hk]
      simp only [SimAbrL, hk, hj]
      exact ⟨σ', ha, hb.mono hslot, rfl⟩
    | blk d slot ty =>
      simp only [SimAbrL, hk]
      cases r with
      | none =>
        have hj : jumpToL ks res l sd false =
            if ty.isSome then stuckRL else .br (.blk d) .unit := by
          simp [jumpToL, hk]
        simp only [Option.isSome_none, Option.isNone_none, Bool.and_true, hj]
        by_cases hty : ty.isSome = true
        · rw [ite_eq_left hty, ite_eq_left hty]
          exact evalL_stuckRL σ'
        · rw [ite_eq_right hty, ite_eq_right hty]
          refine ⟨σ', ha, hb.mono hslot, ?_, rfl⟩
          intro v hv
          simp [blockRes] at hv
      | some v =>
        have hj : jumpToL ks res l sd true =
            mvL (.tmp slot) (.tmp sd) (.br (.blk d) .unit) := by
          simp [jumpToL, hk]
        simp only [Option.isSome_some, Option.isNone_some, Bool.and_false, Bool.false_eq_true,
          ↓reduceIte, hj, evalL_mvL]
        refine ⟨upd σ' (.tmp slot) (σ' (.tmp sd)), ha.upd_tmp _ _,
          (hb.mono hslot).upd_tmp le_rfl _, ?_, rfl⟩
        intro w hw
        have hsv := hs v rfl
        simp only [blockRes] at hw
        split at hw
        · cases hw
          simp [upd, hsv]
        · cases hw

/-- A `block`/`if` body run under its own label, then its join. -/
theorem simRL_block {ks : List TgtL} {sd : Nat} {ty : Option IntType} {hv : Bool}
    {k : LRegion} {σ σ₀ : Store} {x : Res3L} {o : Option (Out (Option WVal))}
    (hctx : CtxOkL ks sd) (hb : Below sd σ σ₀)
    (hsim : SimRL nloc res (.blk ks.length sd ty :: ks) sd (fallRL ks.length ty hv) σ₀ x o)
    (hhv : ∀ ls' r, o = some (.ok ls' r) → r.isSome = hv) :
    SimRL nloc res ks sd k σ (x >>= joinK ks.length k) (o.bind (evalE.blockExit ty)) := by
  rcases o with _ | ⟨ls' , r⟩ | ⟨l, ls', r⟩ | r | _
  · simp only [SimRL] at hsim
    rw [hsim, errL_bind]
    exact rfl
  · obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
    have hr := hhv ls' r rfl
    subst hr
    simp only [Option.bind_some, evalE.blockExit]
    rw [hx]
    by_cases hc : (ty.isSome && r.isNone) = true
    · have hf : fallRL ks.length ty r.isSome = stuckRL := by
        simp only [fallRL, Option.not_isSome]
        rw [ite_eq_left hc]
      rw [ite_eq_left hc, hf]
      simp only [SimRL]
      rw [evalL_stuckRL, errL_bind]
    · have hf : fallRL ks.length ty r.isSome = .br (.blk ks.length) .unit := by
        simp only [fallRL, Option.not_isSome]
        rw [ite_eq_right hc]
      rw [ite_eq_right hc, hf]
      simp only [SimRL]
      refine ⟨upd σ' .junk .unit, ha.upd_junk _, (hb.trans hb').upd_junk _,
        (hs.blockRes' ty).upd_junk _, ?_⟩
      rw [evalL_brUnit, okL_bind, joinK_blk]
  · cases l with
    | zero =>
      simp only [SimRL, SimAbrL, List.getElem?_cons_zero] at hsim
      simp only [Option.bind_some, evalE.blockExit]
      by_cases hc : (ty.isSome && r.isNone) = true
      · rw [ite_eq_left hc] at hsim ⊢
        simp only [SimRL]
        rw [hsim, errL_bind]
      · rw [ite_eq_right hc] at hsim ⊢
        obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
        simp only [SimRL]
        refine ⟨upd σ' .junk .unit, ha.upd_junk _, (hb.trans hb').upd_junk _, hs.upd_junk _, ?_⟩
        rw [hx, okL_bind, joinK_blk]
    | succ l =>
      simp only [SimRL, SimAbrL, List.getElem?_cons_succ, List.length_cons,
        Nat.add_right_cancel_iff] at hsim
      simp only [Option.bind_some, evalE.blockExit, SimRL, SimAbrL]
      cases hk : ks[l]? with
      | none =>
        simp only [hk] at hsim ⊢
        by_cases hl : l = ks.length
        · rw [ite_eq_left hl] at hsim ⊢
          obtain ⟨σ', hx⟩ := hsim
          exact ⟨σ', by rw [hx, okL_bind, joinK_other _ _ (by simp)]⟩
        · rw [ite_eq_right hl] at hsim ⊢
          rw [hsim, errL_bind]
      | some t =>
        have hmem := hctx t (List.mem_of_getElem? hk)
        cases t with
        | blk d slot ty' =>
          simp only [hk] at hsim ⊢
          by_cases hc : (ty'.isSome && r.isNone) = true
          · rw [ite_eq_left hc] at hsim ⊢
            rw [hsim, errL_bind]
          · rw [ite_eq_right hc] at hsim ⊢
            obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
            refine ⟨σ', ha, (hb.mono hmem.1).trans hb', hs, ?_⟩
            have hne : (LLab.blk d, RVal.unit, σ').1 ≠ LLab.blk ks.length := by
              have := hmem.2; simp [TgtL.d] at this ⊢; omega
            rw [hx, okL_bind, joinK_other _ _ hne]
        | lp d slot =>
          simp only [hk] at hsim ⊢
          obtain ⟨σ', ha, hb', hx⟩ := hsim
          refine ⟨σ', ha, (hb.mono hmem.1).trans hb', ?_⟩
          rw [hx, okL_bind, joinK_other _ _ (by simp)]
  · simp only [SimRL, SimAbrL] at hsim
    obtain ⟨σ', hx⟩ := hsim
    simp only [Option.bind_some, evalE.blockExit, SimRL, SimAbrL]
    exact ⟨σ', by rw [hx, okL_bind, joinK_other _ _ (by simp)]⟩
  · simp only [SimRL, SimAbrL] at hsim
    simp only [Option.bind_some, evalE.blockExit, SimRL, SimAbrL]
    rw [hsim, errL_bind]

/-! ## One construct at a time -/

section Steps

variable {n : Nat} {ks : List TgtL} {sd : Nat} {ls : List WVal} {σ : Store} {k : LRegion}

theorem stepL_op (ihA : PAL nloc res n) {o : Silmaril.Wasm.SSA.Op} {args : List Expr}
    (hf : (evalE (n + 1) ls (.op o args)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.op o args) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.op o args)) := by
  have hf' : (evalArgs n ls args).isSome = true := by
    cases h : evalArgs n ls args with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hA := ihA args ks sd ls σ (.let1 (.tmp sd) (.app (.op o) (pack sd args.length)) k)
    hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalArgs n ls args with
  | none =>
    rw [h] at hA
    exact hA
  | some ao =>
    rw [h] at hA
    cases ao with
    | ok ls' vs =>
      dsimp only
      obtain ⟨σ', ha', hb', hs', hx⟩ := hA
      have hlen := evalArgs_length h
      rw [hx, evalL_let1_op, ← hlen, eval_pack_L hs', app_op_ofList]
      cases hv : o.eval vs with
      | none =>
        show liftE (Except.error WErr.stuck) >>= _ = _
        exact errL_bind _ _
      | some rv =>
        cases rv with
        | val v =>
          refine ⟨upd σ' (.tmp sd) (.val v), ha'.upd_tmp _ _, hb'.upd_tmp le_rfl _, ?_, ?_⟩
          · intro w hw
            cases hw
            simp [upd]
          · show liftE (Except.ok (RVal.val v)) >>= _ = _
            rw [liftE_ok, okL_bind]
        | trap =>
          show liftE (Except.error WErr.trap) >>= _ = _
          exact errL_bind _ _
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem stepL_localGet {i : Nat} (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.localGet i) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.localGet i)) := by
  simp only [trEL, evalE]
  by_cases hi : i < nloc
  · have hi' : i < ls.length := ha.1 ▸ hi
    rw [ite_eq_left hi, evalL_mvL, List.getElem?_eq_getElem hi']
    refine ⟨upd σ (.tmp sd) (σ (.loc i)), ha.upd_tmp _ _, (Below.refl sd σ).upd_tmp le_rfl _,
      ?_, rfl⟩
    intro w hw
    cases hw
    simp [upd, ha.2 i hi']
  · have hi' : ls.length ≤ i := by have := ha.1; omega
    rw [ite_eq_right hi, List.getElem?_eq_none hi']
    exact evalL_stuckRL σ

theorem stepL_localSet (ihE : PEL nloc res n) {i : Nat} {e : Expr}
    (hf : (evalE (n + 1) ls (.localSet i e)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.localSet i e) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.localSet i e)) := by
  have hf' : (evalE n ls e).isSome = true := by
    cases h : evalE n ls e with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hE := ihE e ks sd ls σ (needValL (hasVal e) (setLocalL nloc i sd k)) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalE n ls e with
  | none =>
    rw [h] at hE
    exact hE
  | some eo =>
    rw [h] at hE
    cases eo with
    | ok ls' r =>
      obtain ⟨σ', ha', hb', hs', hx⟩ := hE
      have hv := hasVal_ok h
      rw [hx]
      cases r with
      | none =>
        rw [Option.isSome_none] at hv
        rw [← hv]
        exact evalL_stuckRL σ'
      | some v =>
        rw [Option.isSome_some] at hv
        rw [← hv, needValL_true]
        dsimp only
        by_cases hi : i < nloc
        · rw [setLocalL, ite_eq_left hi, evalL_mvL]
          refine ⟨upd σ' (.loc i) (σ' (.tmp sd)), ?_, hb'.upd_loc _ _, SlotRes.none' _ _, rfl⟩
          rw [hs' v rfl]
          exact ha'.set v
        · rw [setLocalL, ite_eq_right hi]
          have hi' : ls'.length ≤ i := by have := ha'.1; omega
          rw [List.set_eq_of_length_le hi']
          exact ⟨σ', ha', hb', SlotRes.none' _ _, rfl⟩
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem stepL_localTee (ihE : PEL nloc res n) {i : Nat} {e : Expr}
    (hf : (evalE (n + 1) ls (.localTee i e)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.localTee i e) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.localTee i e)) := by
  have hf' : (evalE n ls e).isSome = true := by
    cases h : evalE n ls e with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hE := ihE e ks sd ls σ (needValL (hasVal e) (setLocalL nloc i sd k)) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalE n ls e with
  | none =>
    rw [h] at hE
    exact hE
  | some eo =>
    rw [h] at hE
    cases eo with
    | ok ls' r =>
      obtain ⟨σ', ha', hb', hs', hx⟩ := hE
      have hv := hasVal_ok h
      rw [hx]
      cases r with
      | none =>
        rw [Option.isSome_none] at hv
        rw [← hv]
        exact evalL_stuckRL σ'
      | some v =>
        rw [Option.isSome_some] at hv
        rw [← hv, needValL_true]
        dsimp only
        have hsv := hs' v rfl
        by_cases hi : i < nloc
        · rw [setLocalL, ite_eq_left hi, evalL_mvL]
          refine ⟨upd σ' (.loc i) (σ' (.tmp sd)), ?_, hb'.upd_loc _ _, hs'.upd_loc _ _, rfl⟩
          rw [hsv]
          exact ha'.set v
        · rw [setLocalL, ite_eq_right hi]
          have hi' : ls'.length ≤ i := by have := ha'.1; omega
          rw [List.set_eq_of_length_le hi']
          exact ⟨σ', ha', hb', hs', rfl⟩
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem stepL_drop (ihE : PEL nloc res n) {e : Expr}
    (hf : (evalE (n + 1) ls (.drop e)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.drop e) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.drop e)) := by
  have hf' : (evalE n ls e).isSome = true := by
    cases h : evalE n ls e with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hE := ihE e ks sd ls σ k hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalE n ls e with
  | none =>
    rw [h] at hE
    exact hE
  | some eo =>
    rw [h] at hE
    cases eo with
    | ok ls' r =>
      dsimp only
      obtain ⟨σ', ha', hb', -, hx⟩ := hE
      exact ⟨σ', ha', hb', SlotRes.none' _ _, hx⟩
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem stepL_block (ihS : PSL nloc res n) {ty : Option IntType} {body : List Expr}
    (hf : (evalE (n + 1) ls (.block ty body)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.block ty body) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.block ty body)) := by
  have hf' : (evalSeq n ls none body).isSome = true := by
    cases h : evalSeq n ls none body with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hS := ihS body (.blk ks.length sd ty :: ks) sd ls σ
    (fallRL ks.length ty (seqVal false body)) none hf' (hctx.push rfl rfl) ha (SlotRes.none' _ _)
  simp only [trEL, evalE, evalL_joinBlk]
  exact simRL_block hctx (Below.refl sd σ) hS (fun ls' r h => by simpa using seqVal_ok h)

theorem stepL_loop (ihE : PEL nloc res n) (ihS : PSL nloc res n) {ty : Option IntType}
    {body : List Expr}
    (hf : (evalE (n + 1) ls (.loop ty body)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.loop ty body) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.loop ty body)) := by
  have hloop : ∀ σ' : Store, (trEL nloc res ks sd (.loop ty body) k).evalRTL modelL σ' =
      Silmaril.Elgot.iter (loopStep ks.length
        (trSeqL nloc res (.lp ks.length sd :: ks) sd body
          (fallRL ks.length ty (seqVal false body))))
        (RVal.unit, σ') >>= joinK ks.length k := by
    intro σ'
    simp only [trEL]
    exact evalL_loopJoin _ _ _ σ'
  have hf' : (evalSeq n ls none body).isSome = true := by
    cases h : evalSeq n ls none body with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hS := ihS body (.lp ks.length sd :: ks) sd ls (upd σ .junk .unit)
    (fallRL ks.length ty (seqVal false body)) none hf' (hctx.push rfl rfl) (ha.upd_junk _)
    (SlotRes.none' _ _)
  have hb₀ : Below sd σ (upd σ .junk .unit) := (Below.refl sd σ).upd_junk _
  rw [hloop σ]
  simp only [evalE]
  cases h : evalSeq n ls none body with
  | none => rw [h] at hf'; cases hf'
  | some bo =>
    rw [h] at hS
    cases bo with
    | brk l ls' r =>
      cases l with
      | zero =>
        simp only [SimRL, SimAbrL, List.getElem?_cons_zero] at hS
        obtain ⟨σ', ha', hb', hx⟩ := hS
        rw [iterL_cont (loopStep_cont hx)]
        have hf'' : (evalE n ls' (.loop ty body)).isSome = true := by
          simpa [evalE, h] using hf
        have := ihE (.loop ty body) ks sd ls' σ' k hf'' hctx ha'
        rw [hloop σ'] at this
        exact simRL_mono hctx (hb₀.trans hb') this
      | succ l =>
        simp only [SimRL, SimAbrL, List.getElem?_cons_succ, List.length_cons,
          Nat.add_right_cancel_iff] at hS
        simp only [evalE.loopExit, SimRL, SimAbrL]
        cases hk : ks[l]? with
        | none =>
          simp only [hk] at hS ⊢
          by_cases hl : l = ks.length
          · rw [ite_eq_left hl] at hS ⊢
            obtain ⟨σ', hx⟩ := hS
            refine ⟨σ', ?_⟩
            rw [iterL_ret (loopStep_exit hx (by simp)), okL_bind, joinK_other _ _ (by simp)]
          · rw [ite_eq_right hl] at hS ⊢
            rw [iterL_err (loopStep_err hS), errL_bind]
        | some t =>
          have hmem := hctx t (List.mem_of_getElem? hk)
          cases t with
          | blk d slot ty' =>
            simp only [hk] at hS ⊢
            by_cases hc : (ty'.isSome && r.isNone) = true
            · rw [ite_eq_left hc] at hS ⊢
              rw [iterL_err (loopStep_err hS), errL_bind]
            · rw [ite_eq_right hc] at hS ⊢
              obtain ⟨σ', ha', hb', hs', hx⟩ := hS
              refine ⟨σ', ha', (hb₀.mono hmem.1).trans hb', hs', ?_⟩
              have hne : (LLab.blk d, RVal.unit, σ').1 ≠ LLab.blk ks.length := by
                have := hmem.2; simp [TgtL.d] at this ⊢; omega
              rw [iterL_ret (loopStep_exit hx (by simp)), okL_bind, joinK_other _ _ hne]
          | lp d slot =>
            simp only [hk] at hS ⊢
            obtain ⟨σ', ha', hb', hx⟩ := hS
            refine ⟨σ', ha', (hb₀.mono hmem.1).trans hb', ?_⟩
            have hne : (LLab.cont d, RVal.unit, σ').1 ≠ LLab.cont ks.length := by
              have := hmem.2; simp [TgtL.d] at this ⊢; omega
            rw [iterL_ret (loopStep_exit hx hne), okL_bind, joinK_other _ _ (by simp)]
    | ok ls₁ r₁ =>
      obtain ⟨σ₁, ha₁, hb₁, hs₁, hx⟩ := hS
      have hv : r₁.isSome = seqVal false body := by simpa using seqVal_ok h
      simp only [evalE.loopExit]
      by_cases hc : (ty.isSome && r₁.isNone) = true
      · have hfl : fallRL ks.length ty r₁.isSome = stuckRL := by
          simp only [fallRL, Option.not_isSome]
          rw [ite_eq_left hc]
        have hx' : (trSeqL nloc res (.lp ks.length sd :: ks) sd body
            (fallRL ks.length ty (seqVal false body))).evalRTL modelL (upd σ .junk .unit) =
            errL .stuck := by
          rw [hx, ← hv, hfl, evalL_stuckRL]
        rw [ite_eq_left hc, iterL_err (loopStep_err hx'), errL_bind]
        exact rfl
      · have hfl : fallRL ks.length ty r₁.isSome = .br (.blk ks.length) .unit := by
          simp only [fallRL, Option.not_isSome]
          rw [ite_eq_right hc]
        have hx' : (trSeqL nloc res (.lp ks.length sd :: ks) sd body
            (fallRL ks.length ty (seqVal false body))).evalRTL modelL (upd σ .junk .unit) =
            okL (.blk ks.length, .unit, σ₁) := by
          rw [hx, ← hv, hfl, evalL_brUnit]
        rw [ite_eq_right hc, iterL_ret (loopStep_exit hx' (by simp)), okL_bind, joinK_blk]
        exact ⟨upd σ₁ .junk .unit, ha₁.upd_junk _, (hb₀.trans hb₁).upd_junk _,
          (hs₁.blockRes' ty).upd_junk _, rfl⟩
    | ret r =>
      simp only [SimRL, SimAbrL] at hS
      obtain ⟨σ', hx⟩ := hS
      simp only [evalE.loopExit, SimRL, SimAbrL]
      exact ⟨σ', by rw [iterL_ret (loopStep_exit hx (by simp)), okL_bind,
        joinK_other _ _ (by simp)]⟩
    | trap =>
      simp only [SimRL, SimAbrL] at hS
      simp only [evalE.loopExit, SimRL, SimAbrL]
      rw [iterL_err (loopStep_err hS), errL_bind]

theorem stepL_if (ihE : PEL nloc res n) (ihS : PSL nloc res n) {ty : Option IntType} {c : Expr}
    {t el : List Expr}
    (hf : (evalE (n + 1) ls (.if_ ty c t el)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.if_ ty c t el) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.if_ ty c t el)) := by
  have hf' : (evalE n ls c).isSome = true := by
    cases h : evalE n ls c with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hE := ihE c ks sd ls σ (needValL (hasVal c) (ifJoinL ks.length sd
    (trSeqL nloc res (.blk ks.length sd ty :: ks) sd t (fallRL ks.length ty (seqVal false t)))
    (trSeqL nloc res (.blk ks.length sd ty :: ks) sd el (fallRL ks.length ty (seqVal false el)))
    k)) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalE n ls c with
  | none =>
    rw [h] at hE
    exact hE
  | some co =>
    rw [h] at hE
    cases co with
    | ok ls₁ r₁ =>
      obtain ⟨σ₁, ha₁, hb₁, hs₁, hx⟩ := hE
      have hv := hasVal_ok h
      rw [hx]
      cases r₁ with
      | none =>
        rw [Option.isSome_none] at hv
        rw [← hv]
        exact evalL_stuckRL σ₁
      | some cv =>
        rw [Option.isSome_some] at hv
        rw [← hv, needValL_true]
        show SimRL nloc res ks sd k σ
          ((Silmaril.SSA.LambdaRTL.Loop.Region.case (.app .truthy (.var (.tmp sd))) .junk _ .junk _ :
            LRegion).evalRTL modelL σ₁ >>= joinK ks.length k) _
        rw [evalL_case_truthy (hs₁ cv rfl)]
        dsimp only
        have hb₀ : Below sd σ (upd σ₁ .junk .unit) := hb₁.upd_junk _
        have ha₀ : Agree nloc ls₁ (upd σ₁ .junk .unit) := ha₁.upd_junk _
        cases hcv : cv.truthy with
        | none =>
          dsimp only
          exact errL_bind _ _
        | some b =>
          dsimp only
          cases b with
          | true =>
            have hfb : (evalSeq n ls₁ none t).isSome = true := by
              cases hs : evalSeq n ls₁ none t with
              | none => simp [evalE, h, hcv, hs] at hf
              | some _ => rfl
            have hS := ihS t (.blk ks.length sd ty :: ks) sd ls₁ (upd σ₁ .junk .unit)
              (fallRL ks.length ty (seqVal false t)) none hfb (hctx.push rfl rfl) ha₀
              (SlotRes.none' _ _)
            rw [ite_eq_left (rfl : true = true)]
            exact simRL_block hctx hb₀ hS (fun ls' r h' => by simpa using seqVal_ok h')
          | false =>
            have hfb : (evalSeq n ls₁ none el).isSome = true := by
              cases hs : evalSeq n ls₁ none el with
              | none => simp [evalE, h, hcv, hs] at hf
              | some _ => rfl
            have hS := ihS el (.blk ks.length sd ty :: ks) sd ls₁ (upd σ₁ .junk .unit)
              (fallRL ks.length ty (seqVal false el)) none hfb (hctx.push rfl rfl) ha₀
              (SlotRes.none' _ _)
            rw [ite_eq_right Bool.false_ne_true]
            exact simRL_block hctx hb₀ hS (fun ls' r h' => by simpa using seqVal_ok h')
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem stepL_br (ihA : PAL nloc res n) {l : Nat} {args : List Expr}
    (hf : (evalE (n + 1) ls (.br l args)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.br l args) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.br l args)) := by
  have hf' : (evalArgs n ls args).isSome = true := by
    cases h : evalArgs n ls args with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hA := ihA args ks sd ls σ (jumpToL ks res l sd (!args.isEmpty)) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalArgs n ls args with
  | none =>
    rw [h] at hA
    exact hA
  | some ao =>
    rw [h] at hA
    cases ao with
    | ok ls' vs =>
      dsimp only
      obtain ⟨σ', ha', hb', hs', hx⟩ := hA
      rw [hx, isSome_head (evalArgs_length h)]
      exact simAbrL_jumpTo (α := Option WVal) hctx ha' hb' (slotRes_head hs')
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem stepL_brIf (ihA : PAL nloc res n) {l : Nat} {args : List Expr}
    (hf : (evalE (n + 1) ls (.brIf l args)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.brIf l args) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.brIf l args)) := by
  have hf' : (evalArgs n ls args).isSome = true := by
    cases h : evalArgs n ls args with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hA := ihA args ks sd ls σ (brIfTestL ks res l sd k args.length) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalArgs n ls args with
  | none =>
    rw [h] at hA
    exact hA
  | some ao =>
    rw [h] at hA
    cases ao with
    | ok ls' vs =>
      dsimp only
      obtain ⟨σ', ha', hb', hs', hx⟩ := hA
      have hlen := evalArgs_length h
      rw [hx]
      cases hm : args.length with
      | zero =>
        have hvs : vs = [] := List.eq_nil_of_length_eq_zero (hlen.trans hm)
        subst hvs
        exact evalL_stuckRL σ'
      | succ m =>
        have hvl : vs.length = m + 1 := hlen.trans hm
        have hlast : vs.getLast? = some (vs[m]'(by omega)) := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          simp [hvl]
        have hsm : σ' (.tmp (sd + m)) = .val (vs[m]'(by omega)) := hs' m (by omega)
        rw [hlast]
        dsimp only
        rw [brIfTestL, evalL_case_truthy hsm]
        cases hc : (vs[m]'(by omega)).truthy with
        | none => exact rfl
        | some b =>
          cases b with
          | true =>
            have hj := simAbrL_jumpTo (res := res) (l := l) (α := Option WVal) hctx
              (ha'.upd_junk .unit) (hb'.upd_junk _) ((slotRes_dropLast_head hs').upd_junk .unit)
            rw [isSome_dropLast_head hvl] at hj
            exact hj
          | false =>
            exact ⟨upd σ' .junk .unit, ha'.upd_junk _, hb'.upd_junk _,
              (slotRes_dropLast_head hs').upd_junk _, rfl⟩
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem stepL_return (ihA : PAL nloc res n) {args : List Expr}
    (hf : (evalE (n + 1) ls (.return_ args)).isSome = true)
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd (.return_ args) k).evalRTL modelL σ)
      (evalE (n + 1) ls (.return_ args)) := by
  have hf' : (evalArgs n ls args).isSome = true := by
    cases h : evalArgs n ls args with
    | none => simp [evalE, h] at hf
    | some _ => rfl
  have hA := ihA args ks sd ls σ (retRL res sd (!args.isEmpty)) hf' hctx ha
  simp only [trEL, evalE]
  cases h : evalArgs n ls args with
  | none =>
    rw [h] at hA
    exact hA
  | some ao =>
    rw [h] at hA
    cases ao with
    | ok ls' vs =>
      dsimp only
      obtain ⟨σ', -, -, hs', hx⟩ := hA
      rw [hx, isSome_head (evalArgs_length h)]
      exact ⟨σ', evalL_retRL (slotRes_head hs')⟩
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem stepEL (ihE : PEL nloc res n) (ihA : PAL nloc res n) (ihS : PSL nloc res n) :
    PEL nloc res (n + 1) := by
  intro e ks sd ls σ k hf hctx ha
  cases e with
  | op o args => exact stepL_op ihA hf hctx ha
  | localGet i => exact stepL_localGet ha
  | localSet i e => exact stepL_localSet ihE hf hctx ha
  | localTee i e => exact stepL_localTee ihE hf hctx ha
  | drop e => exact stepL_drop ihE hf hctx ha
  | nop =>
    simp only [trEL, evalE]
    exact ⟨σ, ha, Below.refl sd σ, SlotRes.none' _ _, rfl⟩
  | unreachable =>
    simp only [trEL, evalE]
    exact evalL_abort k σ
  | block ty body => exact stepL_block ihS hf hctx ha
  | loop ty body => exact stepL_loop ihE ihS hf hctx ha
  | if_ ty c t el => exact stepL_if ihE ihS hf hctx ha
  | br l args => exact stepL_br ihA hf hctx ha
  | brIf l args => exact stepL_brIf ihA hf hctx ha
  | return_ args => exact stepL_return ihA hf hctx ha

theorem stepAL (ihE : PEL nloc res n) (ihA : PAL nloc res n) : PAL nloc res (n + 1) := by
  intro es ks sd ls σ k hf hctx ha
  cases es with
  | nil =>
    simp only [trArgsL, evalArgs]
    exact ⟨σ, ha, Below.refl sd σ, fun i hi => by simp at hi, rfl⟩
  | cons e es =>
    have hfe : (evalE n ls e).isSome = true := by
      cases h : evalE n ls e with
      | none => simp [evalArgs, h] at hf
      | some _ => rfl
    have hE := ihE e ks sd ls σ (needValL (hasVal e) (trArgsL nloc res ks (sd + 1) es k)) hfe
      hctx ha
    simp only [trArgsL, evalArgs]
    cases h : evalE n ls e with
    | none =>
      rw [h] at hE
      exact hE
    | some eo =>
      rw [h] at hE
      cases eo with
      | ok ls₁ r₁ =>
        obtain ⟨σ₁, ha₁, hb₁, hs₁, hx⟩ := hE
        have hv := hasVal_ok h
        rw [hx]
        cases r₁ with
        | none =>
          rw [Option.isSome_none] at hv
          rw [← hv]
          exact evalL_stuckRL σ₁
        | some v =>
          rw [Option.isSome_some] at hv
          rw [← hv, needValL_true]
          dsimp only
          have hfs : (evalArgs n ls₁ es).isSome = true := by
            cases h' : evalArgs n ls₁ es with
            | none => simp [evalArgs, h, h'] at hf
            | some _ => rfl
          have hA := ihA es ks (sd + 1) ls₁ σ₁ k hfs (hctx.mono (Nat.le_succ sd)) ha₁
          cases h' : evalArgs n ls₁ es with
          | none =>
            rw [h'] at hA
            exact hA
          | some ao =>
            rw [h'] at hA
            cases ao with
            | ok ls₂ vs =>
              dsimp only
              obtain ⟨σ₂, ha₂, hb₂, hs₂, hx₂⟩ := hA
              refine ⟨σ₂, ha₂, hb₁.trans (hb₂.mono (Nat.le_succ sd)), ?_, hx₂⟩
              intro i hi
              cases i with
              | zero =>
                show σ₂ (.tmp (sd + 0)) = .val v
                rw [Nat.add_zero, hb₂ sd (Nat.lt_succ_self sd)]
                exact hs₁ v rfl
              | succ i =>
                have := hs₂ i (by simpa using hi)
                rw [show sd + 1 + i = sd + (i + 1) by omega] at this
                exact this
            | brk l ls₂ r =>
              simp only [SimAL] at hA ⊢
              exact simAbrL_mono hctx hb₁ hA
            | ret r =>
              simp only [SimAL] at hA ⊢
              exact simAbrL_mono hctx hb₁ hA
            | trap =>
              simp only [SimAL] at hA ⊢
              exact simAbrL_mono hctx hb₁ hA
      | brk l ls' r => exact hE
      | ret r => exact hE
      | trap => exact hE

theorem stepSL (ihE : PEL nloc res n) (ihS : PSL nloc res n) : PSL nloc res (n + 1) := by
  intro es ks sd ls σ k r hf hctx ha hs
  cases es with
  | nil =>
    simp only [trSeqL, evalSeq]
    exact ⟨σ, ha, Below.refl sd σ, hs, rfl⟩
  | cons e es =>
    have hfe : (evalE n ls e).isSome = true := by
      cases h : evalE n ls e with
      | none => simp [evalSeq, h] at hf
      | some _ => rfl
    have hE := ihE e ks sd ls σ (trSeqL nloc res ks sd es k) hfe hctx ha
    simp only [trSeqL, evalSeq]
    cases h : evalE n ls e with
    | none =>
      rw [h] at hE
      exact hE
    | some eo =>
      rw [h] at hE
      cases eo with
      | ok ls₁ r₁ =>
        dsimp only
        obtain ⟨σ₁, ha₁, hb₁, hs₁, hx⟩ := hE
        have hfs : (evalSeq n ls₁ r₁ es).isSome = true := by
          simpa [evalSeq, h] using hf
        rw [hx]
        exact simRL_mono hctx hb₁ (ihS es ks sd ls₁ σ₁ k r₁ hfs hctx ha₁ hs₁)
      | brk l ls' r => exact hE
      | ret r => exact hE
      | trap => exact hE

end Steps

/-- **Forward simulation** at every fuel. -/
theorem fwd (n : Nat) : PEL nloc res n ∧ PAL nloc res n ∧ PSL nloc res n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e _ _ ls _ _ hf
      simp [evalE] at hf
    · intro es _ _ ls _ _ hf
      simp [evalArgs] at hf
    · intro es _ _ ls _ _ r hf
      simp [evalSeq] at hf
  | succ n ih =>
    obtain ⟨ihE, ihA, ihS⟩ := ih
    exact ⟨stepEL ihE ihA ihS, stepAL ihE ihA, stepSL ihE ihS⟩

end

end Silmaril.Proofs.Wasm.LambdaRTL
