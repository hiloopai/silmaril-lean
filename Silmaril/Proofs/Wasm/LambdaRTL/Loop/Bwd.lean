module

public import Silmaril.Proofs.Wasm.LambdaRTL.Loop.Fwd
public import Silmaril.Wasm.SSA.Fragment.Thms

/-!
# Wasm fragment → λRTL with loops: λRTL results come from fragment derivations (proofs)

`bwd`: if the translated region terminates without getting stuck (`Good`: some result in the
`Part`, not `.error .stuck`), the expression has a fragment derivation (`Exec`, `Args`, `Seq`).
By structural induction on expressions; each case applies the induction hypothesis to the first
sub-term, reads the λRTL behaviour of that sub-derivation off the forward simulation
(`fwdE`, `fwdA`, `fwdS`), and shows that every case without a fragment derivation makes the
λRTL run stuck. The loop case is an induction on the finite run of the λRTL iteration
(`Silmaril.Elgot.Part.Runs`): a body that jumps to the loop's label re-enters it exactly as
`Exec.loop_back` does.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL (Val Op Model upd)
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq
  Exec Args Seq BlockExit LoopExit BlockOk)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-! ## Terminating, non-stuck results -/

/-- The λRTL computation terminates without getting stuck. -/
def Good {α : Type} (x : LM α) : Prop := ∃ y, y ∈ x.run ∧ y ≠ .error .stuck

theorem not_good_stuck {α : Type} : ¬ Good (errL .stuck : LM α) := by
  rintro ⟨y, hy, hne⟩
  rw [errL_run, Part.mem_some_iff] at hy
  exact hne hy

theorem not_good_stuck_bind {α β : Type} (f : α → LM β) : ¬ Good ((errL .stuck : LM α) >>= f) := by
  rw [errL_bind]
  exact not_good_stuck

theorem good_bind_left {α β : Type} {x : LM α} {f : α → LM β} (h : Good (x >>= f)) : Good x := by
  obtain ⟨y, hy, hne⟩ := h
  change y ∈ Part.bind x.run (ExceptT.bindCont f) at hy
  rw [Part.mem_bind_iff] at hy
  obtain ⟨z, hz, hyz⟩ := hy
  refine ⟨z, hz, ?_⟩
  rintro rfl
  change y ∈ Part.some (Except.error WErr.stuck) at hyz
  rw [Part.mem_some_iff] at hyz
  exact hne hyz

theorem mem_map_run {α β : Type} {g : α → β} {x : LM α} {z : Except WErr β}
    (h : z ∈ (g <$> x).run) : ∃ w ∈ x.run, z = Except.map g w := by
  rw [map_eq_pure_bind] at h
  change z ∈ Part.bind x.run (ExceptT.bindCont fun a => pure (g a)) at h
  rw [Part.mem_bind_iff] at h
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨w, hw, ?_⟩
  cases w with
  | error e =>
    change z ∈ Part.some (Except.error e) at hz
    rw [Part.mem_some_iff] at hz
    rw [hz]
    rfl
  | ok a =>
    change z ∈ Part.some (Except.ok (g a)) at hz
    rw [Part.mem_some_iff] at hz
    rw [hz]
    rfl

theorem mem_okL {α : Type} {a : α} {y : Except WErr α} (h : y ∈ (okL a).run) : y = .ok a := by
  rw [okL_run, Part.mem_some_iff] at h
  exact h

theorem mem_errL {α : Type} {e : WErr} {y : Except WErr α} (h : y ∈ (errL e : LM α).run) :
    y = .error e := by
  rw [errL_run, Part.mem_some_iff] at h
  exact h

/-! ## Forward simulation of derivations -/

section

variable {nloc : Nat} {res : Option IntType}

theorem fwdE {ls : List WVal} {e : Expr} {out : Out (Option WVal)} (h : Exec ls e out)
    {ks : List TgtL} {sd : Nat} {σ : Store} {k : LRegion} (hctx : CtxOkL ks sd)
    (ha : Agree nloc ls σ) :
    SimRL nloc res ks sd k σ ((trEL nloc res ks sd e k).evalRTL modelL σ) (some out) := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalE_complete h
  have := (fwd (nloc := nloc) (res := res) n).1 e ks sd ls σ k (by rw [hn]; rfl) hctx ha
  rwa [hn] at this

theorem fwdA {ls : List WVal} {es : List Expr} {out : Out (List WVal)} (h : Args ls es out)
    {ks : List TgtL} {sd : Nat} {σ : Store} {k : LRegion} (hctx : CtxOkL ks sd)
    (ha : Agree nloc ls σ) :
    SimAL nloc res ks sd k σ ((trArgsL nloc res ks sd es k).evalRTL modelL σ) (some out) := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalArgs_complete h
  have := (fwd (nloc := nloc) (res := res) n).2.1 es ks sd ls σ k (by rw [hn]; rfl) hctx ha
  rwa [hn] at this

theorem fwdS {ls : List WVal} {r : Option WVal} {es : List Expr} {out : Out (Option WVal)}
    (h : Seq ls r es out) {ks : List TgtL} {sd : Nat} {σ : Store} {k : LRegion}
    (hctx : CtxOkL ks sd) (ha : Agree nloc ls σ) (hs : SlotRes sd r σ) :
    SimRL nloc res ks sd k σ ((trSeqL nloc res ks sd es k).evalRTL modelL σ) (some out) := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalSeq_complete h
  have := (fwd (nloc := nloc) (res := res) n).2.2 es ks sd ls σ k r (by rw [hn]; rfl) hctx ha hs
  rwa [hn] at this

theorem hasVal_exec {ls : List WVal} {e : Expr} {ls' : List WVal} {r : Option WVal}
    (h : Exec ls e (.ok ls' r)) : r.isSome = hasVal e := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalE_complete h
  exact hasVal_ok hn

theorem args_length {ls : List WVal} {es : List Expr} {ls' : List WVal} {vs : List WVal}
    (h : Args ls es (.ok ls' vs)) : vs.length = es.length := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalArgs_complete h
  exact evalArgs_length hn

theorem seqVal_exec {ls : List WVal} {r : Option WVal} {es : List Expr} {ls' : List WVal}
    {r' : Option WVal} (h : Seq ls r es (.ok ls' r')) : r'.isSome = seqVal r.isSome es := by
  obtain ⟨n, hn⟩ := Silmaril.Wasm.SSA.evalSeq_complete h
  exact seqVal_ok hn

theorem blockOk_of {ty : Option IntType} {r : Option WVal}
    (h : ¬ (ty.isSome && r.isNone) = true) : BlockOk ty r := by
  intro hty
  cases r with
  | none => simp [hty] at h
  | some _ => rfl

/-- A body under a `block`/`if` label whose join is reached without getting stuck has a block
exit. -/
theorem blockExit_exists {ks : List TgtL} {sd : Nat} {ty : Option IntType} {hv : Bool}
    {k : LRegion} {σ₀ : Store} {x : Res3L} {sout : Out (Option WVal)}
    (hsim : SimRL nloc res (.blk ks.length sd ty :: ks) sd (fallRL ks.length ty hv) σ₀ x
      (some sout))
    (hhv : ∀ ls' r, sout = .ok ls' r → r.isSome = hv) (hg : Good (x >>= joinK ks.length k)) :
    ∃ out', BlockExit ty sout out' := by
  cases sout with
  | ok ls₁ r₁ =>
    obtain ⟨σ₁, -, -, -, hx⟩ := hsim
    have hr := hhv ls₁ r₁ rfl
    subst hr
    by_cases hc : (ty.isSome && r₁.isNone) = true
    · have hf : fallRL ks.length ty r₁.isSome = stuckRL := by
        simp only [fallRL, Option.not_isSome]
        rw [ite_eq_left hc]
      rw [hx, hf, evalL_stuckRL] at hg
      exact absurd hg (not_good_stuck_bind _)
    · exact ⟨_, BlockExit.ok (blockOk_of hc)⟩
  | brk l ls₁ r₁ =>
    cases l with
    | zero =>
      simp only [SimRL, SimAbrL, List.getElem?_cons_zero] at hsim
      by_cases hc : (ty.isSome && r₁.isNone) = true
      · rw [ite_eq_left hc] at hsim
        rw [hsim] at hg
        exact absurd hg (not_good_stuck_bind _)
      · exact ⟨_, BlockExit.brk0 (blockOk_of hc)⟩
    | succ l => exact ⟨_, BlockExit.brk⟩
  | ret r => exact ⟨_, BlockExit.ret⟩
  | trap => exact ⟨_, BlockExit.trap⟩

/-! ## Statements -/

/-- Backward property of an expression. -/
def QE (nloc : Nat) (res : Option IntType) (e : Expr) : Prop :=
  ∀ (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion),
    CtxOkL ks sd → Agree nloc ls σ → Good ((trEL nloc res ks sd e k).evalRTL modelL σ) →
    ∃ out, Exec ls e out

/-- Backward property of an operand list. -/
def QA (nloc : Nat) (res : Option IntType) (es : List Expr) : Prop :=
  ∀ (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion),
    CtxOkL ks sd → Agree nloc ls σ → Good ((trArgsL nloc res ks sd es k).evalRTL modelL σ) →
    ∃ out, Args ls es out

/-- Backward property of a body. -/
def QS (nloc : Nat) (res : Option IntType) (es : List Expr) : Prop :=
  ∀ (ks : List TgtL) (sd : Nat) (ls : List WVal) (σ : Store) (k : LRegion) (r : Option WVal),
    CtxOkL ks sd → Agree nloc ls σ → SlotRes sd r σ →
    Good ((trSeqL nloc res ks sd es k).evalRTL modelL σ) → ∃ out, Seq ls r es out

/-! ## One construct at a time -/

theorem bwd_op {o : Silmaril.Wasm.SSA.Op} {args : List Expr} (ihA : QA nloc res args) :
    QE nloc res (.op o args) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨aout, hA⟩ := ihA ks sd ls σ _ hctx ha hg
  cases aout with
  | ok ls' vs =>
    obtain ⟨σ', -, -, hs', hx⟩ := fwdA (res := res) (k := .let1 (.tmp sd)
      (.app (.op o) (pack sd args.length)) k) hA hctx ha
    rw [hx, evalL_let1_op, ← args_length hA, eval_pack_L hs', app_op_ofList] at hg
    cases hv : o.eval vs with
    | none =>
      rw [hv] at hg
      exact absurd hg (not_good_stuck_bind _)
    | some rv =>
      cases rv with
      | val v => exact ⟨_, Exec.op hA hv⟩
      | trap => exact ⟨_, Exec.op_trap hA hv⟩
  | brk l ls' r => exact ⟨_, Exec.op_abrupt hA trivial⟩
  | ret r => exact ⟨_, Exec.op_abrupt hA trivial⟩
  | trap => exact ⟨_, Exec.op_abrupt hA trivial⟩

theorem bwd_localGet {i : Nat} : QE nloc res (.localGet i) := by
  intro ks sd ls σ k hctx ha hg
  by_cases hi : i < ls.length
  · exact ⟨_, Exec.localGet (List.getElem?_eq_getElem hi)⟩
  · have hi' : ¬ i < nloc := by rw [← ha.1]; exact hi
    simp only [trEL, ite_eq_right hi', evalL_stuckRL] at hg
    exact absurd hg not_good_stuck

theorem bwd_localSet {i : Nat} {e : Expr} (ihE : QE nloc res e) :
    QE nloc res (.localSet i e) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨eout, hE⟩ := ihE ks sd ls σ _ hctx ha hg
  cases eout with
  | ok ls' r =>
    cases r with
    | some v => exact ⟨_, Exec.localSet hE⟩
    | none =>
      have hv := hasVal_exec hE
      obtain ⟨σ', -, -, -, hx⟩ := fwdE (res := res)
        (k := needValL (hasVal e) (setLocalL nloc i sd k)) hE hctx ha
      rw [hx, ← hv] at hg
      simp only [Option.isSome_none, needValL_false, evalL_stuckRL] at hg
      exact absurd hg not_good_stuck
  | brk l ls' r => exact ⟨_, Exec.localSet_abrupt hE trivial⟩
  | ret r => exact ⟨_, Exec.localSet_abrupt hE trivial⟩
  | trap => exact ⟨_, Exec.localSet_abrupt hE trivial⟩

theorem bwd_localTee {i : Nat} {e : Expr} (ihE : QE nloc res e) :
    QE nloc res (.localTee i e) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨eout, hE⟩ := ihE ks sd ls σ _ hctx ha hg
  cases eout with
  | ok ls' r =>
    cases r with
    | some v => exact ⟨_, Exec.localTee hE⟩
    | none =>
      have hv := hasVal_exec hE
      obtain ⟨σ', -, -, -, hx⟩ := fwdE (res := res)
        (k := needValL (hasVal e) (setLocalL nloc i sd k)) hE hctx ha
      rw [hx, ← hv] at hg
      simp only [Option.isSome_none, needValL_false, evalL_stuckRL] at hg
      exact absurd hg not_good_stuck
  | brk l ls' r => exact ⟨_, Exec.localTee_abrupt hE trivial⟩
  | ret r => exact ⟨_, Exec.localTee_abrupt hE trivial⟩
  | trap => exact ⟨_, Exec.localTee_abrupt hE trivial⟩

theorem bwd_drop {e : Expr} (ihE : QE nloc res e) : QE nloc res (.drop e) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨eout, hE⟩ := ihE ks sd ls σ _ hctx ha hg
  cases eout with
  | ok ls' r => exact ⟨_, Exec.drop hE⟩
  | brk l ls' r => exact ⟨_, Exec.drop_abrupt hE trivial⟩
  | ret r => exact ⟨_, Exec.drop_abrupt hE trivial⟩
  | trap => exact ⟨_, Exec.drop_abrupt hE trivial⟩

theorem bwd_block {ty : Option IntType} {body : List Expr} (ihS : QS nloc res body) :
    QE nloc res (.block ty body) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL, evalL_joinBlk] at hg
  have hctx' : CtxOkL (.blk ks.length sd ty :: ks) sd := hctx.push rfl rfl
  obtain ⟨sout, hS⟩ := ihS (.blk ks.length sd ty :: ks) sd ls σ _ none hctx' ha
    (SlotRes.none' _ _) (good_bind_left hg)
  have hsim := fwdS (res := res) (k := fallRL ks.length ty (seqVal false body)) hS
    hctx' ha (SlotRes.none' _ _)
  obtain ⟨out', hx⟩ := blockExit_exists hsim
    (fun ls' r h => by subst h; simpa using seqVal_exec hS) hg
  exact ⟨_, Exec.block hS hx⟩

theorem bwd_if {ty : Option IntType} {c : Expr} {t el : List Expr} (ihC : QE nloc res c)
    (ihT : QS nloc res t) (ihEl : QS nloc res el) : QE nloc res (.if_ ty c t el) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨cout, hC⟩ := ihC ks sd ls σ _ hctx ha hg
  cases cout with
  | ok ls₁ r₁ =>
    obtain ⟨σ₁, ha₁, -, hs₁, hx⟩ := fwdE (res := res) (k := needValL (hasVal c) (ifJoinL
      ks.length sd
      (trSeqL nloc res (.blk ks.length sd ty :: ks) sd t (fallRL ks.length ty (seqVal false t)))
      (trSeqL nloc res (.blk ks.length sd ty :: ks) sd el (fallRL ks.length ty (seqVal false el)))
      k)) hC hctx ha
    have hv := hasVal_exec hC
    rw [hx] at hg
    cases r₁ with
    | none =>
      rw [← hv] at hg
      simp only [Option.isSome_none, needValL_false, evalL_stuckRL] at hg
      exact absurd hg not_good_stuck
    | some cv =>
      rw [← hv, Option.isSome_some, needValL_true] at hg
      change Good ((Silmaril.SSA.LambdaRTL.Loop.Region.case (.app .truthy (.var (.tmp sd))) .junk _
        .junk _ : LRegion).evalRTL modelL σ₁ >>= joinK ks.length k) at hg
      rw [evalL_case_truthy (hs₁ cv rfl)] at hg
      have ha₀ : Agree nloc ls₁ (upd σ₁ .junk .unit) := ha₁.upd_junk _
      have hctx' : CtxOkL (.blk ks.length sd ty :: ks) sd := hctx.push rfl rfl
      cases hcv : cv.truthy with
      | none =>
        rw [hcv] at hg
        exact absurd hg (not_good_stuck_bind _)
      | some b =>
        rw [hcv] at hg
        cases b with
        | true =>
          obtain ⟨sout, hS⟩ := ihT (.blk ks.length sd ty :: ks) sd ls₁ (upd σ₁ .junk .unit) _ none
            hctx' ha₀ (SlotRes.none' _ _) (good_bind_left hg)
          have hsim := fwdS (res := res) (k := fallRL ks.length ty (seqVal false t)) hS
            hctx' ha₀ (SlotRes.none' _ _)
          obtain ⟨out', hx'⟩ := blockExit_exists hsim
            (fun ls' r h => by subst h; simpa using seqVal_exec hS) hg
          exact ⟨_, Exec.if_ hC hcv (by simpa using hS) hx'⟩
        | false =>
          obtain ⟨sout, hS⟩ := ihEl (.blk ks.length sd ty :: ks) sd ls₁ (upd σ₁ .junk .unit) _
            none hctx' ha₀ (SlotRes.none' _ _) (good_bind_left hg)
          have hsim := fwdS (res := res) (k := fallRL ks.length ty (seqVal false el)) hS
            hctx' ha₀ (SlotRes.none' _ _)
          obtain ⟨out', hx'⟩ := blockExit_exists hsim
            (fun ls' r h => by subst h; simpa using seqVal_exec hS) hg
          exact ⟨_, Exec.if_ hC hcv (by simpa using hS) hx'⟩
  | brk l ls' r => exact ⟨_, Exec.if_abrupt hC trivial⟩
  | ret r => exact ⟨_, Exec.if_abrupt hC trivial⟩
  | trap => exact ⟨_, Exec.if_abrupt hC trivial⟩

theorem bwd_br {l : Nat} {args : List Expr} (ihA : QA nloc res args) :
    QE nloc res (.br l args) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨aout, hA⟩ := ihA ks sd ls σ _ hctx ha hg
  cases aout with
  | ok ls' vs => exact ⟨_, Exec.br hA⟩
  | brk l' ls' r => exact ⟨_, Exec.br_abrupt hA trivial⟩
  | ret r => exact ⟨_, Exec.br_abrupt hA trivial⟩
  | trap => exact ⟨_, Exec.br_abrupt hA trivial⟩

theorem bwd_return {args : List Expr} (ihA : QA nloc res args) : QE nloc res (.return_ args) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨aout, hA⟩ := ihA ks sd ls σ _ hctx ha hg
  cases aout with
  | ok ls' vs => exact ⟨_, Exec.return_ hA⟩
  | brk l' ls' r => exact ⟨_, Exec.return_abrupt hA trivial⟩
  | ret r => exact ⟨_, Exec.return_abrupt hA trivial⟩
  | trap => exact ⟨_, Exec.return_abrupt hA trivial⟩

theorem bwd_brIf {l : Nat} {args : List Expr} (ihA : QA nloc res args) :
    QE nloc res (.brIf l args) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trEL] at hg
  obtain ⟨aout, hA⟩ := ihA ks sd ls σ _ hctx ha hg
  cases aout with
  | ok ls' vs =>
    obtain ⟨σ', -, -, hs', hx⟩ := fwdA (res := res) (k := brIfTestL ks res l sd k args.length)
      hA hctx ha
    have hlen := args_length hA
    rw [hx] at hg
    cases hm : args.length with
    | zero =>
      rw [hm] at hg
      simp only [brIfTestL, evalL_stuckRL] at hg
      exact absurd hg not_good_stuck
    | succ m =>
      rw [hm] at hg
      have hvl : vs.length = m + 1 := hlen.trans hm
      have hlast : vs.getLast? = some (vs[m]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        simp [hvl]
      have hsm : σ' (.tmp (sd + m)) = .val (vs[m]'(by omega)) := hs' m (by omega)
      simp only [brIfTestL] at hg
      rw [evalL_case_truthy hsm] at hg
      cases hc : (vs[m]'(by omega)).truthy with
      | none =>
        rw [hc] at hg
        exact absurd hg not_good_stuck
      | some b => exact ⟨_, Exec.brIf hA hlast hc⟩
  | brk l' ls' r => exact ⟨_, Exec.brIf_abrupt hA trivial⟩
  | ret r => exact ⟨_, Exec.brIf_abrupt hA trivial⟩
  | trap => exact ⟨_, Exec.brIf_abrupt hA trivial⟩

/-- The loop: induction on the finite run of the λRTL iteration. -/
theorem bwd_loop {ty : Option IntType} {body : List Expr} (ihS : QS nloc res body) :
    QE nloc res (.loop ty body) := by
  intro ks sd ls σ k hctx ha hg
  have hl : (trEL nloc res ks sd (.loop ty body) k).evalRTL modelL σ =
      Silmaril.Elgot.iter (loopStep ks.length
        (trSeqL nloc res (.lp ks.length sd :: ks) sd body
          (fallRL ks.length ty (seqVal false body))))
        (RVal.unit, σ) >>= joinK ks.length k := by
    simp only [trEL]
    exact evalL_loopJoin _ _ _ σ
  rw [hl] at hg
  obtain ⟨y, hy, hne⟩ := good_bind_left hg
  rw [iterL_run, Silmaril.Elgot.Part.mem_iter_iff] at hy
  have hctx' : CtxOkL (.lp ks.length sd :: ks) sd := hctx.push rfl rfl
  -- the body region and its evaluation
  suffices H : ∀ (a : RVal × Store) (y : Except WErr (LLab × RVal × Store)),
      Silmaril.Elgot.Part.Runs (fun a => routeE <$> (loopStep ks.length
        (trSeqL nloc res (.lp ks.length sd :: ks) sd body
          (fallRL ks.length ty (seqVal false body))) a).run) a y →
      y ≠ .error .stuck → ∀ ls, Agree nloc ls a.2 → ∃ out, Exec ls (.loop ty body) out from
    H _ _ hy hne ls ha
  intro a y hr
  induction hr with
  | @done a y hmem =>
    intro hne ls ha
    obtain ⟨z, hz, hzy⟩ := (Part.mem_map_iff _).1 hmem
    obtain ⟨w, hw, hzw⟩ := mem_map_run hz
    have ha₀ : Agree nloc ls (upd a.2 .junk a.1) := ha.upd_junk _
    have hgood : Good ((trSeqL nloc res (.lp ks.length sd :: ks) sd body
        (fallRL ks.length ty (seqVal false body))).evalRTL modelL (upd a.2 .junk a.1)) := by
      refine ⟨w, hw, ?_⟩
      rintro rfl
      subst hzw
      cases hzy
      exact hne rfl
    obtain ⟨bout, hS⟩ := ihS _ sd ls _ _ none hctx' ha₀ (SlotRes.none' _ _) hgood
    have hsim := fwdS (res := res) (k := fallRL ks.length ty (seqVal false body)) hS hctx' ha₀
      (SlotRes.none' _ _)
    cases bout with
    | brk l ls' r =>
      cases l with
      | zero =>
        simp only [SimRL, SimAbrL, List.getElem?_cons_zero] at hsim
        obtain ⟨σ', -, -, hx⟩ := hsim
        rw [hx] at hw
        have := mem_okL hw
        subst this
        subst hzw
        simp [Except.map, Silmaril.SSA.LambdaRTL.Loop.routeRTL, routeE] at hzy
      | succ l => exact ⟨_, Exec.loop hS LoopExit.brk⟩
    | ok ls₁ r₁ =>
      obtain ⟨σ₁, -, -, -, hx⟩ := hsim
      have hv : r₁.isSome = seqVal false body := by simpa using seqVal_exec hS
      by_cases hc : (ty.isSome && r₁.isNone) = true
      · have hfl : fallRL ks.length ty r₁.isSome = stuckRL := by
          simp only [fallRL, Option.not_isSome]
          rw [ite_eq_left hc]
        rw [hx, ← hv, hfl, evalL_stuckRL] at hw
        have := mem_errL hw
        subst this
        subst hzw
        cases hzy
        exact absurd rfl hne
      · exact ⟨_, Exec.loop hS (LoopExit.ok (blockOk_of hc))⟩
    | ret r => exact ⟨_, Exec.loop hS LoopExit.ret⟩
    | trap => exact ⟨_, Exec.loop hS LoopExit.trap⟩
  | @more a a' y hmem _ ih =>
    intro hne ls ha
    obtain ⟨z, hz, hza⟩ := (Part.mem_map_iff _).1 hmem
    obtain ⟨w, hw, hzw⟩ := mem_map_run hz
    have ha₀ : Agree nloc ls (upd a.2 .junk a.1) := ha.upd_junk _
    -- `z` continues, so `w` is a normal result
    have hwok : ∃ e, w = .ok e := by
      cases w with
      | ok e => exact ⟨e, rfl⟩
      | error er =>
        subst hzw
        simp [Except.map, routeE] at hza
    obtain ⟨e₀, rfl⟩ := hwok
    have hgood : Good ((trSeqL nloc res (.lp ks.length sd :: ks) sd body
        (fallRL ks.length ty (seqVal false body))).evalRTL modelL (upd a.2 .junk a.1)) :=
      ⟨_, hw, by simp⟩
    obtain ⟨bout, hS⟩ := ihS _ sd ls _ _ none hctx' ha₀ (SlotRes.none' _ _) hgood
    have hsim := fwdS (res := res) (k := fallRL ks.length ty (seqVal false body)) hS hctx' ha₀
      (SlotRes.none' _ _)
    -- the only body outcome that re-enters the loop is a branch to its own label
    have hcont : e₀.1 = LLab.cont ks.length ∧ a' = e₀.2 := by
      subst hzw
      simp only [Except.map, Silmaril.SSA.LambdaRTL.Loop.routeRTL] at hza
      by_cases h1 : e₀.1 = LLab.cont ks.length
      · rw [ite_eq_left h1] at hza
        simp only [routeE, Sum.inr.injEq] at hza
        exact ⟨h1, hza.symm⟩
      · rw [ite_eq_right h1] at hza
        simp [routeE] at hza
    cases bout with
    | brk l ls' r =>
      cases l with
      | zero =>
        simp only [SimRL, SimAbrL, List.getElem?_cons_zero] at hsim
        obtain ⟨σ', ha', -, hx⟩ := hsim
        rw [hx] at hw
        have := mem_okL hw
        simp only [Except.ok.injEq] at this
        subst this
        obtain ⟨-, rfl⟩ := hcont
        obtain ⟨out, hout⟩ := ih hne ls' ha'
        exact ⟨out, Exec.loop_back hS hout⟩
      | succ l =>
        exfalso
        simp only [SimRL, SimAbrL, List.getElem?_cons_succ] at hsim
        cases hk : ks[l]? with
        | none =>
          simp only [hk] at hsim
          split at hsim
          · obtain ⟨σ', hx⟩ := hsim
            rw [hx] at hw
            have := mem_okL hw
            simp only [Except.ok.injEq] at this
            subst this
            simp at hcont
          · rw [hsim] at hw
            have := mem_errL hw
            cases this
        | some t =>
          have hmem' := hctx t (List.mem_of_getElem? hk)
          cases t with
          | blk d slot ty' =>
            simp only [hk] at hsim
            split at hsim
            · rw [hsim] at hw
              have := mem_errL hw
              cases this
            · obtain ⟨σ', -, -, -, hx⟩ := hsim
              rw [hx] at hw
              have := mem_okL hw
              simp only [Except.ok.injEq] at this
              subst this
              simp at hcont
          | lp d slot =>
            simp only [hk] at hsim
            obtain ⟨σ', -, -, hx⟩ := hsim
            rw [hx] at hw
            have := mem_okL hw
            simp only [Except.ok.injEq] at this
            subst this
            have hd := hmem'.2
            simp only [TgtL.d] at hd
            simp only [LLab.cont.injEq] at hcont
            omega
    | ok ls₁ r₁ =>
      exfalso
      obtain ⟨σ₁, -, -, -, hx⟩ := hsim
      have hv : r₁.isSome = seqVal false body := by simpa using seqVal_exec hS
      rw [hx, ← hv] at hw
      simp only [fallRL] at hw
      split at hw
      · rw [evalL_stuckRL] at hw
        have := mem_errL hw
        cases this
      · rw [evalL_brUnit] at hw
        have := mem_okL hw
        simp only [Except.ok.injEq] at this
        subst this
        simp at hcont
    | ret r =>
      exfalso
      simp only [SimRL, SimAbrL] at hsim
      obtain ⟨σ', hx⟩ := hsim
      rw [hx] at hw
      have := mem_okL hw
      simp only [Except.ok.injEq] at this
      subst this
      simp at hcont
    | trap =>
      exfalso
      simp only [SimRL, SimAbrL] at hsim
      rw [hsim] at hw
      have := mem_errL hw
      cases this

theorem bwdA_nil : QA nloc res [] := by
  intro ks sd ls σ k hctx ha hg
  exact ⟨_, Args.nil⟩

theorem bwdS_nil : QS nloc res [] := by
  intro ks sd ls σ k r hctx ha hs hg
  exact ⟨_, Seq.nil⟩

theorem bwdA_cons {e : Expr} {es : List Expr} (ihE : QE nloc res e) (ihA : QA nloc res es) :
    QA nloc res (e :: es) := by
  intro ks sd ls σ k hctx ha hg
  simp only [trArgsL] at hg
  obtain ⟨eout, hE⟩ := ihE ks sd ls σ _ hctx ha hg
  cases eout with
  | ok ls₁ r₁ =>
    obtain ⟨σ₁, ha₁, -, -, hx⟩ := fwdE (res := res)
      (k := needValL (hasVal e) (trArgsL nloc res ks (sd + 1) es k)) hE hctx ha
    have hv := hasVal_exec hE
    rw [hx] at hg
    cases r₁ with
    | none =>
      rw [← hv] at hg
      simp only [Option.isSome_none, needValL_false, evalL_stuckRL] at hg
      exact absurd hg not_good_stuck
    | some v =>
      rw [← hv, Option.isSome_some, needValL_true] at hg
      obtain ⟨aout, hA⟩ := ihA ks (sd + 1) ls₁ σ₁ k (hctx.mono (Nat.le_succ sd)) ha₁ hg
      cases aout with
      | ok ls₂ vs => exact ⟨_, Args.cons hE hA⟩
      | brk l ls₂ r => exact ⟨_, Args.tail_abrupt hE hA trivial⟩
      | ret r => exact ⟨_, Args.tail_abrupt hE hA trivial⟩
      | trap => exact ⟨_, Args.tail_abrupt hE hA trivial⟩
  | brk l ls' r => exact ⟨_, Args.head_abrupt hE trivial⟩
  | ret r => exact ⟨_, Args.head_abrupt hE trivial⟩
  | trap => exact ⟨_, Args.head_abrupt hE trivial⟩

theorem bwdS_cons {e : Expr} {es : List Expr} (ihE : QE nloc res e) (ihS : QS nloc res es) :
    QS nloc res (e :: es) := by
  intro ks sd ls σ k r hctx ha hs hg
  simp only [trSeqL] at hg
  obtain ⟨eout, hE⟩ := ihE ks sd ls σ _ hctx ha hg
  cases eout with
  | ok ls₁ r₁ =>
    obtain ⟨σ₁, ha₁, -, hs₁, hx⟩ := fwdE (res := res) (k := trSeqL nloc res ks sd es k) hE hctx ha
    rw [hx] at hg
    obtain ⟨sout, hS⟩ := ihS ks sd ls₁ σ₁ k r₁ hctx ha₁ hs₁ hg
    exact ⟨_, Seq.cons hE hS⟩
  | brk l ls' r => exact ⟨_, Seq.abrupt hE trivial⟩
  | ret r => exact ⟨_, Seq.abrupt hE trivial⟩
  | trap => exact ⟨_, Seq.abrupt hE trivial⟩

/-- **Backward simulation**: every terminating, non-stuck λRTL result of a translated expression,
operand list or body comes from a fragment derivation. -/
theorem bwd : ∀ e : Expr, QE nloc res e := by
  intro e
  induction e using Silmaril.Wasm.SSA.Expr.rec
    (motive_2 := fun es => QA nloc res es ∧ QS nloc res es) with
  | op o args ih => exact bwd_op ih.1
  | localGet i => exact bwd_localGet
  | localSet i e ih => exact bwd_localSet ih
  | localTee i e ih => exact bwd_localTee ih
  | drop e ih => exact bwd_drop ih
  | nop => intro ks sd ls σ k _ _ _; exact ⟨_, Exec.nop⟩
  | unreachable => intro ks sd ls σ k _ _ _; exact ⟨_, Exec.unreachable⟩
  | block ty body ih => exact bwd_block ih.2
  | loop ty body ih => exact bwd_loop ih.2
  | if_ ty c t el ihc iht ihe => exact bwd_if ihc iht.2 ihe.2
  | br l args ih => exact bwd_br ih.1
  | brIf l args ih => exact bwd_brIf ih.1
  | return_ args ih => exact bwd_return ih.1
  | nil => exact ⟨bwdA_nil, bwdS_nil⟩
  | cons e es ihe ihes => exact ⟨bwdA_cons ihe ihes.1, bwdS_cons ihe ihes.2⟩

/-- Bodies. -/
theorem bwdS (es : List Expr) : QS nloc res es := by
  induction es with
  | nil => exact bwdS_nil
  | cons e es ih => exact bwdS_cons (bwd e) ih

end

end Silmaril.Proofs.Wasm.LambdaRTL
