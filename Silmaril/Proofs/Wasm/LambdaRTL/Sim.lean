module

public import Silmaril.Proofs.Wasm.LambdaRTL.Basic

/-!
# Wasm fragment → λRTL: the simulation (proofs)

`sim n` states, for fuel `n` that suffices (`fuelE e ≤ n`, …) or on which the interpreter
returns a result, that the translated region computes exactly what the fragment's fuel
interpreter computes, in the sense of `SimR`/`SimA`: stuck ↦ `.error .stuck`, trap ↦
`.error .trap`, a normal outcome ↦ the continuation run from a store holding the new locals and
the result, a branch ↦ the jump to the target's join (or the function exit) with the carried value
in the target's slot, a return ↦ the function exit.

The proof is one induction on the fuel, with a lemma per construct.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-! ## The statements -/

/-- Simulation of expressions at fuel `n`. -/
def PE (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (e : Expr) (ks : List Tgt) (sd : Nat) (ls : List WVal) (σ : Store) (k : WRegion),
    loopFree e = true → (fuelE e ≤ n ∨ (evalE n ls e).isSome = true) → CtxOk ks sd →
    Agree nloc ls σ →
    SimR nloc res ks sd k σ ((trE nloc res ks sd e k).evalRTL model σ) (evalE n ls e)

/-- Simulation of operand lists at fuel `n`. -/
def PA (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ks : List Tgt) (sd : Nat) (ls : List WVal) (σ : Store) (k : WRegion),
    loopFreeL es = true → (fuelArgs es ≤ n ∨ (evalArgs n ls es).isSome = true) → CtxOk ks sd →
    Agree nloc ls σ →
    SimA nloc res ks sd k σ ((trArgs nloc res ks sd es k).evalRTL model σ) (evalArgs n ls es)

/-- Simulation of bodies at fuel `n`. -/
def PS (nloc : Nat) (res : Option IntType) (n : Nat) : Prop :=
  ∀ (es : List Expr) (ks : List Tgt) (sd : Nat) (ls : List WVal) (σ : Store) (k : WRegion)
    (r : Option WVal),
    loopFreeL es = true → (fuelSeq es ≤ n ∨ (evalSeq n ls r es).isSome = true) → CtxOk ks sd →
    Agree nloc ls σ → SlotRes sd r σ →
    SimR nloc res ks sd k σ ((trSeq nloc res ks sd es k).evalRTL model σ) (evalSeq n ls r es)

section

variable {nloc : Nat} {res : Option IntType}

/-! ## Building blocks -/

theorem eval_retR {sd : Nat} {r : Option WVal} {σ : Store} (hs : SlotRes sd r σ) :
    (retR res sd r.isSome).evalRTL model σ = .ok (.ret, encR (blockRes res r), σ) := by
  cases r with
  | none => cases res <;> rfl
  | some v =>
    cases res with
    | none => rfl
    | some t =>
      show Except.ok (WLab.ret, σ (.tmp sd), σ) = _
      rw [hs v rfl]
      rfl

@[simp] theorem needVal_true (k : WRegion) : needVal true k = k := rfl

@[simp] theorem needVal_false (k : WRegion) : needVal false k = stuckR := rfl

theorem eval_br_unit (ℓ : WLab) (σ : Store) :
    (Region.br ℓ .unit : WRegion).evalRTL model σ = .ok (ℓ, .unit, σ) := rfl

theorem eval_ifJoin (d sd : Nat) (rt re k : WRegion) (σ : Store) :
    (ifJoin d sd rt re k).evalRTL model σ =
      (Region.case (.app .truthy (.var (.tmp sd))) .junk rt .junk re : WRegion).evalRTL model σ >>=
        fun e => if e.1 = WLab.blk d then k.evalRTL model (upd e.2.2 .junk e.2.1) else pure e :=
  rfl

theorem SlotRes.blockRes' {sd : Nat} {r : Option WVal} {σ : Store} (h : SlotRes sd r σ)
    (ty : Option IntType) : SlotRes sd (blockRes ty r) σ := by
  intro v hv
  simp only [blockRes] at hv
  split at hv
  · exact h v hv
  · cases hv

theorem slotRes_head {sd : Nat} {vs : List WVal} {σ : Store} (hs : SlotsRes sd vs σ) :
    SlotRes sd vs.head? σ := by
  intro v hv
  cases vs with
  | nil => cases hv
  | cons w ws =>
    simp only [List.head?_cons, Option.some.injEq] at hv
    subst hv
    exact hs 0 (by simp)

theorem slotRes_dropLast_head {sd : Nat} {vs : List WVal} {σ : Store} (hs : SlotsRes sd vs σ) :
    SlotRes sd vs.dropLast.head? σ := by
  intro v hv
  rcases vs with _ | ⟨w, _ | ⟨u, us⟩⟩
  · simp at hv
  · simp at hv
  · simp only [List.dropLast_cons_cons, List.head?_cons, Option.some.injEq] at hv
    subst hv
    exact hs 0 (by simp)

theorem isSome_head {vs : List WVal} {args : List Expr} (h : vs.length = args.length) :
    (!args.isEmpty) = vs.head?.isSome := by
  cases vs <;> cases args <;> simp_all

theorem isSome_dropLast_head {vs : List WVal} {m : Nat} (h : vs.length = m + 1) :
    vs.dropLast.head?.isSome = decide (1 ≤ m) := by
  rcases vs with _ | ⟨w, _ | ⟨u, us⟩⟩
  · simp at h
  · simp at h; simp [h]
  · simp at h; simp; omega

theorem simAbr_jumpTo {ks : List Tgt} {sd l : Nat} {ls' : List WVal} {r : Option WVal}
    {σ σ' : Store} {α : Type} (hctx : CtxOk ks sd) (ha : Agree nloc ls' σ')
    (hb : Below sd σ σ') (hs : SlotRes sd r σ') :
    SimAbr nloc res ks σ ((jumpTo ks res l sd r.isSome).evalRTL model σ')
      (Out.brk (α := α) l ls' r) := by
  cases hk : ks[l]? with
  | none =>
    have hj : jumpTo ks res l sd r.isSome =
        if l = ks.length then retR res sd r.isSome else stuckR := by
      simp [jumpTo, hk]
    simp only [SimAbr, hk, hj]
    by_cases hl : l = ks.length
    · rw [ite_eq_left hl, ite_eq_left hl]
      exact ⟨σ', eval_retR hs⟩
    · rw [ite_eq_right hl, ite_eq_right hl]
      rfl
  | some t =>
    obtain ⟨hslot, -⟩ := hctx t (List.mem_of_getElem? hk)
    simp only [SimAbr, hk]
    cases r with
    | none =>
      have hj : jumpTo ks res l sd false =
          if t.ty.isSome then stuckR else .br (.blk t.d) .unit := by
        simp [jumpTo, hk]
      simp only [Option.isSome_none, Option.isNone_none, Bool.and_true, hj]
      by_cases hty : t.ty.isSome = true
      · rw [ite_eq_left hty, ite_eq_left hty]
        rfl
      · rw [ite_eq_right hty, ite_eq_right hty]
        refine ⟨σ', ha, hb.mono hslot, ?_, rfl⟩
        intro v hv
        simp [blockRes] at hv
    | some v =>
      have hj : jumpTo ks res l sd true =
          mv (.tmp t.slot) (.tmp sd) (.br (.blk t.d) .unit) := by
        simp [jumpTo, hk]
      simp only [Option.isSome_some, Option.isNone_some, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, hj, eval_mv]
      refine ⟨upd σ' (.tmp t.slot) (σ' (.tmp sd)), ha.upd_tmp _ _,
        (hb.mono hslot).upd_tmp le_rfl _, ?_, rfl⟩
      intro w hw
      have hsv := hs v rfl
      simp only [blockRes] at hw
      split at hw
      · cases hw
        simp [upd, hsv]
      · cases hw

/-- A `block`/`if` body run under its own label, then its join. -/
theorem simR_block {ks : List Tgt} {sd : Nat} {ty : Option IntType} {hv : Bool} {k : WRegion}
    {σ σ₀ : Store} {x : Res3} {o : Option (Out (Option WVal))}
    (hctx : CtxOk ks sd) (hb : Below sd σ σ₀)
    (hsim : SimR nloc res (⟨ks.length, sd, ty⟩ :: ks) sd (fallR ks.length ty hv) σ₀ x o)
    (hhv : ∀ ls' r, o = some (.ok ls' r) → r.isSome = hv) :
    SimR nloc res ks sd k σ
      (x >>= fun e =>
        if e.1 = WLab.blk ks.length then k.evalRTL model (upd e.2.2 .junk e.2.1) else pure e)
      (o.bind (evalE.blockExit ty)) := by
  rcases o with _ | ⟨ls' , r⟩ | ⟨l, ls', r⟩ | r | _
  · simp only [SimR] at hsim ⊢
    rw [hsim]
    rfl
  · obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
    have hr := hhv ls' r rfl
    subst hr
    simp only [Option.bind_some, evalE.blockExit]
    rw [hx]
    by_cases hc : (ty.isSome && r.isNone) = true
    · have hf : fallR ks.length ty r.isSome = stuckR := by
        simp only [fallR, Option.not_isSome]
        rw [ite_eq_left hc]
      rw [ite_eq_left hc, hf]
      rfl
    · have hf : fallR ks.length ty r.isSome = .br (.blk ks.length) .unit := by
        simp only [fallR, Option.not_isSome]
        rw [ite_eq_right hc]
      rw [ite_eq_right hc, hf]
      simp only [SimR]
      refine ⟨upd σ' .junk .unit, ha.upd_junk _, (hb.trans hb').upd_junk _,
        (hs.blockRes' ty).upd_junk _, ?_⟩
      rw [eval_br_unit]
      simp
  · cases l with
    | zero =>
      simp only [SimR, SimAbr, List.getElem?_cons_zero] at hsim
      simp only [Option.bind_some, evalE.blockExit]
      by_cases hc : (ty.isSome && r.isNone) = true
      · rw [ite_eq_left hc] at hsim ⊢
        rw [hsim]
        rfl
      · rw [ite_eq_right hc] at hsim ⊢
        obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
        simp only [SimR]
        refine ⟨upd σ' .junk .unit, ha.upd_junk _, (hb.trans hb').upd_junk _, hs.upd_junk _, ?_⟩
        rw [hx]
        simp
    | succ l =>
      simp only [SimR, SimAbr, List.getElem?_cons_succ, List.length_cons,
        Nat.add_right_cancel_iff] at hsim
      simp only [Option.bind_some, evalE.blockExit, SimR, SimAbr]
      cases hk : ks[l]? with
      | none =>
        simp only [hk] at hsim ⊢
        by_cases hl : l = ks.length
        · rw [ite_eq_left hl] at hsim ⊢
          obtain ⟨σ', hx⟩ := hsim
          exact ⟨σ', by rw [hx]; rfl⟩
        · rw [ite_eq_right hl] at hsim ⊢
          rw [hsim]
          rfl
      | some t =>
        simp only [hk] at hsim ⊢
        obtain ⟨hslot, hd⟩ := hctx t (List.mem_of_getElem? hk)
        by_cases hc : (t.ty.isSome && r.isNone) = true
        · rw [ite_eq_left hc] at hsim ⊢
          rw [hsim]
          rfl
        · rw [ite_eq_right hc] at hsim ⊢
          obtain ⟨σ', ha, hb', hs, hx⟩ := hsim
          refine ⟨σ', ha, (hb.mono hslot).trans hb', hs, ?_⟩
          have hne : WLab.blk t.d ≠ WLab.blk ks.length := by simp; omega
          rw [hx]
          simp [hne]
  · simp only [SimR, SimAbr] at hsim
    obtain ⟨σ', hx⟩ := hsim
    simp only [Option.bind_some, evalE.blockExit, SimR, SimAbr]
    exact ⟨σ', by rw [hx]; rfl⟩
  · simp only [SimR, SimAbr] at hsim
    simp only [Option.bind_some, evalE.blockExit, SimR, SimAbr]
    rw [hsim]
    rfl

/-! ## One construct at a time -/

section Steps

variable {n : Nat} {ks : List Tgt} {sd : Nat} {ls : List WVal} {σ : Store} {k : WRegion}

theorem step_op (ihA : PA nloc res n) {o : Silmaril.Wasm.SSA.Op} {args : List Expr}
    (hlf : loopFree (.op o args) = true)
    (hf : fuelE (.op o args) ≤ n + 1 ∨ (evalE (n + 1) ls (.op o args)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.op o args) k).evalRTL model σ)
      (evalE (n + 1) ls (.op o args)) := by
  have hlf' : loopFreeL args = true := by simpa [loopFree] using hlf
  have hf' : fuelArgs args ≤ n ∨ (evalArgs n ls args).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalArgs n ls args with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hA := ihA args ks sd ls σ (.let1 (.tmp sd) (.app (.op o) (pack sd args.length)) k)
    hlf' hf' hctx ha
  simp only [trE, evalE]
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
      rw [hx, eval_let1_op, ← hlen, eval_pack hs', app_op_ofList]
      cases hv : o.eval vs with
      | none => exact rfl
      | some rv =>
        cases rv with
        | val v =>
          refine ⟨upd σ' (.tmp sd) (.val v), ha'.upd_tmp _ _, hb'.upd_tmp le_rfl _, ?_, rfl⟩
          intro w hw
          cases hw
          simp [upd]
        | trap => exact rfl
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem step_localGet {i : Nat} (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.localGet i) k).evalRTL model σ)
      (evalE (n + 1) ls (.localGet i)) := by
  simp only [trE, evalE]
  by_cases hi : i < nloc
  · have hi' : i < ls.length := ha.1 ▸ hi
    rw [ite_eq_left hi, eval_mv, List.getElem?_eq_getElem hi']
    refine ⟨upd σ (.tmp sd) (σ (.loc i)), ha.upd_tmp _ _, (Below.refl sd σ).upd_tmp le_rfl _, ?_,
      rfl⟩
    intro w hw
    cases hw
    simp [upd, ha.2 i hi']
  · have hi' : ls.length ≤ i := by have := ha.1; omega
    rw [ite_eq_right hi, List.getElem?_eq_none hi']
    exact rfl

theorem step_localSet (ihE : PE nloc res n) {i : Nat} {e : Expr}
    (hlf : loopFree (.localSet i e) = true)
    (hf : fuelE (.localSet i e) ≤ n + 1 ∨ (evalE (n + 1) ls (.localSet i e)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.localSet i e) k).evalRTL model σ)
      (evalE (n + 1) ls (.localSet i e)) := by
  have hlf' : loopFree e = true := by simpa [loopFree] using hlf
  have hf' : fuelE e ≤ n ∨ (evalE n ls e).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalE n ls e with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hE := ihE e ks sd ls σ (needVal (hasVal e) (setLocal nloc i sd k)) hlf' hf' hctx ha
  simp only [trE, evalE]
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
        exact rfl
      | some v =>
        rw [Option.isSome_some] at hv
        rw [← hv, needVal_true]
        dsimp only
        by_cases hi : i < nloc
        · rw [setLocal, ite_eq_left hi, eval_mv]
          refine ⟨upd σ' (.loc i) (σ' (.tmp sd)), ?_, hb'.upd_loc _ _, SlotRes.none' _ _, rfl⟩
          rw [hs' v rfl]
          exact ha'.set v
        · rw [setLocal, ite_eq_right hi]
          have hi' : ls'.length ≤ i := by have := ha'.1; omega
          rw [List.set_eq_of_length_le hi']
          exact ⟨σ', ha', hb', SlotRes.none' _ _, rfl⟩
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem step_localTee (ihE : PE nloc res n) {i : Nat} {e : Expr}
    (hlf : loopFree (.localTee i e) = true)
    (hf : fuelE (.localTee i e) ≤ n + 1 ∨ (evalE (n + 1) ls (.localTee i e)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.localTee i e) k).evalRTL model σ)
      (evalE (n + 1) ls (.localTee i e)) := by
  have hlf' : loopFree e = true := by simpa [loopFree] using hlf
  have hf' : fuelE e ≤ n ∨ (evalE n ls e).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalE n ls e with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hE := ihE e ks sd ls σ (needVal (hasVal e) (setLocal nloc i sd k)) hlf' hf' hctx ha
  simp only [trE, evalE]
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
        exact rfl
      | some v =>
        rw [Option.isSome_some] at hv
        rw [← hv, needVal_true]
        dsimp only
        have hsv := hs' v rfl
        by_cases hi : i < nloc
        · rw [setLocal, ite_eq_left hi, eval_mv]
          refine ⟨upd σ' (.loc i) (σ' (.tmp sd)), ?_, hb'.upd_loc _ _, hs'.upd_loc _ _, rfl⟩
          rw [hsv]
          exact ha'.set v
        · rw [setLocal, ite_eq_right hi]
          have hi' : ls'.length ≤ i := by have := ha'.1; omega
          rw [List.set_eq_of_length_le hi']
          exact ⟨σ', ha', hb', hs', rfl⟩
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem step_drop (ihE : PE nloc res n) {e : Expr}
    (hlf : loopFree (.drop e) = true)
    (hf : fuelE (.drop e) ≤ n + 1 ∨ (evalE (n + 1) ls (.drop e)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.drop e) k).evalRTL model σ)
      (evalE (n + 1) ls (.drop e)) := by
  have hlf' : loopFree e = true := by simpa [loopFree] using hlf
  have hf' : fuelE e ≤ n ∨ (evalE n ls e).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalE n ls e with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hE := ihE e ks sd ls σ k hlf' hf' hctx ha
  simp only [trE, evalE]
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

theorem step_block (ihS : PS nloc res n) {ty : Option IntType} {body : List Expr}
    (hlf : loopFree (.block ty body) = true)
    (hf : fuelE (.block ty body) ≤ n + 1 ∨ (evalE (n + 1) ls (.block ty body)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.block ty body) k).evalRTL model σ)
      (evalE (n + 1) ls (.block ty body)) := by
  have hlf' : loopFreeL body = true := by simpa [loopFree] using hlf
  have hf' : fuelSeq body ≤ n ∨ (evalSeq n ls none body).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalSeq n ls none body with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hS := ihS body (⟨ks.length, sd, ty⟩ :: ks) sd ls σ
    (fallR ks.length ty (seqVal false body)) none hlf' hf' (hctx.push ty) ha (SlotRes.none' _ _)
  simp only [trE, evalE, eval_join]
  exact simR_block hctx (Below.refl sd σ) hS (fun ls' r h => by simpa using seqVal_ok h)

theorem step_if (ihE : PE nloc res n) (ihS : PS nloc res n) {ty : Option IntType} {c : Expr}
    {t el : List Expr}
    (hlf : loopFree (.if_ ty c t el) = true)
    (hf : fuelE (.if_ ty c t el) ≤ n + 1 ∨ (evalE (n + 1) ls (.if_ ty c t el)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.if_ ty c t el) k).evalRTL model σ)
      (evalE (n + 1) ls (.if_ ty c t el)) := by
  simp only [loopFree, Bool.and_eq_true] at hlf
  obtain ⟨⟨hlc, hlt⟩, hle⟩ := hlf
  have hf' : fuelE c ≤ n ∨ (evalE n ls c).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalE n ls c with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hE := ihE c ks sd ls σ (needVal (hasVal c) (ifJoin ks.length sd
    (trSeq nloc res (⟨ks.length, sd, ty⟩ :: ks) sd t (fallR ks.length ty (seqVal false t)))
    (trSeq nloc res (⟨ks.length, sd, ty⟩ :: ks) sd el (fallR ks.length ty (seqVal false el)))
    k)) hlc hf' hctx ha
  simp only [trE, evalE]
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
        exact rfl
      | some cv =>
        rw [Option.isSome_some] at hv
        rw [← hv, needVal_true, eval_ifJoin, eval_case_truthy (hs₁ cv rfl)]
        dsimp only
        have hb₀ : Below sd σ (upd σ₁ .junk .unit) := hb₁.upd_junk _
        have ha₀ : Agree nloc ls₁ (upd σ₁ .junk .unit) := ha₁.upd_junk _
        cases hcv : cv.truthy with
        | none => exact rfl
        | some b =>
          dsimp only
          cases b with
          | true =>
            have hfb : fuelSeq t ≤ n ∨ (evalSeq n ls₁ none t).isSome = true := by
              rcases hf with hf | hf
              · left
                simp only [fuelE] at hf
                omega
              · right
                cases hs : evalSeq n ls₁ none t with
                | none => simp [evalE, h, hcv, hs] at hf
                | some _ => rfl
            have hS := ihS t (⟨ks.length, sd, ty⟩ :: ks) sd ls₁ (upd σ₁ .junk .unit)
              (fallR ks.length ty (seqVal false t)) none hlt hfb (hctx.push ty) ha₀
              (SlotRes.none' _ _)
            rw [ite_eq_left (rfl : true = true)]
            exact simR_block hctx hb₀ hS (fun ls' r h' => by simpa using seqVal_ok h')
          | false =>
            have hfb : fuelSeq el ≤ n ∨ (evalSeq n ls₁ none el).isSome = true := by
              rcases hf with hf | hf
              · left
                simp only [fuelE] at hf
                omega
              · right
                cases hs : evalSeq n ls₁ none el with
                | none => simp [evalE, h, hcv, hs] at hf
                | some _ => rfl
            have hS := ihS el (⟨ks.length, sd, ty⟩ :: ks) sd ls₁ (upd σ₁ .junk .unit)
              (fallR ks.length ty (seqVal false el)) none hle hfb (hctx.push ty) ha₀
              (SlotRes.none' _ _)
            rw [ite_eq_right Bool.false_ne_true]
            exact simR_block hctx hb₀ hS (fun ls' r h' => by simpa using seqVal_ok h')
    | brk l ls' r => exact hE
    | ret r => exact hE
    | trap => exact hE

theorem step_br (ihA : PA nloc res n) {l : Nat} {args : List Expr}
    (hlf : loopFree (.br l args) = true)
    (hf : fuelE (.br l args) ≤ n + 1 ∨ (evalE (n + 1) ls (.br l args)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.br l args) k).evalRTL model σ)
      (evalE (n + 1) ls (.br l args)) := by
  have hlf' : loopFreeL args = true := by simpa [loopFree] using hlf
  have hf' : fuelArgs args ≤ n ∨ (evalArgs n ls args).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalArgs n ls args with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hA := ihA args ks sd ls σ (jumpTo ks res l sd (!args.isEmpty)) hlf' hf' hctx ha
  simp only [trE, evalE]
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
      exact simAbr_jumpTo (α := Option WVal) hctx ha' hb' (slotRes_head hs')
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem step_brIf (ihA : PA nloc res n) {l : Nat} {args : List Expr}
    (hlf : loopFree (.brIf l args) = true)
    (hf : fuelE (.brIf l args) ≤ n + 1 ∨ (evalE (n + 1) ls (.brIf l args)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.brIf l args) k).evalRTL model σ)
      (evalE (n + 1) ls (.brIf l args)) := by
  have hlf' : loopFreeL args = true := by simpa [loopFree] using hlf
  have hf' : fuelArgs args ≤ n ∨ (evalArgs n ls args).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalArgs n ls args with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hA := ihA args ks sd ls σ (brIfTest ks res l sd k args.length) hlf' hf' hctx ha
  simp only [trE, evalE]
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
        exact rfl
      | succ m =>
        have hvl : vs.length = m + 1 := hlen.trans hm
        have hlast : vs.getLast? = some (vs[m]'(by omega)) := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
          simp [hvl]
        have hsm : σ' (.tmp (sd + m)) = .val (vs[m]'(by omega)) := hs' m (by omega)
        rw [hlast]
        dsimp only
        rw [brIfTest, eval_case_truthy hsm]
        cases hc : (vs[m]'(by omega)).truthy with
        | none => exact rfl
        | some b =>
          cases b with
          | true =>
            have hj := simAbr_jumpTo (res := res) (l := l) (α := Option WVal) hctx
              (ha'.upd_junk .unit) (hb'.upd_junk _) ((slotRes_dropLast_head hs').upd_junk .unit)
            rw [isSome_dropLast_head hvl] at hj
            exact hj
          | false =>
            exact ⟨upd σ' .junk .unit, ha'.upd_junk _, hb'.upd_junk _,
              (slotRes_dropLast_head hs').upd_junk _, rfl⟩
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem step_return (ihA : PA nloc res n) {args : List Expr}
    (hlf : loopFree (.return_ args) = true)
    (hf : fuelE (.return_ args) ≤ n + 1 ∨ (evalE (n + 1) ls (.return_ args)).isSome = true)
    (hctx : CtxOk ks sd) (ha : Agree nloc ls σ) :
    SimR nloc res ks sd k σ ((trE nloc res ks sd (.return_ args) k).evalRTL model σ)
      (evalE (n + 1) ls (.return_ args)) := by
  have hlf' : loopFreeL args = true := by simpa [loopFree] using hlf
  have hf' : fuelArgs args ≤ n ∨ (evalArgs n ls args).isSome = true := by
    rcases hf with hf | hf
    · left; simp only [fuelE] at hf; omega
    · right
      cases h : evalArgs n ls args with
      | none => simp [evalE, h] at hf
      | some _ => rfl
  have hA := ihA args ks sd ls σ (retR res sd (!args.isEmpty)) hlf' hf' hctx ha
  simp only [trE, evalE]
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
      exact ⟨σ', eval_retR (slotRes_head hs')⟩
    | brk l ls' r => exact hA
    | ret r => exact hA
    | trap => exact hA

theorem stepE (ihE : PE nloc res n) (ihA : PA nloc res n) (ihS : PS nloc res n) :
    PE nloc res (n + 1) := by
  intro e ks sd ls σ k hlf hf hctx ha
  cases e with
  | op o args => exact step_op ihA hlf hf hctx ha
  | localGet i => exact step_localGet ha
  | localSet i e => exact step_localSet ihE hlf hf hctx ha
  | localTee i e => exact step_localTee ihE hlf hf hctx ha
  | drop e => exact step_drop ihE hlf hf hctx ha
  | nop =>
    simp only [trE, evalE]
    exact ⟨σ, ha, Below.refl sd σ, SlotRes.none' _ _, rfl⟩
  | unreachable =>
    simp only [trE, evalE]
    exact eval_abort k σ
  | block ty body => exact step_block ihS hlf hf hctx ha
  | loop ty body => simp [loopFree] at hlf
  | if_ ty c t el => exact step_if ihE ihS hlf hf hctx ha
  | br l args => exact step_br ihA hlf hf hctx ha
  | brIf l args => exact step_brIf ihA hlf hf hctx ha
  | return_ args => exact step_return ihA hlf hf hctx ha

theorem stepA (ihE : PE nloc res n) (ihA : PA nloc res n) : PA nloc res (n + 1) := by
  intro es ks sd ls σ k hlf hf hctx ha
  cases es with
  | nil =>
    simp only [trArgs, evalArgs]
    exact ⟨σ, ha, Below.refl sd σ, fun i hi => by simp at hi, rfl⟩
  | cons e es =>
    simp only [loopFreeL, Bool.and_eq_true] at hlf
    obtain ⟨hle, hles⟩ := hlf
    have hfe : fuelE e ≤ n ∨ (evalE n ls e).isSome = true := by
      rcases hf with hf | hf
      · left; simp only [fuelArgs] at hf; omega
      · right
        cases h : evalE n ls e with
        | none => simp [evalArgs, h] at hf
        | some _ => rfl
    have hE := ihE e ks sd ls σ (needVal (hasVal e) (trArgs nloc res ks (sd + 1) es k)) hle hfe
      hctx ha
    simp only [trArgs, evalArgs]
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
          exact rfl
        | some v =>
          rw [Option.isSome_some] at hv
          rw [← hv, needVal_true]
          dsimp only
          have hfs : fuelArgs es ≤ n ∨ (evalArgs n ls₁ es).isSome = true := by
            rcases hf with hf | hf
            · left; simp only [fuelArgs] at hf; omega
            · right
              cases h' : evalArgs n ls₁ es with
              | none => simp [evalArgs, h, h'] at hf
              | some _ => rfl
          have hA := ihA es ks (sd + 1) ls₁ σ₁ k hles hfs (hctx.mono (Nat.le_succ sd)) ha₁
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
              simp only [SimA] at hA ⊢
              exact simAbr_mono hctx hb₁ hA
            | ret r =>
              simp only [SimA] at hA ⊢
              exact simAbr_mono hctx hb₁ hA
            | trap =>
              simp only [SimA] at hA ⊢
              exact simAbr_mono hctx hb₁ hA
      | brk l ls' r => exact hE
      | ret r => exact hE
      | trap => exact hE

theorem stepS (ihE : PE nloc res n) (ihS : PS nloc res n) : PS nloc res (n + 1) := by
  intro es ks sd ls σ k r hlf hf hctx ha hs
  cases es with
  | nil =>
    simp only [trSeq, evalSeq]
    exact ⟨σ, ha, Below.refl sd σ, hs, rfl⟩
  | cons e es =>
    simp only [loopFreeL, Bool.and_eq_true] at hlf
    obtain ⟨hle, hles⟩ := hlf
    have hfe : fuelE e ≤ n ∨ (evalE n ls e).isSome = true := by
      rcases hf with hf | hf
      · left; simp only [fuelSeq] at hf; omega
      · right
        cases h : evalE n ls e with
        | none => simp [evalSeq, h] at hf
        | some _ => rfl
    have hE := ihE e ks sd ls σ (trSeq nloc res ks sd es k) hle hfe hctx ha
    simp only [trSeq, evalSeq]
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
        have hfs : fuelSeq es ≤ n ∨ (evalSeq n ls₁ r₁ es).isSome = true := by
          rcases hf with hf | hf
          · left; simp only [fuelSeq] at hf; omega
          · right
            simpa [evalSeq, h] using hf
        rw [hx]
        exact simR_mono hctx hb₁ (ihS es ks sd ls₁ σ₁ k r₁ hles hfs hctx ha₁ hs₁)
      | brk l ls' r => exact hE
      | ret r => exact hE
      | trap => exact hE

end Steps

/-- The simulation at every fuel. -/
theorem sim (n : Nat) : PE nloc res n ∧ PA nloc res n ∧ PS nloc res n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro e _ _ ls _ _ _ hf
      have := fuelE_pos e
      simp [evalE] at hf
      omega
    · intro es _ _ ls _ _ _ hf
      have := fuelArgs_pos es
      simp [evalArgs] at hf
      omega
    · intro es _ _ ls _ _ r _ hf
      have := fuelSeq_pos es
      simp [evalSeq] at hf
      omega
  | succ n ih =>
    obtain ⟨ihE, ihA, ihS⟩ := ih
    exact ⟨stepE ihE ihA ihS, stepA ihE ihA, stepS ihE ihS⟩

end

end Silmaril.Proofs.Wasm.LambdaRTL
