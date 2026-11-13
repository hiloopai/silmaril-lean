module

public import Silmaril.Wasm.LambdaRTL.Defs

/-!
# Wasm fragment → λRTL: invariants and basic facts (proofs)

The simulation invariants relating fragment locals and results to λRTL stores (`Agree`,
`Below`, `SlotRes`, `SlotsRes`, `CtxOk`), the simulation predicates `SimAbr`, `SimR`, `SimA`
used by `Silmaril.Proofs.Wasm.LambdaRTL.Sim`, evaluation equations of the translation's building
blocks, and the static facts about results (`hasVal_ok`, `evalArgs_length`, `seqVal_ok`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-! ## The monad and evaluation equations -/

@[simp] theorem ok_bind {α β : Type} (a : α) (f : α → WM β) :
    ((Except.ok a : WM α) >>= f) = f a := rfl

@[simp] theorem error_bind {α β : Type} (e : WErr) (f : α → WM β) :
    ((Except.error e : WM α) >>= f) = Except.error e := rfl

@[simp] theorem pure_wm {α : Type} (a : α) : (pure a : WM α) = Except.ok a := rfl

theorem eval_br (ℓ : WLab) (a : Val WReg) (σ : Store) :
    (Region.br ℓ a : WRegion).evalRTL model σ = .ok (ℓ, a.eval model σ, σ) := rfl

@[simp] theorem eval_stuckR (σ : Store) : stuckR.evalRTL model σ = .error .stuck := rfl

@[simp] theorem eval_mv (dst src : WReg) (k : WRegion) (σ : Store) :
    (mv dst src k).evalRTL model σ = k.evalRTL model (upd σ dst (σ src)) := rfl

theorem eval_join (r : WRegion) (ℓ : WLab) (x : WReg) (t : WRegion) (σ : Store) :
    (Region.join r ℓ x t).evalRTL model σ =
      r.evalRTL model σ >>= fun e =>
        if e.1 = ℓ then t.evalRTL model (upd e.2.2 x e.2.1) else pure e := rfl

theorem eval_abort (k : WRegion) (σ : Store) :
    (Region.let1 .junk (.abort .unit) k : WRegion).evalRTL model σ = .error .trap := rfl

theorem eval_case_truthy {σ : Store} {y : WReg} {v : WVal} (h : σ y = .val v) (x : WReg)
    (r s : WRegion) :
    (Region.case (.app .truthy (.var y)) x r x s : WRegion).evalRTL model σ =
      match v.truthy with
      | some true => r.evalRTL model (upd σ x .unit)
      | some false => s.evalRTL model (upd σ x .unit)
      | none => .error .stuck := by
  cases hv : v.truthy with
  | none => simp [Region.evalRTL, Silmaril.SSA.LambdaRTL.Op.eval, Val.eval, h, model, app, hv]
  | some b =>
    cases b <;> simp [Region.evalRTL, Silmaril.SSA.LambdaRTL.Op.eval, Val.eval, h, model, app, hv]

theorem eval_let1_op (sd : Nat) (o : Silmaril.Wasm.SSA.Op) (a : Val WReg) (k : WRegion) (σ : Store) :
    (Region.let1 (.tmp sd) (.app (.op o) a) k : WRegion).evalRTL model σ =
      app (.op o) (a.eval model σ) >>= fun b => k.evalRTL model (upd σ (.tmp sd) b) := rfl

theorem toList_ofList : ∀ vs : List WVal, (RVal.ofList vs).toList = some vs
  | [] => rfl
  | v :: vs => by simp [RVal.ofList, RVal.toList, toList_ofList vs]

theorem app_op_ofList (o : Silmaril.Wasm.SSA.Op) (vs : List WVal) :
    app (.op o) (RVal.ofList vs) = ofRes (o.eval vs) := by
  simp [app, toList_ofList]

/-! ## Invariants -/

/-- The store holds the fragment locals `ls`; `nloc` is their (invariant) number. -/
def Agree (nloc : Nat) (ls : List WVal) (σ : Store) : Prop :=
  ls.length = nloc ∧ ∀ i (h : i < ls.length), σ (.loc i) = .val ls[i]

/-- `σ'` keeps the operand-stack slots below `sd` of `σ`. -/
def Below (sd : Nat) (σ σ' : Store) : Prop := ∀ j, j < sd → σ' (.tmp j) = σ (.tmp j)

/-- Slot `sd` holds the result, if there is one. -/
def SlotRes (sd : Nat) (r : Option WVal) (σ : Store) : Prop :=
  ∀ v, r = some v → σ (.tmp sd) = .val v

/-- Slots `sd, sd+1, …` hold the operand values. -/
def SlotsRes (sd : Nat) (vs : List WVal) (σ : Store) : Prop :=
  ∀ i (h : i < vs.length), σ (.tmp (sd + i)) = .val vs[i]

/-- A label context: every block result slot is at most the current depth, and its join label
depth is below the context length (inner joins use larger depths). -/
def CtxOk (ks : List Tgt) (sd : Nat) : Prop := ∀ t ∈ ks, t.slot ≤ sd ∧ t.d < ks.length

theorem Agree.upd_tmp {nloc : Nat} {ls : List WVal} {σ : Store} (h : Agree nloc ls σ) (j : Nat)
    (a : RVal) : Agree nloc ls (upd σ (.tmp j) a) :=
  ⟨h.1, fun i hi => by simp [upd, h.2 i hi]⟩

theorem Agree.upd_junk {nloc : Nat} {ls : List WVal} {σ : Store} (h : Agree nloc ls σ)
    (a : RVal) : Agree nloc ls (upd σ .junk a) :=
  ⟨h.1, fun i hi => by simp [upd, h.2 i hi]⟩

theorem Agree.set {nloc : Nat} {ls : List WVal} {σ : Store} (h : Agree nloc ls σ) {i : Nat}
    (v : WVal) : Agree nloc (ls.set i v) (upd σ (.loc i) (.val v)) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  simp only [List.length_set] at hj
  by_cases hji : j = i
  · subst hji
    simp [upd]
  · have hne : WReg.loc j ≠ WReg.loc i := by simp [hji]
    simp only [upd, ite_eq_right hne, h.2 j hj]
    rw [List.getElem_set_ne (Ne.symm hji)]

theorem Below.refl (sd : Nat) (σ : Store) : Below sd σ σ := fun _ _ => rfl

theorem Below.trans {sd : Nat} {σ₁ σ₂ σ₃ : Store} (h₁ : Below sd σ₁ σ₂) (h₂ : Below sd σ₂ σ₃) :
    Below sd σ₁ σ₃ := fun j hj => (h₂ j hj).trans (h₁ j hj)

theorem Below.mono {sd sd' : Nat} {σ σ' : Store} (h : Below sd σ σ') (hle : sd' ≤ sd) :
    Below sd' σ σ' := fun j hj => h j (by omega)

theorem Below.upd_tmp {sd j : Nat} {σ σ' : Store} (h : Below sd σ σ') (hj : sd ≤ j) (a : RVal) :
    Below sd σ (upd σ' (.tmp j) a) := fun i hi => by
  have hne : WReg.tmp i ≠ WReg.tmp j := by simp; omega
  simp only [upd, ite_eq_right hne, h i hi]

theorem Below.upd_loc {sd : Nat} {σ σ' : Store} (h : Below sd σ σ') (i : Nat) (a : RVal) :
    Below sd σ (upd σ' (.loc i) a) := fun j hj => by simp [upd, h j hj]

theorem Below.upd_junk {sd : Nat} {σ σ' : Store} (h : Below sd σ σ') (a : RVal) :
    Below sd σ (upd σ' .junk a) := fun j hj => by simp [upd, h j hj]

theorem SlotRes.none' (sd : Nat) (σ : Store) : SlotRes sd none σ := fun _ h => by cases h

theorem SlotRes.upd_loc {sd : Nat} {r : Option WVal} {σ : Store} (h : SlotRes sd r σ) (i : Nat)
    (a : RVal) : SlotRes sd r (upd σ (.loc i) a) := fun v hv => by simp [upd, h v hv]

theorem SlotRes.upd_junk {sd : Nat} {r : Option WVal} {σ : Store} (h : SlotRes sd r σ)
    (a : RVal) : SlotRes sd r (upd σ .junk a) := fun v hv => by simp [upd, h v hv]

theorem CtxOk.mono {ks : List Tgt} {sd sd' : Nat} (h : CtxOk ks sd) (hle : sd ≤ sd') :
    CtxOk ks sd' := fun t ht => ⟨(h t ht).1.trans hle, (h t ht).2⟩

theorem CtxOk.push {ks : List Tgt} {sd : Nat} (h : CtxOk ks sd) (ty : Option IntType) :
    CtxOk (⟨ks.length, sd, ty⟩ :: ks) sd := by
  intro t ht
  simp only [List.mem_cons] at ht
  rcases ht with rfl | ht
  · simp
  · exact ⟨(h t ht).1, by simp; have := (h t ht).2; omega⟩

theorem eval_pack {σ : Store} : ∀ {sd : Nat} {vs : List WVal}, SlotsRes sd vs σ →
    (pack sd vs.length).eval model σ = RVal.ofList vs
  | _, [], _ => rfl
  | sd, v :: vs, h => by
    have h0 : σ (.tmp sd) = .val v := h 0 (by simp)
    have h1 : SlotsRes (sd + 1) vs σ := fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show sd + (i + 1) = sd + 1 + i by omega] at this
      exact this
    show Val.eval model σ (.pair (.var (.tmp sd)) (pack (sd + 1) vs.length)) = _
    simp only [Val.eval, h0, eval_pack h1, RVal.ofList]
    rfl

/-! ## Simulation predicates -/

/-- Result type of a λRTL region evaluation in the model. -/
abbrev Res3 := WM (WLab × RVal × Store)

/-- The λRTL result `x` of a fragment outcome that leaves the current expression abruptly, under
the labels `ks`, from the store `σ` at the start of the expression. -/
def SimAbr (nloc : Nat) (res : Option IntType) (ks : List Tgt) (σ : Store) (x : Res3)
    {α : Type} : Out α → Prop
  | .ok _ _ => False
  | .trap => x = .error .trap
  | .ret r => ∃ σ', x = .ok (.ret, encR (blockRes res r), σ')
  | .brk l ls' r =>
      match ks[l]? with
      | some t =>
          if t.ty.isSome && r.isNone then x = .error .stuck
          else ∃ σ', Agree nloc ls' σ' ∧ Below t.slot σ σ' ∧
            SlotRes t.slot (blockRes t.ty r) σ' ∧ x = .ok (.blk t.d, .unit, σ')
      | none =>
          if l = ks.length then ∃ σ', x = .ok (.ret, encR (blockRes res r), σ')
          else x = .error .stuck

/-- The λRTL result `x` of an expression or body translated at depth `sd` with continuation `k`,
for an interpreter result (`none`: stuck). -/
def SimR (nloc : Nat) (res : Option IntType) (ks : List Tgt) (sd : Nat) (k : WRegion)
    (σ : Store) (x : Res3) : Option (Out (Option WVal)) → Prop
  | none => x = .error .stuck
  | some (.ok ls' r) => ∃ σ', Agree nloc ls' σ' ∧ Below sd σ σ' ∧ SlotRes sd r σ' ∧
      x = k.evalRTL model σ'
  | some (.brk l ls' r) => SimAbr nloc res ks σ x (Out.brk (α := Option WVal) l ls' r)
  | some (.ret r) => SimAbr nloc res ks σ x (Out.ret (α := Option WVal) r)
  | some .trap => SimAbr nloc res ks σ x (Out.trap (α := Option WVal))

/-- The same for operand lists, whose values occupy consecutive slots from `sd`. -/
def SimA (nloc : Nat) (res : Option IntType) (ks : List Tgt) (sd : Nat) (k : WRegion)
    (σ : Store) (x : Res3) : Option (Out (List WVal)) → Prop
  | none => x = .error .stuck
  | some (.ok ls' vs) => ∃ σ', Agree nloc ls' σ' ∧ Below sd σ σ' ∧ SlotsRes sd vs σ' ∧
      x = k.evalRTL model σ'
  | some (.brk l ls' r) => SimAbr nloc res ks σ x (Out.brk (α := List WVal) l ls' r)
  | some (.ret r) => SimAbr nloc res ks σ x (Out.ret (α := List WVal) r)
  | some .trap => SimAbr nloc res ks σ x (Out.trap (α := List WVal))

theorem simAbr_mono {nloc : Nat} {res : Option IntType} {ks : List Tgt} {sd : Nat}
    {σ σ₁ : Store} (hctx : CtxOk ks sd) (hb : Below sd σ σ₁) {x : Res3} {α : Type} :
    ∀ {o : Out α}, SimAbr nloc res ks σ₁ x o → SimAbr nloc res ks σ x o
  | .ok _ _, h => h
  | .trap, h => h
  | .ret _, h => h
  | .brk l ls' r, h => by
    simp only [SimAbr] at h ⊢
    cases hk : ks[l]? with
    | none => simp only [hk] at h ⊢; exact h
    | some t =>
      simp only [hk] at h ⊢
      have hmem : t ∈ ks := List.mem_of_getElem? hk
      by_cases hc : (t.ty.isSome && r.isNone) = true
      · rw [ite_eq_left hc] at h ⊢; exact h
      · rw [ite_eq_right hc] at h ⊢
        obtain ⟨σ', ha, hb', hs, hx⟩ := h
        exact ⟨σ', ha, (hb.mono (hctx t hmem).1).trans hb', hs, hx⟩

theorem simAbr_cast {nloc : Nat} {res : Option IntType} {ks : List Tgt} {σ : Store} {x : Res3}
    {α β : Type} : ∀ {o : Out α}, o.Abrupt →
      (SimAbr nloc res ks σ x (o.cast : Out β) ↔ SimAbr nloc res ks σ x o)
  | .ok _ _, h => absurd h (by simp [Out.Abrupt])
  | .trap, _ => Iff.rfl
  | .ret _, _ => Iff.rfl
  | .brk _ _ _, _ => Iff.rfl

theorem simR_mono {nloc : Nat} {res : Option IntType} {ks : List Tgt} {sd : Nat} {k : WRegion}
    {σ σ₁ : Store} (hctx : CtxOk ks sd) (hb : Below sd σ σ₁) {x : Res3} :
    ∀ {o : Option (Out (Option WVal))}, SimR nloc res ks sd k σ₁ x o → SimR nloc res ks sd k σ x o
  | none, h => h
  | some (.ok _ _), h => by
    obtain ⟨σ', ha, hb', hs, hx⟩ := h
    exact ⟨σ', ha, hb.trans hb', hs, hx⟩
  | some (.brk _ _ _), h => by simp only [SimR] at h ⊢; exact simAbr_mono hctx hb h
  | some (.ret _), h => by simp only [SimR] at h ⊢; exact simAbr_mono hctx hb h
  | some .trap, h => by simp only [SimR] at h ⊢; exact simAbr_mono hctx hb h

/-- An abrupt interpreter outcome, seen through `SimR`. -/
theorem simR_abrupt {nloc : Nat} {res : Option IntType} {ks : List Tgt} {sd : Nat} {k : WRegion}
    {σ : Store} {x : Res3} {α : Type} {o : Out α} (ho : o.Abrupt) :
    SimR nloc res ks sd k σ x (some o.cast) ↔ SimAbr nloc res ks σ x o := by
  cases o with
  | ok => exact absurd ho (by simp [Out.Abrupt])
  | brk => rfl
  | ret => rfl
  | trap => rfl

/-- The same for operand lists. -/
theorem simA_abrupt {nloc : Nat} {res : Option IntType} {ks : List Tgt} {sd : Nat} {k : WRegion}
    {σ : Store} {x : Res3} {α : Type} {o : Out α} (ho : o.Abrupt) :
    SimA nloc res ks sd k σ x (some o.cast) ↔ SimAbr nloc res ks σ x o := by
  cases o with
  | ok => exact absurd ho (by simp [Out.Abrupt])
  | brk => rfl
  | ret => rfl
  | trap => rfl

/-! ## Static facts about results -/

theorem fuelE_pos (e : Expr) : 1 ≤ fuelE e := by
  cases e <;> simp [fuelE]

theorem fuelArgs_pos (es : List Expr) : 1 ≤ fuelArgs es := by
  cases es <;> simp [fuelArgs]

theorem fuelSeq_pos (es : List Expr) : 1 ≤ fuelSeq es := by
  cases es <;> simp [fuelSeq]

/-- Whether a normal outcome carries a value is static (`hasVal`, `seqVal`), and operand lists
produce one value per operand. -/
theorem stat (n : Nat) :
    (∀ ls e ls' r, evalE n ls e = some (.ok ls' r) → r.isSome = hasVal e) ∧
    (∀ ls es ls' vs, evalArgs n ls es = some (.ok ls' vs) → vs.length = es.length) ∧
    (∀ ls r es ls' r', evalSeq n ls r es = some (.ok ls' r') → r'.isSome = seqVal r.isSome es) := by
  induction n with
  | zero =>
    refine ⟨fun _ _ _ _ h => ?_, fun _ _ _ _ h => ?_, fun _ _ _ _ _ h => ?_⟩ <;>
      simp [evalE, evalArgs, evalSeq] at h
  | succ n ih =>
    obtain ⟨ihE, ihA, ihS⟩ := ih
    refine ⟨fun ls e ls' r h => ?_, fun ls es ls' vs h => ?_, fun ls r es ls' r' h => ?_⟩
    · cases e with
      | op o args =>
        simp only [evalE] at h
        cases ha : evalArgs n ls args with
        | none => simp [ha] at h
        | some ao =>
          cases ao with
          | ok ls₁ vs =>
            simp only [ha] at h
            cases hv : o.eval vs with
            | none => simp [hv] at h
            | some rv =>
              cases rv with
              | val v =>
                simp only [hv, Option.some.injEq, Out.ok.injEq] at h
                obtain ⟨-, rfl⟩ := h
                rfl
              | trap => simp [hv] at h
          | brk => simp [ha, Out.cast] at h
          | ret => simp [ha, Out.cast] at h
          | trap => simp [ha, Out.cast] at h
      | localGet i =>
        simp only [evalE] at h
        cases hi : ls[i]? with
        | none => simp [hi] at h
        | some v =>
          simp [hi] at h
          obtain ⟨-, rfl⟩ := h
          rfl
      | localSet i e =>
        simp only [evalE] at h
        cases he : evalE n ls e with
        | none => simp [he] at h
        | some eo =>
          cases eo with
          | ok ls₁ r₁ => cases r₁ <;> simp_all [hasVal]
          | brk => simp [he] at h
          | ret => simp [he] at h
          | trap => simp [he] at h
      | localTee i e =>
        simp only [evalE] at h
        cases he : evalE n ls e with
        | none => simp [he] at h
        | some eo =>
          cases eo with
          | ok ls₁ r₁ =>
            cases r₁ with
            | none => simp [he] at h
            | some v =>
              simp [he] at h
              obtain ⟨-, rfl⟩ := h
              rfl
          | brk => simp [he] at h
          | ret => simp [he] at h
          | trap => simp [he] at h
      | drop e =>
        simp only [evalE] at h
        cases he : evalE n ls e with
        | none => simp [he] at h
        | some eo =>
          cases eo with
          | ok ls₁ r₁ => simp_all [hasVal]
          | brk => simp [he] at h
          | ret => simp [he] at h
          | trap => simp [he] at h
      | nop => simp_all [evalE, hasVal]
      | unreachable => simp [evalE] at h
      | block ty body =>
        simp only [evalE] at h
        cases hb : evalSeq n ls none body with
        | none => simp [hb] at h
        | some bo =>
          rw [hb, Option.bind_some] at h
          cases bo with
          | ok ls₁ r₁ =>
            simp only [evalE.blockExit] at h
            split at h
            · cases h
            · simp only [Option.some.injEq, Out.ok.injEq] at h
              obtain ⟨-, rfl⟩ := h
              cases ty <;> cases r₁ <;> simp_all [blockRes, hasVal]
          | brk l ls₁ r₁ =>
            cases l with
            | zero =>
              simp only [evalE.blockExit] at h
              split at h
              · cases h
              · simp only [Option.some.injEq, Out.ok.injEq] at h
                obtain ⟨-, rfl⟩ := h
                cases ty <;> cases r₁ <;> simp_all [blockRes, hasVal]
            | succ l => simp [evalE.blockExit] at h
          | ret => simp [evalE.blockExit] at h
          | trap => simp [evalE.blockExit] at h
      | loop ty body =>
        simp only [evalE] at h
        cases hb : evalSeq n ls none body with
        | none => simp [hb] at h
        | some bo =>
          cases bo with
          | ok ls₁ r₁ =>
            simp only [hb, evalE.loopExit] at h
            split at h
            · cases h
            · simp only [Option.some.injEq, Out.ok.injEq] at h
              obtain ⟨-, rfl⟩ := h
              cases ty <;> cases r₁ <;> simp_all [blockRes, hasVal]
          | brk l ls₁ r₁ =>
            cases l with
            | zero =>
              simp only [hb] at h
              exact ihE _ _ _ _ h
            | succ l => simp [hb, evalE.loopExit] at h
          | ret => simp [hb, evalE.loopExit] at h
          | trap => simp [hb, evalE.loopExit] at h
      | if_ ty c t el =>
        simp only [evalE] at h
        cases hc : evalE n ls c with
        | none => simp [hc] at h
        | some co =>
          cases co with
          | ok ls₁ r₁ =>
            cases r₁ with
            | none => simp [hc] at h
            | some cv =>
              simp only [hc] at h
              cases ht : cv.truthy with
              | none => simp [ht] at h
              | some b =>
                simp only [ht] at h
                cases hb : evalSeq n ls₁ none (if b then t else el) with
                | none => simp [hb] at h
                | some bo =>
                  rw [hb, Option.bind_some] at h
                  cases bo with
                  | ok ls₂ r₂ =>
                    simp only [evalE.blockExit] at h
                    split at h
                    · cases h
                    · simp only [Option.some.injEq, Out.ok.injEq] at h
                      obtain ⟨-, rfl⟩ := h
                      cases ty <;> cases r₂ <;> simp_all [blockRes, hasVal]
                  | brk l ls₂ r₂ =>
                    cases l with
                    | zero =>
                      simp only [evalE.blockExit] at h
                      split at h
                      · cases h
                      · simp only [Option.some.injEq, Out.ok.injEq] at h
                        obtain ⟨-, rfl⟩ := h
                        cases ty <;> cases r₂ <;> simp_all [blockRes, hasVal]
                    | succ l => simp [evalE.blockExit] at h
                  | ret => simp [evalE.blockExit] at h
                  | trap => simp [evalE.blockExit] at h
          | brk => simp [hc] at h
          | ret => simp [hc] at h
          | trap => simp [hc] at h
      | br l args =>
        simp only [evalE] at h
        cases ha : evalArgs n ls args with
        | none => simp [ha] at h
        | some ao => cases ao <;> simp [ha, Out.cast] at h
      | brIf l args =>
        simp only [evalE] at h
        cases ha : evalArgs n ls args with
        | none => simp [ha] at h
        | some ao =>
          cases ao with
          | ok ls₁ vs =>
            have hlen := ihA _ _ _ _ ha
            simp only [ha] at h
            cases hl : vs.getLast? with
            | none => simp [hl] at h
            | some c =>
              simp only [hl] at h
              cases hc : c.truthy with
              | none => simp [hc] at h
              | some b =>
                cases b with
                | false =>
                  simp [hc] at h
                  obtain ⟨-, rfl⟩ := h
                  simp only [hasVal]
                  rw [← hlen]
                  rcases vs with _ | ⟨v, _ | ⟨w, ws⟩⟩ <;> simp
                | true => simp [hc] at h
          | brk => simp [ha, Out.cast] at h
          | ret => simp [ha, Out.cast] at h
          | trap => simp [ha, Out.cast] at h
      | return_ args =>
        simp only [evalE] at h
        cases ha : evalArgs n ls args with
        | none => simp [ha] at h
        | some ao => cases ao <;> simp [ha, Out.cast] at h
    · cases es with
      | nil =>
        simp only [evalArgs, Option.some.injEq, Out.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
      | cons e es =>
        simp only [evalArgs] at h
        cases he : evalE n ls e with
        | none => simp [he] at h
        | some eo =>
          cases eo with
          | ok ls₁ r₁ =>
            cases r₁ with
            | none => simp [he] at h
            | some v =>
              simp only [he] at h
              cases ha : evalArgs n ls₁ es with
              | none => simp [ha] at h
              | some ao =>
                cases ao with
                | ok ls₂ vs₂ =>
                  simp only [ha, Option.some.injEq, Out.ok.injEq] at h
                  obtain ⟨-, rfl⟩ := h
                  simp [ihA _ _ _ _ ha]
                | brk => simp [ha] at h
                | ret => simp [ha] at h
                | trap => simp [ha] at h
          | brk => simp [he, Out.cast] at h
          | ret => simp [he, Out.cast] at h
          | trap => simp [he, Out.cast] at h
    · cases es with
      | nil =>
        simp only [evalSeq, Option.some.injEq, Out.ok.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
      | cons e es =>
        simp only [evalSeq] at h
        cases he : evalE n ls e with
        | none => simp [he] at h
        | some eo =>
          cases eo with
          | ok ls₁ r₁ =>
            simp only [he] at h
            rw [ihS _ _ _ _ _ h, ihE _ _ _ _ he]
            rfl
          | brk => simp [he] at h
          | ret => simp [he] at h
          | trap => simp [he] at h

theorem hasVal_ok {n : Nat} {ls : List WVal} {e : Expr} {ls' : List WVal} {r : Option WVal}
    (h : evalE n ls e = some (.ok ls' r)) : r.isSome = hasVal e := (stat n).1 _ _ _ _ h

theorem evalArgs_length {n : Nat} {ls : List WVal} {es : List Expr} {ls' : List WVal}
    {vs : List WVal} (h : evalArgs n ls es = some (.ok ls' vs)) : vs.length = es.length :=
  (stat n).2.1 _ _ _ _ h

theorem seqVal_ok {n : Nat} {ls : List WVal} {r : Option WVal} {es : List Expr}
    {ls' : List WVal} {r' : Option WVal} (h : evalSeq n ls r es = some (.ok ls' r')) :
    r'.isSome = seqVal r.isSome es := (stat n).2.2 _ _ _ _ _ h

end Silmaril.Proofs.Wasm.LambdaRTL
