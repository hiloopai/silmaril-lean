module

public import Silmaril.Wasm.LambdaRTL.Loop.Defs
public import Silmaril.Semantics.Elgot.Thms
public import Silmaril.Proofs.Wasm.LambdaRTL.Sim

/-!
# Wasm fragment → λRTL with loops: the monad, invariants and building blocks (proofs)

* `LM = ExceptT WErr Part`: terminating results `okL`/`errL` and the bind, map and iteration
  equations used by the simulations (`okL_bind`, `errL_bind`, `iterL_cont`, `iterL_ret`,
  `iterL_err`, `iterL_run`).
* `CtxOkL`, `SimAbrL`, `SimRL`, `SimAL`: the simulation predicates of the loop-free proof
  (`Silmaril.Proofs.Wasm.LambdaRTL.Basic`) for labels that may be loops, in `LM`.
* Evaluation equations of the translation's building blocks in `modelL`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LambdaRTL

open Silmaril.SSA.LambdaRTL (Val Op Model upd)
open Silmaril.Wasm.SSA (WVal Expr FragFunc FOut Out Res blockRes funcExit evalE evalArgs evalSeq)
open Silmaril.Wasm.LambdaRTL
open Silmaril.Wasm (IntType)

/-! ## The monad -/

/-- A terminating normal result. -/
def okL {α : Type} (a : α) : LM α := liftE (.ok a)

/-- A terminating error. -/
def errL {α : Type} (e : WErr) : LM α := liftE (.error e)

theorem okL_bind {α β : Type} (a : α) (f : α → LM β) : (okL a >>= f) = f a := by
  show (Part.some (Except.ok a)).bind (ExceptT.bindCont f) = f a
  rw [Part.bind_some]
  rfl

theorem errL_bind {α β : Type} (e : WErr) (f : α → LM β) : (errL e >>= f) = errL e := by
  show (Part.some (Except.error e)).bind (ExceptT.bindCont f) = Part.some (Except.error e)
  rw [Part.bind_some]
  rfl

theorem pure_eq_okL {α : Type} (a : α) : (pure a : LM α) = okL a := rfl

theorem liftE_ok {α : Type} (a : α) : liftE (.ok a) = okL a := rfl

theorem liftE_error {α : Type} (e : WErr) : (liftE (.error e) : LM α) = errL e := rfl

theorem map_okL {α β : Type} (g : α → β) (a : α) : g <$> okL a = okL (g a) := by
  rw [map_eq_pure_bind, okL_bind]
  rfl

theorem map_errL {α β : Type} (g : α → β) (e : WErr) : g <$> (errL e : LM α) = errL e := by
  rw [map_eq_pure_bind, errL_bind]

theorem okL_run {α : Type} (a : α) : (okL a).run = Part.some (Except.ok a) := rfl

theorem errL_run {α : Type} (e : WErr) : (errL e : LM α).run = Part.some (Except.error e) := rfl

/-! ## Iteration -/

theorem iterL_run {A B : Type} (f : A → LM (B ⊕ A)) (a : A) :
    (Silmaril.Elgot.iter f a).run = Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a := rfl

/-- One step that continues. -/
theorem iterL_cont {A B : Type} {f : A → LM (B ⊕ A)} {a a' : A} (h : f a = okL (.inr a')) :
    Silmaril.Elgot.iter f a = Silmaril.Elgot.iter f a' := by
  show Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a =
    Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a'
  rw [congrFun (Silmaril.Elgot.Part.fixpoint (fun a => routeE <$> (f a).run)) a]
  show Part.bind (routeE <$> (f a).run) _ = _
  rw [h, okL_run]
  show Part.bind (Part.map routeE (Part.some (Except.ok (Sum.inr a')))) _ = _
  rw [Part.map_some, Part.bind_some]
  rfl

/-- One step that returns. -/
theorem iterL_ret {A B : Type} {f : A → LM (B ⊕ A)} {a : A} {b : B} (h : f a = okL (.inl b)) :
    Silmaril.Elgot.iter f a = okL b := by
  show Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a = Part.some (Except.ok b)
  rw [congrFun (Silmaril.Elgot.Part.fixpoint (fun a => routeE <$> (f a).run)) a]
  show Part.bind (routeE <$> (f a).run) _ = _
  rw [h, okL_run]
  show Part.bind (Part.map routeE (Part.some (Except.ok (Sum.inl b)))) _ = _
  rw [Part.map_some, Part.bind_some]
  rfl

/-- One step that fails. -/
theorem iterL_err {A B : Type} {f : A → LM (B ⊕ A)} {a : A} {e : WErr} (h : f a = errL e) :
    Silmaril.Elgot.iter f a = (errL e : LM B) := by
  show Silmaril.Elgot.iter (fun a => routeE <$> (f a).run) a = Part.some (Except.error e)
  rw [congrFun (Silmaril.Elgot.Part.fixpoint (fun a => routeE <$> (f a).run)) a]
  show Part.bind (routeE <$> (f a).run) _ = _
  rw [h, errL_run]
  show Part.bind (Part.map routeE (Part.some (Except.error e))) _ = _
  rw [Part.map_some, Part.bind_some]
  rfl

/-! ## Evaluation of the building blocks -/

/-- Values are evaluated alike in `modelL` and `model`. -/
theorem valEval_L (σ : Store) : ∀ a : Val WReg, a.eval modelL σ = a.eval model σ
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
    show RVal.pair (a.eval modelL σ) (b.eval modelL σ) = RVal.pair (a.eval model σ) (b.eval model σ)
    rw [valEval_L σ a, valEval_L σ b]

theorem evalL_br (ℓ : LLab) (a : Val WReg) (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.br ℓ a : LRegion).evalRTL modelL σ =
      okL (ℓ, a.eval modelL σ, σ) := rfl

theorem evalL_brUnit (ℓ : LLab) (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.br ℓ .unit : LRegion).evalRTL modelL σ =
      okL (ℓ, .unit, σ) := rfl

theorem evalL_stuckRL (σ : Store) : stuckRL.evalRTL modelL σ = errL .stuck := by
  show liftE (Except.error WErr.stuck) >>= _ = _
  exact errL_bind _ _

theorem evalL_mvL (dst src : WReg) (k : LRegion) (σ : Store) :
    (mvL dst src k).evalRTL modelL σ = k.evalRTL modelL (upd σ dst (σ src)) := by
  show (pure (σ src) : LM RVal) >>= _ = _
  rw [pure_eq_okL, okL_bind]

theorem evalL_join (r : LRegion) (ℓ : LLab) (x : WReg) (t : LRegion) (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.join r ℓ x t : LRegion).evalRTL modelL σ =
      r.evalRTL modelL σ >>= fun e =>
        if e.1 = ℓ then t.evalRTL modelL (upd e.2.2 x e.2.1) else pure e := rfl

theorem evalL_abort (k : LRegion) (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.let1 .junk (.abort .unit) k : LRegion).evalRTL modelL σ =
      errL .trap := by
  show liftE (Except.error WErr.trap) >>= _ = _
  exact errL_bind _ _

theorem evalL_let1_op (sd : Nat) (o : Silmaril.Wasm.SSA.Op) (a : Val WReg) (k : LRegion)
    (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.let1 (.tmp sd) (.app (.op o) a) k : LRegion).evalRTL
        modelL σ =
      liftE (app (.op o) (a.eval modelL σ)) >>= fun b => k.evalRTL modelL (upd σ (.tmp sd) b) :=
  rfl

theorem evalL_case_truthy {σ : Store} {y : WReg} {v : WVal} (h : σ y = .val v) (x : WReg)
    (r s : LRegion) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.case (.app .truthy (.var y)) x r x s : LRegion).evalRTL
        modelL σ =
      match v.truthy with
      | some true => r.evalRTL modelL (upd σ x .unit)
      | some false => s.evalRTL modelL (upd σ x .unit)
      | none => errL .stuck := by
  show liftE (app .truthy (σ y)) >>= (fun c => liftE (model.split c)) >>= _ = _
  rw [h]
  cases hv : v.truthy with
  | none =>
    simp only [app, hv]
    rw [liftE_error, errL_bind, errL_bind]
  | some b =>
    cases b with
    | true =>
      simp only [app, hv]
      rw [liftE_ok, okL_bind]
      show liftE (Except.ok (Sum.inl RVal.unit)) >>= _ = _
      rw [liftE_ok, okL_bind]
    | false =>
      simp only [app, hv]
      rw [liftE_ok, okL_bind]
      show liftE (Except.ok (Sum.inr RVal.unit)) >>= _ = _
      rw [liftE_ok, okL_bind]

/-- The join after a construct at depth `d`: its fallthrough label `blk d` continues with `k`. -/
noncomputable def joinK (d : Nat) (k : LRegion) (e : LLab × RVal × Store) :
    LM (LLab × RVal × Store) :=
  if e.1 = LLab.blk d then k.evalRTL modelL (upd e.2.2 .junk e.2.1) else pure e

theorem joinK_blk (d : Nat) (k : LRegion) (v : RVal) (σ : Store) :
    joinK d k (.blk d, v, σ) = k.evalRTL modelL (upd σ .junk v) := by
  simp [joinK]

theorem joinK_other (d : Nat) (k : LRegion) {e : LLab × RVal × Store} (h : e.1 ≠ LLab.blk d) :
    joinK d k e = okL e := by
  simp [joinK, h, pure_eq_okL]

theorem evalL_joinBlk (r : LRegion) (d : Nat) (k : LRegion) (σ : Store) :
    (Silmaril.SSA.LambdaRTL.Loop.Region.join r (.blk d) .junk k : LRegion).evalRTL modelL σ =
      r.evalRTL modelL σ >>= joinK d k := rfl

/-- One iteration of the loop at depth `d`: run the body, re-enter on `cont d`. -/
noncomputable def loopStep (d : Nat) (body : LRegion) (p : RVal × Store) :
    LM ((LLab × RVal × Store) ⊕ (RVal × Store)) :=
  Silmaril.SSA.LambdaRTL.Loop.routeRTL (LLab.cont d) <$> body.evalRTL modelL (upd p.2 .junk p.1)

theorem loopStep_cont {d : Nat} {body : LRegion} {p : RVal × Store} {v : RVal} {σ' : Store}
    (h : body.evalRTL modelL (upd p.2 .junk p.1) = okL (.cont d, v, σ')) :
    loopStep d body p = okL (.inr (v, σ')) := by
  simp only [loopStep, h, map_okL, Silmaril.SSA.LambdaRTL.Loop.routeRTL]
  rfl

theorem loopStep_exit {d : Nat} {body : LRegion} {p : RVal × Store} {e : LLab × RVal × Store}
    (h : body.evalRTL modelL (upd p.2 .junk p.1) = okL e) (hne : e.1 ≠ LLab.cont d) :
    loopStep d body p = okL (.inl e) := by
  simp only [loopStep, h, map_okL, Silmaril.SSA.LambdaRTL.Loop.routeRTL, hne, ite_false]

theorem loopStep_err {d : Nat} {body : LRegion} {p : RVal × Store} {er : WErr}
    (h : body.evalRTL modelL (upd p.2 .junk p.1) = errL er) :
    loopStep d body p = errL er := by
  simp only [loopStep, h, map_errL]

/-- The loop of depth `d` from `σ`: the iteration from `((), σ)`, then the join. -/
theorem evalL_loopJoin (d : Nat) (body k : LRegion) (σ : Store) :
    (loopJoin d body k).evalRTL modelL σ =
      Silmaril.Elgot.iter (loopStep d body) (RVal.unit, σ) >>= joinK d k := by
  show ((Silmaril.SSA.LambdaRTL.Loop.Region.br (LLab.cont d) Val.unit : LRegion).evalRTL modelL σ >>=
      fun e => if e.1 = LLab.cont d then Silmaril.Elgot.iter (loopStep d body) e.2 else pure e) >>=
        joinK d k = _
  rw [evalL_brUnit, okL_bind]
  simp

theorem toList_ofList' (vs : List WVal) : (RVal.ofList vs).toList = some vs := toList_ofList vs

/-! ## Simulation predicates -/

/-- λRTL results with loops. -/
abbrev Res3L := LM (LLab × RVal × Store)

/-- Label contexts: result slots at most the depth, label depths below the context length. -/
def CtxOkL (ks : List TgtL) (sd : Nat) : Prop := ∀ t ∈ ks, t.slot ≤ sd ∧ t.d < ks.length

theorem CtxOkL.mono {ks : List TgtL} {sd sd' : Nat} (h : CtxOkL ks sd) (hle : sd ≤ sd') :
    CtxOkL ks sd' := fun t ht => ⟨(h t ht).1.trans hle, (h t ht).2⟩

theorem CtxOkL.push {ks : List TgtL} {sd : Nat} (h : CtxOkL ks sd) {t : TgtL}
    (hs : t.slot = sd) (hd : t.d = ks.length) : CtxOkL (t :: ks) sd := by
  intro t' ht'
  simp only [List.mem_cons] at ht'
  rcases ht' with rfl | ht'
  · exact ⟨hs.le, by simp [hd]⟩
  · exact ⟨(h t' ht').1, by simp; have := (h t' ht').2; omega⟩

/-- An abrupt fragment outcome, seen in λRTL with loops (cf. `SimAbr`). -/
def SimAbrL (nloc : Nat) (res : Option IntType) (ks : List TgtL) (σ : Store) (x : Res3L)
    {α : Type} : Out α → Prop
  | .ok _ _ => False
  | .trap => x = errL .trap
  | .ret r => ∃ σ', x = okL (.ret, encR (blockRes res r), σ')
  | .brk l ls' r =>
      match ks[l]? with
      | some (.blk d slot ty) =>
          if ty.isSome && r.isNone then x = errL .stuck
          else ∃ σ', Agree nloc ls' σ' ∧ Below slot σ σ' ∧
            SlotRes slot (blockRes ty r) σ' ∧ x = okL (.blk d, .unit, σ')
      | some (.lp d slot) => ∃ σ', Agree nloc ls' σ' ∧ Below slot σ σ' ∧
          x = okL (.cont d, .unit, σ')
      | none =>
          if l = ks.length then ∃ σ', x = okL (.ret, encR (blockRes res r), σ')
          else x = errL .stuck

/-- An expression or body result, seen in λRTL with loops (cf. `SimR`). -/
def SimRL (nloc : Nat) (res : Option IntType) (ks : List TgtL) (sd : Nat) (k : LRegion)
    (σ : Store) (x : Res3L) : Option (Out (Option WVal)) → Prop
  | none => x = errL .stuck
  | some (.ok ls' r) => ∃ σ', Agree nloc ls' σ' ∧ Below sd σ σ' ∧ SlotRes sd r σ' ∧
      x = k.evalRTL modelL σ'
  | some (.brk l ls' r) => SimAbrL nloc res ks σ x (Out.brk (α := Option WVal) l ls' r)
  | some (.ret r) => SimAbrL nloc res ks σ x (Out.ret (α := Option WVal) r)
  | some .trap => SimAbrL nloc res ks σ x (Out.trap (α := Option WVal))

/-- An operand-list result, seen in λRTL with loops (cf. `SimA`). -/
def SimAL (nloc : Nat) (res : Option IntType) (ks : List TgtL) (sd : Nat) (k : LRegion)
    (σ : Store) (x : Res3L) : Option (Out (List WVal)) → Prop
  | none => x = errL .stuck
  | some (.ok ls' vs) => ∃ σ', Agree nloc ls' σ' ∧ Below sd σ σ' ∧ SlotsRes sd vs σ' ∧
      x = k.evalRTL modelL σ'
  | some (.brk l ls' r) => SimAbrL nloc res ks σ x (Out.brk (α := List WVal) l ls' r)
  | some (.ret r) => SimAbrL nloc res ks σ x (Out.ret (α := List WVal) r)
  | some .trap => SimAbrL nloc res ks σ x (Out.trap (α := List WVal))

theorem simAbrL_mono {nloc : Nat} {res : Option IntType} {ks : List TgtL} {sd : Nat}
    {σ σ₁ : Store} (hctx : CtxOkL ks sd) (hb : Below sd σ σ₁) {x : Res3L} {α : Type} :
    ∀ {o : Out α}, SimAbrL nloc res ks σ₁ x o → SimAbrL nloc res ks σ x o
  | .ok _ _, h => h
  | .trap, h => h
  | .ret _, h => h
  | .brk l ls' r, h => by
    simp only [SimAbrL] at h ⊢
    cases hk : ks[l]? with
    | none => simp only [hk] at h ⊢; exact h
    | some t =>
      have hslot := (hctx t (List.mem_of_getElem? hk)).1
      cases t with
      | blk d slot ty =>
        simp only [hk] at h ⊢
        by_cases hc : (ty.isSome && r.isNone) = true
        · rw [ite_eq_left hc] at h ⊢; exact h
        · rw [ite_eq_right hc] at h ⊢
          obtain ⟨σ', ha, hb', hs, hx⟩ := h
          exact ⟨σ', ha, (hb.mono hslot).trans hb', hs, hx⟩
      | lp d slot =>
        simp only [hk] at h ⊢
        obtain ⟨σ', ha, hb', hx⟩ := h
        exact ⟨σ', ha, (hb.mono hslot).trans hb', hx⟩

theorem simRL_mono {nloc : Nat} {res : Option IntType} {ks : List TgtL} {sd : Nat}
    {k : LRegion} {σ σ₁ : Store} (hctx : CtxOkL ks sd) (hb : Below sd σ σ₁) {x : Res3L} :
    ∀ {o : Option (Out (Option WVal))},
      SimRL nloc res ks sd k σ₁ x o → SimRL nloc res ks sd k σ x o
  | none, h => h
  | some (.ok _ _), h => by
    obtain ⟨σ', ha, hb', hs, hx⟩ := h
    exact ⟨σ', ha, hb.trans hb', hs, hx⟩
  | some (.brk _ _ _), h => by simp only [SimRL] at h ⊢; exact simAbrL_mono hctx hb h
  | some (.ret _), h => by simp only [SimRL] at h ⊢; exact simAbrL_mono hctx hb h
  | some .trap, h => by simp only [SimRL] at h ⊢; exact simAbrL_mono hctx hb h

end Silmaril.Proofs.Wasm.LambdaRTL
