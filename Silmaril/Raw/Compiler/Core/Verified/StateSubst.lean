module

public import Silmaril.Compiler.Core.Verified.StateProcLocal.Defs

/-! # Instantiating symbolic State definitions

Substitution is used only by proofs. The compiler retains the original expression
and computes it at run time. Instantiating an input preserves every arithmetic
operation and its overflow obligation, including the selected-branch condition.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.StateSubst

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open StateExpr (Key close values)
open StateMem (defsOf Defined update Inv Local)

/-- Replace the one runtime input with a term, retaining all operations. -/
def subst (v : IntExpr.Term) : IntExpr.Term → IntExpr.Term
  | .lit c => .lit c
  | .var => v
  | .bin o a b => .bin o (subst v a) (subst v b)
  | .cmp r a b x y => .cmp r a b (subst v x) (subst v y)
  | .cond c a b => .cond (subst v c) (subst v a) (subst v b)
  | .bit o a b => .bit o (subst v a) (subst v b)
  | .divpos o d a => .divpos o d (subst v a)

/-- Substitution agrees with evaluation, without evaluating the source program. -/
theorem subst_val (v t : IntExpr.Term) (n : Int) :
    (subst v t).val n = t.val (v.val n) := by
  induction t <;> simp_all [subst, IntExpr.Term.val]

/-- Definedness retains intermediate overflow and branch selection. -/
theorem subst_ok (v t : IntExpr.Term) (n : Int) (hv : v.Ok n) :
    (subst v t).Ok n ↔ t.Ok (v.val n) := by
  induction t <;> simp_all [subst, IntExpr.Term.Ok, subst_val, IntExpr.Term.int_of_ok v hv]

/-- Apply input substitution to each initialized slot definition. -/
def defs (v : IntExpr.Term) (ds : Key → Option IntExpr.Term) : Key → Option IntExpr.Term :=
  fun q => (ds q).map (subst v)

theorem defsOf_defs (v : IntExpr.Term) (ds : Key → Option IntExpr.Term) (q : Key) :
    defsOf (defs v ds) q = subst v (defsOf ds q) := by
  cases h : ds q <;> simp [defsOf, defs, h, subst]

theorem defined_defs (v : IntExpr.Term) (ds : Key → Option IntExpr.Term) (t : StateExpr.Term) :
    Defined (defs v ds) t = Defined ds t := by
  simp [Defined, defs]

theorem close_subst (v : IntExpr.Term) (ds : Key → IntExpr.Term) (t : StateExpr.Term) :
    close (fun q => subst v (ds q)) t = subst v (close ds t) := by
  induction t <;> simp_all [close, subst]

theorem close_defs (v : IntExpr.Term) (ds : Key → Option IntExpr.Term) (t : StateExpr.Term) :
    close (defsOf (defs v ds)) t = subst v (close (defsOf ds) t) := by
  rw [show defsOf (defs v ds) = fun q => subst v (defsOf ds q) from funext (defsOf_defs v ds)]
  exact close_subst v _ t

theorem defs_update (v : IntExpr.Term) (ds : Key → Option IntExpr.Term) (q : Key)
    (t : Option IntExpr.Term) :
    defs v (update ds q t) = update (defs v ds) q (t.map (subst v)) := by
  funext k
  by_cases h : k = q <;> simp [defs, update, h]

theorem subst_choose (v c a b : IntExpr.Term) :
    subst v (StmtIf.choose c a b) = StmtIf.choose (subst v c) (subst v a) (subst v b) := rfl

/-- The recognizer is parametric in symbolic definitions: substitution changes
its result, but never changes which statements or guards it accepts. -/
theorem stmts_subst (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (ds : Key → Option IntExpr.Term) (sz : Key → Nat) (e : ReturnLit.Eff) (v : IntExpr.Term) :
    State.stmts file ret xs (defs v ds) sz e =
      (State.stmts file ret xs ds sz e).map (subst v) := by
  unfold State.stmts
  split
  next ann pann ty s rest =>
    rename_i sz _ _ _
    split
    next t hc => simp only [defined_defs, close_defs]; split <;> rfl
    next c a hc =>
      simp only [defined_defs]
      split
      · rw [stmts_subst file ret xs ds sz rest v]
        cases State.stmts file ret xs ds sz rest <;> simp [close_defs, subst_choose]
      · rfl
    next x t hc =>
      simp only [defined_defs]
      split
      · simp only [close_defs]
        simpa only [defs_update, Option.map_some] using
          stmts_subst file ret xs (update ds x.key (some (close (defsOf ds) t)))
            (fun q => if q = x.key then State.closeSize sz t else sz q) rest v
      · rfl
    next x t hc =>
      simp only [defined_defs]
      split
      · simp only [close_defs]
        simpa only [defs_update, Option.map_some] using
          stmts_subst file ret xs (update ds x.key (some (close (defsOf ds) t)))
            (fun q => if q = x.key then State.closeSize sz t else sz q) rest v
      · rfl
    next x hc =>
      split
      · simpa only [defs_update, Option.map_none] using
          stmts_subst file ret xs (update ds x.key none) sz rest v
      · rfl
    next => rfl
  next => rfl
termination_by sizeOf e

/-- The slot invariant for symbolic definitions at an actual input. -/
structure At (n : Int) (env : Env) (m : Mem.Concrete.State) (ls : List Local)
    (ds : Key → Option IntExpr.Term) : Prop where
  env : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (StateMem.ptr l)
  live : ∀ l ∈ ls, Mem.Concrete.LiveInt m l.id l.addr
  apart : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key →
    a.id ≠ b.id ∧ Slots.Apart a.addr 4 b.addr 4
  defs : ∀ q d, ds q = some d → d.Ok n ∧
    ∃ l ∈ ls, l.sym.key = q ∧ Locals.Slot m l.id l.addr (d.val n)

/-- Instantiate only in the proof, reusing the existing concrete State invariant. -/
theorem At.instantiate {n : Int} {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} (h : At n env m ls ds) (hn : ConvInt.IsInt n) :
    StateMem.Inv env m ls (StateSubst.defs (.lit n) ds) where
  env := h.env
  live := h.live
  apart := h.apart
  defs q d hd := by
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨ok, l, hl, hk, slot⟩ := h.defs q t ht
    exact ⟨(subst_ok (.lit n) t 0 hn).mpr ok, l, hl, hk, by simpa [subst_val, IntExpr.Term.val] using slot⟩

/-- Every existing successful State statement trace can be instantiated at a
runtime parameter value, including assignments and conditional returns. -/
theorem stmts_returns {file : Program} {labels L : Labels} {caller : List Frame}
    {ret : Sym} (hret : ReturnLit.ReturnLabel L ret) {xs : List Sym}
    (nodup : (xs.map (·.key)).Nodup) (ds : Key → Option IntExpr.Term) (sz : Key → Nat)
    (e : ReturnLit.Eff) {t : IntExpr.Term} (h : State.stmts file ret xs ds sz e = some t)
    (n : Int) (hn : ConvInt.IsInt n) (env : Env) (m : Mem.Concrete.State) (ls : List Local)
    (inv : At n env m ls ds) (hls : StateStmt.Keys ls xs) (k : List Frame)
    (hk : StateProc.Context (labels := labels) L caller k) :
    (t.Ok n ∧ ∃ m', m'.stdout = m.stdout ∧
      Silmaril.Cerberus.Core.Interleave.LocalReaches file labels false
        ⟨.effectExpr e env, k, m⟩ ⟨.value (IntExpr.spec (t.val n)), .procedureReturn L :: caller, m'⟩) ∨
    ArenaFail.Fails file labels false ⟨.effectExpr e env, k, m⟩ IntExpr.overflow := by
  have hs : State.stmts file ret xs (defs (.lit n) ds) sz e = some (subst (.lit n) t) := by
    rw [stmts_subst, h]; rfl
  have result := StateProcLocal.stmts_returns hret nodup _ sz e hs env m ls (inv.instantiate hn) hls k hk
  simpa only [StateProcLocal.Returns, subst_ok (.lit n) t 0 hn, subst_val, IntExpr.Term.val] using result

end Silmaril.Compile.Core.Verified.StateSubst
