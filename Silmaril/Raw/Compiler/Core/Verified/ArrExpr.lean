module

public import Silmaril.Compiler.Core.Verified.ArrRead.Defs
public import Silmaril.Compiler.Core.Verified.ArrStmt.Defs
/-! Array expression translation by substitution of element definitions.
The generated integer expression is executed by the existing proved backend. -/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArrExpr

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.Interleave (LocalStep LocalReaches taskFlag)
open ReturnLit (Eff)
open LoadTask (Touched)
open IntExpr (spec overflow unseq_pair guard_local requestAux_tuple_bind)
open StateMem (Defined defsOf)

/-- Closed scalar expressions, initialized array reads, and guarded arithmetic. -/
def translate (file : File Codec.wireModel Unit Unit) (x : Sym) (N : Nat)
    (ds : ArrMem.Defs) (e : Eff) : Option IntExpr.Term :=
  match StateExpr.term file e with
  | some t => if Defined (fun _ => none) t then
      some (StateExpr.close (defsOf (fun _ => none)) t) else none
  | none => match ArrRead.readOf file e with
    | some (r, i) => if r.key = x.key ∧ 0 ≤ i ∧ i < N then ds (x.key, i.toNat) else none
    | none => match e with
      | .mk _ (.wseq (.mk _ (.ctor .tuple [.mk _ (.base (some a, _)), .mk _ (.base (some b, _))]))
          (.mk _ (.unseq [e₁, e₂])) (.mk _ (.pure g))) => do
          let op ← Guard.guard file a b g
          let t₁ ← translate file x N ds e₁
          let t₂ ← translate file x N ds e₂
          pure (.bin op t₁ t₂)
      | _ => none
termination_by sizeOf e

/-- A structural certificate, independent of the translator's implementation. -/
inductive Derivation (file : File Codec.wireModel Unit Unit) (x : Sym) (N : Nat)
    (ds : ArrMem.Defs) : Eff → IntExpr.Term → Prop where
  | closed {e t} (ht : StateExpr.term file e = some t) (hd : Defined (fun _ => none) t = true) :
      Derivation file x N ds e (StateExpr.close (defsOf (fun _ => none)) t)
  | read {e r t} {i : Nat} (hr : ArrRead.readOf file e = some (r, (i : Int)))
      (hx : r.key = x.key) (hi : i < N) (hd : ds (x.key, i) = some t) :
      Derivation file x N ds e t
  | bin {e₁ e₂ t₁ t₂ op an pp p1 p2 au ag a b ta tb g}
      (hg : Guard.guard file a b g = some op)
      (h₁ : Derivation file x N ds e₁ t₁) (h₂ : Derivation file x N ds e₂ t₂)
      (same : e₁ = e₂ → t₁ = t₂) :
      Derivation file x N ds
        (.mk an (.wseq (.mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))]))
          (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) (.bin op t₁ t₂)

theorem translate_spec {file x N ds e t} (h : translate file x N ds e = some t) :
    Derivation file x N ds e t := by
  unfold translate at h
  split at h
  · rename_i t' ht
    split at h
    · cases h; exact .closed ht ‹_›
    · cases h
  · split at h
    · rename_i r i hr
      split at h
      · rename_i hi
        have eq : (i.toNat : Int) = i := Int.toNat_of_nonneg hi.2.1
        exact .read (by rwa [eq]) hi.1 (by omega) h
      · cases h
    · split at h
      · rename_i an pp p1 a ta p2 b tb au e₁ e₂ ag g
        simp only [bind, pure, Option.bind_eq_some_iff] at h
        obtain ⟨op, hg, t₁, h₁, t₂, h₂, h⟩ := h
        cases h
        exact .bin hg (translate_spec h₁) (translate_spec h₂) (by
          intro eq; rw [← eq, h₁] at h₂; exact Option.some.inj h₂)
      · cases h
termination_by sizeOf e

theorem Derivation.noCall {file x N ds e t} (h : Derivation file x N ds e t) :
    hasCCall e = false := by
  induction h with
  | closed ht _ => exact StateExpr.term_calls _ ht
  | read hr _ _ _ => exact ArrRead.readOf_noCall hr
  | bin hg _ _ _ ih₁ ih₂ => simp [hasCCall, ih₁, ih₂]

variable {file : Program} {labels : Labels} {x : Sym} {N : Nat} {ds : ArrMem.Defs}

/-- The memory predicate for one array; the source allocation remains an aggregate. -/
def Holds (env : Env) (a : ArrMem.Array) (ds : ArrMem.Defs) (m : Mem.Concrete.State) : Prop :=
  ArrMem.Inv m [a] ds ∧ ArrMem.EnvOk env [a]

theorem Holds.touched {env a ds m m'} (h : Holds env a ds m) (t : Touched m m') :
    Holds env a ds m' := ⟨h.1.touched t, h.2⟩

theorem scalarEmpty (env : Env) (m : Mem.Concrete.State) :
    StateMem.Inv env m [] (fun _ => none) := by
  constructor <;> simp

theorem Derivation.runs {e t} (h : Derivation file x N ds e t) :
    ∀ {env a}, a.object.sym.key = x.key → a.length = N → t.Ok 0 →
      PtrDeref.Runs (file := file) (labels := labels) (Holds env a ds) env e (spec (t.val 0)) := by
  induction h with
  | closed ht hd =>
    intro env a key len ok
    refine ⟨StateExpr.term_calls _ ht, fun k m hm => ?_⟩
    have inv := scalarEmpty env m
    have okt := StateExpr.ok_of_close _ _ (inv.defs_ok hd) ok
    have run := StateExpr.term_runs (file := file) (labels := labels) _ ht okt k m (inv.locs hd)
    simpa only [StateExpr.close_val] using run
  | read hr hx hi hd =>
    intro env a key len ok
    refine ⟨ArrRead.readOf_noCall hr, fun k m hm => ?_⟩
    have run := ArrRead.read_runs (file := file) (labels := labels) hr hm.2
      (a := a) (by simp) (hx.trans key.symm) (by simpa [key] using hd) ok
      (Holds env a ds) (fun _ _ h t => h.touched t) (fun _ h => h.1)
      (hm.1.aligned a (by simp)) (by omega)
    exact run.2 k m hm
  | @bin e₁ e₂ t₁ t₂ op an pp p1 p2 au ag a b ta tb g hg h₁ h₂ same ih₁ ih₂ =>
    intro env array key len ok
    refine ⟨by simp [hasCCall, h₁.noCall, h₂.noCall], fun k m hm => ?_⟩
    obtain ⟨ok₁, ok₂, okr⟩ := ok
    let I := Holds env array ds
    have hI : ∀ m m', I m → Touched m m' → I m' := fun _ _ h t => h.touched t
    let PAT : Pattern Sym := .mk pp (.ctor .tuple [.mk p1 (.base (some a, ta)), .mk p2 (.base (some b, tb))])
    have s₁ : LocalReaches file labels false
        ⟨.effectExpr (.mk an (.wseq PAT (.mk au (.unseq [e₁, e₂])) (.mk ag (.pure g)))) env, k, m⟩
        ⟨.effectExpr (.mk au (.unseq [e₁, e₂])) env, .effectBind PAT (.mk ag (.pure g)) env :: k, m⟩ :=
      .single (.next (LoadTask.requestAux_wseq m an _ _ _ env k false) (LoadTask.plain_effectExpr _ _))
    obtain ⟨xs, m₁, rd, tch, s₂⟩ := unseq_pair (file := file) (labels := labels)
      (k := .effectBind PAT (.mk ag (.pure g)) env :: k) (annots := au) I hI
      (ih₁ key len ok₁).task (ih₂ key len ok₂).task
      (by intro eq; rw [same eq]) m hm
    have s₃ : LocalReaches file labels false
        ⟨.value (.tuple [spec (t₁.val 0), spec (t₂.val 0)]),
          .annotations xs :: .effectBind PAT (.mk ag (.pure g)) env :: k, m₁⟩
        ⟨.effectExpr (.mk ag (.pure g)) (Guard.operands a b (t₁.val 0) (t₂.val 0) env),
          .annotations xs :: k, m₁⟩ :=
      .single (.next (requestAux_tuple_bind m₁ xs pp p1 p2 a b ta tb _ _ _ env k)
        (LoadTask.plain_effectExpr _ _))
    obtain ⟨l', s₄⟩ := guard_local (file := file) (labels := labels) ag g
      (Guard.operands a b (t₁.val 0) (t₂.val 0) env) (.annotations xs :: k) m₁
    let m₂ : Mem.Concrete.State := {m₁ with currentLocation := l'}
    have s₅ := PureLocal.eval_local file (PureEval.tagsOf file m₂) (wc := false) (labels := labels)
      (Guard.guard_eval hg env (IntExpr.Term.int_of_ok t₁ ok₁) (IntExpr.Term.int_of_ok t₂ ok₂) okr)
      (.diagnosticLocation m₁.currentLocation :: .annotations xs :: k) m₂ rfl
    refine ⟨xs, m₂, [.annotations xs], .inr rfl, rd, tch.trans ⟨l', m₁.lastUsed, rfl⟩,
      s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.tail ?_))))⟩
    exact .next (Interleave.requestAux_value_diagnostic file labels _ _ _ _ false)
      (LoadTask.plain_value _)

end Silmaril.Compile.Core.Verified.ArrExpr
