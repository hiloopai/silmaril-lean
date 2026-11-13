module

public import Silmaril.Compiler.Core.Verified.RmwSound.Defs

/-! # Value-producing sequenced read-modify-write

A bound post-increment/decrement updates the slot and returns its previous value. The
write footprint is discharged by the enclosing bound before its caller continues.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Rmw

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open ConvInt (Pure Fun IsInt lookupFun lookup_one)
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf argState)
open Silmaril.Cerberus.Core.Interleave (LocalReaches LocalStep TaskRuns TasksRun interleave_runs
  requestAux_end NoRace taskFlag)
open StateExpr (Key Term values close)
open StateMem (Local Inv defsOf update ptr)
open StateStmt (Overflows)
open Locals (Slot stored)

variable {file : Program} {labels : Labels}

theorem boundRmw_inv {e : EE} {x : Sym} {op : IntOp} (h : boundRmw file e = some (x, op)) :
    ∃ (A2 A3 A4 : List Annot) (p : Sym) (T1 : BaseType)
      (A5 A6 A7 : List Annot) (L : Loc) (U : Unit) (A8 A9 A10 : List Annot) (p' v : Sym)
      (A11 A12 : List Annot) (v' : Sym) (A13 A14 : List Annot) (z : Sym) (T2 : BaseType)
      (A15 A16 : List Annot) (c : Sym) (A17 A18 A19 : List Annot) (q : PE) (A20 : List Annot)
      (rest : List (Pattern Sym × PE)),
      e = .mk A2 (.bound (.mk A3 (.wseq (.mk A4 (.base (some p, T1))) (.mk A5 (.pure (.mk A6 () (.sym x))))
          (.mk A7 (.action (.mk .pos (.mk L U (.seqRmw false
            (.mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int)))))))
            (.mk A10 () (.sym p')) v
            (upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest))))))))) ∧
      p'.key = p.key ∧ v'.key = v.key ∧ (op = .add ∨ op = .sub) ∧ Guard.convOf file z q = true ∧
      ∃ d, lookupFun file c = some d ∧ ConvInt.convInt file d = true := by
  unfold boundRmw at h
  split at h
  · split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hp, hv, rfl, hop⟩, hq⟩, hc⟩ := hc
      unfold convFun at hc
      split at hc
      · rename_i d hl
        exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, hp, hv, hop, hq, d, hl, hc⟩
      · cases hc
    · cases h
  · cases h

/-- The old value is returned only after the update and its bound have completed. -/
theorem boundRmw_runs {e : EE} {x : Sym} {op : IntOp} (h : boundRmw file e = some (x, op))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    {ps : List Local} {pts : Key → Option StateExpr.PtsTo}
    (inv : Inv env m ls ds ps pts) (hd : (ds x.key).isSome) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      (Term.bin op (.var x.key) (.lit 1)).Ok (values (defsOf ds)) ∧ ∃ m', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds x.key (some (close (defsOf ds) (.bin op (.var x.key) (.lit 1))))) ps pts ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value (IntExpr.spec (values (defsOf ds) x.key)), k, m'⟩ := by
  obtain ⟨A2, A3, A4, p, T1, A5, A6, A7, L, U, A8, A9, A10, p', v, A11, A12, v', A13, A14,
    z, T2, A15, A16, c, A17, A18, A19, q, A20, rest, rfl, hp', hv, hop, hq, d, hl, hc⟩ :=
    boundRmw_inv h
  obtain ⟨dx, hdx⟩ := Option.isSome_iff_exists.mp hd
  obtain ⟨okx, l, hlm, hk, slot⟩ := inv.defs x.key dx hdx
  let σ := values (defsOf ds)
  let n := dx.val 0
  have hσ : σ x.key = n := by simp [σ, n, values, defsOf, hdx]
  have hn : IsInt n := IntExpr.Term.int_of_ok dx okx
  let t : Term := .bin op (.var x.key) (.lit 1)
  let UPD := upd A11 A12 v' A13 A14 z T2 A15 A16 c A17 A18 A19 op q A20 rest
  let ACT : EE := .mk A7 (.action (.mk .pos (.mk L U (.seqRmw false
    (.mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int))))))) (.mk A10 () (.sym p')) v UPD))))
  let BODY : EE := .mk A3 (.wseq (.mk A4 (.base (some p, T1))) (.mk A5 (.pure (.mk A6 () (.sym x)))) ACT)
  let K := k
  let m₁ := ReturnConst.focusMemory A5 m
  let env₁ := extendEnv [(p, ptr l)] env
  have hx : env.lookup x = some (ptr l) := inv.lookup hlm hk.symm
  -- Up to the action: the sequence, the bound, the weak sequence and the read of `x`'s pointer.
  have pre : Reaches file labels ⟨.effectExpr (.mk A2 (.bound BODY)) env, k, m⟩
      ⟨.effectExpr ACT env₁, .bound :: K, m₁⟩ :=
    (ReturnLit.bound_reaches A2 BODY env K m).trans
      ((Locals.wseq_reaches A3 _ _ ACT env (.bound :: K) m).trans
        ((ReturnConst.effect_pure_reaches file labels A5 _ env _ m).trans
          (((SeqReach.pure_symbol A6 x env _ hx) _ _).trans
            ((ReturnConst.diagnostic_reaches file labels m.currentLocation (ptr l) _ m₁).trans
              (Locals.wbind_reaches A4 p T1 (ptr l) ACT env (.bound :: K) m₁)))))
  -- The action: its location, then its operands.
  let m₂ := ReturnConst.focusMemory A7 m₁
  let OP : Prim := .seqRMW false v UPD env₁
  let tyArg : PE := .mk A8 () (.val (.ctype (.mk A9 (.basic (.integer (.signed .int))))))
  let pArg : PE := .mk A10 () (.sym p')
  have hp'l : env₁.lookup p' = some (ptr l) := by
    rw [ReturnLit.lookup_key hp']; exact lookup_one rfl
  have req : requestAux file labels m₁ (.effectExpr ACT env₁) (.bound :: K) false =
      if (ReturnConst.focusMemory A7 m₁).currentLocation == m₁.currentLocation then
        .next (.pureExpr tyArg env₁) (.arguments OP [] [pArg] env₁ :: .bound :: K)
      else .next (.setLocation (ReturnConst.focusMemory A7 m₁).currentLocation (.pureExpr tyArg env₁))
        (.arguments OP [] [pArg] env₁ :: .bound :: K) := by
    simp only [ACT, requestAux, awaitsScheduling, arguments]
    rfl
  have hf : LocalReaches file labels false ⟨.effectExpr ACT env₁, .bound :: K, m₁⟩
      ⟨.pureExpr tyArg env₁, .arguments OP [] [pArg] env₁ :: .bound :: K, m₂⟩ := by
    obtain ⟨loc, hfocus⟩ := Locals.focusMemory_eq A7 m₁
    simp only [m₂]
    rw [hfocus] at req ⊢
    by_cases same : loc == m₁.currentLocation
    · have eq : loc = m₁.currentLocation := by simpa using same
      subst loc
      simpa using Relation.ReflTransGen.single (Interleave.LocalStep.next
        (by simpa using req) (LoadTask.plain_pureExpr tyArg env₁))
    · exact .head (.next (by simpa [same] using req) (LoadTask.plain_setLocation _ _))
        (.single (.update (Interleave.requestAux_setLocation file labels m₁ loc _ _ false)))
  have eval : Eval file (tagsOf file m₁) env₁ (.inr [tyArg, pArg])
      (.inr [.ctype (Mem.Concrete.intType A9), ptr l]) := .cons .val (.cons (.sym hp'l) .nil)
  have args := PureLocal.args_local file (tagsOf file m₁) (labels := labels) (wc := false) eval OP []
    (.bound :: K) m₂ (Locals.tagsOf_focus A7 m₁)
  simp only [argState, List.nil_append] at args
  have toApply := hf.trans args
  have slot₂ : Slot m₂ l.id l.addr n := Locals.slot_focus A7 (Locals.slot_focus A5 slot)
  have inv₂ : Inv env m₂ ls ds ps pts := (inv.focus A5).focus A7
  have tdef : StateMem.Defined ds (Term.bin op (.var x.key) (.lit 1)) = true := by
    simp [StateMem.Defined, Term.vars, hd]
  by_cases hr : IsInt (Guard.apply op n 1)
  · -- The update is in range: store it, lift the write, return `unit`.
    right
    let n' := Guard.apply op n 1
    have hupd : evalUpdate m₂.enumTypes 256 file UPD (env₁.insert v (.loaded (.specified (.integer n)))) =
        .ok (.loaded (.specified (.integer n'))) :=
      update_ok m₂.enumTypes hv hop hq hl hc hn hr env₁ 243
    let w : Val := .loaded (.specified (.integer n))
    let m₃ := stored {m₂ with lastUsed := some l.id} l.id l.addr n'
    have memStep : LocalStep file labels false ⟨.apply OP [.ctype (Mem.Concrete.intType A9), ptr l], .bound :: K, m₂⟩
        ⟨.rmwFinish w l.addr 4, .bound :: K, m₃⟩ :=
      .memory (requestAux_rmw A9 (.bound :: K) slot₂ hn hr v UPD env₁ hupd)
    let m₄ : Mem.Concrete.State := {m₃ with nextExcluded := m₃.nextExcluded + 1}
    let a : Access := ⟨some m₃.nextExcluded, [], true, l.addr, 4⟩
    let tasks : List (Nat × (Control × List Frame)) :=
      [(0, .rmwMarker l.addr 4, [.excluded m₃.nextExcluded]), (1, .value w, [])]
    let results : List (Nat × (Val × List Access)) := [(0, .unit, [a]), (1, w, [])]
    let K' := Frame.liftedResult :: .bound :: K
    have finStep : LocalStep file labels false ⟨.rmwFinish w l.addr 4, .bound :: K, m₃⟩
        ⟨.interleave [] tasks, K', m₄⟩ :=
      .update (requestAux_finish w l.addr K m₃)
    have run : TasksRun file labels false K' tasks m₄ results m₄ := by
      have r0 : TasksRun file labels false K' [(0, .rmwMarker l.addr 4, [.excluded m₃.nextExcluded])]
          m₄ [(0, .unit, [a])] m₄ :=
        .snoc (marker_runs l.addr m₃.nextExcluded m₄ _) .nil
      exact .snoc ⟨[], .refl, rfl⟩ r0
    have arena := interleave_runs file labels run (by simp [tasks]) (by
      intro t ht
      simp only [tasks, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> simp [activeCall]) []
    have norace : NoRace results := by
      intro x hx y hy ne aa haa bb hbb
      simp only [results, List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
    have sorted : results.Pairwise fun a b => a.1 ≤ b.1 := by simp [results]
    have endStep := Interleave.LocalStep.next (requestAux_end file labels m₄ results K' false
      norace sorted) (LoadTask.plain_value _)
    rw [List.append_nil] at arena
    have local₁ := toApply.trans (Relation.ReflTransGen.single memStep |>.tail finStep |>.trans
      (arena.tail endStep))
    have selected : Reaches file labels
        ⟨.value (.tuple [.unit, w]), .annotations [a] :: K', m₄⟩
        ⟨.value w, .annotations [a] :: .bound :: K, m₄⟩ :=
      next_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling, K'])
    have tail := selected.trans (Locals.annotations_bound_reaches [a] w K m₄)
    have middle := Interleave.reaches_of_local file labels local₁
    simp only [results, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at middle
    have hval : (close (defsOf ds) (Term.bin op (.var x.key) (.lit 1))).val 0 = n' := by
      rw [StateExpr.close_val]
      simp only [Term.val]
      rw [show values (defsOf ds) x.key = n from hσ]
    have tok : (Term.bin op (.var x.key) (.lit 1)).Ok σ := by
      refine ⟨?_, ?_, ?_⟩
      · change IsInt (σ x.key); rw [hσ]; exact hn
      · change IsInt 1; constructor <;> decide
      · change IsInt (Guard.apply op (σ x.key) 1); rw [hσ]; exact hr
    have okc := StateExpr.close_ok _ _ (inv.defs_ok tdef) tok
    have inv₃ := (inv₂.touched ⟨m₂.currentLocation, some l.id, rfl⟩).store hlm okc
    rw [hval, hk] at inv₃
    refine ⟨tok, m₄, ?_, inv₃.nextExcluded _, ?_⟩
    · simp [m₄, m₃, m₂, m₁, Locals.stored_stdout]
    · change Reaches file labels _ ⟨.value (IntExpr.spec (σ x.key)), K, m₄⟩
      rw [hσ]
      exact pre.trans (middle.trans tail)
  · -- The update leaves `int`: Cerberus's exceptional condition.
    left
    have hupd : evalUpdate m₂.enumTypes 256 file UPD (env₁.insert v (.loaded (.specified (.integer n)))) =
        .error IntExpr.overflow :=
      update_ub m₂.enumTypes hv hop hq hn hr env₁ 243
    have hreq : request file labels ⟨.apply OP [.ctype (Mem.Concrete.intType A9), ptr l], .bound :: K, m₂⟩ =
        .end_ IntExpr.overflow := by
      simp only [request]
      rw [requestAux_rmw_ub A9 (.bound :: K) slot₂ hn v UPD env₁ hupd]
    refine ⟨⟨.halt IntExpr.overflow, [], m₂⟩, pre.trans ((Interleave.reaches_of_local file labels toApply).trans
      (.single ⟨_, Step.respond (by intro o h; cases h) (hreq ▸ Respond.end_)⟩)), rfl⟩

/-- The expression computing the old value is in range whenever the update is. -/
theorem oldTerm_ok_val (x : Sym) {op : IntOp} (hop : op = .add ∨ op = .sub)
    {σ : Key → Int} (ok : (Term.bin op (.var x.key) (.lit 1)).Ok σ) :
    (oldTerm x op).Ok σ ∧ (oldTerm x op).val σ = σ x.key := by
  rcases hop with rfl | rfl
  · have hv : (oldTerm x .add).val σ = σ x.key := by simp [oldTerm, Term.val, Guard.apply]
    refine ⟨⟨ok, ok.2.1, ?_⟩, hv⟩
    change IsInt ((oldTerm x .add).val σ)
    rw [hv]
    exact ok.1
  · have hv : (oldTerm x .sub).val σ = σ x.key := by simp [oldTerm, Term.val, Guard.apply]
    refine ⟨⟨ok, ok.2.1, ?_⟩, hv⟩
    change IsInt ((oldTerm x .sub).val σ)
    rw [hv]
    exact ok.1

end Silmaril.Compile.Core.Verified.Rmw
