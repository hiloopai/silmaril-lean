module

public import Silmaril.X86.Concurrency.Cir.Proc.Defs

/-!
# Process-level threads: the thread-local simulation

Each step of a lowered process-IR thread is matched by zero or one
step of the CIR thread it implements (`sim_top`), with the cases the process layer needs:
silent steps, memory labels (the join loop's control reads are separated out), and the
syscalls the lowering emits (`futex` wait/wake, `clone`, `exit`, `exit_group`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Proc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl (Heap TStep upd)
open Silmaril.X86.Concurrency.Cir.Proc

/-! ## Registers -/

theorem set_apply (rs : Regs) (r q : Reg) (v : Word) :
    rs.set r v q = if q = r then v else rs q := rfl

theorem ag_refl (rs : Regs) : Ag rs rs := fun _ _ => rfl

theorem ag_set {rs rs' : Regs} (h : Ag rs rs') (r : Reg) (v : Word) :
    Ag (rs.set r v) (rs'.set r v) := by
  intro q hq; simp only [set_apply]; split <;> [rfl; exact h q hq]

theorem ag_set_scratch {rs rs' : Regs} (h : Ag rs rs') (v : Word) : Ag (rs.set scratch v) rs' := by
  intro q hq; simp only [set_apply, ite_eq_right hq]; exact h q hq

theorem ag_setMany {rs rs' : Regs} (h : Ag rs rs') :
    ∀ (l : List Reg) (vs : List Nat), Ag (rs.setMany l vs) (rs'.setMany l vs)
  | [], _ => by simpa [Regs.setMany] using h
  | _ :: _, [] => by simpa [Regs.setMany] using h
  | r :: l, v :: vs => by simp only [Regs.setMany]; exact ag_setMany (ag_set h r _) l vs

theorem eval_ag {rs rs' : Regs} (h : Ag rs rs') : ∀ {e : Expr}, e.noR scratch = true →
    e.eval rs = e.eval rs'
  | .lit _, _ => rfl
  | .reg q, hn => by
    simp only [Expr.noR, bne_iff_ne, ne_eq] at hn; exact h q hn
  | .bin o a b, hn => by
    simp only [Expr.noR, Bool.and_eq_true] at hn
    simp only [Expr.eval, eval_ag h hn.1, eval_ag h hn.2]

theorem rmw_result_ag {rs rs' : Regs} (h : Ag rs rs') {op : RmwOp} (hn : op.noR scratch = true)
    (sz old : Nat) (arg : Word) : op.result rs sz old arg = op.result rs' sz old arg := by
  cases op <;> simp only [RmwOp.result]
  case cas e => rw [eval_ag h (by simpa [RmwOp.noR] using hn)]

theorem map_ag {rs rs' : Regs} (h : Ag rs rs') : ∀ {l : List Reg}, l.contains scratch = false →
    l.map (fun r => (rs r).toNat) = l.map (fun r => (rs' r).toNat)
  | [], _ => rfl
  | q :: l, hn => by
    simp only [List.contains_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hn
    simp only [List.map_cons, h q (Ne.symm hn.1), map_ag h hn.2]

/-- **CIR thread steps respect register agreement** (for statements that do not read the
scratch register). -/
theorem tstep_ag {s : Stmt} {rs : Regs} {l : Option Lab} {s2 : Stmt} {rs2 : Regs}
    (h : TStep s rs l s2 rs2) : ∀ {rs' : Regs}, s.noR scratch = true → Ag rs rs' →
    ∃ rs2', TStep s rs' l s2 rs2' ∧ Ag rs2 rs2' := by
  induction h with
  | assign =>
    intro rs' hn ha; simp only [Stmt.noR] at hn
    exact ⟨_, .assign, by rw [eval_ag ha hn]; exact ag_set ha _ _⟩
  | load hv =>
    intro rs' hn ha; simp only [Stmt.noR] at hn
    refine ⟨_, ?_, ag_set ha _ _⟩
    rw [eval_ag ha hn]; exact .load hv
  | store =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    refine ⟨_, ?_, ha⟩
    rw [eval_ag ha hn.1, eval_ag ha hn.2]; exact .store
  | rmw hv =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    refine ⟨_, ?_, ag_set ha _ _⟩
    rw [eval_ag ha hn.1.2, eval_ag ha hn.2, rmw_result_ag ha hn.1.1]; exact .rmw hv
  | fence => intro rs' _ ha; exact ⟨_, .fence, ha⟩
  | fwait hv hr =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    rw [eval_ag ha hn.1, eval_ag ha hn.2]
    exact ⟨_, .fwait hv hr, ag_set ha _ _⟩
  | fwake hq =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    refine ⟨_, ?_, ha⟩
    rw [eval_ag ha hn.1, eval_ag ha hn.2]; exact .fwake hq
  | spawn => intro rs' _ ha; exact ⟨_, .spawn, ha⟩
  | join => intro rs' _ ha; exact ⟨_, .join, ha⟩
  | blk hspec hi hr ho =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.not_eq_true'] at hn
    refine ⟨_, ?_, ag_setMany ha _ _⟩
    rw [map_ag ha hn] at hspec; exact .blk hspec hi hr ho
  | seq _ ih =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    obtain ⟨rs2', h2, ha2⟩ := ih hn.1 ha
    exact ⟨_, .seq h2, ha2⟩
  | seqSkip => intro rs' _ ha; exact ⟨_, .seqSkip, ha⟩
  | iteT hc =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    exact ⟨_, .iteT (by rw [← eval_ag ha hn.1.1]; exact hc), ha⟩
  | iteF hc =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    exact ⟨_, .iteF (by rw [← eval_ag ha hn.1.1]; exact hc), ha⟩
  | loopT hc =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    exact ⟨_, .loopT (by rw [← eval_ag ha hn.1]; exact hc), ha⟩
  | loopF hc =>
    intro rs' hn ha; simp only [Stmt.noR, Bool.and_eq_true] at hn
    exact ⟨_, .loopF (by rw [← eval_ag ha hn.1]; exact hc), ha⟩

/-! ## The simulation outcome -/

/-- What one process-IR step of a thread implementing `(s, rs')` (under relation `R`) is on
the CIR side. -/
def Out (code : Nat → PStmt) (L : Layout) (R : PStmt → Regs → Stmt → Regs → Prop)
    (act : UAct PSt) (s : Stmt) (rs' : Regs) : Prop :=
  match act with
  | .tau x => R x.1 x.2 s rs' ∨ ∃ s2 rs2, TStep s rs' none s2 rs2 ∧ R x.1 x.2 s2 rs2
  | .mem l x =>
    (∃ s2 rs2, TStep s rs' (some l) s2 rs2 ∧ R x.1 x.2 s2 rs2) ∨
      ∃ u v, l = .rd .acq .wb (ctlAddr u % 2 ^ 64) 4 v ∧
        (∃ s2 rs2, TStep s rs' (some (.join u)) s2 rs2) ∧ (v ≠ 0 → R x.1 x.2 s rs') ∧
        (v = 0 → ∃ s2 rs2, TStep s rs' (some (.join u)) s2 rs2 ∧ R x.1 x.2 s2 rs2)
  | .sys nr args k ch =>
    (nr = nrFutex ∧ ∃ a v, args = [a, BitVec.ofNat 64 128, v] ∧ ∀ seen, seen < 2 ^ 32 →
      ∃ s2 rs2, TStep s rs' (some (.fwait a.toNat (v.toNat % 2 ^ 32) seen 0)) s2 rs2 ∧
        R (k (if seen = v.toNat % 2 ^ 32 then 0 else errAgain)).1
          (k (if seen = v.toNat % 2 ^ 32 then 0 else errAgain)).2 s2 rs2) ∨
    (nr = nrFutex ∧ ∃ u v, args = [BitVec.ofNat 64 (ctlAddr u), BitVec.ofNat 64 128, v] ∧
      (∃ s2 rs2, TStep s rs' (some (.join u)) s2 rs2) ∧ ∀ w, R (k w).1 (k w).2 s rs') ∨
    (nr = nrFutex ∧ ∃ a n, args = [a, BitVec.ofNat 64 129, n] ∧
      ∃ s2 rs2, TStep s rs' (some (.fwake a.toNat n.toNat 0)) s2 rs2 ∧ ∀ w, R (k w).1 (k w).2 s2 rs2) ∨
    (nr = nrClone ∧ ∃ u, args = [BitVec.ofNat 64 cloneMusl, BitVec.ofNat 64 (L.stk u),
        BitVec.ofNat 64 (ctlAddr u), BitVec.ofNat 64 (ctlAddr u), BitVec.ofNat 64 (L.tls u)] ∧
      ch.1 = code u ∧
      ∃ s2 rs2, TStep s rs' (some (.spawn u)) s2 rs2 ∧ ∀ w, R (k w).1 (k w).2 s2 rs2)

/-- The top-level outcome: an `Out` for `Top`, or `exit`/`exit_group` from a finished
thread. -/
def OutT (code : Nat → PStmt) (L : Layout) (act : UAct PSt) (s : Stmt) (rs' : Regs) : Prop :=
  Out code L (Top L) act s rs' ∨
    ((∃ nr args k ch, act = .sys nr args k ch ∧ (nr = nrExit ∨ nr = nrExitGroup)) ∧ s = .skip)

/-- Transport an outcome along a context: `f` on process states, `F` on CIR statements. -/
theorem out_map {code : Nat → PStmt} {L : Layout} {R R' : PStmt → Regs → Stmt → Regs → Prop}
    (f : PStmt → PStmt) (F : Stmt → Stmt)
    (hF : ∀ {s rs l s2 rs2}, TStep s rs l s2 rs2 → TStep (F s) rs l (F s2) rs2)
    (hR : ∀ {p rs s rs'}, R p rs s rs' → R' (f p) rs (F s) rs')
    {act : UAct PSt} {s : Stmt} {rs' : Regs} (h : Out code L R act s rs') :
    Out code L R' (act.wrap (fun x => (f x.1, x.2))) (F s) rs' := by
  cases act with
  | tau x =>
    rcases h with h | ⟨s2, rs2, hs, hr⟩
    · exact Or.inl (hR h)
    · exact Or.inr ⟨_, _, hF hs, hR hr⟩
  | mem l x =>
    rcases h with ⟨s2, rs2, hs, hr⟩ | ⟨u, v, hl, ⟨s2, rs2, hj⟩, h1, h2⟩
    · exact Or.inl ⟨_, _, hF hs, hR hr⟩
    · refine Or.inr ⟨u, v, hl, ⟨_, _, hF hj⟩, fun hv => hR (h1 hv), fun hv => ?_⟩
      obtain ⟨s3, rs3, hs3, hr3⟩ := h2 hv
      exact ⟨_, _, hF hs3, hR hr3⟩
  | sys nr args k ch =>
    rcases h with ⟨hn, a, v, ha, h⟩ | ⟨hn, u, v, ha, ⟨s2, rs2, hj⟩, h⟩ |
        ⟨hn, a, n, ha, s2, rs2, hs, h⟩ | ⟨hn, u, ha, hc, s2, rs2, hs, h⟩
    · refine Or.inl ⟨hn, a, v, ha, fun seen hs => ?_⟩
      obtain ⟨s2, rs2, h1, h2⟩ := h seen hs
      exact ⟨_, _, hF h1, hR h2⟩
    · exact Or.inr (Or.inl ⟨hn, u, v, ha, ⟨_, _, hF hj⟩, fun w => hR (h w)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hn, a, n, ha, _, _, hF hs, fun w => hR (h w)⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hn, u, ha, hc, _, _, hF hs, fun w => hR (h w)⟩))

/-! ## Inversion helpers -/

theorem lower_skip {L : Layout} {s : Stmt} (h : lower L s = .skip) : s = .skip := by
  cases s <;> simp_all [lower, fwS, fkS, spawnS, joinS]

theorem corr_skip {L : Layout} {p : PStmt} {rs : Regs} {s : Stmt} {rs' : Regs}
    (h : Corr L p rs s rs') (hp : p = .skip) : s = .skip ∧ Ag rs rs' := by
  cases h with
  | low hs ha => exact ⟨lower_skip hp, ha⟩
  | seq => cases hp
  | jn hj => rcases hj with hj | ⟨_, hj⟩ <;> [skip; rcases hj with hj | hj | hj | hj | hj | hj] <;>
      simp_all [joinS, jW]
  | jnPost hj => rcases hj with ⟨_, hj | hj | hj | hj⟩ <;> simp_all [jW]
  | fw => cases hp
  | fw2 => cases hp

theorem truthy_nz (rs : Regs) (r : Reg) : truthy ((nz (.reg r)).eval rs) = decide (rs r ≠ 0) := by
  show truthy (if rs r = BitVec.ofNat 64 0 then 0 else 1) = _
  split
  · next h => simp [h, truthy]
  · next h =>
    have : rs r ≠ 0 := h
    simp only [truthy]; rw [decide_eq_true this]; decide

theorem ofNat_ne_zero {v : Nat} (hv : v < 2 ^ 32) (h0 : v ≠ 0) : (BitVec.ofNat 64 v) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp at this
  omega

theorem nrm_eval (rs : Regs) (d : Reg) (w : Word) :
    (nrm d).eval (rs.set d w) = if w = 0 then 0 else 11 := by
  show (BitVec.ofNat 64 11) &&&
    (BitVec.ofNat 64 0 - (if rs.set d w d = BitVec.ofNat 64 0 then 0 else 1)) = _
  have e : rs.set d w d = w := by simp [set_apply]
  rw [e]
  split
  · next h => have : w = 0 := h; simp only [this]; decide
  · next h => have : w ≠ 0 := h; simp only [this]; decide

theorem set_set (rs : Regs) (r : Reg) (v w : Word) : (rs.set r v).set r w = rs.set r w := by
  funext q; simp only [set_apply]; split <;> rfl

theorem errAgain_ne : errAgain ≠ 0 := by decide

/-! ## The join loop -/

section
variable {code : Nat → PStmt} {L : Layout} {tp : Word}

/-- The steps of the join loop before it has seen `0`. -/
theorem sim_jres {u : Nat} {p : PStmt} {rs rs' : Regs} (hj : JRes u p rs) (ha : Ag rs rs')
    {act : UAct PSt} (h : PTStep code tp p rs act) : Out code L (Corr L) act (.join u) rs' := by
  rcases hj with rfl | ⟨hr, rfl | rfl | rfl | rfl | rfl | rfl⟩
  · -- `r11 := 1`
    simp only [joinS, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', ⟨rs2, ⟨ht, rfl⟩ | ⟨l, ht, rfl⟩⟩, rfl⟩
    · cases h
    · cases ht
      refine Or.inl (.jn (Or.inr ⟨?_, Or.inl rfl⟩) (ag_set_scratch ha _))
      show rs.set scratch (Expr.eval rs (.lit 1)) scratch ≠ 0
      rw [set_apply, ite_eq_left rfl]; show BitVec.ofNat 64 1 ≠ 0; decide
    · cases ht
  · simp only [PTStep] at h
    rcases h with ⟨-, rfl⟩ | ⟨a', h, -⟩
    · exact Or.inl (.jn (Or.inr ⟨hr, Or.inr (Or.inl rfl)⟩) ha)
    · exact h.elim
  · simp only [jW, PTStep] at h; subst h
    rw [truthy_nz, decide_eq_true hr, ite_eq_left rfl]
    exact Or.inl (.jn (Or.inr ⟨hr, Or.inr (Or.inr (Or.inl rfl))⟩) ha)
  · -- the load of the control word
    simp only [jLd, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', h, rfl⟩
    · cases h
    rcases h with ⟨h, -⟩ | ⟨a'', ⟨rs2, ⟨ht, rfl⟩ | ⟨l, ht, rfl⟩⟩, rfl⟩
    · cases h
    · cases ht
    · cases ht with
      | load hv =>
        rename_i v
        refine Or.inr ⟨u, v, by simp [Expr.eval, BitVec.toNat_ofNat], ⟨_, _, .join⟩,
          fun hv0 => ?_, fun hv0 => ⟨_, _, .join, ?_⟩⟩
        · exact .jn (Or.inr ⟨by simp only [set_apply]; exact ofNat_ne_zero hv hv0,
            Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩) (ag_set_scratch ha _)
        · subst hv0
          exact .jnPost ⟨by simp only [set_apply]; rfl, Or.inl rfl⟩ (ag_set_scratch ha _)
  · simp only [PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', h, rfl⟩
    · cases h
    rcases h with ⟨-, rfl⟩ | ⟨a'', h, -⟩
    · exact Or.inl (.jn (Or.inr ⟨hr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩) ha)
    · exact h.elim
  · simp only [jIt, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', rfl, rfl⟩
    · cases h
    rw [truthy_nz, decide_eq_true hr, ite_eq_left rfl]
    exact Or.inl (.jn (Or.inr ⟨hr, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩) ha)
  · simp only [jFw, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', rfl, rfl⟩
    · cases h
    refine Or.inr (Or.inl ⟨rfl, u, rs scratch, by simp [Expr.eval], ⟨_, _, .join⟩, fun w => ?_⟩)
    exact .jn (Or.inr ⟨hr, Or.inl rfl⟩) ha

/-- The steps of the join loop after it has seen `0`. -/
theorem sim_jpost {u : Nat} {p : PStmt} {rs rs' : Regs} (hj : JPost u p rs) (ha : Ag rs rs')
    {act : UAct PSt} (h : PTStep code tp p rs act) : Out code L (Corr L) act .skip rs' := by
  obtain ⟨hr, rfl | rfl | rfl | rfl⟩ := hj
  · simp only [PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', h, rfl⟩
    · cases h
    rcases h with ⟨-, rfl⟩ | ⟨a'', h, -⟩
    · exact Or.inl (.jnPost ⟨hr, Or.inr (Or.inl rfl)⟩ ha)
    · exact h.elim
  · simp only [jIt, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', rfl, rfl⟩
    · cases h
    have : truthy ((nz (.reg scratch)).eval rs) = false := by rw [truthy_nz]; simp [hr]
    rw [this]
    exact Or.inl (.jnPost ⟨hr, Or.inr (Or.inr (Or.inl rfl))⟩ ha)
  · simp only [PTStep] at h
    rcases h with ⟨-, rfl⟩ | ⟨a', h, -⟩
    · exact Or.inl (.jnPost ⟨hr, Or.inr (Or.inr (Or.inr rfl))⟩ ha)
    · exact h.elim
  · simp only [jW, PTStep] at h; subst h
    have : truthy ((nz (.reg scratch)).eval rs) = false := by rw [truthy_nz]; simp [hr]
    rw [this]
    exact Or.inl (Corr.low (s := .skip) rfl ha)

/-! ## Lowered code -/

/-- An atomic CIR statement. -/
theorem sim_cir {s : Stmt} {rs rs' : Regs} (hn : s.noR scratch = true) (ha : Ag rs rs')
    {act : UAct PSt} (h : PTStep code tp (.cir s) rs act) : Out code L (Corr L) act s rs' := by
  simp only [PTStep] at h
  obtain ⟨rs2, ⟨ht, rfl⟩ | ⟨l, ht, rfl⟩⟩ := h
  · obtain ⟨rs2', ht', ha'⟩ := tstep_ag ht hn ha
    exact Or.inr ⟨_, _, ht', Corr.low (s := .skip) rfl ha'⟩
  · obtain ⟨rs2', ht', ha'⟩ := tstep_ag ht hn ha
    exact Or.inl ⟨_, _, ht', Corr.low (s := .skip) rfl ha'⟩

/-- Sequencing. -/
theorem sim_seq {p : PStmt} {rs : Regs} {s t : Stmt} {rs' : Regs} (hc : Corr L p rs s rs')
    (ih : ∀ {act}, PTStep code tp p rs act → Out code L (Corr L) act s rs')
    (ht : t.noR scratch = true) {act : UAct PSt} (h : PTStep code tp (.seq p (lower L t)) rs act) :
    Out code L (Corr L) act (.seq s t) rs' := by
  simp only [PTStep] at h
  rcases h with ⟨hp, rfl⟩ | ⟨a', h, rfl⟩
  · obtain ⟨rfl, ha⟩ := corr_skip hc hp
    exact Or.inr ⟨_, _, .seqSkip, .low ht ha⟩
  · exact out_map (fun p => .seq p (lower L t)) (fun s => .seq s t) (fun h => .seq h)
      (fun h => .seq h ht) (ih h)

/-- **Lowered code simulates its source.** -/
theorem sim_low (s : Stmt) : ∀ {rs rs' : Regs}, s.noR scratch = true → Ag rs rs' →
    ∀ {act : UAct PSt}, PTStep code tp (lower L s) rs act → Out code L (Corr L) act s rs' := by
  induction s with
  | skip => intro rs rs' _ _ act h; exact h.elim
  | assign => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | load => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | store => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | rmw => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | fence => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | «local» => intro rs rs' hn ha act h; exact sim_cir hn ha h
  | futexWait d a v =>
    intro rs rs' hn ha act h
    simp only [Stmt.noR, Bool.and_eq_true] at hn
    simp only [lower, fwS, PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', rfl, rfl⟩
    · cases h
    refine Or.inl ⟨rfl, a.eval rs, v.eval rs, by simp [Expr.eval], fun seen hs => ?_⟩
    rw [eval_ag ha hn.1, eval_ag ha hn.2]
    refine ⟨_, _, .fwait hs (by decide), .fw ?_⟩
    simp only [Regs.setO, nrm_eval, set_set]
    by_cases hq : seen = (v.eval rs').toNat % 2 ^ 32
    · simp only [hq, ite_true]; exact ag_set ha _ _
    · simp only [hq, ite_false, errAgain_ne]; exact ag_set ha _ _
  | futexWake a n =>
    intro rs rs' hn ha act h
    simp only [Stmt.noR, Bool.and_eq_true] at hn
    simp only [lower, fkS, PTStep] at h; subst h
    refine Or.inr (Or.inr (Or.inl ⟨rfl, a.eval rs, n.eval rs, by simp [Expr.eval], _, _, ?_,
      fun w => Corr.low (s := .skip) rfl ha⟩))
    rw [eval_ag ha hn.1, eval_ag ha hn.2]; exact .fwake (by decide)
  | spawn u =>
    intro rs rs' _ ha act h
    simp only [lower, spawnS, PTStep] at h; subst h
    exact Or.inr (Or.inr (Or.inr ⟨rfl, u, by simp [Expr.eval], rfl, _, _, .spawn,
      fun w => Corr.low (s := .skip) rfl ha⟩))
  | join u => intro rs rs' _ ha act h; exact sim_jres (Or.inl rfl) ha h
  | seq s t ihs _ =>
    intro rs rs' hn ha act h
    simp only [Stmt.noR, Bool.and_eq_true] at hn
    exact sim_seq (.low hn.1 ha) (ihs hn.1 ha) hn.2 h
  | ite c s t _ _ =>
    intro rs rs' hn ha act h
    simp only [Stmt.noR, Bool.and_eq_true] at hn
    simp only [lower, PTStep] at h; subst h
    by_cases hc : truthy (c.eval rs) = true
    · rw [ite_eq_left hc]
      exact Or.inr ⟨_, _, .iteT (by rw [← eval_ag ha hn.1.1]; exact hc), .low hn.1.2 ha⟩
    · rw [ite_eq_right hc]
      exact Or.inr ⟨_, _, .iteF (by rw [← eval_ag ha hn.1.1]; simpa using hc), .low hn.2 ha⟩
  | loop n c b _ =>
    intro rs rs' hn ha act h
    simp only [Stmt.noR, Bool.and_eq_true] at hn
    cases n with
    | zero =>
      simp only [lower, PTStep] at h
      obtain ⟨hc, rfl⟩ := h
      exact Or.inr ⟨_, _, .loopF (by rw [← eval_ag ha hn.1]; exact hc), Corr.low (s := .skip) rfl ha⟩
    | succ n =>
      simp only [lower, PTStep] at h; subst h
      by_cases hc : truthy (c.eval rs) = true
      · rw [ite_eq_left hc]
        refine Or.inr ⟨_, _, .loopT (by rw [← eval_ag ha hn.1]; exact hc), ?_⟩
        exact Corr.low (s := .seq b (.loop n c b)) (by simp [Stmt.noR, hn.1, hn.2]) ha
      · rw [ite_eq_right hc]
        exact Or.inr ⟨_, _, .loopF (by rw [← eval_ag ha hn.1]; simpa using hc),
          Corr.low (s := .skip) rfl ha⟩

/-- **The thread simulation** inside lowered code. -/
theorem sim_corr {p : PStmt} {rs : Regs} {s : Stmt} {rs' : Regs} (hc : Corr L p rs s rs') :
    ∀ {act : UAct PSt}, PTStep code tp p rs act → Out code L (Corr L) act s rs' := by
  induction hc with
  | low hs ha => exact sim_low _ hs ha
  | seq hc ht ih => exact sim_seq hc ih ht
  | jn hj ha => exact sim_jres hj ha
  | jnPost hj ha => exact sim_jpost hj ha
  | fw ha =>
    intro act h
    simp only [PTStep] at h
    rcases h with ⟨-, rfl⟩ | ⟨a', h, -⟩
    · exact Or.inl (.fw2 ha)
    · exact h.elim
  | fw2 ha =>
    intro act h
    simp only [PTStep] at h
    obtain ⟨rs2, ⟨ht, rfl⟩ | ⟨l, ht, rfl⟩⟩ := h
    · cases ht; exact Or.inl (Corr.low (s := .skip) rfl ha)
    · cases ht

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> simp [allRegs]

/-- **The top-level thread simulation**: lowered code with its exit tail and prologue. -/
theorem sim_top {p : PStmt} {rs : Regs} {s : Stmt} {rs' : Regs} (hc : Top L p rs s rs')
    {act : UAct PSt} (h : PTStep code tp p rs act) : OutT code L act s rs' := by
  cases hc with
  | tail hc he =>
    simp only [PTStep] at h
    rcases h with ⟨hp, rfl⟩ | ⟨a', h, rfl⟩
    · obtain ⟨rfl, -⟩ := corr_skip hc hp
      exact Or.inl (Or.inl (.fin he))
    · exact Or.inl (out_map (fun p => .seq p _) id (fun h => h) (fun h => .tail h he) (sim_corr hc h))
  | fin he =>
    rcases he with rfl | rfl <;> simp only [exitS, exitGroupS, PTStep] at h <;> subst h
    · exact Or.inr ⟨⟨_, _, _, _, rfl, Or.inl rfl⟩, rfl⟩
    · exact Or.inr ⟨⟨_, _, _, _, rfl, Or.inr rfl⟩, rfl⟩
  | pro hb hz =>
    rename_i lst
    simp only [PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', h, rfl⟩
    · cases h
    cases lst with
    | nil =>
      simp only [zeroAll, PTStep] at h
      rcases h with ⟨-, rfl⟩ | ⟨a'', h, -⟩
      · refine Or.inl (Or.inl (.tail (.low hb fun r _ => ?_) (Or.inl rfl)))
        exact hz r (by simp)
      · exact h.elim
    | cons r l =>
      simp only [zeroAll, PTStep] at h
      rcases h with ⟨h, -⟩ | ⟨a'', h, rfl⟩
      · cases h
      rcases h with ⟨h, -⟩ | ⟨a3, ⟨rs2, ⟨ht, rfl⟩ | ⟨lb, ht, rfl⟩⟩, rfl⟩
      · cases h
      · cases ht
        refine Or.inl (Or.inl (.proS hb fun q hq => ?_))
        simp only [set_apply]
        split
        · rfl
        · exact hz q (by simp_all)
      · cases ht
  | proS hb hz =>
    simp only [PTStep] at h
    rcases h with ⟨h, -⟩ | ⟨a', h, rfl⟩
    · cases h
    rcases h with ⟨h, -⟩ | ⟨a'', h, rfl⟩
    · cases h
    rcases h with ⟨-, rfl⟩ | ⟨a3, h, -⟩
    · exact Or.inl (Or.inl (.pro hb hz))
    · exact h.elim

/-- The child of a lowered `spawn u` implements thread `u` from its start, whatever its
registers. -/
theorem top_child (b : Stmt) (hb : b.noR scratch = true) (rs : Regs) :
    Top L (childCode L b) rs b Regs.zero :=
  .pro hb fun r hr => absurd (mem_allRegs r) hr

end

end Silmaril.Proofs.X86.Concurrency.Cir.Proc
