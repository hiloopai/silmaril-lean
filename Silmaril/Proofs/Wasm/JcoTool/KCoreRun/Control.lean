module

public import Silmaril.Proofs.Wasm.JcoTool.KCoreRun.Straight

/-!
# Sequences, blocks, `if` and loops on Core 3.0, and every statement

`run_seq`, `run_block`, `run_ite`, `run_loop` (by induction on the loop fuel of `dloopN`: a run
that `bexec` finishes within its fuel is a Core run, however Core's loop is unbounded), and
**`stmt_run`**: every statement of the fragment has `SRun`, by induction on it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.JcoTool.KCoreRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.JcoTool.KCoreRun
open Silmaril.Wasm.JcoTool.KCore (E S BI Out M32 upd mcopy)
open Silmaril.Wasm.JcoTool.KDrop (DSt dexec)
open Silmaril.Wasm.JcoTool.KCoreEmit (ix eCode sCode ma0)
open Silmaril.Wasm.FX.Asyncify.Tool (W stackA)

variable {H : Type} {Pf : Profile} {hb : BI → H} {ma nl : Nat}

theorem run_seq {f : Nat} {a b : S} (iha : SRun Pf hb ma nl a f) (ihb : SRun Pf hb ma nl b f) :
    SRun Pf hb ma nl (.seq a b) f := by
  intro s o s' cs F hx h
  obtain ⟨o₁, s₁, ha, hcase⟩ := bexec_seq hx
  obtain ⟨hk₁, hv₁, ra⟩ := iha ha h
  have e₀ (rest : List Admin) : (sCode (.seq a b)).map Admin.plain ++ rest =
      (sCode a).map Admin.plain ++ ((sCode b).map Admin.plain ++ rest) := by
    simp [sCode]
  rcases hcase with ⟨rfl, hb'⟩ | ⟨hn, ho, hs⟩
  · show SRes Pf hb ma nl cs F (.seq a b) s o s'
    refine ⟨fun k hk => (ihb hb' (ra []).choose_spec.choose_spec.choose_spec.1).1 k hk,
      fun v hv => (ihb hb' (ra []).choose_spec.choose_spec.choose_spec.1).2.1 v hv, fun rest => ?_⟩
    obtain ⟨cs₁, F₁, j₁, hR₁, hF₁, hf₁, hj₁, r₁⟩ := ra ((sCode b).map Admin.plain ++ rest)
    obtain ⟨-, -, rb⟩ := ihb hb' hR₁
    obtain ⟨cs₂, F₂, j₂, hR₂, hF₂, hf₂, hj₂, r₂⟩ := rb rest
    have r₁' : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode a).map Admin.plain ++
        ((sCode b).map Admin.plain ++ rest)⟩)
        ((s₁.st, s₁.rp), ⟨cs₁, F₁, (sCode b).map Admin.plain ++ rest⟩) := by
      simpa [hj₁ rfl, outCode] using r₁
    exact ⟨cs₂, F₂, j₂, hR₂, hF₂.trans hF₁, hf₂.trans hf₁, hj₂, (e₀ rest) ▸ r₁'.trans r₂⟩
  · rw [ho, hs]
    refine ⟨hk₁, hv₁, fun rest => ?_⟩
    obtain ⟨cs₁, F₁, j₁, hR₁, hF₁, hf₁, -, r₁⟩ := ra ((sCode b).map Admin.plain ++ rest)
    refine ⟨cs₁, F₁, j₁ ++ (sCode b).map Admin.plain, hR₁, hF₁, hf₁, fun h' => absurd h' hn, ?_⟩
    have e₁ : outCode o₁ ++ j₁ ++ ((sCode b).map Admin.plain ++ rest) =
        outCode o₁ ++ (j₁ ++ (sCode b).map Admin.plain) ++ rest := by simp
    exact (e₀ rest) ▸ e₁ ▸ r₁

/-! ## Labels -/

theorem labOut_br {o : Out} {k : Nat} (h : labOut o = .br k) : o = .br (k + 1) := by
  rcases o with _ | (_ | j) | v <;> simp_all [labOut]

theorem labOut_ret {o : Out} {v : Nat} (h : labOut o = .ret v) : o = .ret v := by
  rcases o with _ | (_ | j) | u <;> simp_all [labOut]


/-- A statement whose code enters a label around the body `S'`, then runs it. -/
theorem sres_label {cs : Store H} {F : Frame} {T T' : S} {s s' : DSt} {o₁ : Out}
    (hr : SRes Pf hb ma nl cs F T' s o₁ s') (cont : List Instr) (h0 : o₁ = .br 0 → cont = [])
    (pre : ∀ rest : List Admin, HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, (sCode T).map Admin.plain ++ rest⟩)
      ((s.st, s.rp), ⟨cs, F, .label 0 cont ((sCode T').map Admin.plain) :: rest⟩)) :
    SRes Pf hb ma nl cs F T s (labOut o₁) s' := by
  obtain ⟨hk, hv, hrun⟩ := hr
  refine ⟨fun k h' => ?_, fun v h' => hv v (labOut_ret h'), fun rest => ?_⟩
  · have hk1 : k + 1 < M32 := hk (k + 1) (labOut_br h')
    omega
  · obtain ⟨cs', F', j, hR, hF, hfs, hj, r⟩ := hrun []
    have r' : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, .label 0 cont ((sCode T').map Admin.plain) :: rest⟩)
        ((s'.st, s'.rp), ⟨cs', F', .label 0 cont (outCode o₁ ++ j) :: rest⟩) := by
      simpa using hsteps_app rest (hsteps_label 0 cont r)
    have r'' : HSteps Pf hb ma ((s'.st, s'.rp), ⟨cs', F', .label 0 cont (outCode o₁ ++ j) :: rest⟩)
        ((s'.st, s'.rp), ⟨cs', F', outCode (labOut o₁) ++ [] ++ rest⟩) := by
      simpa using lab_exit cont h0 hk j hj rest
    exact ⟨cs', F', [], hR, hF, hfs, fun _ => rfl, (pre rest).trans (r'.trans r'')⟩

theorem block_step {q : HQ} {cs : Store H} {F : Frame} (body : List Instr) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨cs, F, Admin.plain (.block .empty body) :: rest⟩)
      (q, ⟨cs, F, .label 0 [] (body.map Admin.plain) :: rest⟩) :=
  step_app (Step.block (bt := .empty) (body := body) (vs := []) (t₁ := []) (t₂ := []) rfl rfl) rest

theorem run_block {f : Nat} {b : S} (ih : SRun Pf hb ma nl b f) : SRun Pf hb ma nl (.block b) f := by
  intro s o s' cs F hx h
  obtain ⟨o₁, hb', rfl⟩ := bexec_block hx
  exact sres_label (ih hb' h) [] (fun _ => rfl) fun rest => block_step (sCode b) rest

theorem run_ite {f : Nat} {c : E} {t e : S} (iht : SRun Pf hb ma nl t f) (ihe : SRun Pf hb ma nl e f) :
    SRun Pf hb ma nl (.ite c t e) f := by
  intro s o s' cs F hx h
  obtain ⟨v, o₁, hv, hr, rfl⟩ := bexec_ite hx
  obtain ⟨hvl, re⟩ := expr_run (Pf := Pf) (q := (s.st, s.rp)) h c hv
  have e₀ (rest : List Admin) := split2 (eCode c) [Instr.if_ .empty (sCode t) (sCode e)] rest
  by_cases h0 : v ≠ 0
  · show SRes Pf hb ma nl cs F (.ite c t e) s (labOut o₁) s'
    have hr' : bexec nl t f s = some (o₁, s') := by rw [ite_t h0] at hr; exact hr
    refine sres_label (iht hr' h) [] (fun _ => rfl) fun rest => ?_
    have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++
        .plain (.if_ .empty (sCode t) (sCode e)) :: rest⟩)
        ((s.st, s.rp), ⟨cs, F, Admin.plain (.block .empty (sCode t)) :: rest⟩) :=
      step_app (Step.ifTrue (s := cs) (f := F) (bt := .empty) (b₂ := sCode e) (w_ne_zero hvl h0)) rest
    exact (e₀ rest) ▸ (re [] _).trans (r₂.trans (block_step _ rest))
  · show SRes Pf hb ma nl cs F (.ite c t e) s (labOut o₁) s'
    have hr' : bexec nl e f s = some (o₁, s') := by rw [ite_f h0] at hr; exact hr
    have hv0 : v = 0 := Classical.not_not.mp h0
    refine sres_label (ihe hr' h) [] (fun _ => rfl) fun rest => ?_
    have r₂ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, stackA [w v] ++
        .plain (.if_ .empty (sCode t) (sCode e)) :: rest⟩)
        ((s.st, s.rp), ⟨cs, F, Admin.plain (.block .empty (sCode e)) :: rest⟩) := by
      rw [hv0]
      exact step_app (Step.ifFalse (s := cs) (f := F) (bt := .empty) (b₁ := sCode t)) rest
    exact (e₀ rest) ▸ (re [] _).trans (r₂.trans (block_step _ rest))

/-! ## Loops -/

theorem dloopN_succ {body : DSt → Option (Out × DSt)} {n : Nat} {s s' : DSt} {o : Out}
    (h : dexec.dloopN body (n + 1) s = some (o, s')) :
    ∃ o₁ s₁, body s = some (o₁, s₁) ∧
      ((o₁ = .br 0 ∧ dexec.dloopN body n s₁ = some (o, s')) ∨
        (o₁ ≠ .br 0 ∧ o = labOut o₁ ∧ s' = s₁)) := by
  cases hb : body s with
  | none => simp [dexec.dloopN, hb] at h
  | some r =>
    obtain ⟨o₁, s₁⟩ := r
    refine ⟨o₁, s₁, rfl, ?_⟩
    rcases o₁ with _ | (_ | k) | v
    · have h' : some (Out.norm, s₁) = some (o, s') := by simpa [dexec.dloopN, hb] using h
      exact .inr ⟨by simp, (Prod.mk.inj (Option.some.inj h')).1.symm, (Prod.mk.inj (Option.some.inj h')).2.symm⟩
    · exact .inl ⟨rfl, by simpa [dexec.dloopN, hb] using h⟩
    · have h' : some (Out.br k, s₁) = some (o, s') := by simpa [dexec.dloopN, hb] using h
      exact .inr ⟨by simp, (Prod.mk.inj (Option.some.inj h')).1.symm, (Prod.mk.inj (Option.some.inj h')).2.symm⟩
    · have h' : some (Out.ret v, s₁) = some (o, s') := by simpa [dexec.dloopN, hb] using h
      exact .inr ⟨by simp, (Prod.mk.inj (Option.some.inj h')).1.symm, (Prod.mk.inj (Option.some.inj h')).2.symm⟩

theorem loop_step {q : HQ} {cs : Store H} {F : Frame} (body : List Instr) (rest : List Admin) :
    HSteps Pf hb ma (q, ⟨cs, F, Admin.plain (.loop .empty body) :: rest⟩)
      (q, ⟨cs, F, .label 0 [.loop .empty body] (body.map Admin.plain) :: rest⟩) :=
  step_app (Step.loop (bt := .empty) (body := body) (vs := []) (t₁ := []) (t₂ := []) rfl rfl) rest

/-- The loop, by induction on the iterations `dloopN` allows. -/
theorem loop_aux {f : Nat} {b : S} (ih : SRun Pf hb ma nl b f) :
    ∀ (n : Nat) {s s' : DSt} {o : Out} {cs : Store H} {F : Frame},
      dexec.dloopN (bexec nl b f) n s = some (o, s') → Rel hb nl ma cs F s →
      SRes Pf hb ma nl cs F (.loop b) s o s'
  | 0, s, s', o, cs, F, hx, _ => by simp [dexec.dloopN] at hx
  | n + 1, s, s', o, cs, F, hx, h => by
    obtain ⟨o₁, s₁, hb', hc⟩ := dloopN_succ hx
    rcases hc with ⟨rfl, hn⟩ | ⟨hne, ho, hs⟩
    · obtain ⟨-, -, hrun⟩ := ih hb' h
      obtain ⟨cs₁, F₁, j, hR₁, hF₁, hf₁, -, r⟩ := hrun []
      obtain ⟨hk', hv', hrun'⟩ := loop_aux ih n hn hR₁
      refine ⟨hk', hv', fun rest => ?_⟩
      obtain ⟨cs₂, F₂, j₂, hR₂, hF₂, hf₂, hj₂, r₂⟩ := hrun' rest
      have r₁ : HSteps Pf hb ma ((s.st, s.rp), ⟨cs, F, .label 0 [.loop .empty (sCode b)]
          ((sCode b).map Admin.plain) :: rest⟩)
          ((s₁.st, s₁.rp), ⟨cs₁, F₁, .label 0 [.loop .empty (sCode b)] (outCode (.br 0) ++ j) :: rest⟩) := by
        simpa using hsteps_app rest (hsteps_label 0 [.loop .empty (sCode b)] r)
      have back : HSteps Pf hb ma ((s₁.st, s₁.rp), ⟨cs₁, F₁, .label 0 [.loop .empty (sCode b)]
          (outCode (.br 0) ++ j) :: rest⟩)
          ((s₁.st, s₁.rp), ⟨cs₁, F₁, (sCode (.loop b)).map Admin.plain ++ rest⟩) :=
        step_app (Step.brLabelZero (n := 0) (cont := [.loop .empty (sCode b)]) (vs' := []) (vs := [])
          (l := ix 0) (rest := j) rfl rfl) rest
      exact ⟨cs₂, F₂, j₂, hR₂, hF₂.trans hF₁, hf₂.trans hf₁, hj₂, (loop_step _ rest).trans (r₁.trans (back.trans r₂))⟩
    · rw [ho, hs]
      exact sres_label (ih hb' h) [.loop .empty (sCode b)] (fun h' => absurd h' hne)
        fun rest => loop_step (sCode b) rest

theorem run_loop {f : Nat} {b : S} (ih : SRun Pf hb ma nl b f) : SRun Pf hb ma nl (.loop b) f := by
  intro s o s' cs F hx h
  exact loop_aux ih f (by simpa only [bexec] using hx) h

/-! ## Every statement -/

theorem bexec_nop {f : Nat} {s s' : DSt} {o : Out} (h : bexec nl .nop f s = some (o, s')) :
    o = .norm ∧ s = s' := by
  simp only [bexec, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2⟩

/-- **Every checked run of a statement is a Core 3.0 run** (with the built-ins as host calls). -/
theorem stmt_run : ∀ (S : S) (f : Nat), SRun Pf hb ma nl S f
  | .nop, _ => fun hx h => by
    obtain ⟨rfl, rfl⟩ := bexec_nop hx
    exact run_nop h
  | .unreachable, _ => fun hx _ => by simp [bexec] at hx
  | .lset _ _, _ => fun hx h => run_lset h hx
  | .gset _ _, _ => fun hx h => run_gset h hx
  | .st8 _ _, _ => fun hx h => run_st8 h hx
  | .mcopy _ _ _, _ => fun hx h => run_mcopy h hx
  | .seq a b, f => run_seq (stmt_run a f) (stmt_run b f)
  | .ite _ t e, f => run_ite (stmt_run t f) (stmt_run e f)
  | .block b, f => run_block (stmt_run b f)
  | .loop b, f => run_loop (stmt_run b f)
  | .br _, _ => fun hx h => run_br h hx
  | .brIf _ _, _ => fun hx h => run_brIf h hx
  | .ret _, _ => fun hx h => run_ret h hx
  | .call _ _ _, _ => fun hx h => run_call h hx

end Silmaril.Proofs.Wasm.JcoTool.KCoreRun
