module

public import Silmaril.X86.Concurrency.Cir.Defs
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms

/-!
# CIR: model monotonicity and the sequential semantics

PROVED (standard axioms only):

* `MLe.refl`, `MLe.trans`, `sc_le_tso`, `tso_le_xl`, `sc_le_xl`: `⊑` is a preorder and
  SC ⊑ TSO ⊑ XL (from `Exec.tso_of_sc` and `Exec.xl_of_tso`);
* `behavIn_mono`, `behav_mono`: behaviours are monotone in the model;
* `safe_anti`, `safe_tso_of_xl`, `safe_sc_of_xl`: a safety property proved under a weaker
  model holds under every stronger one, so XL results transfer to TSO and SC;
* `forbidden_of_xl`, `allowed_of_sc`: the same for litmus verdicts;
* `behavIn_behav`: behaviours over one domain are behaviours;
* `seqRun_threadRun`: a sequential run is a thread run;
* `not_cirDomain_without_blocksClosed`, `not_cirSeqSc_without_posSizes`: the two Task
  statements are false without their `BlocksClosed` and `posSizes` hypotheses.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir

open Silmaril.X86.MemoryModel.Litmus
  (Final Loc Test Verdict allowed_mono forbidden_anti axReach_mono initByte)
open Silmaril.X86.MemoryModel.Axiomatic (Exec)

theorem MLe.refl (M : Exec → Prop) : M ⊑ M := fun _ h => h

theorem MLe.trans {M M' M'' : Exec → Prop} (h : M ⊑ M') (h' : M' ⊑ M'') : M ⊑ M'' :=
  fun x hx => h' x (h x hx)

/-- SC ⊑ TSO. -/
theorem sc_le_tso : Exec.Sc ⊑ Exec.Tso := fun x hx => x.tso_of_sc hx

/-- TSO ⊑ XL. -/
theorem tso_le_xl : Exec.Tso ⊑ Exec.Xl := fun x hx => x.xl_of_tso hx

/-- SC ⊑ XL. -/
theorem sc_le_xl : Exec.Sc ⊑ Exec.Xl := sc_le_tso.trans tso_le_xl

/-- **Behaviours over a domain are monotone in the model.** -/
theorem behavIn_mono {P : Prog} {dom : List Nat} {M M' : Exec → Prop} (h : M ⊑ M') {f : Final}
    (hf : BehavIn P dom M f) : BehavIn P dom M' f :=
  axReach_mono h hf

/-- **Behaviours are monotone in the model.** -/
theorem behav_mono {P : Prog} {M M' : Exec → Prop} (h : M ⊑ M') {f : Final} (hf : Behav P M f) :
    Behav P M' f :=
  let ⟨dom, hd⟩ := hf; ⟨dom, behavIn_mono h hd⟩

theorem behavIn_behav {P : Prog} {dom : List Nat} {M : Exec → Prop} {f : Final}
    (h : BehavIn P dom M f) : Behav P M f := ⟨dom, h⟩

/-- **Safety is anti-monotone in the model**: proved for a weaker model, it holds for a
stronger one. -/
theorem safe_anti {P : Prog} {M M' : Exec → Prop} {Q : Final → Prop} (h : M ⊑ M')
    (hs : Safe P M' Q) : Safe P M Q :=
  fun f hf => hs f (behav_mono h hf)

/-- An XL safety result holds under TSO. -/
theorem safe_tso_of_xl {P : Prog} {Q : Final → Prop} (h : Safe P Exec.Xl Q) : Safe P Exec.Tso Q :=
  safe_anti tso_le_xl h

/-- An XL safety result holds under SC. -/
theorem safe_sc_of_xl {P : Prog} {Q : Final → Prop} (h : Safe P Exec.Xl Q) : Safe P Exec.Sc Q :=
  safe_anti sc_le_xl h

/-- An XL-forbidden witness is TSO- and SC-forbidden, over any domain. -/
theorem forbidden_of_xl {t : Test} {P : Prog} {dom : List Nat}
    (h : Verdict.forbidden.Holds t (BehavIn P dom Exec.Xl)) :
    Verdict.forbidden.Holds t (BehavIn P dom Exec.Tso) ∧
      Verdict.forbidden.Holds t (BehavIn P dom Exec.Sc) :=
  ⟨forbidden_anti (fun _ => behavIn_mono tso_le_xl) h,
    forbidden_anti (fun _ => behavIn_mono sc_le_xl) h⟩

/-- An SC-allowed witness is TSO- and XL-allowed. -/
theorem allowed_of_sc {t : Test} {P : Prog} {dom : List Nat}
    (h : Verdict.allowed.Holds t (BehavIn P dom Exec.Sc)) :
    Verdict.allowed.Holds t (BehavIn P dom Exec.Tso) ∧
      Verdict.allowed.Holds t (BehavIn P dom Exec.Xl) :=
  ⟨allowed_mono (fun _ => behavIn_mono sc_le_tso) h,
    allowed_mono (fun _ => behavIn_mono sc_le_xl) h⟩

/-- A sequential run is a thread run. -/
theorem seqRun_threadRun {s : Stmt} {rs rs' : Regs} {m m' : Mem} {tr : List Lab}
    (h : SeqRun s rs m tr rs' m') : ThreadRun s rs tr rs' := h.1

/-- A program without local blocks has closed blocks over every domain. -/
theorem blocksClosed_of_noBlocks {P : Prog} (h : P.threads.all (·.body.blocks.isEmpty) = true)
    (dom : List Nat) : P.BlocksClosed dom := by
  intro th hth b hb
  have := List.all_eq_true.mp h th hth
  rw [List.isEmpty_iff] at this
  rw [this] at hb
  cases hb

/-! ## The Task hypotheses are needed

`Task.cirDomain` and `Task.cirSeqSc` were first stated without `Prog.BlocksClosed` and
`Stmt.posSizes`; both statements were false. The counterexamples below are kept so that the
hypotheses cannot be dropped silently. -/

/-- A local block whose contract forces `rax = 5`. -/
def Ex.five : Block where
  name := "five"
  ins := []
  outs := []
  rin := []
  rout := [.rax]
  spec := fun _ o => o = [5]
  dec := fun _ _ => inferInstance

/-- One thread running `five`. -/
def Ex.p5 : Prog := ⟨[], [⟨.local Ex.five, false⟩]⟩

/-- Its run over `[5]`. -/
def Ex.tr5 : Silmaril.X86.MemoryModel.Litmus.XTrace :=
  Thread.xtrace ⟨.local Ex.five, false⟩ 0
    ([.blk "five" [] [] [5]], Regs.zero.setMany [.rax] [5])

/-- **Domain closure fails without `BlocksClosed`**: `p5` is uniform and `[0]` is closed for it
(it has no run over `[0]`, so it writes nothing), yet it has an SC behaviour over `[5]` and none
over `[0]`. -/
theorem not_cirDomain_without_blocksClosed :
    ¬ ∀ (P : Prog) (dom : List Nat), P.uniformB = true → P.closedB dom = true →
      ∀ (M : Silmaril.X86.MemoryModel.Litmus.Model) (f : Final), Behav P M.Holds f →
        BehavIn P dom M.Holds f := by
  intro h
  have hU : Ex.p5.uniformB = true := by decide +kernel
  have hC : Ex.p5.closedB [0] = true := by decide +kernel
  have h5 : Ex.p5.traces [5] = [[Ex.tr5]] := rfl
  have h0 : Ex.p5.traces [0] = [[]] := rfl
  have hb : BehavIn Ex.p5 [5] Exec.Sc
      (Silmaril.X86.MemoryModel.Litmus.finalAx Ex.p5.memTest [Ex.tr5] { evs := [] }) := by
    refine ⟨[Ex.tr5], by rw [h5]; exact .cons (List.mem_singleton.mpr rfl) .nil, { evs := [] },
      rfl, rfl, by decide +kernel, fun r hr => absurd hr (Nat.not_lt_zero _), by decide +kernel,
      rfl⟩
  obtain ⟨trs, hf, -⟩ := h Ex.p5 [0] hU hC .sc _ ⟨[5], hb⟩
  rw [h0] at hf
  cases hf with
  | cons ha _ => simp at ha

/-- A size-`0` store at address `0`. -/
def Ex.s0 : Stmt := .store .rlx 0 .wb (.lit 0) (.lit 0)

/-- **The single-thread lift fails without `posSizes`**: `s0` replays sequentially, but its
memory unit has size `0`, which `Exec.Wf` rejects, so it has no SC behaviour. -/
theorem not_cirSeqSc_without_posSizes :
    ¬ ∀ (locs : List Loc) (s : Stmt), s.threadFree = true → ∀ f : Final,
      Behav ⟨locs, [⟨s, false⟩]⟩ Exec.Sc f ↔
        ∃ tr rs m, SeqRun s Regs.zero (initByte locs) tr rs m ∧
          f = ⟨fun i r => if i = 0 then rs r else 0, m⟩ := by
  intro h
  have hr := (h [] Ex.s0 rfl
    ⟨fun i r => if i = 0 then Regs.zero r else 0, Mem.put (initByte []) 0 0 0⟩).mpr
    ⟨[.wr .rlx .wb 0 0 0], Regs.zero, Mem.put (initByte []) 0 0 0,
      ⟨⟨[], List.mem_singleton.mpr rfl⟩, rfl⟩, rfl⟩
  obtain ⟨dom, trs, hf, x, hevs, -, hwf, -⟩ := hr
  have hT : Prog.traces ⟨[], [⟨Ex.s0, false⟩]⟩ dom =
      [[Thread.xtrace ⟨Ex.s0, false⟩ 0 ([.wr .rlx .wb 0 0 0], Regs.zero)]] := rfl
  rw [hT] at hf
  obtain ⟨a, rest, ha, hrest, rfl⟩ := List.forall₂_cons_right_iff.mp hf
  cases hrest
  rw [List.mem_singleton] at ha
  subst ha
  have hlast : x.evs.all (fun e =>
      if e.isM then
        decide (0 < e.size) && decide (e.accAddr ≤ e.addr) &&
          decide (e.addr + e.size ≤ e.accAddr + e.accSize) && (!e.isW || e.data.length == e.size)
      else e.size == 0) = false := by
    rw [hevs]; decide +kernel
  simp only [Exec.Wf, hlast, Bool.and_false] at hwf
  exact absurd hwf (by decide)

end Silmaril.X86.Concurrency.Cir
