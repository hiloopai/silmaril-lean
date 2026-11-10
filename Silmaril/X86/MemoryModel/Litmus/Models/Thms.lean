module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.MemoryModel.Litmus.Thms
import Silmaril.Proofs.X86.MemoryModel.Litmus.Models.Verdict
import Silmaril.Proofs.X86.MemoryModel.Litmus.Models.Ax

/-!
# Litmus outcomes under operational TSO and axiomatic SC/TSO/XL: theorems

PROVED (standard axioms only; proofs in `Silmaril.Proofs.X86.MemoryModel.Litmus.Models.*`), for
every test and every list `T` of per-thread trace sets:

* `opOut_spec`: when `Test.opOut` succeeds, its outcomes are exactly the outcomes of the final
  states of operational x86-TSO (`OpReach`: one trace per thread run on `Tso.XStep`/`Tso.XFlush`
  to completion with every buffer drained);
* `axJudge_spec`: when `Test.axJudge` succeeds, the outcomes of its judged candidates
  consistent under SC, TSO or XL are exactly the outcomes of `AxReach` under that model;
* `axReach_mono`: `AxReach` under SC is contained in TSO, and TSO in XL (from
  `Exec.tso_of_sc` and `Exec.xl_of_tso`), so per test SC ⊆ TSO ⊆ XL for outcomes and verdicts
  (`allowed_mono`, `forbidden_anti` of `MemoryModel.Litmus`);
* `verdictOf_holds`: the verdict computed from an exact outcome list holds;
* `tsoVerdicts_of_check`: `Test.checkTso T = true` gives `TsoVerdicts t T`, and
  `tsoVerdicts_of_checkBytes` does so for the traces extracted from the bytes;
* `xl_of_checkXl`: `Test.checkXl T = true` gives the recorded XL verdict; `loose_of_check` and
  `plainLoose_of_check` give the loose-corner statements;
* every per-test check also requires a nonempty SC outcome list, so no `forbidden` verdict is
  vacuous (`TsoVerdicts.sc_some`, `TsoVerdicts.op_some`).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Litmus

open Silmaril.X86.MemoryModel.Axiomatic (Exec Ev)

/-- **The operational TSO enumerator is exact.** -/
theorem opOut_spec {t : Test} {T : List (List XTrace)} {os : List Outcome}
    (h : t.opOut T = some os) (o : Outcome) :
    o ∈ os ↔ ∃ f, OpReach t T f ∧ t.outcome f = o :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.opOut_spec h o

/-- **The axiomatic enumerator is exact**, for each of SC, TSO and XL. -/
theorem axJudge_spec {t : Test} {T : List (List XTrace)} {js : List Judged}
    (h : t.axJudge T = some js) (M : Model) (o : Outcome) :
    o ∈ outsBy js M.sel ↔ ∃ f, AxReach t T M.Holds f ∧ t.outcome f = o :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.axJudge_spec h M o

/-- `AxReach` is monotone in the model. -/
theorem axReach_mono {t : Test} {T : List (List XTrace)} {M M' : Exec → Prop}
    (h : ∀ x, M x → M' x) {f : Final} (hf : AxReach t T M f) : AxReach t T M' f := by
  obtain ⟨trs, htrs, x, h1, h2, h3, h4, h5, h6⟩ := hf
  exact ⟨trs, htrs, x, h1, h2, h3, h4, h x h5, h6⟩

/-- **SC ⊆ TSO** for every test and trace sets. -/
theorem axReach_sc_tso {t : Test} {T : List (List XTrace)} {f : Final}
    (h : AxReach t T Exec.Sc f) : AxReach t T Exec.Tso f :=
  axReach_mono (fun x hx => x.tso_of_sc hx) h

/-- **TSO ⊆ XL** for every test and trace sets. -/
theorem axReach_tso_xl {t : Test} {T : List (List XTrace)} {f : Final}
    (h : AxReach t T Exec.Tso f) : AxReach t T Exec.Xl f :=
  axReach_mono (fun x hx => x.xl_of_tso hx) h

/-- A verdict forbidden by XL is forbidden by TSO, and one forbidden by TSO by SC. -/
theorem forbidden_xl_tso {t : Test} {T : List (List XTrace)}
    (h : Verdict.forbidden.Holds t (AxReach t T Exec.Xl)) :
    Verdict.forbidden.Holds t (AxReach t T Exec.Tso) :=
  forbidden_anti (fun _ => axReach_tso_xl) h

theorem forbidden_tso_sc {t : Test} {T : List (List XTrace)}
    (h : Verdict.forbidden.Holds t (AxReach t T Exec.Tso)) :
    Verdict.forbidden.Holds t (AxReach t T Exec.Sc) :=
  forbidden_anti (fun _ => axReach_sc_tso) h

/-- **The verdict of an exact outcome list holds.** -/
theorem verdictOf_holds {t : Test} {os : List Outcome} {R : Final → Prop}
    (h : ∀ o, o ∈ os ↔ ∃ f, R f ∧ t.outcome f = o) : (t.verdictOf os).Holds t R :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.verdictOf_holds h

/-- **A passing `checkTso` gives the TSO-covered verdict statements.** -/
theorem tsoVerdicts_of_check {t : Test} {T : List (List XTrace)} (h : t.checkTso T = true) :
    TsoVerdicts t T :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.tsoVerdicts_of_check h

/-- **A passing `checkTsoBytes` gives the verdict statements for the traces extracted from the
test's bytes.** -/
theorem tsoVerdicts_of_checkBytes {t : Test} (h : t.checkTsoBytes = true) :
    ∃ T, t.traces = some T ∧ TsoVerdicts t T := by
  unfold Test.checkTsoBytes at h
  split at h
  · rename_i T hT; exact ⟨T, hT, tsoVerdicts_of_check h⟩
  · cases h

/-- **A passing `checkPlainLoose`**: operational and axiomatic TSO have the same outcomes and
forbid the witness, the recorded XL verdict holds, axiomatic SC forbids the witness, and some SC
execution exists. -/
theorem plainLoose_of_check {t : Test} {T : List (List XTrace)} (h : t.checkPlainLoose T = true) :
    (∀ o, (∃ f, OpReach t T f ∧ t.outcome f = o) ↔ (∃ f, AxReach t T Exec.Tso f ∧ t.outcome f = o)) ∧
      Verdict.forbidden.Holds t (OpReach t T) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
      t.xl.Holds t (AxReach t T Exec.Xl) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧
      ∃ f, AxReach t T Exec.Sc f :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.plainLoose_of_check h

/-- **A passing `checkLoose`**: the recorded XL verdict holds, axiomatic TSO and SC forbid the
witness, and some SC execution exists. -/
theorem loose_of_check {t : Test} {T : List (List XTrace)} (h : t.checkLoose T = true) :
    t.xl.Holds t (AxReach t T Exec.Xl) ∧ Verdict.forbidden.Holds t (AxReach t T Exec.Tso) ∧
      Verdict.forbidden.Holds t (AxReach t T Exec.Sc) ∧ ∃ f, AxReach t T Exec.Sc f :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.loose_of_check h

/-- Some SC execution gives an operational TSO final state (via SC ⊆ TSO and `op_eq_ax`). -/
theorem TsoVerdicts.op_some {t : Test} {T : List (List XTrace)} (h : TsoVerdicts t T) :
    ∃ f, OpReach t T f := by
  obtain ⟨f, hf⟩ := h.sc_some
  obtain ⟨g, hg, _⟩ := (h.op_eq_ax _).mpr ⟨f, axReach_sc_tso hf, rfl⟩
  exact ⟨g, hg⟩

/-- **A passing `checkXl` gives the recorded XL verdict.** -/
theorem xl_of_checkXl {t : Test} {T : List (List XTrace)} (h : t.checkXl T = true) :
    t.xl.Holds t (AxReach t T Exec.Xl) :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.xl_of_checkXl h

/-! ## Completeness of the candidate enumeration

The candidate enumerator `candidates` is complete for every model whose consistent executions
have no two-cycle in `com`: such an execution agrees with an enumerated candidate on every
argument of `rf` and `co` that the relations look at. Exported so that other consistency
predicates (RC11 on CIR can reuse the enumerator. -/

/-- Two executions over the same units and pairs that agree on every `rf` and `co` argument the
relations look at (the public form of the enumerator's agreement relation). -/
structure Agrees (x x' : Exec) : Prop where
  evs : x.evs = x'.evs
  rmw : x.rmw = x'.rmw
  rf : ∀ r y, (x.evN r).isR = true → y ∈ (x.evN r).bytes → x.rf r y = x'.rf r y
  co : ∀ y ∈ x.touched, x.co y = x'.co y

/-- **Every well-formed candidate whose reads are right and whose `com` has no two-cycle agrees
with an enumerated candidate.** -/
theorem candidates_complete (t : Test) {evs : List Ev} {exps : List (List Byte)}
    {rmw : List (Nat × Nat)} (hc : cellsOk evs = true) {x : Exec} (hx : x.evs = evs)
    (hrmw : x.rmw = rmw) (hwf : x.Wf = true) (hro : ReadsOk t x exps)
    (hn : ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False) :
    ∃ x' ∈ candidates t evs exps rmw, Agrees x x' := by
  obtain ⟨x', hx', h⟩ := Silmaril.Proofs.X86.MemoryModel.Litmus.cand_complete t hc hx hrmw hwf hro hn
  exact ⟨x', hx', ⟨h.evs, h.rmw, h.rf, h.co⟩⟩

/-- Agreeing executions are consistent under the same stage-1 models, equally well formed, read
the same bytes and end in the same final state. -/
theorem Agrees.models {x x' : Exec} (h : Agrees x x') :
    (x.Sc ↔ x'.Sc) ∧ (x.Tso ↔ x'.Tso) ∧ (x.Xl ↔ x'.Xl) ∧ x.Wf = x'.Wf ∧
      (∀ t exps, ReadsOk t x exps ↔ ReadsOk t x' exps) ∧
      ∀ t trs, finalAx t trs x = finalAx t trs x' :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.agree_all ⟨h.evs, h.rmw, h.rf, h.co⟩

/-- Agreeing executions over the same units have the same `rf`, `co` and `fr` relations. -/
theorem Agrees.rels {evs : List Ev} {rf rf' : Nat → Nat → Option Nat} {co co' : Nat → List Nat}
    {rmw : List (Nat × Nat)} (h : Agrees ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.rfR ⟨evs, rf, co, rmw⟩ = Exec.rfR ⟨evs, rf', co', rmw⟩ ∧
      Exec.coR ⟨evs, rf, co, rmw⟩ = Exec.coR ⟨evs, rf', co', rmw⟩ ∧
      Exec.frR ⟨evs, rf, co, rmw⟩ = Exec.frR ⟨evs, rf', co', rmw⟩ :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.agree_rels ⟨h.evs, h.rmw, h.rf, h.co⟩

/-- TSO-consistent executions have no two-cycle in `com`. -/
theorem noTwo_of_tso {x : Exec} (h : x.Tso) :
    ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.noTwo_of_tso h

/-- XL-consistent executions have no two-cycle in `com`. -/
theorem noTwo_of_xl {x : Exec} (h : x.Xl) :
    ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False :=
  Silmaril.Proofs.X86.MemoryModel.Litmus.noTwo_of_xl h

end Silmaril.X86.MemoryModel.Litmus
