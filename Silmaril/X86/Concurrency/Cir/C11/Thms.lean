module

public import Silmaril.X86.Concurrency.Cir.C11.Defs
public import Silmaril.X86.Concurrency.Cir.Tv.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms
public import Silmaril.X86.MemoryModel.Xl.Thms
import Silmaril.Proofs.X86.Concurrency.Cir.C11
import Silmaril.Proofs.X86.Concurrency.Cir.C11Map.Exec
import Silmaril.Proofs.X86.Concurrency.Cir.C11Map.Units
import Silmaril.Proofs.X86.Concurrency.Cir.C11Map.Counter

/-!
# C11 litmus tests on CIR: theorems

PROVED (standard axioms only):

* `C11Test.holds_of_check`: a passing `C11Test.check` gives `C11Test.Holds`: refinement
  from the x86 bytes to the CIR program; every XL-consistent candidate execution of the
  CIR program is RC11-consistent (the compilation is correct on the test, execution by
  execution); the RC11 verdict (racy, allowed or forbidden) is the expected one; some RC11
  execution exists; the CIR's XL and TSO verdicts are the recorded x86 ones; a forbidden RC11
  verdict holds for the x86 bytes under XL; and `stronger` marks exactly the tests where XL
  forbids what RC11 allows.

**The mapping theorem**, for every program, not only the tested ones:

* `tso_rc11`: a well-formed x86-TSO-consistent candidate whose memory units form cells
  (`Cells`) and whose roles respect the mapping (`MapRoles`: SC writes locked, SC fences
  `mfence` or locked) is RC11-consistent. `partial_forward_tso`: without `Cells` it is false.
* `cells_units`, `mapRoles_units`: both hypotheses hold on the units of the runs of a
  `c11MapOk` program;
* **`cirTsoRc11 : Task.cirTsoRc11`** (the Task as stated, now a theorem), and
  `tame_xl_rc11` (XL on tame candidates);
* behaviours: `behav_tso_rc11`, `behav_tameXl_rc11` (every TSO, and every tame XL, behaviour of
  a `c11MapOk` CIR program is an RC11 behaviour);
* **compiled C11 programs** (`C11Test.x86_rc11`, `C11Test.forbidden_x86`): for a C11 program
  compiled to x86 and validated into a `c11MapOk` CIR program, every tame XL (in particular
  every TSO) behaviour of the bytes has the witness value of an RC11 behaviour of the CIR
  program, so a witness RC11 forbids is forbidden for the bytes.
-/

@[expose] public section

namespace Silmaril.X86.Concurrency.Cir.C11

open Silmaril.X86.MemoryModel.Axiomatic (Exec)
open Silmaril.X86.MemoryModel.Litmus (XTrace units rmwPairs AxReach Final Verdict Test)

/-- **A passing check gives everything a C11 test states.** -/
theorem C11Test.holds_of_check {c : C11Test} (h : c.check = true) : c.Holds :=
  Silmaril.Proofs.X86.Concurrency.Cir.C11.holds_of_check h

/-! ## The mapping theorem -/

/-- **The x86 mapping is correct for RC11, execution by execution.** -/
theorem tso_rc11 {x : Exec} {ro : Nat → Role} (hwf : x.Wf = true) (ht : x.Tso) (hc : Cells x)
    (hm : MapRoles ro x) : Rc11.Consistent ro x :=
  Silmaril.Proofs.X86.Concurrency.Cir.C11Map.tso_rc11 hwf ht hc hm

/-- **`Cells` is needed**: a well-formed TSO-consistent execution with relaxed roles (so
`MapRoles` holds) and a one-byte store forwarded into an overlapping two-byte load is not
RC11-consistent. -/
theorem partial_forward_tso : ∃ x : Exec, x.Wf = true ∧ x.Tso ∧ ¬ Cells x ∧
    MapRoles (fun _ => .acc .rlx) x ∧ ¬ Rc11.Consistent (fun _ => .acc .rlx) x :=
  open Silmaril.Proofs.X86.Concurrency.Cir.C11Map in
  ⟨pfx, pfx_wf, pfx_tso, pfx_not_cells, pfx_mapRoles, pfx_not_rc11⟩

/-- The units of CIR runs form cells. -/
theorem cells_units {trs : List XTrace} {x : Exec} (hx : x.evs = (units trs).map Prod.fst) :
    Cells x :=
  Silmaril.Proofs.X86.Concurrency.Cir.C11Map.cells_units hx

/-- The roles of a `c11MapOk` program respect the mapping on the units of its runs. -/
theorem mapRoles_units {P : Prog} {dom : List Nat} (hP : P.c11MapOk = true) {trs : List XTrace}
    (htr : List.Forall₂ (· ∈ ·) trs (P.traces dom)) {x : Exec}
    (hx : x.evs = (units trs).map Prod.fst) : MapRoles (P.roles x) x :=
  Silmaril.Proofs.X86.Concurrency.Cir.C11Map.mapRoles_units hP htr hx

/-- **`Task.cirTsoRc11` holds**: TSO-consistent candidates of mapping-respecting CIR programs
are RC11-consistent. -/
theorem cirTsoRc11 : Task.cirTsoRc11 := by
  intro P dom hP trs htr x hx _ hwf ht
  exact tso_rc11 hwf ht (cells_units hx) (mapRoles_units hP htr hx)

/-- On tame candidates (write-back, not tearable) XL is TSO, so the same holds for XL. -/
theorem tame_xl_rc11 {P : Prog} {dom : List Nat} (hP : P.c11MapOk = true) {trs : List XTrace}
    (htr : List.Forall₂ (· ∈ ·) trs (P.traces dom)) {x : Exec}
    (hx : x.evs = (units trs).map Prod.fst) (hwf : x.Wf = true) (hxl : x.Xl) (hta : x.Tame) :
    P.Rc11 x :=
  tso_rc11 hwf ((x.xl_iff_tso_of_tame hta).mp hxl) (cells_units hx) (mapRoles_units hP htr hx)

/-! ## Behaviours -/

/-- Every TSO behaviour of a `c11MapOk` CIR program is an RC11 behaviour. -/
theorem behav_tso_rc11 {P : Prog} {dom : List Nat} (hP : P.c11MapOk = true) {f : Final}
    (h : BehavIn P dom Exec.Tso f) : BehavIn P dom P.Rc11 f := by
  obtain ⟨trs, htr, x, hx, hr, hwf, hro, ht, hf⟩ := h
  exact ⟨trs, htr, x, hx, hr, hwf, hro,
    tso_rc11 hwf ht (cells_units hx) (mapRoles_units hP htr hx), hf⟩

/-- **Every tame XL behaviour of a `c11MapOk` CIR program is an RC11 behaviour.** -/
theorem behav_tameXl_rc11 {P : Prog} {dom : List Nat} (hP : P.c11MapOk = true) {f : Final}
    (h : BehavIn P dom (fun x => x.Xl ∧ x.Tame) f) : BehavIn P dom P.Rc11 f := by
  obtain ⟨trs, htr, x, hx, hr, hwf, hro, ⟨hxl, hta⟩, hf⟩ := h
  exact ⟨trs, htr, x, hx, hr, hwf, hro, tame_xl_rc11 hP htr hx hwf hxl hta, hf⟩

/-! ## Compiled C11 programs -/

/-- **Compiled C11 programs are correct under tame XL**: for a C11 program compiled to x86 and
validated into a `c11MapOk` CIR program, every tame XL behaviour of the x86 bytes has the
witness value of an RC11 behaviour of the CIR program. -/
theorem C11Test.x86_rc11 {c : C11Test} (h : c.tv.tvOk = true) (hd : c.tv.domOk = true)
    (hm : c.prog.c11MapOk = true) {T : List (List XTrace)} (hT : c.tv.test.traces = some T)
    {f : Final} (hf : AxReach c.tv.test T (fun x => x.Xl ∧ x.Tame) f) :
    ∃ f', c.Rc f' ∧ c.tv.test.witness.eval f' = c.tv.test.witness.eval f := by
  obtain ⟨f', hf', hw⟩ := Tv.TvTest.refines h hd hT hf
  exact ⟨f', behav_tameXl_rc11 hm hf', hw⟩

/-- The same under TSO, with no tameness hypothesis. -/
theorem C11Test.x86_tso_rc11 {c : C11Test} (h : c.tv.tvOk = true) (hd : c.tv.domOk = true)
    (hm : c.prog.c11MapOk = true) {T : List (List XTrace)} (hT : c.tv.test.traces = some T)
    {f : Final} (hf : AxReach c.tv.test T Exec.Tso f) :
    ∃ f', c.Rc f' ∧ c.tv.test.witness.eval f' = c.tv.test.witness.eval f := by
  obtain ⟨f', hf', hw⟩ := Tv.TvTest.refines h hd hT hf
  exact ⟨f', behav_tso_rc11 hm hf', hw⟩

/-- **A witness RC11 forbids is forbidden for the compiled bytes** under tame XL. -/
theorem C11Test.forbidden_x86 {c : C11Test} (h : c.tv.tvOk = true) (hd : c.tv.domOk = true)
    (hm : c.prog.c11MapOk = true) {T : List (List XTrace)} (hT : c.tv.test.traces = some T)
    (hc : Verdict.forbidden.Holds c.tv.test c.Rc) :
    Verdict.forbidden.Holds c.tv.test (AxReach c.tv.test T (fun x => x.Xl ∧ x.Tame)) := by
  rintro ⟨f, hf, hw⟩
  obtain ⟨f', hf', hw'⟩ := C11Test.x86_rc11 h hd hm hT hf
  exact hc ⟨f', hf', hw'.trans hw⟩

end Silmaril.X86.Concurrency.Cir.C11
