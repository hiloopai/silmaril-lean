module

public import Silmaril.X86.MemoryModel.Lattice.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms
public import Silmaril.X86.MemoryModel.Litmus.Models.Thms
public import Silmaril.X86.Concurrency.Cir.Defs
import Silmaril.Proofs.X86.MemoryModel.Lattice.Drf

/-!
# A lattice of x86 memory models: theorems

PROVED (standard axioms only; the longer proofs are in
`Silmaril.Proofs.X86.MemoryModel.Lattice.Drf`). Every statement is about **every** candidate
execution; none needs well-formedness.

## The order

`Model.Le M N` is `M ≤ N` in the complete lattice `Exec → Prop` (`Model.le_iff`), so meets,
joins, `⊤ = top` and `⊥` come from Mathlib. Proved edges (the Hasse diagram, bottom to top):

```
              top
             /    \
           xl    cfPlain
            |    /     \
            |  ra       cf
             \  |      /
               tso ----
                |
               sc
```

* `sc_le_tso` (herd's SC ⊆ x86-TSO), `tso_le_xl` (x86-TSO ⊆ XL);
* `tso_le_ra`: **x86-TSO executions are release/acquire**;
* `ra_le_cfPlain`: **DRF-SC for release/acquire**;
* `tso_le_cf`: **DRF-SC for x86-TSO, modulo locked synchronisation** (below);
* `cf_le_cfPlain`, `xl_le_top`, `cfPlain_le_top`, and the composites;
* `Name.le_sound`: every pair `Name.le` lists is a proved `⊑`; `HoldsUnder.mono` moves a
  result stated under a named model down the order; `le_iff_mLe` identifies `⊑` with the
  `Cir.MLe` order that process lifts and problem statements quantify over, and
  `Name.between_sc_xl` places `sc` and `tso` between SC and XL.

## DRF-SC

* `drf_sc_tso` (the sanity check): an x86-TSO execution in which each access is one unit and
  every pair of conflicting accesses of different threads, except two locked ones, is ordered
  by `hbL = (po ∪ rf ∪ lockCom)⁺` is **sequentially consistent**. Locked accesses (lock words,
  `lock cmpxchg`, `xchg`, `lock xadd`) are the primitives: they may race with each other, and
  their communication synchronises. The plain variant (`drf_sc_tso_plain`, `hb = (po ∪ rf)⁺`)
  is the corollary for programs whose accesses are all plain or release/acquire;
* `drf_sc_ra`: the same for release/acquire;
* `drf_sc_xl_tame` (the loose model): an XL execution whose memory units are all tame
  (write-back, single-copy atomic, no mixed sizes) is SC when DRF. **Tameness is needed**:
  `mpNt_drf_not_sc` is a race-free, unsplit XL execution that is not SC (message passing with a
  non-temporal data store);
* `axReach_sc_of_drf`: per litmus test, every final state of a DRF x86-TSO candidate is an SC
  final state.

This is the **execution-level** DRF-SC theorem: its hypothesis is that the TSO execution
itself is race-free. The **program-level** theorem (if every SC execution of a program is
race-free, then every TSO execution is SC) follows from it by the usual minimal-counterexample
argument, which needs a program semantics closed under prefixes and under changing the value
of the last read (receptiveness). That step is not formalised here; the plan is: (1) order the
units of a non-SC TSO execution by a linear extension of `ghb ∪ po`; (2) take the shortest
prefix that is not SC; (3) re-read its last read from the SC-latest write, which by
receptiveness gives an SC execution of the program; (4) the pair formed by that read and the
write it missed is a race in that SC execution, contradicting program DRF.

## Separations (checked by `decide`)

| edge | witness | allowed by | forbidden by |
|---|---|---|---|
| sc ⊏ tso | `Sanity.sb` (SB) | tso, ra, xl | sc |
| tso ⊏ xl | `Sanity.mpNt` (MP+movnti), `Sanity.torn` | xl | tso, ra, cf, cfPlain |
| tso ⊏ ra | `iriw` (IRIW), `w22` (2+2W) | ra | tso, xl |
| (none) | `mp` (MP), `lb` (LB) | top | all others |
| ra ⊏ cfPlain | `Sanity.lockInc` | cfPlain | ra, cf |
| tso ⊏ cf | `Sanity.sbMfence` (SB+mfences) | cf, cfPlain, ra | tso, xl |
| cf ⊏ cfPlain | `Sanity.lockInc` (two racing `lock inc`) | cfPlain | cf |
| xl ⊏ top, cfPlain ⊏ top | `coWR` (a read missing its own write) | top | all others |

Incomparable pairs: `xl ∥ ra`, `xl ∥ cf`, `xl ∥ cfPlain`. Open: whether `ra ⊑ cf`.

## Experimental validation

`scripts/x86-litmus-hw` runs the litmus shapes above on the host CPU (inline assembly of the
same instructions, pinned threads, a barrier per iteration) and compares every observed outcome
with these verdicts (see its README for a recorded run).
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.Lattice

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Axiomatic.Sanity
open Silmaril.X86.MemoryModel.Litmus (Test XTrace Final AxReach)

namespace Model

theorem le_iff {M N : Model} : Le M N ↔ M ≤ N := Iff.rfl

theorem le_refl (M : Model) : Le M M := fun _ h => h

theorem le_trans {M N K : Model} (h1 : Le M N) (h2 : Le N K) : Le M K :=
  fun x h => h2 x (h1 x h)

theorem le_top (M : Model) : Le M top := fun _ _ => trivial

theorem top_eq : top = ⊤ := rfl

/-- A separating execution refutes the reverse inclusion. -/
theorem not_le_of_sep {x : Exec} {M N : Model} (h : Sep x M N) : ¬ Le N M :=
  fun hle => h.2 (hle x h.1)

/-- Results move along `⊑`: a property of all `N`-allowed executions holds for all
`M`-allowed ones. -/
theorem Le.transfer {M N : Model} (h : Le M N) {P : Exec → Prop} (hP : ∀ x, N x → P x) :
    ∀ x, M x → P x := fun x hx => hP x (h x hx)

end Model

open Model

/-! ## Edges -/

theorem sc_le_tso : Le sc tso := fun x h => x.tso_of_sc h

theorem tso_le_xl : Le tso xl := fun x h => x.xl_of_tso h

/-- **x86-TSO executions are release/acquire.** -/
theorem tso_le_ra : Le tso ra := fun x h => Proofs.Lattice.ra_of_tso x h

/-- **DRF-SC for x86-TSO**, as an inclusion. -/
theorem tso_le_cf : Le tso cf := fun x h => Proofs.Lattice.cf_of_tso x h

/-- **DRF-SC for release/acquire**, as an inclusion. -/
theorem ra_le_cfPlain : Le ra cfPlain := fun x h => Proofs.Lattice.cfPlain_of_ra x h

theorem cf_le_cfPlain : Le cf cfPlain := fun x h => Proofs.Lattice.cfPlain_of_cf x h

theorem xl_le_top : Le xl top := le_top xl
theorem cfPlain_le_top : Le cfPlain top := le_top cfPlain

theorem sc_le_xl : Le sc xl := le_trans sc_le_tso tso_le_xl
theorem sc_le_ra : Le sc ra := le_trans sc_le_tso tso_le_ra
theorem sc_le_cf : Le sc cf := le_trans sc_le_tso tso_le_cf
theorem tso_le_cfPlain : Le tso cfPlain := le_trans tso_le_cf cf_le_cfPlain
theorem sc_le_cfPlain : Le sc cfPlain := le_trans sc_le_tso tso_le_cfPlain

/-- On tame executions XL is below `tso`, hence below `cf`. -/
theorem xl_tame_le_tso : Le (xl ⊓ tame) tso := fun x h => (x.xl_iff_tso_of_tame h.2).mp h.1

/-- **Every pair `Name.le` lists is a proved inclusion.** -/
theorem Name.le_sound {a b : Name} (h : a.le b = true) : Le a.model b.model := by
  cases a <;> cases b <;> simp [Name.le] at h <;> simp only [Name.model] <;>
    first
    | exact le_refl _ | exact le_top _ | exact sc_le_tso | exact sc_le_ra | exact sc_le_xl
    | exact sc_le_cf | exact sc_le_cfPlain | exact tso_le_ra | exact tso_le_xl | exact tso_le_cf
    | exact tso_le_cfPlain | exact ra_le_cfPlain | exact cf_le_cfPlain

/-- Results stated under a named model hold under every model below it. -/
theorem HoldsUnder.mono {a b : Name} (h : a.le b = true) {P : Exec → Prop}
    (hb : HoldsUnder b P) : HoldsUnder a P := (Name.le_sound h).transfer hb

/-- `⊑` is the model order `Cir.MLe` that concurrency results and problems quantify over. -/
theorem le_iff_mLe {M N : Model} : Le M N ↔ Silmaril.X86.Concurrency.Cir.MLe M N := Iff.rfl

/-- SC and TSO lie between SC and XL, so every result stated for all `M` with
`Cir.MLe Exec.Sc M` and `Cir.MLe M Exec.Xl` (process lifts, problem statements) applies to them
by name. -/
theorem Name.between_sc_xl {a : Name} (h : a = .sc ∨ a = .tso) :
    Silmaril.X86.Concurrency.Cir.MLe Exec.Sc a.model ∧
      Silmaril.X86.Concurrency.Cir.MLe a.model Exec.Xl := by
  rcases h with rfl | rfl
  · exact ⟨le_refl _, sc_le_xl⟩
  · exact ⟨sc_le_tso, tso_le_xl⟩

/-! ## DRF-SC -/

/-- **DRF-SC for x86-TSO** (locked accesses synchronise). -/
theorem drf_sc_tso {x : Exec} (h : x.Tso) (hu : x.Unsplit) (hd : x.DrfL) : x.Sc :=
  tso_le_cf x h hu hd

/-- DRF-SC for x86-TSO with `hb = (po ∪ rf)⁺`. -/
theorem drf_sc_tso_plain {x : Exec} (h : x.Tso) (hu : x.Unsplit) (hd : x.Drf) : x.Sc :=
  tso_le_cfPlain x h hu hd

/-- **DRF-SC for release/acquire.** -/
theorem drf_sc_ra {x : Exec} (h : x.Ra) (hu : x.Unsplit) (hd : x.Drf) : x.Sc :=
  ra_le_cfPlain x h hu hd

/-- **DRF-SC for tame XL executions.** -/
theorem drf_sc_xl_tame {x : Exec} (h : x.Xl) (ht : x.Tame) (hu : x.Unsplit) (hd : x.DrfL) :
    x.Sc := drf_sc_tso ((x.xl_iff_tso_of_tame ht).mp h) hu hd

/-! ## Boolean checks -/

theorem unsplitB_iff (x : Exec) : x.unsplitB = true ↔ x.Unsplit := Proofs.Lattice.unsplitB_iff x

theorem drfB_iff {x : Exec} (hc : x.hbClosedB = true) : x.drfB = true ↔ x.Drf :=
  Proofs.Lattice.drfB_iff x hc

theorem drfLB_iff {x : Exec} (hc : x.hbLClosedB = true) : x.drfLB = true ↔ x.DrfL :=
  Proofs.Lattice.drfLB_iff x hc

theorem ra_iff_check {x : Exec} (hc : x.hbClosedB = true) :
    x.Ra ↔ (x.atomicB && x.uniproc.acyclicB && x.thinAir.acyclicB && x.raCohB) = true := by
  simp only [Exec.Ra, Bool.and_eq_true, ← BRel.acyclic_iff, Proofs.Lattice.raCohB_iff x hc,
    and_assoc]

/-! ## Separating executions -/

/-- IRIW: two writers, two readers that see the writes in opposite orders. -/
def iriw : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 2, pos := 0, act := .read, addr := 0, size := 1 },
          { tid := 2, pos := 1, act := .read, addr := 1, size := 1 },
          { tid := 3, pos := 0, act := .read, addr := 1, size := 1 },
          { tid := 3, pos := 1, act := .read, addr := 0, size := 1 }]
  rf := fun r y => if r = 2 ∧ y = 0 then some 0 else if r = 4 ∧ y = 1 then some 1 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [1] else []

/-- CoWR: one thread writes `x` and then reads the initial value of `x`. -/
def coWR : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .read, addr := 0, size := 1 }]
  co := fun y => if y = 0 then [0] else []

/-- MP: `x := 1; y := 1 ∥ r0 := y (= 1); r1 := x (= 0)`. -/
def mp : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 1, act := .read, addr := 0, size := 1 }]
  rf := fun r y => if r = 2 ∧ y = 1 then some 1 else none
  co := fun y => if y = 0 then [0] else if y = 1 then [1] else []

/-- LB: `r0 := x (= 1); y := 1 ∥ r1 := y (= 1); x := 1`. -/
def lb : Exec where
  evs := [{ tid := 0, pos := 0, act := .read, addr := 0, size := 1 },
          { tid := 0, pos := 1, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 0, act := .read, addr := 1, size := 1 },
          { tid := 1, pos := 1, act := .write, addr := 0, size := 1, data := [1] }]
  rf := fun r y => if r = 0 ∧ y = 0 then some 3 else if r = 2 ∧ y = 1 then some 1 else none
  co := fun y => if y = 0 then [3] else if y = 1 then [1] else []

/-- 2+2W: `x := 1; y := 2 ∥ y := 1; x := 2`, ending with `x = 1`, `y = 1`. -/
def w22 : Exec where
  evs := [{ tid := 0, pos := 0, act := .write, addr := 0, size := 1, data := [1] },
          { tid := 0, pos := 1, act := .write, addr := 1, size := 1, data := [2] },
          { tid := 1, pos := 0, act := .write, addr := 1, size := 1, data := [1] },
          { tid := 1, pos := 1, act := .write, addr := 0, size := 1, data := [2] }]
  co := fun y => if y = 0 then [3, 0] else if y = 1 then [1, 2] else []

/-- The weak outcomes of MP and LB are forbidden by SC, TSO, XL and RA (and, being race-free,
by the catch-fire models: `mp_lb_drf`); 2+2W's is forbidden by TSO and XL and allowed by RA. -/
theorem weak_verdicts :
    mp.Wf = true ∧ ¬ mp.Tso ∧ ¬ mp.Xl ∧ ¬ mp.Ra ∧
    lb.Wf = true ∧ ¬ lb.Tso ∧ ¬ lb.Xl ∧ ¬ lb.Ra ∧
    w22.Wf = true ∧ ¬ w22.Tso ∧ ¬ w22.Xl ∧ w22.Ra :=
  ⟨by decide, by decide, by decide, fun h => absurd ((ra_iff_check (x := mp) (by decide)).mp h)
    (by decide), by decide, by decide, by decide,
    fun h => absurd ((ra_iff_check (x := lb) (by decide)).mp h) (by decide), by decide,
    by decide, by decide, (ra_iff_check (by decide)).mpr (by decide)⟩

/-- MP and LB are race-free, so only `top` allows their weak outcomes. -/
theorem mp_lb_drf : ¬ mp.CfPlain ∧ ¬ mp.Cf ∧ ¬ lb.CfPlain ∧ ¬ lb.Cf := by
  have hm : ¬ mp.CfPlain := fun h =>
    absurd (h ((unsplitB_iff _).mp (by decide)) ((drfB_iff (by decide)).mp (by decide)))
      (by decide)
  have hl : ¬ lb.CfPlain := fun h =>
    absurd (h ((unsplitB_iff _).mp (by decide)) ((drfB_iff (by decide)).mp (by decide)))
      (by decide)
  exact ⟨hm, fun h => hm (cf_le_cfPlain _ h), hl, fun h => hl (cf_le_cfPlain _ h)⟩

/-- 2+2W also separates TSO from RA. -/
theorem sep_tso_ra_w22 : Sep w22 tso ra := ⟨weak_verdicts.2.2.2.2.2.2.2.2.2.2.2,
  weak_verdicts.2.2.2.2.2.2.2.2.2.1⟩

theorem iriw_wf : iriw.Wf = true := by decide
theorem coWR_wf : coWR.Wf = true := by decide

/-- SB: SC ⊏ TSO. -/
theorem sep_sc_tso : Sep sb sc tso := ⟨sb_verdict.2.2.1, sb_verdict.2.1⟩

/-- MP+movnti: TSO ⊏ XL. -/
theorem sep_tso_xl : Sep mpNt tso xl := ⟨mpNt_verdict.2.2, mpNt_verdict.2.1⟩

/-- A torn misaligned store: TSO ⊏ XL. -/
theorem sep_tso_xl_torn : Sep torn tso xl := ⟨torn_verdict.2.2.2.1, torn_verdict.2.2.1⟩

/-- IRIW: TSO ⊏ RA. -/
theorem sep_tso_ra : Sep iriw tso ra :=
  ⟨(ra_iff_check (by decide)).mpr (by decide), by show ¬ Exec.Tso iriw; decide⟩

/-- IRIW is not XL. -/
theorem sep_xl_ra : Sep iriw xl ra := ⟨sep_tso_ra.1, by show ¬ Exec.Xl iriw; decide⟩

/-- MP+movnti is not RA. -/
theorem sep_ra_xl : Sep mpNt ra xl :=
  ⟨mpNt_verdict.2.2, fun h => absurd ((ra_iff_check (x := mpNt) (by decide)).mp h) (by decide)⟩

/-- **MP+movnti is race-free, unsplit, XL and not SC**: DRF-SC fails for XL without tameness. -/
theorem mpNt_drf_not_sc :
    mpNt.Unsplit ∧ mpNt.Drf ∧ mpNt.Xl ∧ ¬ mpNt.Sc ∧ ¬ mpNt.Tame :=
  ⟨(unsplitB_iff _).mp (by decide), (drfB_iff (by decide)).mp (by decide), mpNt_verdict.2.2,
    by decide, by decide⟩

/-- MP+movnti separates `cfPlain` (and so `cf`) from XL. -/
theorem sep_cfPlain_xl : Sep mpNt cfPlain xl :=
  ⟨mpNt_verdict.2.2, fun h => mpNt_drf_not_sc.2.2.2.1 (h mpNt_drf_not_sc.1 mpNt_drf_not_sc.2.1)⟩

theorem sep_cf_xl : Sep mpNt cf xl :=
  ⟨sep_cfPlain_xl.1, fun h => sep_cfPlain_xl.2 (cf_le_cfPlain _ h)⟩

/-- SB+mfences is racy, so the catch-fire models allow it; TSO and XL forbid it. -/
theorem sbMfence_racy : ¬ sbMfence.DrfL ∧ ¬ sbMfence.Drf :=
  ⟨fun h => absurd ((drfLB_iff (by decide)).mpr h) (by decide),
    fun h => absurd ((drfB_iff (by decide)).mpr h) (by decide)⟩

theorem sep_tso_cf : Sep sbMfence tso cf :=
  ⟨fun _ hd => absurd hd sbMfence_racy.1, sbMfence_verdict.2.1⟩

theorem sep_xl_cf : Sep sbMfence xl cf := ⟨sep_tso_cf.1, sbMfence_verdict.2.2⟩

theorem sep_xl_cfPlain : Sep sbMfence xl cfPlain :=
  ⟨cf_le_cfPlain _ sep_tso_cf.1, sbMfence_verdict.2.2⟩

/-- Two racing `lock inc`: unsplit and race-free modulo locked accesses (the only conflicts are
between locked accesses), racy for `hb = (po ∪ rf)⁺`, not atomic, not SC. -/
theorem lockInc_facts :
    lockInc.Unsplit ∧ lockInc.DrfL ∧ ¬ lockInc.Drf ∧ ¬ lockInc.Sc ∧ ¬ lockInc.Ra :=
  ⟨(unsplitB_iff _).mp (by decide), (drfLB_iff (by decide)).mp (by decide),
    fun h => absurd ((drfB_iff (by decide)).mpr h) (by decide), by decide,
    fun h => absurd ((ra_iff_check (x := lockInc) (by decide)).mp h) (by decide)⟩

/-- `cf ⊏ cfPlain`. -/
theorem sep_cf_cfPlain : Sep lockInc cf cfPlain :=
  ⟨fun _ hd => absurd hd lockInc_facts.2.2.1,
    fun h => lockInc_facts.2.2.2.1 (h lockInc_facts.1 lockInc_facts.2.1)⟩

/-- `ra ⊏ cfPlain`. -/
theorem sep_ra_cfPlain : Sep lockInc ra cfPlain := ⟨sep_cf_cfPlain.1, lockInc_facts.2.2.2.2⟩

/-- CoWR: race-free (one thread), unsplit, not SC, not XL, not RA. -/
theorem coWR_facts : coWR.Unsplit ∧ coWR.Drf ∧ ¬ coWR.Sc ∧ ¬ coWR.Xl ∧ ¬ coWR.Ra :=
  ⟨(unsplitB_iff _).mp (by decide), (drfB_iff (by decide)).mp (by decide), by decide, by decide,
    fun h => absurd ((ra_iff_check (x := coWR) (by decide)).mp h) (by decide)⟩

theorem sep_cfPlain_top : Sep coWR cfPlain top :=
  ⟨trivial, fun h => coWR_facts.2.2.1 (h coWR_facts.1 coWR_facts.2.1)⟩

theorem sep_xl_top : Sep coWR xl top := ⟨trivial, coWR_facts.2.2.2.1⟩

/-! ## Strict edges and incomparable pairs -/

theorem sc_lt_tso : Lt sc tso := ⟨sc_le_tso, _, sep_sc_tso⟩
theorem tso_lt_xl : Lt tso xl := ⟨tso_le_xl, _, sep_tso_xl⟩
theorem tso_lt_ra : Lt tso ra := ⟨tso_le_ra, _, sep_tso_ra⟩
theorem tso_lt_cf : Lt tso cf := ⟨tso_le_cf, _, sep_tso_cf⟩
theorem ra_lt_cfPlain : Lt ra cfPlain := ⟨ra_le_cfPlain, _, sep_ra_cfPlain⟩
theorem cf_lt_cfPlain : Lt cf cfPlain := ⟨cf_le_cfPlain, _, sep_cf_cfPlain⟩
theorem xl_lt_top : Lt xl top := ⟨xl_le_top, _, sep_xl_top⟩
theorem cfPlain_lt_top : Lt cfPlain top := ⟨cfPlain_le_top, _, sep_cfPlain_top⟩

theorem xl_ra_incomparable : Incomparable xl ra := ⟨⟨_, sep_xl_ra⟩, _, sep_ra_xl⟩
theorem xl_cf_incomparable : Incomparable xl cf := ⟨⟨_, sep_xl_cf⟩, _, sep_cf_xl⟩
theorem xl_cfPlain_incomparable : Incomparable xl cfPlain :=
  ⟨⟨_, sep_xl_cfPlain⟩, _, sep_cfPlain_xl⟩

/-! ## Litmus behaviours move along `⊑` -/

/-- Litmus final states are monotone in the model. -/
theorem Le.axReach {M N : Model} (h : Le M N) {t : Test} {T : List (List XTrace)} {f : Final}
    (hf : AxReach t T M f) : AxReach t T N f :=
  Litmus.axReach_mono h hf

/-- A verdict `forbidden` under `N` holds under every `M ⊑ N`. -/
theorem Le.forbidden {M N : Model} (h : Le M N) {t : Test} {T : List (List XTrace)}
    (hb : Litmus.Verdict.forbidden.Holds t (AxReach t T N)) :
    Litmus.Verdict.forbidden.Holds t (AxReach t T M) :=
  Litmus.forbidden_anti (fun _ => Le.axReach h) hb

/-- **DRF-SC per litmus test**: a final state of a race-free, unsplit x86-TSO candidate is an
SC final state. -/
theorem axReach_sc_of_drf {t : Test} {T : List (List XTrace)} {f : Final}
    (hf : AxReach t T (fun x => x.Tso ∧ x.Unsplit ∧ x.DrfL) f) : AxReach t T Exec.Sc f :=
  Le.axReach (M := fun x => x.Tso ∧ x.Unsplit ∧ x.DrfL) (fun _ h => drf_sc_tso h.1 h.2.1 h.2.2) hf

end Silmaril.X86.MemoryModel.Lattice
