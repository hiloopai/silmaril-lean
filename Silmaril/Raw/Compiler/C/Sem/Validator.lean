module

public import Silmaril.Compiler.C.Sem.Runtime.Defs
public import Silmaril.Compiler.C.Sem.LirFast.Defs
public import Silmaril.Compiler.C.Sem.C1.Defs
public import Silmaril.Compiler.C.Sem.C2.Defs
public import Silmaril.Compiler.C.Sem.C3.Defs
public import Silmaril.Compiler.C.Sem.C4.Defs
public import Silmaril.Compiler.C.Sem.C5.Defs
public import Silmaril.Compiler.C.Sem.ElabC0.Defs
public import Silmaril.Compiler.C.Sem.ElabC2.Defs
public import Silmaril.Compiler.C.Sem.ElabC3.Defs
public import Silmaril.Compiler.C.Sem.ElabC4.Defs
public import Silmaril.Compiler.C.Sem.ElabC5.Defs
public import Silmaril.Compiler.C.Sem.ElabC1.Defs
public import Silmaril.Compile.Category.Pass

@[expose] public section

/-!
# Per-program validation: ccomp's Ail → Mir (C0 to C5), and C0 → Core

The two **checked** routes of the campaign (translation validation). Both are
untrusted-but-checked functions whose positive answers carry a theorem, so they are honest and
incremental: the metric counts corpus programs they accept, and they score only once their
soundness target is proved.

* `checkC0 p`: accept when ccomp's Mir for `p` linked with ccomp's C library (`ccompMirRt p`,
  `Runtime.lean`) is a valid, non-vacuous compilation of `p` under C0 at the read-back
  convention `Core.cAM` (target `Targets.ccomp_rt_tv_sound`). The checker may compute ccomp's
  output itself, and use any witness it recovers from it. `Targets.ccomp_tv_sound`, the same
  statement over `ccompMir` (no C library), is not proved for it: the programs that call
  `abort` or `exit` do not link without the library, and `checkC0` accepts them.
* `checkC1 p`: the same for C1 (`C1.lean`, flat byte memory), target
  `Targets.ccomp_rt_tv_sound_c1` (`TargetsC1.lean`); see the section on `checkC1` below.
* `checkC2 p`: the same for C2 (`C2.lean`, structs and unions), target
  `Targets.ccomp_rt_tv_sound_c2` (`TargetsC2.lean`).
* `checkC3 p`: the same for C3 (`C3.lean`, real floating types), target
  `Targets.ccomp_rt_tv_sound_c3` (`TargetsC3.lean`).
* `checkC4 p`: the same for C4 (`C4.lean`, function pointers and typed variadic calls), target
  `Targets.ccomp_rt_tv_sound_c4` (`TargetsC4.lean`).
* `checkC5 p`: the same for C5 (`C5.lean`, the heap), target `Targets.ccomp_rt_tv_sound_c5`
  (`TargetsC5.lean`).
* `elabC0 p`: a C0-only elaboration of typed Ail into Cerberus Core, `none` outside what it
  handles; whenever it answers, Core realises C0 on `p` (target `Targets.c0_core_realises`), which
  is the hypothesis of the triangle `C.Sem.factor` on `{p | (elabC0 p).isSome}`.

`elabC0` uses the structural translator and exact execution checks in `ElabC0`;
`elabC0Pass` exposes it to the composition API. This file is not frozen: the
statements in `Targets.lean` hold for the definitions here.

## `checkC0`: run and compare (stage A)

Corpus programs are closed (no input), so a program has one C0 behaviour unless it is undefined,
and its Mir has one Lir behaviour unless it gets stuck (Lir is deterministic,
`Lir.sem_deterministic`). `checkC0` computes `ccompMirRt p`, links it, runs the closed Lir
program with the **specification's own stepper** (`Lir.run`, whose final results are Lir
behaviours: `Lir.run_returned`, `Lir.run_trapped`), runs `C0.run`, and accepts when both end
and the Lir outcome reads back (`Core.readBack ctlAddress`) as C0's observation. Then the Mir
behaviours are exactly that one outcome (`mirOutcome_beh`), which is non-empty and reads back
into `C0.beh p` (`checkC0_sound`). No adequacy of the interpreter `Mir.run` is needed: the run
is `Lir.run` itself, computed with hash-map frames and a hash-map memory over the start memory
(`FastLir`, proved equal to `Lir.run`), within a fuel bound.
The run and compare is generic in the front end and the source interpreter (`checkRunWith front
run`, sound for any `front` and any `run` whose final observations are behaviours,
`checkRunWith_sound`); it runs the source first, so a program the source cannot run costs no Lir
run. Over `ccompMir` it accepted 120 of the 371 C0 dev programs:
249 of the others call `abort` or `exit`, which only ccomp's C library defines. Over
`ccompMirRt` it accepts 366; the other 5 read uninitialised locals (C0: undefined).
-/

namespace Silmaril.Compile.C.Sem

open Silmaril.Machine Silmaril.Compile.Category

/-- The Lir steps `checkC0` runs ccomp's link for. -/
def tvLirFuel : Nat := 50000000

/-- The fuel `checkC0` runs C0 with (`csem run`'s). -/
def tvC0Fuel : Nat := 100000000

/-- The Lir outcome of ccomp's link `us`, by at most `fuel` steps of `Lir.run` from the start
state of `Mir.beh`, computed with the hash-map frames of `FastLir` (equal to `Lir.run`,
`FastLir.run_abs`): `some` only when the run returns or traps. -/
def mirOutcome (fuel : Nat) (us : Array Mir.Unit) : Option Mir.LirOutcome :=
  match Mir.link mirConfig.layout us with
  | .ok l =>
    match FastLir.start l.prog 0 [] (Mir.initMem mirConfig l) with
    | some s =>
      match FastLir.run l.prog fuel s with
      | .returned vs m => some (.returned (vs, m.abs))
      | .trapped m => some (.trapped m.abs)
      | _ => none
    | none => none
  | .error _ => none

/-- A closed Lir program whose run returns or traps has that outcome as its only behaviour. -/
theorem LirProgram.beh_eq_of_behaves {q : Mir.LirProgram} {s : Lir.State Nat}
    (hs : q.prog.start q.entry q.args q.mem = some s) {b : Lir.Behavior}
    (hb : Lir.Behaves q.prog s b) (hns : b.toOutcome ≠ .undefined) : q.beh = {b.toOutcome} := by
  have hB : (Lir.sem q.prog).Beh s b.toOutcome := Lir.beh_iff_behaves.mpr hb
  unfold Mir.LirProgram.beh
  rw [hs]
  ext o
  refine ⟨fun ho => ?_, fun ho => Mir.subset_ubClose _ (Set.mem_singleton_iff.mp ho ▸ hB)⟩
  rcases ho with ho | ho
  · exact Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _) ho hB
  · exact absurd (Behaviour.Semantics.Beh.unique (Lir.sem_deterministic _)
      (show (Lir.sem q.prog).Beh s .undefined from ho) hB).symm hns

/-- **The outcome `mirOutcome` finds is the only behaviour of the Mir program.** -/
theorem mirOutcome_beh {fuel : Nat} {us : Array Mir.Unit} {O : Mir.LirOutcome}
    (h : mirOutcome fuel us = some O) : Mir.beh mirConfig us = {O} := by
  unfold mirOutcome at h
  split at h
  · rename_i l hl
    rw [Mir.beh_eq_link mirConfig us l hl]
    split at h
    · rename_i s hs
      have hs' : (Mir.toLir mirConfig l).prog.start 0 [] (Mir.initMem mirConfig l) = some s.abs := by
        change l.prog.start 0 [] (Mir.initMem mirConfig l) = _
        rw [FastLir.start_abs, hs]; rfl
      split at h
      · rename_i vs m hr
        cases h
        have hr' : Lir.run l.prog fuel s.abs = .returned vs m.abs := by rw [FastLir.run_abs, hr]; rfl
        exact LirProgram.beh_eq_of_behaves hs' (Lir.run_returned hr') (by nofun)
      · rename_i m hr
        cases h
        have hr' : Lir.run l.prog fuel s.abs = .trapped m.abs := by rw [FastLir.run_abs, hr]; rfl
        exact LirProgram.beh_eq_of_behaves hs' (Lir.run_trapped hr') (by nofun)
      · cases h
    · cases h
  · cases h

/-- Validity at `cAM` of a Mir program with a single behaviour that reads back as a behaviour
of the source. -/
theorem valid_cAM_of_beh_eq {S : Semantics} {p : Silmaril.Cerberus.Ail.TypedProgram}
    {us : Array Mir.Unit} {O : Mir.LirOutcome} (hb : Mir.beh mirConfig us = {O})
    (hO : Core.readBack ctlAddress O ∈ S p) : Valid (Core.cAM S mirConfig ctlAddress) p us := by
  refine (valid_iff_beh _ _ _).2 ⟨rfl, fun o ho => ?_⟩
  have ho' : (o : Mir.LirOutcome) ∈ Mir.beh mirConfig us := ho
  rw [hb] at ho'
  obtain rfl : o = O := ho'
  exact ⟨_, hO, rfl⟩

/-- Run and compare with explicit fuels, for the front end `front` and the source interpreter
`run`: `run` ends first (it is the cheaper run, and most rejections are its), then `front p`'s Mir
ends, with the same observation. -/
def checkRunWith (front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit))
    (run : Nat → Silmaril.Cerberus.Ail.TypedProgram → C0.Result) (lirFuel fuel : Nat)
    (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  match run fuel p with
  | .done o =>
    match front p with
    | some us =>
      match mirOutcome lirFuel us with
      | some O => decide (Core.readBack ctlAddress O = o)
      | none => false
    | none => false
  | _ => false

/-- Run and compare with explicit fuels, for the front end `front`: `front p`'s Mir and C0 both
end, with the same observation. -/
def checkFrontWith (front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit))
    (lirFuel c0Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith front C0.run lirFuel c0Fuel p

/-- `checkC0` with explicit fuels: ccomp's Mir linked with its C library and C0 both end, with
the same observation. -/
def checkC0With (lirFuel c0Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkFrontWith ccompMirRt lirFuel c0Fuel p

/-- Why `checkRunWith front run` rejects a program, where `units` is the compilation `front`
links and `name` names the source interpreter (diagnostics for `csem why`; `none` when it
accepts). -/
def checkRunWhy (front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit))
    (units : Silmaril.Cerberus.Ail.TypedProgram → Except String (Array Mir.Unit))
    (run : Nat → Silmaril.Cerberus.Ail.TypedProgram → C0.Result) (name : String)
    (lirFuel fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  match units p with
  | .error e => some s!"ccomp: {e}"
  | .ok _ =>
  match front p with
  | none => some "ccomp: no main"
  | some us =>
    match Mir.link mirConfig.layout us with
    | .error e => some s!"link: {e.message}"
    | .ok l =>
      match FastLir.start l.prog 0 [] (Mir.initMem mirConfig l) with
      | none => some "lir: no start state"
      | some s =>
        match run fuel p with
        | .outOfFuel => some s!"{name}: out of fuel"
        | .undefined why => some s!"{name}: undefined: {why}"
        | .unsupported why => some s!"{name}: unsupported: {why}"
        | .done _ =>
          match FastLir.run l.prog lirFuel s with
          | .running _ => some "lir: out of fuel"
          | .stuck => some "lir: stuck"
          | _ =>
            if checkRunWith front run lirFuel fuel p then none else some "observations differ"

/-- Why `checkFrontWith front` rejects a program, where `units` is the compilation `front`
links (diagnostics for `csem why`; `none` when it accepts). -/
def checkFrontWhy (front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit))
    (units : Silmaril.Cerberus.Ail.TypedProgram → Except String (Array Mir.Unit))
    (lirFuel c0Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy front units C0.run "c0" lirFuel c0Fuel p

/-- ccomp's units of a program linked with its C library, with ccomp's error (as `ccompMirRt`
compiles them). -/
def ccompUnitsRt (p : Silmaril.Cerberus.Ail.TypedProgram) : Except String (Array Mir.Unit) :=
  match ccompLibc with
  | none => .error "no C library"
  | some libc => Silmaril.Compile.Forks.Csem.C.compileReachableUnits
      #[{ tag := "u0", prog := libc, weak := true }, { tag := "u1", prog := p }] ["main"]

/-- Why `checkC0With` rejects a program (diagnostics for `csem why`; `none` when it accepts). -/
def checkC0Why (lirFuel c0Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkFrontWhy ccompMirRt ccompUnitsRt lirFuel c0Fuel p

/-- The Ail → Mir validator for C0, with ccomp's C library: run and compare (`checkC0With`). -/
def checkC0 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC0With tvLirFuel tvC0Fuel p

/-- **Soundness of run and compare**, for any source semantics `S` whose interpreter `run`'s
final observations are behaviours: acceptance at any fuels gives `front p`'s Mir, valid at `cAM`
for `S` and with a behaviour. -/
theorem checkRunWith_sound {S : Semantics}
    {run : Nat → Silmaril.Cerberus.Ail.TypedProgram → C0.Result}
    (hrun : ∀ {p n o}, run n p = .done o → o ∈ S p)
    {front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit)}
    {lirFuel fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkRunWith front run lirFuel fuel p = true) :
    ∃ us, front p = some us ∧
      Valid (Core.cAM S mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty := by
  unfold checkRunWith at h
  split at h
  · rename_i o ho
    split at h
    · rename_i us hus
      split at h
      · rename_i O hO
        have hb := mirOutcome_beh hO
        have he : Core.readBack ctlAddress O = o := of_decide_eq_true h
        exact ⟨us, hus, valid_cAM_of_beh_eq hb (he ▸ hrun ho), hb ▸ ⟨O, rfl⟩⟩
      · cases h
    · cases h
  · cases h

/-- **Soundness of run and compare** against C0: acceptance at any fuels gives `front p`'s Mir,
valid at `cAM` for C0 and with a behaviour. -/
theorem checkFrontWith_sound {front : Silmaril.Cerberus.Ail.TypedProgram → Option (Array Mir.Unit)}
    {lirFuel c0Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkFrontWith front lirFuel c0Fuel p = true) :
    ∃ us, front p = some us ∧
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C0.run) (front := front) (lirFuel := lirFuel) (fuel := c0Fuel)
    C0.beh_of_done h

/-- **Soundness of the validator**: acceptance at any fuels gives ccomp's Mir linked with its
C library, valid at `cAM` for C0 and with a behaviour. -/
theorem checkC0With_sound {lirFuel c0Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC0With lirFuel c0Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkFrontWith_sound h

theorem checkC0_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC0 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C0.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC0With_sound h

/-- Checked structural C0 elaboration; see `ElabC0` for the supported subset. -/
def elabC0 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC0.elaborate p

/-- Structural C1 elaboration, accepted only after exact behaviour checks. -/
def elabC1 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC1.elaborate p

/-- Checked structural C2 elaboration; unsupported syntax and unfinished or
disagreeing executions decline. See `ElabC2` for the supported subset. -/
def elabC2 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC2.elaborate p

/-- The C2 elaborator as a composable pass at the Ail/Core convention. -/
def elabC2Pass : Category.Pass (Core.cAC C2.sem) where
  run := elabC2
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C2.beh p
    rw [← (ElabC2.elaborate_sound h).2]
    exact ho

/-- Checked structural C3 elaboration; unsupported syntax and unfinished or
disagreeing executions decline. See `ElabC3` for the supported subset. -/
def elabC3 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC3.elaborate p

/-- Checked structural C4 elaboration with symbolic function pointers and indirect
calls. Variadic operations and observable integer code tokens decline. -/
def elabC4 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC4.elaborate p

/-- Checked structural C5 elaboration: C4's, with `malloc` as Core's `alloc`, `free` as a
null test and a static kill, and `calloc`/`realloc` through Core zeroing and byte-copy
procedures. Unsupported syntax and unfinished or disagreeing executions decline; see
`ElabC5`. -/
def elabC5 (p : Silmaril.Cerberus.Ail.TypedProgram) :
    Option Silmaril.Cerberus.Core.Dynamics.Program := ElabC5.elaborate p

/-- The C5 elaborator as a composable pass at the Ail/Core convention. -/
def elabC5Pass : Category.Pass (Core.cAC C5.sem) where
  run := elabC5
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C5.beh p
    rw [← (ElabC5.elaborate_sound h).2]
    exact ho

/-- The C4 elaborator as a composable pass at the Ail/Core convention. -/
def elabC4Pass : Category.Pass (Core.cAC C4.sem) where
  run := elabC4
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C4.beh p
    rw [← (ElabC4.elaborate_sound h).2]
    exact ho

/-- The C3 elaborator as a composable pass at the Ail/Core convention. -/
def elabC3Pass : Category.Pass (Core.cAC C3.sem) where
  run := elabC3
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C3.beh p
    rw [← (ElabC3.elaborate_sound h).2]
    exact ho

/-- The elaborator as a composable pass at the Ail/Core convention. -/
def elabC0Pass : Category.Pass (Core.cAC C0.sem) where
  run := elabC0
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C0.beh p
    rw [← (ElabC0.elaborate_sound h).2]
    exact ho

/-- Checked C1 realisation composes with every valid Core backend. -/
def elabC1Pass : Category.Pass (Core.cAC C1.sem) where
  run := elabC1
  sound p q h := by
    apply (Category.valid_iff_beh _ _ _).mpr
    refine ⟨rfl, ?_⟩
    intro o ho
    refine ⟨o, ?_, rfl⟩
    change o ∈ C1.beh p
    rw [← (ElabC1.elaborate_sound h).2]
    exact ho

/-- An accepted elaboration is an actual intermediate for every valid direct
lowering of that source program, with no extra simulation hypothesis. -/
theorem factor_elabC0 {p : Silmaril.Cerberus.Ail.TypedProgram}
    {q : Silmaril.Cerberus.Core.Dynamics.Program} (h : elabC0 p = some q)
    (cfg : Mir.Config) (ctl : Nat) {m : Array Mir.Unit}
    (hv : Category.Valid (Core.cAM C0.sem cfg ctl) p m) :
    Category.Valid (Core.cAC C0.sem) p q ∧ Category.Valid (Core.cCM cfg ctl) q m := by
  apply factor (F := {p}) (elaborate := fun _ => q) ?_ cfg ctl (Set.mem_singleton p) hv
  intro p' hp
  have eq : p' = p := hp
  subst p'
  exact (ElabC0.elaborate_sound h).2

/-! ## `checkC1`: run and compare against C1

The same run and compare, with C1's interpreter (`C1.run`, flat byte memory) as the source:
`checkC1` accepts when `C1.run` and ccomp's Mir linked with its C library both end, with the same
observation, and is sound for `Targets.ccomp_rt_tv_sound_c1` (`checkC1_sound`). C1's addresses
need not be ccomp's: only the observations (output and exit) are compared, so a program whose
output depends on the layout is rejected, never accepted wrongly. -/

/-- The fuel `checkC1` runs C1 with (`csem run`'s). -/
def tvC1Fuel : Nat := 100000000

/-- `checkC1` with explicit fuels: C1 and ccomp's Mir linked with its C library both end, with
the same observation. -/
def checkC1With (lirFuel c1Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C1.run lirFuel c1Fuel p

/-- The Ail → Mir validator for C1, with ccomp's C library: run and compare (`checkC1With`). -/
def checkC1 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC1With tvLirFuel tvC1Fuel p

/-- **Soundness of the C1 validator**: acceptance at any fuels gives ccomp's Mir linked with its
C library, valid at `cAM` for C1 and with a behaviour. -/
theorem checkC1With_sound {lirFuel c1Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC1With lirFuel c1Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C1.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C1.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c1Fuel)
    C1.beh_of_done h

theorem checkC1_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC1 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C1.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC1With_sound h

/-- Why `checkC1With` rejects a program (diagnostics for `csem why1`; `none` when it accepts). -/
def checkC1Why (lirFuel c1Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C1.run "c1" lirFuel c1Fuel p

/-! ## `checkC2`: run and compare against C2

Only the source interpreter changes from `checkC1`: acceptance compares the complete C2
observation with ccomp's linked Mir observation. `C2.beh_of_done` supplies the local semantic
lemma to the generic soundness proof. -/

/-- The fuel `checkC2` runs C2 with (`csem run`'s). -/
def tvC2Fuel : Nat := 100000000

/-- `checkC2` with explicit fuels: C2 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC2With (lirFuel c2Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C2.run lirFuel c2Fuel p

/-- The Ail → Mir validator for C2, with ccomp's C library: run and compare. -/
def checkC2 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC2With tvLirFuel tvC2Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C2 and with a behaviour. -/
theorem checkC2With_sound {lirFuel c2Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC2With lirFuel c2Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C2.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C2.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c2Fuel)
    C2.beh_of_done h

theorem checkC2_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC2 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C2.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC2With_sound h

/-- Why `checkC2With` rejects a program (`csem why2`; `none` when it accepts). -/
def checkC2Why (lirFuel c2Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C2.run "c2" lirFuel c2Fuel p

/-! ## `checkC3`: run and compare against C3

Only the source interpreter changes from `checkC2`: `C3.run` (real floating types) is the
source. Floats are compared through the observation alone (output and exit), so a compiler
that rounds one value differently from C3 is accepted only when no observation shows it.
`C3.beh_of_done` supplies the local semantic lemma to the generic soundness proof. -/

/-- The fuel `checkC3` runs C3 with (`csem run`'s). -/
def tvC3Fuel : Nat := 100000000

/-- `checkC3` with explicit fuels: C3 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC3With (lirFuel c3Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C3.run lirFuel c3Fuel p

/-- The Ail → Mir validator for C3, with ccomp's C library: run and compare. -/
def checkC3 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC3With tvLirFuel tvC3Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C3 and with a behaviour. -/
theorem checkC3With_sound {lirFuel c3Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC3With lirFuel c3Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C3.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C3.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c3Fuel)
    C3.beh_of_done h

theorem checkC3_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC3 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C3.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC3With_sound h

/-- Why `checkC3With` rejects a program (`csem why3`; `none` when it accepts). -/
def checkC3Why (lirFuel c3Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C3.run "c3" lirFuel c3Fuel p

/-! ## `checkC4`: run and compare against C4

Only the source interpreter changes from `checkC3`: `C4.run` (function pointers, indirect calls
and typed variadic calls) is the source. Code addresses and `va_list` cursors are internal to
both sides; only the observation (output and exit) is compared, so a program that prints a
function address or a cursor value is accepted only when ccomp's and C4's agree.
`C4.beh_of_done` supplies the local semantic lemma to the generic soundness proof. -/

/-- The fuel `checkC4` runs C4 with (`csem run`'s). -/
def tvC4Fuel : Nat := 100000000

/-- `checkC4` with explicit fuels: C4 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC4With (lirFuel c4Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C4.run lirFuel c4Fuel p

/-- The Ail → Mir validator for C4, with ccomp's C library: run and compare. -/
def checkC4 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC4With tvLirFuel tvC4Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C4 and with a behaviour. -/
theorem checkC4With_sound {lirFuel c4Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC4With lirFuel c4Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C4.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C4.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c4Fuel)
    C4.beh_of_done h

theorem checkC4_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC4 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C4.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC4With_sound h

/-- Why `checkC4With` rejects a program (`csem why4`; `none` when it accepts). -/
def checkC4Why (lirFuel c4Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C4.run "c4" lirFuel c4Fuel p

/-! ## `checkC5`: run and compare against C5

Only the source interpreter changes from `checkC4`: `C5.run` (the heap: `malloc`, `calloc`,
`realloc`, `free`) is the source. ccomp's allocator is C code of its C library, compiled and
linked with the program, so the Mir run includes it; C5's block addresses and ccomp's are
different choices, and only the observation (output and exit) is compared, so a program whose
output depends on a heap address is accepted only when ccomp's and C5's agree. Undefined heap
uses (use after `free`, double `free`, overruns) make `C5.run` undefined, and the program is
rejected. `C5.beh_of_done` supplies the local semantic lemma to the generic soundness proof. -/

/-- The fuel `checkC5` runs C5 with (`csem run`'s). -/
def tvC5Fuel : Nat := 100000000

/-- `checkC5` with explicit fuels: C5 and ccomp's Mir linked with its C library both end,
with the same observation. -/
def checkC5With (lirFuel c5Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool :=
  checkRunWith ccompMirRt C5.run lirFuel c5Fuel p

/-- The Ail → Mir validator for C5, with ccomp's C library: run and compare. -/
def checkC5 (p : Silmaril.Cerberus.Ail.TypedProgram) : Bool := checkC5With tvLirFuel tvC5Fuel p

/-- Acceptance at any fuels gives ccomp's Mir linked with its C library, valid at `cAM`
for C5 and with a behaviour. -/
theorem checkC5With_sound {lirFuel c5Fuel : Nat} {p : Silmaril.Cerberus.Ail.TypedProgram}
    (h : checkC5With lirFuel c5Fuel p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C5.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkRunWith_sound (run := C5.run) (front := ccompMirRt) (lirFuel := lirFuel) (fuel := c5Fuel)
    C5.beh_of_done h

theorem checkC5_sound {p : Silmaril.Cerberus.Ail.TypedProgram} (h : checkC5 p = true) :
    ∃ us, ccompMirRt p = some us ∧
      Valid (Core.cAM C5.sem mirConfig ctlAddress) p us ∧ (Mir.beh mirConfig us).Nonempty :=
  checkC5With_sound h

/-- Why `checkC5With` rejects a program (`csem why5`; `none` when it accepts). -/
def checkC5Why (lirFuel c5Fuel : Nat) (p : Silmaril.Cerberus.Ail.TypedProgram) : Option String :=
  checkRunWhy ccompMirRt ccompUnitsRt C5.run "c5" lirFuel c5Fuel p

end Silmaril.Compile.C.Sem
