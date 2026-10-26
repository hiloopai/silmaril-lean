module

public import Silmaril.Process.LPS.Problems.Basic
public import Silmaril.Process.LPS.Machines.X86NativeLaunch
public import Silmaril.Process.LPS.RunHelpers
public import Silmaril.Data.IncludeBytes
public import Silmaril.Process.LPS.Machines.X86LaunchControls

/-!
# OSS Verify problems on native x86-64

`Problems.Basic` states a harness's problems through the `Shapes` of `Shapes.v`, which run the
reference (asm-generic numbered) syscall table with the RISC-V entry stack. On x86-64 that is
the renumbering machine `Machines.x86Ext`, which is right only where both ISAs share a layout.
This file gives each shape of `Shapes.v` again over the native x86-64 launch of
`Machines.X86NativeLaunch`, so that an x86-64 statement is the analogue of the riscv64 one:

* the image is an `X86Launch.Snapshot` (ELF header, program headers and the loaded image) and an
  entry is valid when `X86Launch.ValidEntry` holds (fixed-address static `ET_EXEC`, x86-64
  SysV stack, x86-64 user address space);
* the run is `X86Launch.runWith` with `NativeX86.extendedSyscallSpec` (native x86-64 numbers,
  `arch_prctl(ARCH_SET_FS)`) and the native refusal filter of the reading
  (`NativeX86.defaultRefusalFilter`, or no filter for the may-fail reading, as `run`);
* budget refusal is `NativeX86.RunBudgetRefusedWithStack` with the same stack, table and filter;
* the inputs are the shared `ValidInputCore` with an `AT_HWCAP` value in the problem's
  `HwcapDomain` (every value by default, since real x86-64 kernels advertise `CPUID.1:EDX`) and
  the `abort()` stance of the shape (`ValidInput`, as the riscv64
  `valid_input`/`valid_input_abort` fix `abortTerminal`). The `noHwcap` domain is
  `X86Launch.ValidInput` (`validInput_noHwcap`), a narrower variant implied by the default
  (`NativeProblem.denote_noHwcap`).

Each shape below is the `Shapes.lean` definition with exactly these four substitutions; the
budgets, readings, exit sets, classifier limits and verdicts are the shared `Shapes`/LPS
constants. `_rv64gc` shapes restrict the riscv64 hardware capabilities to RV64GC; x86-64 has no
such base value, so on x86-64 each `_rv64gc` shape is its plain form over the whole domain
(`AgreeShape.denoteX86`), which is at least as strong.

`NativeProblem.denote?` is `Problem.denote?` with these shapes. As there (#3670), a statement
about a build without an image, or a bound statement without a distribution, is untranslated
(`none`): neither provable nor refutable, never `False` (upstream's bound holds at `b = 1`). A
snapshot on which `X86Launch.ValidEntry` never holds would make a statement vacuous, so
`ImageWf` (the analogue of `Images.v` `image_wf`) requires room for the launch envelope's stack
and a valid break besides `X86Launch.ValidSnapshot`, and `imageWf_entry` proves that on such an
image every valid input has a valid entry. `NativeProblem.ImagesValid` is `ImageWf` for every
image (`<build>_wf`), and the classifier of `agreementDecidable` must satisfy it.

This is the **reviewed-default, minimal-launch** lattice point: the table declines every call
outside the twenty-two reviewed reference arms and `arch_prctl` (`writev`, `readv`, `lseek`,
`open`, `unlink` among them), so a run that reaches one fails closed. The default statements of
the generated modules are `Problems.NativeX86Complete`'s, over the complete native table and the
realistic launch; that module says how the two points relate (no implication either way in
general).

Not claimed: that the native x86-64 ABI and the reference ABI agree, or that a snapshot is the
image of particular ELF bytes (`X86Launch` leaves that binding to the loader; the generated
image modules record the ELF's SHA-256).
-/

@[expose] public section
set_option autoImplicit false

namespace Silmaril.Process.LPS.Problems.NativeX86

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes Silmaril.Process.LPS.Machines

abbrev Snapshot := X86Launch.Snapshot

/-! ## Inputs

`X86Launch.ValidInput` fixes `AT_HWCAP = 0`. A real x86-64 kernel advertises `CPUID.1:EDX`
there, which is never zero, so no real launch is in that domain. The statements here range over
a `HwcapDomain` of `AT_HWCAP` values instead: `anyHwcap` (every value, a superset of every real
launch) by default, and `noHwcap` (the `X86Launch.ValidInput` profile) as a narrower variant.
Every shape is antitone in the domain (`NativeProblem.denote_narrow`): a statement over
`anyHwcap` implies the same statement over `noHwcap`. -/

/-- The `AT_HWCAP` values a statement ranges over. -/
abbrev HwcapDomain := Word → Prop

/-- Every `AT_HWCAP` value: the default domain, containing every `CPUID.1:EDX`. -/
def anyHwcap : HwcapDomain := fun _ => True

/-- The minimal launch profile of `X86Launch.ValidInput`: no capability advertised. -/
def noHwcap : HwcapDomain := fun h => h = 0

/-- The native refusal filter of a reading: none for the may-fail reading (`run`), the native
filter of the environment otherwise (`run_scfg`). -/
def readingFilter : Reading → RefusalFilter
  | none => noFilter
  | some cfg => NativeX86.defaultRefusalFilter cfg

/-- The native run of a snapshot under a reading (`runIn`). -/
def runIn (isa : UserIsa) (r : Reading) (snap : Snapshot) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Behavior :=
  X86Launch.runWith isa NativeX86.extendedSyscallSpec (readingFilter r) snap lim en inp

/-- Native refusal for budget under a reading (`BudgetRefusedIn`). -/
def BudgetRefusedIn (isa : UserIsa) (r : Reading) (snap : Snapshot) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  NativeX86.RunBudgetRefusedWithStack isa X86Launch.entryStack NativeX86.extendedSyscallSpec
    (readingFilter r) snap.image lim en inp

/-- The x86-64 valid inputs over a hardware-capability domain, with an `abort()` stance
(`valid_input`, `valid_input_abort`). -/
def ValidInput (hw : HwcapDomain) (abortModelled : Bool) (inp : ProcInput) : Prop :=
  ValidInputCore inp ∧ hw inp.hwcap ∧ inp.abortTerminal = abortModelled

/-- Over `noHwcap`, the inputs are exactly `X86Launch.ValidInput` with the stance. -/
theorem validInput_noHwcap (a : Bool) (inp : ProcInput) :
    ValidInput noHwcap a inp ↔ X86Launch.ValidInput inp ∧ inp.abortTerminal = a := by
  simp only [ValidInput, noHwcap, X86Launch.ValidInput, and_assoc]

/-- A smaller hardware-capability domain has fewer valid inputs. -/
theorem ValidInput.widen {hw hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {a : Bool}
    {inp : ProcInput} (v : ValidInput hw' a inp) : ValidInput hw a inp :=
  ⟨v.1, sub _ v.2.1, v.2.2⟩

/-- `MustExitIn` over the native launch. -/
def MustExitIn (isa : UserIsa) (r : Reading) (S : List Word) (snap : Snapshot) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Prop :=
  MustExitInAt snap.image.segments NativeX86.extendedSyscallSpec (readingFilter r) S
    (X86Launch.init isa snap en lim inp)

/-! ## Images

`ImageWf` is the anti-vacuity obligation on a snapshot (`Images.v` `image_wf`). The riscv64
`ImageWf` makes `ValidEntry` inhabited for every valid input (`imageWf_entry`); on x86-64,
`X86Launch.ValidEntry` additionally needs every segment below the stack reservation of some
stack pointer in the launch window, which `X86Launch.ValidSnapshot` does not imply. `ImageWf`
adds that room (`EntryRoom`, at the lowest stack pointer of the window) and a satisfiable break,
and `imageWf_entry` proves that every valid input then has a valid entry. -/

/-- Every segment ends below the 8 MiB stack reservation of the lowest stack pointer of the
x86-64 launch window. -/
def EntryRoom (segs : List Segment) : Prop :=
  ∀ g ∈ segs, (g.base : Int) + g.size ≤ x86LaunchBounds.spWindowLo - stackMaxSize

/-- The native-launch `x86-64` analogue of `ImageWf`: a valid launch image with room for the
launch envelope's stack and a valid break. -/
def ImageWf (isa : UserIsa) (snap : Snapshot) : Prop :=
  X86Launch.ValidSnapshot isa snap ∧ imageBrkSatisfiable snap.image.segments = true ∧
    EntryRoom snap.image.segments

theorem stringAddrs_length (base : Word) (l : List (List Byte)) :
    (stringAddrs base l).1.length = l.length := by
  induction l generalizing base with
  | nil => rfl
  | cons s rest ih => simp only [stringAddrs, List.length_cons, ih]

theorem flatMap_wordLe8_length (l : List Word) : (l.flatMap wordLe8).length = 8 * l.length := by
  induction l with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.flatMap_cons, List.length_append, ih, wordLe8, List.length_map,
      List.length_range, List.length_cons]
    omega

theorem buildAuxv_length (l : List (Word × Word)) : (buildAuxv l).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    have step : buildAuxv (e :: rest) = (wordLe8 e.1 ++ wordLe8 e.2) ++ buildAuxv rest := by
      simp only [buildAuxv, List.flatMap_cons]
    rw [step, List.length_append, List.length_append, ih]
    simp only [wordLe8, List.length_map, List.length_range, List.length_cons]
    omega

theorem flattenStrings_length (l : List (List Byte)) :
    ((flattenStrings l).length : Int) = totalArgBytes l := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    have step : flattenStrings (a :: rest) = (a ++ [0]) ++ flattenStrings rest := by
      simp only [flattenStrings, List.flatMap_cons]
    have total : totalArgBytes (a :: rest) = a.length + 1 + totalArgBytes rest := rfl
    rw [step, total, List.length_append, List.length_append, List.length_singleton]
    push_cast
    omega

/-- The valid argument and environment limits bound the x86-64 entry block. -/
theorem stackBytes_length_le (img : Image) (en : ExecEntry) (inp : ProcInput)
    (ha : ValidArgv inp.argv) (he : ValidEnvp inp.envp) :
    ((X86Launch.stackBytes img en inp).length : Int) ≤ 2300000 := by
  have fa := flattenStrings_length inp.argv
  have fe := flattenStrings_length inp.envp
  have pad : X86Launch.randomPadding inp.argv inp.envp < 16 := by
    unfold X86Launch.randomPadding
    exact Nat.mod_lt _ (by decide)
  have haLen := ha.2.1
  have haBytes := ha.2.2.1
  have heLen := he.1
  have heBytes := he.2.1
  simp only [X86Launch.stackBytes, List.length_append, flatMap_wordLe8_length,
    stringAddrs_length, buildAuxv_length, X86Launch.auxiliaryEntries_length, wordLe8,
    List.length_map, List.length_range, List.length_replicate, atRandomBytes,
    X86Launch.platformBytes, X86Launch.auxiliaryCount, List.length_cons, List.length_nil]
  push_cast
  omega

/-- On a well-formed image every valid input has a valid entry: the stack pointer
`0x7fff7ffff000` (inside the window, which reaches lower since the x86 launch bounds cover
x86-64 stack ASLR), a valid break, and the highest mmap base. -/
theorem imageWf_entry (isa : UserIsa) (snap : Snapshot) (wf : ImageWf isa snap)
    (inp : ProcInput) (core : ValidInputCore inp) : ∃ en, X86Launch.ValidEntry isa snap en inp := by
  obtain ⟨valid, brkOk, room⟩ := wf
  obtain ⟨brk, hbrk⟩ := imageBrkSatisfiable_sound _ brkOk
  let en : ExecEntry := ⟨0x7fff7ffff000, brk, 0x7ffff7fff000, ⟨0, fun _ => 0⟩⟩
  have len := stackBytes_length_le snap.image en inp core.1 core.2.1
  have hsp : uns en.sp = 0x7fff7ffff000 :=
    (by decide : uns (0x7fff7ffff000 : Word) = 0x7fff7ffff000)
  have hmm : uns en.mmapBase = 0x7ffff7fff000 :=
    (by decide : uns (0x7ffff7fff000 : Word) = 0x7ffff7fff000)
  have lo : x86LaunchBounds.spWindowLo ≤ 0x7fff7ffff000 := by decide
  refine ⟨en, valid, ?_, ?_, ?_, hbrk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsp]; exact lo
  · rw [hsp]; decide
  · rw [hsp]; decide
  · rw [hmm]; decide
  · rw [hmm]; decide
  · rw [hmm]; decide
  · have top : x86AddressSpace.taskSize = 0x7ffffffff000 := rfl
    unfold entryPageTop entryBlockTop pageRoundUp pageSize
    rw [hsp, top]
    omega
  · intro g mem
    have := room g mem
    rw [hsp]
    unfold stackMaxSize at *
    omega

/-! ### Byte facts of generated snapshots

A generated snapshot holds each segment's bytes as `IncludeBytes.decode` chunk literals. Their
length and the readability of a range follow from the literals' count and the segment extents,
without decoding a byte. -/

theorem length_bytesChunks (c len : Nat) (cs : List Nat) :
    (Silmaril.IncludeBytes.bytesChunks c len cs).length = min len (c * cs.length) := by
  induction cs generalizing len with
  | nil => simp [Silmaril.IncludeBytes.bytesChunks]
  | cons x cs ih =>
    rw [Silmaril.IncludeBytes.bytesChunks_cons, List.length_append,
      Silmaril.IncludeBytes.length_bytesLE, ih, List.length_cons, Nat.mul_succ]
    generalize c * cs.length = m
    omega

/-- The bytes of a generated segment fill it. -/
theorem decode_bytes_length (c len : Nat) (cs : List Nat) (h : len ≤ c * cs.length) :
    ((Silmaril.IncludeBytes.decode c len cs).data.toList.map UInt8.toBitVec).length = len := by
  rw [List.length_map]
  change (Silmaril.IncludeBytes.bytesChunks c len cs).length = len
  rw [length_bytesChunks]
  omega

theorem findSegment_some {segs : List Segment} {a n : Int} {g : Segment}
    (h : findSegment segs a n = some g) : (g.base : Int) ≤ a ∧ a + n ≤ g.base + g.size := by
  induction segs with
  | nil => simp [findSegment] at h
  | cons s rest ih =>
    simp only [findSegment] at h
    split at h
    · cases h
      assumption
    · exact ih h

theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (∀ x ∈ l, (f x).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
      (mapM_isSome f l fun y m => h y (List.mem_cons_of_mem _ m))
    simp [List.mapM_cons, hb, hbs]

/-- A range inside a readable segment whose bytes fill it is readable. -/
theorem memoryRead_isSome {segs : List Segment} {addr : Word} {n : Nat} {g : Segment}
    (hf : findSegment segs (uns addr) n = some g) (hr : g.readable = true)
    (hl : g.bytes.length = g.size) : (memoryRead segs addr n).isSome = true := by
  have b := findSegment_some hf
  unfold memoryRead
  rw [hf]
  simp only [hr, ↓reduceIte]
  apply mapM_isSome
  intro k mem
  have hk := List.mem_range.mp mem
  unfold Segment.byteAt
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- `memoryRead_isSome` for a range in the first segment. -/
theorem memoryRead_head_isSome {g : Segment} {rest : List Segment} {addr : Word} {n : Nat}
    (cover : (g.base : Int) ≤ uns addr ∧ uns addr + n ≤ g.base + g.size) (hr : g.hasPerm 'r' = true)
    (hl : g.bytes.length = g.size) : (memoryRead (g :: rest) addr n).isSome = true :=
  memoryRead_isSome (by simp only [findSegment, cover, and_self, ↓reduceIte]) (g.readable_eq.trans hr) hl

/-- A well-formed image is a valid launch snapshot. -/
theorem ImageWf.validSnapshot {isa : UserIsa} {snap : Snapshot} (wf : ImageWf isa snap) :
    X86Launch.ValidSnapshot isa snap := wf.1

/-! ### `ImageWf` is satisfiable

The control executable of `X86LaunchControls` (one PT_LOAD segment, checked against its ELF
bytes) is a well-formed image, and its control input is valid over both domains, so the
premises of every shape are inhabited on it. -/

theorem controls_imageWf : ImageWf Machines.x86ExtNative X86Launch.Controls.snapshot :=
  ⟨X86Launch.Controls.snapshot_valid, by decide +kernel, by
    intro g mem
    simp only [X86Launch.Controls.snapshot, X86Launch.Controls.image, List.mem_cons,
      List.not_mem_nil, or_false] at mem
    subst mem
    decide +kernel⟩

theorem controls_input_valid (hw : HwcapDomain) (h0 : hw 0) :
    ValidInput hw false X86Launch.Controls.input :=
  ⟨X86Launch.Controls.input_valid.1, h0, rfl⟩

theorem controls_launch_inhabited :
    ∃ en inp, X86Launch.ValidEntry Machines.x86ExtNative X86Launch.Controls.snapshot en inp ∧
      ValidInput noHwcap false inp ∧ ValidInput anyHwcap false inp :=
  ⟨_, _, X86Launch.Controls.entry_valid, controls_input_valid _ rfl,
    controls_input_valid _ trivial⟩

section Agreement

variable (isaP isaS : UserIsa) (hw : HwcapDomain)

/-- The agreement conclusion of every agreement shape, at a reading and an `abort()` stance. -/
def agreement (r : Reading) (abortModelled : Bool) (limPlain limSan : Int) (plain san : Snapshot) :
    Prop :=
  ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
    X86Launch.ValidEntry isaP plain enPlain inp → X86Launch.ValidEntry isaS san enSan inp →
    ValidInput hw abortModelled inp →
    ¬ BudgetRefusedIn isaP r plain limPlain enPlain inp →
    (if abortModelled then ErrorFreeUnkilled (runIn isaP r plain limPlain enPlain inp)
      else ErrorFree (runIn isaP r plain limPlain enPlain inp)) ∧
    (if abortModelled then ErrorFreeUnkilled (runIn isaS r san limSan enSan inp)
      else ErrorFree (runIn isaS r san limSan enSan inp)) ∧
    TraceEquiv (runIn isaP r plain limPlain enPlain inp).traces
      (runIn isaS r san limSan enSan inp).traces

/-- `Shapes.agrees` on native x86-64. -/
def agrees (limPlain limSan : Int) (plain san : Snapshot) : Prop :=
  agreement isaP isaS hw none false limPlain limSan plain san

/-- `Shapes.agreesIn` on native x86-64. -/
def agreesIn (env : SpuriousCfg) (limPlain limSan : Int) (plain san : Snapshot) : Prop :=
  agreement isaP isaS hw (some env) false limPlain limSan plain san

/-- `Shapes.agreesAbortModelled` on native x86-64. -/
def agreesAbortModelled (limPlain limSan : Int) (plain san : Snapshot) : Prop :=
  agreement isaP isaS hw none true limPlain limSan plain san

/-- `Shapes.agreesInAbortModelled` on native x86-64. -/
def agreesInAbortModelled (env : SpuriousCfg) (limPlain limSan : Int) (plain san : Snapshot) :
    Prop :=
  agreement isaP isaS hw (some env) true limPlain limSan plain san

/-- Written out, `agrees` is `Shapes.agrees` with the native run, budget, entry and inputs. -/
theorem agrees_unfold (lp ls : Int) (p s : Snapshot) :
    agrees isaP isaS hw lp ls p s ↔
      ∀ (enPlain enSan : ExecEntry) (inp : ProcInput),
        X86Launch.ValidEntry isaP p enPlain inp → X86Launch.ValidEntry isaS s enSan inp →
        ValidInput hw false inp → ¬ BudgetRefusedIn isaP none p lp enPlain inp →
        ErrorFree (runIn isaP none p lp enPlain inp) ∧ ErrorFree (runIn isaS none s ls enSan inp) ∧
          TraceEquiv (runIn isaP none p lp enPlain inp).traces (runIn isaS none s ls enSan inp).traces :=
  Iff.rfl

variable {isaP isaS hw} in
/-- Agreement over a domain implies agreement over a smaller one. -/
theorem agreement.narrow {hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {r : Reading}
    {a : Bool} {lp ls : Int} {p s : Snapshot} (h : agreement isaP isaS hw r a lp ls p s) :
    agreement isaP isaS hw' r a lp ls p s :=
  fun e₁ e₂ inp v₁ v₂ vi hb => h e₁ e₂ inp v₁ v₂ (vi.widen sub) hb

end Agreement

section Halting

variable (isa : UserIsa) (hw : HwcapDomain)

/-- `Shapes.haltsWithinBudget` on native x86-64. -/
def haltsWithinBudget (lim : Int) (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), X86Launch.ValidEntry isa snap en inp →
    ValidInput hw false inp →
    ¬ BudgetRefusedIn isa (some forcedOnlyCfg) snap lim en inp →
    MustExitIn isa (some forcedOnlyCfg) allowed snap lim en inp

/-- `Shapes.haltsMayFail` on native x86-64. -/
def haltsMayFail (allowed : List Word) (snap : Snapshot) : Prop :=
  ∀ (en : ExecEntry) (inp : ProcInput), X86Launch.ValidEntry isa snap en inp →
    ValidInput hw false inp →
    MustExitIn isa (some mayFailCfg) allowed snap sourceAllocLimit en inp

/-- `halts_within_budget_mono`: a larger exit set is weaker. -/
theorem haltsWithinBudget_mono {lim : Int} {S₁ S₂ : List Word} {snap : Snapshot} (sub : S₁ ⊆ S₂)
    (h : haltsWithinBudget isa hw lim S₁ snap) : haltsWithinBudget isa hw lim S₂ snap :=
  fun en inp he hi hb => Shapes.mustExitInAt_mono isa sub (h en inp he hi hb)

/-- `halts_may_fail_mono`. -/
theorem haltsMayFail_mono {S₁ S₂ : List Word} {snap : Snapshot} (sub : S₁ ⊆ S₂)
    (h : haltsMayFail isa hw S₁ snap) : haltsMayFail isa hw S₂ snap :=
  fun en inp he hi => Shapes.mustExitInAt_mono isa sub (h en inp he hi)

variable {isa hw} in
theorem haltsWithinBudget.narrow {hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {lim : Int}
    {S : List Word} {snap : Snapshot} (h : haltsWithinBudget isa hw lim S snap) :
    haltsWithinBudget isa hw' lim S snap :=
  fun en inp he hi hb => h en inp he (hi.widen sub) hb

variable {isa hw} in
theorem haltsMayFail.narrow {hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {S : List Word}
    {snap : Snapshot} (h : haltsMayFail isa hw S snap) : haltsMayFail isa hw' S snap :=
  fun en inp he hi => h en inp he (hi.widen sub)

end Halting

section Classification

variable (isa : UserIsa) (hw : HwcapDomain)

/-- The x86-64 valid finite inputs (`valid_fin_input`). -/
def ValidFinInput (f : FinProcInput) : Prop := ValidInput hw false f.toProcInput

/-- `GoodInputS` on native x86-64: under the reading, at the shared source and target limits,
both builds are error free and agree, for every entry draw. -/
def GoodInputS (env : SpuriousCfg) (plain san : Snapshot) (inp : ProcInput) : Prop :=
  ∀ en₁ en₂, X86Launch.ValidEntry isa plain en₁ inp → X86Launch.ValidEntry isa san en₂ inp →
    ErrorFree (runIn isa (some env) plain sourceAllocLimit en₁ inp) ∧
      ErrorFree (runIn isa (some env) san targetAllocLimit en₂ inp) ∧
      TraceEquiv (runIn isa (some env) plain sourceAllocLimit en₁ inp).traces
        (runIn isa (some env) san targetAllocLimit en₂ inp).traces

/-- `Shapes.disagreesAtMost` on native x86-64. -/
def disagreesAtMost (env : SpuriousCfg) (w : FinProcInput → ℚ) (M : ℚ) (plain san : Snapshot)
    (b : ℚ) : Prop :=
  ∀ l : List FinProcInput, (l.map (·.core)).Nodup →
    (∀ f ∈ l, ValidFinInput hw f ∧ ¬ GoodInputS isa env plain san f.toProcInput) →
    sumWeights w l ≤ b * M

/-- `Shapes.classifies` on native x86-64: the x86-64 program `C` exits `0` exactly on the inputs
where the builds agree, and `1` otherwise, in the forced-only reading. -/
def classifies (env : SpuriousCfg) (plain san C : Snapshot) : Prop :=
  ∀ f : FinProcInput, ValidFinInput hw f → ∀ en : ExecEntry,
    X86Launch.ValidEntry isa C en f.toProcInput →
    (MustExitIn isa (some forcedOnlyCfg) [verdictAccept] C classifierAllocLimit en f.toProcInput ↔
      GoodInputS isa env plain san f.toProcInput) ∧
    (MustExitIn isa (some forcedOnlyCfg) [verdictAccept] C classifierAllocLimit en f.toProcInput ∨
      MustExitIn isa (some forcedOnlyCfg) [verdictReject] C classifierAllocLimit en f.toProcInput)

/-- `Shapes.agreementDecidable` on native x86-64: some well-formed x86-64 launch image
classifies. `ImageWf` makes the classifier's entry quantifier inhabited on every valid input
(`imageWf_entry`), so a classifier cannot hold vacuously. -/
def agreementDecidable (env : SpuriousCfg) (plain san : Snapshot) : Prop :=
  ∃ C : Snapshot, ImageWf isa C ∧ classifies isa hw env plain san C

/-- The classifier's launch quantifier is inhabited on every valid input. -/
theorem classifies_entry {C : Snapshot} (wf : ImageWf isa C) (f : FinProcInput)
    (v : ValidFinInput hw f) : ∃ en, X86Launch.ValidEntry isa C en f.toProcInput :=
  imageWf_entry isa C wf _ v.1

variable {isa hw} in
theorem disagreesAtMost.narrow {hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {env : SpuriousCfg}
    {w : FinProcInput → ℚ} {M : ℚ} {p s : Snapshot} {b : ℚ}
    (h : disagreesAtMost isa hw env w M p s b) : disagreesAtMost isa hw' env w M p s b :=
  fun l nd hl => h l nd fun f mem => ⟨(hl f mem).1.widen sub, (hl f mem).2⟩

variable {isa hw} in
theorem agreementDecidable.narrow {hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h)
    {env : SpuriousCfg} {p s : Snapshot} (h : agreementDecidable isa hw env p s) :
    agreementDecidable isa hw' env p s := by
  obtain ⟨C, wf, cl⟩ := h
  exact ⟨C, wf, fun f vf en ve => cl f (vf.widen sub) en ve⟩

end Classification

/-- The meaning of an agreement shape on native x86-64 (`AgreeShape.denote`). The `_rv64gc`
shapes restrict the riscv64 hardware capabilities to RV64GC; x86-64 has no such base-ISA value,
so each is read as its plain form over the whole domain `hw`, which is at least as strong. -/
def _root_.Silmaril.Process.LPS.Problems.AgreeShape.denoteX86 (isaP isaS : UserIsa)
    (hw : HwcapDomain) (limP limS : Int) (plain san : Snapshot) : AgreeShape → Prop
  | .agrees | .rv64gc => agrees isaP isaS hw limP limS plain san
  | .agreesIn env | .inRv64gc env => agreesIn isaP isaS hw env.cfg limP limS plain san
  | .abortModelled | .abortModelledRv64gc => agreesAbortModelled isaP isaS hw limP limS plain san
  | .inAbortModelled env => agreesInAbortModelled isaP isaS hw env.cfg limP limS plain san

theorem _root_.Silmaril.Process.LPS.Problems.AgreeShape.denoteX86_narrow {isaP isaS : UserIsa}
    {hw hw' : HwcapDomain} (sub : ∀ h, hw' h → hw h) {lp ls : Int} {p s : Snapshot}
    (shape : AgreeShape) (h : shape.denoteX86 isaP isaS hw lp ls p s) :
    shape.denoteX86 isaP isaS hw' lp ls p s := by
  cases shape <;> exact agreement.narrow sub h

/-- A harness on native x86-64: the machine (`x86ExtNative`, or another x86-64 `UserIsa` such
as a Wire machine), the launch snapshot of each build, and the `AT_HWCAP` domain the statements
range over (every value by default). -/
structure NativeProblem where
  harness : Harness
  isa : UserIsa
  images : Build → Option Snapshot
  hwcap : HwcapDomain := anyHwcap

namespace NativeProblem

variable (p : NativeProblem)

/-- `k` at the image of `b`, or `none` where the build has none. -/
def withImage {α : Type _} (b : Build) (k : Snapshot → α) : Option α :=
  (p.images b).map k

/-- `k` at the plain image and the image of `san`, or `none` where one is missing. -/
def withImages {α : Type _} (san : Build) (k : Snapshot → Snapshot → α) : Option α :=
  (p.images .plain).bind fun plain => p.withImage san (k plain)

/-- The meaning of a statement on native x86-64: `Problem.denote?` with the native shapes. A
statement naming a build without an image, or a bound statement without a distribution, is
untranslated (`none`), as in `Problems.Problem.denote?` (#3670): neither provable nor refutable,
in particular not `False`. -/
def denote? : (s : Statement) → Option s.Sort
  | .agrees san budgets shape =>
    p.withImages san fun plain sanImg =>
      shape.denoteX86 p.isa p.isa p.hwcap budgets.budgets.limSource budgets.budgets.limTarget
        plain sanImg
  | .haltsWithinBudget b budgets exits =>
    p.withImage b fun img => haltsWithinBudget p.isa p.hwcap budgets.budgets.limSource exits.codes img
  | .haltsMayFail b exits =>
    p.withImage b fun img => haltsMayFail p.isa p.hwcap exits.codes img
  | .disagreesAtMost san env _ =>
    p.harness.distribution.bind fun d =>
      p.withImages san fun plain sanImg bound =>
        disagreesAtMost p.isa p.hwcap env.cfg d.w d.M plain sanImg bound
  | .agreementDecidable san env _ =>
    p.withImages san fun plain sanImg => agreementDecidable p.isa p.hwcap env.cfg plain sanImg

/-- Whether the statement is untranslated (`Problems.Problem.isUntranslated`). -/
def isUntranslated (s : Statement) : Bool :=
  (s.needsDistribution && p.harness.distribution.isNone) ||
    s.builds.any fun b => (p.images b).isNone

/-- A statement has no Lean proposition exactly when it is untranslated. -/
theorem denote?_eq_none_iff (s : Statement) :
    p.denote? s = none ↔ p.isUntranslated s = true := by
  rcases s with ⟨san, _, _⟩ | ⟨b, _, _⟩ | ⟨b, _⟩ | ⟨san, _, _⟩ | ⟨san, _, _⟩ <;>
    simp only [denote?, isUntranslated, Statement.needsDistribution, Statement.builds,
      withImages, withImage, List.any_cons, List.any_nil]
  · cases p.images .plain <;> cases p.images san <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images b <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images b <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
    (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h
  · cases p.images .plain <;> cases p.images san <;> (try simp) <;>
    first | rfl | exact fun h => Option.some_ne_none _ h

/-- Every image is well formed: the anti-vacuity obligation (`Images.v` `<build>_wf`). With it,
every valid input has a valid entry on every image (`imagesValid_entry`), so no agreement or
halting premise is empty because of the image. -/
def ImagesValid : Prop := ∀ b img, p.images b = some img → ImageWf p.isa img

theorem imagesValid_entry (v : p.ImagesValid) {b : Build} {img : Snapshot}
    (h : p.images b = some img) (inp : ProcInput) (core : ValidInputCore inp) :
    ∃ en, X86Launch.ValidEntry p.isa img en inp :=
  imageWf_entry p.isa img (v b img h) inp core

/-- Every statement names only builds the problem has images of. -/
def Scoped : Prop :=
  ∀ s ∈ p.harness.statements, ∀ b ∈ s.2.builds, (p.images b).isSome = true

/-- The same problem over another `AT_HWCAP` domain. -/
def withHwcap (hw : HwcapDomain) : NativeProblem := { p with hwcap := hw }

/-- `P` implies `Q` as statements of the sort of `s` (for every bound, for a bound statement). -/
def Implies : (s : Statement) → s.Sort → s.Sort → Prop
  | .agrees .., P, Q => P → Q
  | .haltsWithinBudget .., P, Q => P → Q
  | .haltsMayFail .., P, Q => P → Q
  | .disagreesAtMost .., P, Q => ∀ b, P b → Q b
  | .agreementDecidable .., P, Q => P → Q

/-- Both untranslated, or both translated with the first implying the second. -/
def ImpliesOpt (s : Statement) : Option s.Sort → Option s.Sort → Prop
  | some P, some Q => Implies s P Q
  | none, none => True
  | _, _ => False

/-- Every statement over a domain implies the same statement over a smaller domain: in
particular the default `anyHwcap` statements imply the `noHwcap` (`X86Launch.ValidInput`)
ones. Untranslated statements stay untranslated. -/
theorem denote?_narrow (hw : HwcapDomain) (sub : ∀ h, hw h → p.hwcap h) (s : Statement) :
    ImpliesOpt s (p.denote? s) ((p.withHwcap hw).denote? s) := by
  cases s with
  | agrees san budgets shape =>
    simp only [denote?, withImages, withImage, withHwcap]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact shape.denoteX86_narrow sub
  | haltsWithinBudget b budgets exits =>
    simp only [denote?, withImage, withHwcap]
    cases p.images b <;> first | trivial | exact haltsWithinBudget.narrow sub
  | haltsMayFail b exits =>
    simp only [denote?, withImage, withHwcap]
    cases p.images b <;> first | trivial | exact haltsMayFail.narrow sub
  | disagreesAtMost san env rv =>
    simp only [denote?, withImages, withImage, withHwcap]
    cases p.harness.distribution <;> cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact fun _ => disagreesAtMost.narrow sub
  | agreementDecidable san env rv =>
    simp only [denote?, withImages, withImage, withHwcap]
    cases p.images .plain <;> cases p.images san <;>
      first | trivial | exact agreementDecidable.narrow sub

/-- The default statements imply their `X86Launch.ValidInput` (`AT_HWCAP = 0`) variants. -/
theorem denote?_noHwcap (s : Statement) (default : p.hwcap = anyHwcap) :
    ImpliesOpt s (p.denote? s) ((p.withHwcap noHwcap).denote? s) :=
  p.denote?_narrow noHwcap (fun h _ => by rw [default]; trivial) s

/-- A statement about a build without an image is untranslated. -/
theorem denote?_halts_absent (b : Build) (budgets : BudgetChoice) (exits : ExitChoice)
    (absent : p.images b = none) : p.denote? (.haltsWithinBudget b budgets exits) = none := by
  simp only [denote?, withImage, absent]
  rfl

theorem denote?_agrees_absent (san : Build) (budgets : BudgetChoice) (shape : AgreeShape)
    (absent : p.images san = none) : p.denote? (.agrees san budgets shape) = none := by
  simp only [denote?, withImages, withImage, absent]
  cases p.images .plain <;> rfl

/-- Without a distribution, a bound statement is untranslated, whatever the images. -/
theorem denote?_disagreesAtMost_of_none (absent : p.harness.distribution = none) (san : Build)
    (env : EnvChoice) (rv : Bool) : p.denote? (.disagreesAtMost san env rv) = none := by
  simp [denote?, absent]

end NativeProblem

/-! ## Pinned layouts

The generated harness modules do not hold the bytes of a build (the binaries are not committed);
they pin, for each x86-64 build, the ELF's SHA-256 and size and everything of its snapshot but
the segment bytes: the ELF header, every program header, and the base, size and permissions of
each loaded segment, with the entry point and the program-header table. `Layout.Matches` says a
snapshot has that layout; `Layout.HeaderOk`, `Layout.LoadOk` and `Layout.BoundsOk` are the parts of `ImageWf` that depend
only on the layout, checked by `decide +kernel` in the generated modules and transported to
every matching snapshot (`Layout.imageWf_of`, which leaves exactly the byte-dependent parts:
the segment bytes fill their segments, the entry point fetches, the program headers read). -/

/-- The pinned layout of one build. -/
structure Layout where
  elfSha256 : String
  elfBytes : Nat
  header : Silmaril.Formats.ELF.Header
  programHeaders : List Silmaril.Formats.ELF.ProgramHeader
  /-- Base, size and permission letters of each loaded segment, in order. -/
  segments : List (Nat × Nat × String)
  initPc : Nat
  phdrs : PhdrInfo

namespace Layout

variable (l : Layout)

/-- The snapshot has this layout. -/
def Matches (s : Snapshot) : Prop :=
  s.header = l.header ∧ s.programHeaders = l.programHeaders ∧
    s.image.segments.map (fun g => (g.base, g.size, g.perms)) = l.segments ∧
    s.image.initPc = l.initPc ∧ s.image.phdrs = l.phdrs

/-- `X86Launch.HeaderMatches`, stated on the layout. -/
def HeaderOk : Prop :=
  l.header.machine = 62 ∧ l.header.fileType = 2 ∧ l.header.version = 1 ∧
    (l.header.osABI = 0 ∨ l.header.osABI = 3) ∧ l.header.abiVersion = 0 ∧
    l.header.flags = 0 ∧ l.header.headerSize = 64 ∧
    l.header.programEntrySize = 56 ∧ l.header.programCount > 0 ∧
    l.header.programCount = l.programHeaders.length ∧
    l.header.entry = l.initPc ∧
    l.phdrs.ent = 56 ∧ l.phdrs.num = l.header.programCount ∧
    ∀ ph ∈ l.programHeaders, ph.kind ≠ 3

instance : Decidable l.HeaderOk := by unfold HeaderOk; infer_instance

theorem headerMatches {s : Snapshot} (m : l.Matches s) (ok : l.HeaderOk) :
    X86Launch.HeaderMatches s := by
  obtain ⟨hh, hp, -, hi, hph⟩ := m
  unfold X86Launch.HeaderMatches
  rw [hh, hp, hi, hph]
  exact ok

/-- `X86Launch.ProgramHeaderMatches` on a layout triple, with the permission letters read
through `String.toList` (which reduces in the kernel). -/
def phMatches (ph : Silmaril.Formats.ELF.ProgramHeader) (t : Nat × Nat × String) : Prop :=
  ph.kind = 1 ∧ ph.virtualAddress = t.1 ∧ ph.memorySize = t.2.1 ∧
    ph.fileSize ≤ ph.memorySize ∧
    (ph.flags % 2 = 1 ↔ t.2.2.toList.contains 'x' = true) ∧
    (ph.flags / 2 % 2 = 1 ↔ t.2.2.toList.contains 'w' = true) ∧
    (ph.flags / 4 % 2 = 1 ↔ t.2.2.toList.contains 'r' = true)

instance (ph : Silmaril.Formats.ELF.ProgramHeader) (t : Nat × Nat × String) :
    Decidable (phMatches ph t) := by unfold phMatches; infer_instance

/-- `X86Launch.LoadLayoutMatches`, stated on the layout. -/
def LoadOk : Prop :=
  (∀ t ∈ l.segments, ∃ ph ∈ l.programHeaders, phMatches ph t) ∧
    (∀ ph ∈ l.programHeaders, ph.kind = 1 → ∃ t ∈ l.segments, phMatches ph t)

instance : Decidable l.LoadOk := by unfold LoadOk; infer_instance

theorem phMatches_iff (ph : Silmaril.Formats.ELF.ProgramHeader) (g : Segment) :
    phMatches ph (g.base, g.size, g.perms) ↔ X86Launch.ProgramHeaderMatches ph g := by
  simp only [phMatches, X86Launch.ProgramHeaderMatches, Segment.executable, Segment.writable,
    Segment.readable, Segment.contains_eq_hasPerm, Segment.hasPerm]

theorem loadLayoutMatches {s : Snapshot} (m : l.Matches s) (ok : l.LoadOk) :
    X86Launch.LoadLayoutMatches s := by
  obtain ⟨-, hp, hs, -, -⟩ := m
  obtain ⟨ok₁, ok₂⟩ := ok
  constructor
  · intro g mem
    obtain ⟨ph, phMem, h⟩ := ok₁ _ (hs ▸ List.mem_map_of_mem mem)
    exact ⟨ph, hp ▸ phMem, (phMatches_iff ph g).mp h⟩
  · intro ph mem kind
    obtain ⟨t, tMem, h⟩ := ok₂ ph (hp ▸ mem) kind
    rw [← hs] at tMem
    obtain ⟨g, gMem, rfl⟩ := List.mem_map.mp tMem
    exact ⟨g, gMem, (phMatches_iff ph g).mp h⟩

/-- The loaded segments of the layout, without their bytes. -/
def bareSegments : List Segment := l.segments.map fun t => ⟨t.1, t.2.1, t.2.2, []⟩

/-- The parts of `X86Launch.ValidSnapshot` and `ImageWf` that depend only on the segment
extents: each segment is nonempty and ends below the stack reservation of the launch window
(hence below `TASK_SIZE`), the segments are pairwise disjoint, and a valid break exists. -/
def BoundsOk : Prop :=
  (∀ t ∈ l.segments, 0 < t.2.1 ∧ (t.1 : Int) + t.2.1 ≤ x86LaunchBounds.spWindowLo - stackMaxSize) ∧
    l.segments.Pairwise (fun a b => a.1 + a.2.1 ≤ b.1 ∨ b.1 + b.2.1 ≤ a.1) ∧
    imageBrkSatisfiable l.bareSegments = true

instance : Decidable l.BoundsOk := by unfold BoundsOk; infer_instance

theorem segmentsReserved_bare (segs : List Segment) :
    segmentsReserved segs =
      segmentsReserved ((segs.map fun g => (g.base, g.size, g.perms)).map
        fun t => (⟨t.1, t.2.1, t.2.2, []⟩ : Segment)) := by
  simp only [segmentsReserved, List.map_map]
  rfl

/-- A snapshot with a checked layout is well formed once its bytes fill the segments, its entry
point fetches and its program headers are readable: these three are all that depends on bytes. -/
theorem imageWf_of {isa : UserIsa} {s : Snapshot} (m : l.Matches s) (hok : l.HeaderOk)
    (lok : l.LoadOk) (bok : l.BoundsOk)
    (bytes : ∀ g ∈ s.image.segments, g.bytes.length = g.size)
    (fetch : isa.entryFetchable s.image.segments s.image.initPc = true)
    (phdrs : (memoryRead s.image.segments (zw s.image.phdrs.addr)
      (s.image.phdrs.num * s.image.phdrs.ent)).isSome = true) :
    ImageWf isa s := by
  have hs := m.2.2.1
  obtain ⟨bounds, disjoint, brk⟩ := bok
  have seg : ∀ g ∈ s.image.segments,
      0 < g.size ∧ (g.base : Int) + g.size ≤ x86LaunchBounds.spWindowLo - stackMaxSize :=
    fun g mem => bounds _ (hs ▸ List.mem_map_of_mem mem)
  have below : x86LaunchBounds.spWindowLo - stackMaxSize ≤ x86AddressSpace.taskSize := by decide
  refine ⟨⟨l.headerMatches m hok, l.loadLayoutMatches m lok, ?_, ?_, fetch, phdrs⟩, ?_, ?_⟩
  · intro g mem
    obtain ⟨pos, top⟩ := seg g mem
    exact ⟨bytes g mem, pos, le_trans top below⟩
  · rw [← hs] at disjoint
    exact List.pairwise_map.mp disjoint
  · unfold imageBrkSatisfiable imageBrkWitness at brk ⊢
    rw [segmentsReserved_bare, hs]
    exact brk
  · exact fun g mem => (seg g mem).2

end Layout

/-- The snapshots of `p` are well formed and have their builds' pinned layouts: no snapshot
without a layout. A build with a layout but no snapshot is allowed, as its statements are
untranslated (`none`). This excludes the vacuous choices of `images` (bytes that fail `ImageWf`); it does not
bind a snapshot to the bytes of the ELF with the pinned SHA-256, which is the loader's
obligation. -/
def PinnedLayouts (layouts : Build → Option Layout) (p : NativeProblem) : Prop :=
  p.ImagesValid ∧ ∀ b s, p.images b = some s → ∃ l, layouts b = some l ∧ l.Matches s

end Silmaril.Process.LPS.Problems.NativeX86
