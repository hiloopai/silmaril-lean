module

public import Silmaril.Process.LPS.Isa
public import Silmaril.Process.LPS.StackLayout
public import Silmaril.Process.LPS.Table
public import Silmaril.Process.LPS.Sys.FsIo.Namei
public import Silmaril.Process.LPS.Sys.MmExt

/-!
# LPS in Lean: the run semantics, behaviours, spurious refusals, budgets and valid inputs

Translation of LPS `Run.v` (upstream commit `f1006fe8`), parametric in the ISA (`UserIsa`)
and in the syscall table (`List SpecArm`; `specTable` by default).

* `SStep` is LPS's `sstep`: an instruction, a fault or an unmodelled instruction (the last
  two go to `SError`), a syscall (apply the effect, step past the trap, charge newly touched
  lazy pages, or fault when the budget refuses), an exit (`exitEv` with the final file
  system), a kill (`killEv`) and an unmodelled syscall (`SError`). A halted configuration has
  no successor.
* LPS defines `sstep` and `sstep_cfg cfg` separately; they differ only in the side condition
  `~ spurious_refusal_cfg cfg …` on the syscall rules. Here one relation `SStep` takes that
  filter as a parameter: `sstep` is `SStep noFilter` and `sstep_cfg cfg` is
  `SStep (spuriousRefusalCfg cfg)`.
* `Behavior` is LPS's `behavior`: prefix-closed traces, `errors` (some reachable `SError`),
  `allErrors` (inductive: every execution errors) and `unmodeled` (the model, not the
  program, gave up).
-/

@[expose] public section

namespace Silmaril.Process.LPS

variable (isa : UserIsa)

/-- LPS `Run.v:203` `config`. -/
structure Config where
  ms : isa.State
  model : Model

/-- LPS `Run.v:221` `step_to`. -/
inductive StepTo where
  | next (c : Config isa)
  | error

/-- LPS `Run.v:80` `behavior`: everything observable about one binary on one input. -/
structure Behavior where
  traces : List Event → Prop
  errors : Prop
  allErrors : Prop
  unmodeled : Prop

/-- LPS `Run.v:211` `segment_reservation`. -/
def segmentReservation (s : Segment) : Word × Word :=
  let lo := pageRoundDown s.base
  let hi := pageRoundUp (s.base + s.size)
  (zw lo, zw (hi - lo))

/-- LPS `Run.v:216` `segments_reserved`. -/
def segmentsReserved (segs : List Segment) : List (Word × Word) := segs.map segmentReservation

/-- LPS `Run.v:394` `sys_input`. -/
def sysInput (segs : List Segment) (ms : isa.State) (x8 : Word) : SyscallInput :=
  ⟨x8, isa.syscallArgs ms, isa.readByte segs ms, isa.writableByte segs ms⟩

/-- LPS `Run.v:316` `mi_account_step`: an instruction, charging the lazy pages it touches. -/
def accountStep (segs : List Segment) (ms : isa.State) (model : Model) :
    MachineResult (isa.State × Model) :=
  if !isa.reportsAccesses && !model.vmLazy.isEmpty then .unmodeled else
  match isa.step segs ms with
  | .ok report =>
    match materializeModelAccesses model report.accessed with
    | some model' => .ok (report.value, model')
    | none => .fault
  | .fault => .fault
  | .unmodeled => .unmodeled

/-- A filter on syscall outcomes: which outcomes a reading of the environment excludes. -/
abbrev RefusalFilter := SyscallInput → Model → SyscallEffect → Prop

/-- No filter: LPS's plain `sstep`. -/
def noFilter : RefusalFilter := fun _ _ _ => False

variable {isa}

/-- LPS `Run.v:399` `sstep` and `Run.v:1618` `sstep_cfg`, for a syscall table `spec` and a
refusal filter `refused`. -/
inductive SStep (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter) :
    Config isa → List Event → StepTo isa → Prop where
  | instr {ms model ms' model'} :
      model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .ok (ms', model') →
      SStep segs spec refused ⟨ms, model⟩ [] (.next ⟨ms', model'⟩)
  | instrFault {ms model} :
      model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .fault →
      SStep segs spec refused ⟨ms, model⟩ [] .error
  | instrUnmodeled {ms model} :
      model.halted = none → isa.svcPending ms = none →
      accountStep isa segs ms model = .unmodeled →
      SStep segs spec refused ⟨ms, model⟩ [] .error
  | syscall {ms model x8 eff model' model'' evs} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      ¬ refused (sysInput isa segs ms x8) model eff →
      model'.halted = none →
      materializeModelAccesses model' (syscallEffectAccesses eff) = some model'' →
      SStep segs spec refused ⟨ms, model⟩ evs
        (.next ⟨isa.advancePastSvc (isa.applyEffect ms eff), model''⟩)
  | syscallMaterializationFault {ms model x8 eff model' evs} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      ¬ refused (sysInput isa segs ms x8) model eff →
      model'.halted = none →
      materializeModelAccesses model' (syscallEffectAccesses eff) = none →
      SStep segs spec refused ⟨ms, model⟩ [] .error
  | exit {ms model x8 eff model' evs code} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      model'.halted = some code → model'.killedBy = none →
      SStep segs spec refused ⟨ms, model⟩ (evs ++ [.exitEv code model'.fs]) (.next ⟨ms, model'⟩)
  | killed {ms model x8 eff model' evs sig} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model (.ok eff model' evs) →
      model'.killedBy = some sig →
      SStep segs spec refused ⟨ms, model⟩ (evs ++ [.killEv sig model'.fs]) (.next ⟨ms, model'⟩)
  | syscallUnmodeled {ms model x8} :
      model.halted = none → isa.svcPending ms = some x8 →
      spec (sysInput isa segs ms x8) model .unmodeled →
      SStep segs spec refused ⟨ms, model⟩ [] .error

/-- LPS `Run.v:468` `star` (and `star_cfg`). -/
inductive Star (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter) :
    Config isa → List Event → Config isa → Prop where
  | refl (c) : Star segs spec refused c [] c
  | step {c₁ evs c₂ tr c₃} : SStep segs spec refused c₁ evs (.next c₂) →
      Star segs spec refused c₂ tr c₃ → Star segs spec refused c₁ (evs ++ tr) c₃

section Observations

variable (segs : List Segment) (spec : Sys SyscallEffect) (refused : RefusalFilter)

/-- LPS `Run.v:496` `obs_trace`: the prefixes of finite executions. -/
def ObsTrace (c₀ : Config isa) (tr : List Event) : Prop :=
  ∃ tr' c, Star segs spec refused c₀ tr' c ∧ tr <+: tr'

/-- LPS `Run.v:689` `reaches_error`. -/
def ReachesError (c₀ : Config isa) : Prop :=
  ∃ tr c evs, Star segs spec refused c₀ tr c ∧ SStep segs spec refused c evs .error

/-- LPS `Run.v:805` `unmodeled_at`: the next instruction or syscall is unmodelled. -/
def UnmodeledAt (c : Config isa) : Prop :=
  c.model.halted = none ∧
    ((isa.svcPending c.ms = none ∧ accountStep isa segs c.ms c.model = .unmodeled) ∨
      ∃ x8, isa.svcPending c.ms = some x8 ∧ spec (sysInput isa segs c.ms x8) c.model .unmodeled)

/-- LPS `Run.v:813` `reaches_unmodeled`. -/
def ReachesUnmodeled (c₀ : Config isa) : Prop :=
  ∃ tr c, Star segs spec refused c₀ tr c ∧ UnmodeledAt segs spec c

/-- LPS `Run.v:879` `all_traces_error`: inductive, so an infinite run of successful steps is
never "all error". -/
inductive AllTracesError : Config isa → Prop where
  | intro {c} : (∃ evs st, SStep segs spec refused c evs st) →
      (∀ evs c', SStep segs spec refused c evs (.next c') → AllTracesError c') →
      AllTracesError c

end Observations

/-- LPS `Run.v:955` `entry_block_top`. -/
def entryBlockTop (sp : Word) (bytes : List Byte) : Int := uns sp + bytes.length
/-- LPS `Run.v:958` `entry_page_top`. -/
def entryPageTop (sp : Word) (bytes : List Byte) : Int := pageRoundUp (entryBlockTop sp bytes)
/-- LPS `Run.v:961` `entry_slack_len`. -/
def entrySlackLen (sp : Word) (bytes : List Byte) : Nat :=
  (entryPageTop sp bytes - entryBlockTop sp bytes).toNat
/-- LPS `Run.v:964` `entry_slack`: the drawn bytes from the block to the end of its page. -/
def entrySlack (sp : Word) (bytes : List Byte) (slack : Word → Byte) : List Byte :=
  (List.range (entrySlackLen sp bytes)).map fun k => slack (zw (entryBlockTop sp bytes + k))

/-- LPS `Run.v:969` `entry_stack_image`. -/
def entryStackImage (ph : PhdrInfo) (sp : Word) (argv envp : List (List Byte))
    (uid hwcap : Word) (draw : EntryDraw) : List Byte :=
  let bytes := buildStackBytes ph sp argv envp uid hwcap draw
  bytes ++ entrySlack sp bytes draw.slack

/-- LPS `Run.v:1138` `ExecEntry`: the kernel's choices at `execve` (stack pointer, initial
break, mmap base, entropy). It is quantified independently for each binary. -/
structure ExecEntry where
  sp : Word
  brk : Word
  mmapBase : Word
  draw : EntryDraw

variable (isa)

/-- LPS `Run.v:1096` `init_config`. -/
def initConfig (img : Image) (en : ExecEntry) (lim : Int) (inp : ProcInput) : Config isa :=
  ⟨isa.init img.segments img.initPc en.sp
      (entryStackImage img.phdrs en.sp inp.argv inp.envp inp.uid inp.hwcap en.draw),
    initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp⟩

/-- LPS `Run.v:1164` `run` (with `refused := noFilter`) and `Run.v:1910` `run_scfg`, over a
syscall table. -/
def runWith (spec : Sys SyscallEffect) (refused : RefusalFilter) (img : Image) (lim : Int)
    (en : ExecEntry) (inp : ProcInput) : Behavior :=
  let c₀ := initConfig isa img en lim inp
  { traces := ObsTrace img.segments spec refused c₀
    errors := ReachesError img.segments spec refused c₀
    allErrors := AllTracesError img.segments spec refused c₀
    unmodeled := ReachesUnmodeled img.segments spec refused c₀ }

/-- An opt-in architecture-specific entry block. Existing RISC-V launches
continue to use `entryStackImage` through the unchanged `initConfig`. -/
abbrev EntryStackBuilder := Image → ExecEntry → ProcInput → List Byte

def legacyEntryStack : EntryStackBuilder := fun img en inp =>
  entryStackImage img.phdrs en.sp inp.argv inp.envp inp.uid inp.hwcap en.draw

/-- The opt-in launch path uses the ISA's explicit address-space profile as
well as its own stack builder. It shares the actual LPS transitions below;
it is not a detached byte-generation API. -/
def initConfigWithStack (stack : EntryStackBuilder) (img : Image) (en : ExecEntry)
    (lim : Int) (inp : ProcInput) : Config isa :=
  ⟨isa.init img.segments img.initPc en.sp (stack img en inp),
    isa.initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp⟩

def runWithStack (stack : EntryStackBuilder) (spec : Sys SyscallEffect)
    (refused : RefusalFilter) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Behavior :=
  let c₀ := initConfigWithStack isa stack img en lim inp
  { traces := ObsTrace img.segments spec refused c₀
    errors := ReachesError img.segments spec refused c₀
    allErrors := AllTracesError img.segments spec refused c₀
    unmodeled := ReachesUnmodeled img.segments spec refused c₀ }

/-- Backward compatibility is conditional on the model profile, rather than
silently changing the legacy launch for any virtual-address-width input. -/
theorem initConfigWithStack_legacy (img : Image) (en : ExecEntry) (lim : Int) (inp : ProcInput)
    (sameModel : isa.initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp =
      initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp) :
    initConfigWithStack isa legacyEntryStack img en lim inp = initConfig isa img en lim inp := by
  unfold initConfigWithStack initConfig
  rw [sameModel]
  rfl

theorem runWithStack_legacy (spec : Sys SyscallEffect) (refused : RefusalFilter)
    (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput)
    (sameModel : isa.initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp =
      initModel (segmentsReserved img.segments) en.brk en.mmapBase en.sp lim inp) :
    runWithStack isa legacyEntryStack spec refused img lim en inp =
      runWith isa spec refused img lim en inp := by
  unfold runWithStack runWith
  rw [initConfigWithStack_legacy isa img en lim inp sameModel]

/-! ## Spurious refusals: the readings of the failure model (LPS `Run.v:1294-1563`) -/

/-- LPS `Run.v:1294` `SpuriousFamily`. -/
inductive SpuriousFamily where
  | alloc | fs | fd | net | cred | intr
  deriving DecidableEq, Repr

/-- LPS `Run.v:1301` `SpuriousCfg`: for each family, whether a call may fail without cause
(`true`) or only when the failure is forced (`false`). -/
structure SpuriousCfg where
  alloc : Bool
  fs : Bool
  fd : Bool
  net : Bool
  cred : Bool
  intr : Bool
  deriving DecidableEq, Repr

/-- LPS `Run.v:1310` `may_fail_cfg`. -/
def mayFailCfg : SpuriousCfg := ⟨true, true, true, true, true, true⟩
/-- LPS `Run.v:1311` `forced_only_cfg`. -/
def forcedOnlyCfg : SpuriousCfg := ⟨false, false, false, false, false, false⟩
/-- LPS `Run.v:1315` `alloc_only_cfg`. -/
def allocOnlyCfg (allocMayFail : Bool) : SpuriousCfg := ⟨allocMayFail, true, true, true, true, true⟩

/-- LPS `Run.v:1318` `family_may_fail`. -/
def familyMayFail (cfg : SpuriousCfg) : SpuriousFamily → Bool
  | .alloc => cfg.alloc
  | .fs => cfg.fs
  | .fd => cfg.fd
  | .net => cfg.net
  | .cred => cfg.cred
  | .intr => cfg.intr

/-- LPS `Run.v:1331` `cfg_le`. -/
def cfgLe (cfg₁ cfg₂ : SpuriousCfg) : Prop :=
  ∀ f, familyMayFail cfg₁ f = true → familyMayFail cfg₂ f = true

/-- LPS `Run.v:1346` `InjectedArm`. -/
structure InjectedArm where
  no : Nat
  family : SpuriousFamily
  errnos : List Int

/-- LPS `Sys/Kernel/Sys.v:756` `setid_errnos`. -/
def setidErrnos (realUidChanges : Bool) : List Int :=
  if realUidChanges then [ENOMEM, EAGAIN] else [ENOMEM]

/-- LPS `Run.v:1358` `injected_table`: the calls with environment-injected failures, their
family and their errnos (`Sys/Fs/DPath.v:46`, `Sys/Fs/File.v:166`, `Sys/Fs/Namei.v:257`,
`Sys/Fs/Open.v:27,1755`, `Sys/Fs/Pipe.v:41`, `Sys/Net/Socket.v:35-45,2108,2135`,
`Sys/Mm/Mremap.v:115`, `Sys/Kernel/Fork.v:510`, `Sys/Mm/Mmap.v:645`, `Sys/Mm/Mprotect.v:78`,
`Sys/Drivers/Char/Random.v:26`). -/
def injectedTable : List InjectedArm :=
  [ ⟨17, .fs, [ENOMEM, ENOENT, ENAMETOOLONG]⟩, ⟨23, .fd, [ENOMEM, EMFILE]⟩,
    ⟨35, .fs, [ENOMEM, EACCES, EPERM, EROFS, EBUSY]⟩, ⟨48, .fs, [ENOMEM, EACCES]⟩,
    ⟨56, .fs, [ENOMEM, EACCES, EMFILE, ENFILE]⟩, ⟨59, .fd, [EMFILE, ENFILE, ENOMEM]⟩,
    ⟨101, .intr, [EINTR]⟩, ⟨144, .cred, setidErrnos true⟩, ⟨146, .cred, setidErrnos true⟩,
    ⟨147, .cred, setidErrnos true⟩, ⟨149, .cred, setidErrnos true⟩, ⟨157, .cred, [EPERM]⟩,
    ⟨198, .fd, [ENOMEM, EMFILE, ENFILE]⟩, ⟨199, .fd, [EMFILE, ENOMEM] ++ [ENFILE, ENOMEM]⟩,
    ⟨200, .net, [EADDRINUSE]⟩, ⟨201, .net, [EADDRINUSE]⟩, ⟨202, .fd, [ENOMEM, EMFILE, ENFILE]⟩,
    ⟨214, .alloc, []⟩, ⟨216, .alloc, [ENOMEM]⟩, ⟨220, .fd, [EAGAIN, ENOMEM, EMFILE, EACCES]⟩,
    ⟨222, .alloc, mmapErrnos⟩, ⟨226, .alloc, [ENOMEM]⟩, ⟨242, .fd, [ENOMEM, EMFILE, ENFILE]⟩,
    ⟨278, .intr, getrandomErrnos⟩, ⟨435, .fd, [EAGAIN, ENOMEM, EMFILE, EACCES]⟩ ]

/-- LPS `Run.v:1394` `injected_arm`. -/
def injectedArm (no : Nat) : Option InjectedArm := injectedTable.find? (·.no = no)

/-- LPS `Run.v:1398` `ret_in_errnos`. -/
def retInErrnos (es : List Int) (r : Word) : Bool := es.any fun e => r == errnoRet e

/-- LPS `Run.v:1406` `brk_refusal_b`: `brk` answered with the old break. -/
def brkRefusalB (m : Model) (req ret : Word) : Bool :=
  let h := m.vmmaps
  !wIs0 req && !decide (uns req < uns (minBrk h)) && !(req == h.brk) && ret == h.brk

/-- LPS `Run.v:1418` `refusal_b`: the outcome is a refusal. -/
def refusalB (i : SyscallInput) (m : Model) (ret : Word) : Bool :=
  let no := i.sysno.toNat
  if no = 214 then brkRefusalB m (i.arg 0) ret
  else match injectedArm no with
    | some a => retInErrnos a.errnos ret
    | none => false

/-- LPS `Run.v:1451` `alloc_budget_refused_b`: the budget marks of `brk`, `mremap`, `mmap`
and `mprotect`. -/
def allocBudgetRefusedB (i : SyscallInput) (m : Model) : Bool :=
  let no := i.sysno.toNat
  if no = 214 then brkBudgetRefusedB m (i.arg 0)
  else if no = 216 then mremapBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) m
  else if no = 222 then
    mmapBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) (i.arg 3) (i.arg 4) (i.arg 5) m
  else if no = 226 then mprotectBudgetRefusedB (i.arg 0) (i.arg 1) (i.arg 2) m
  else false

/-- LPS `Run.v:1533` `injected_family_off`. -/
def injectedFamilyOff (cfg : SpuriousCfg) (i : SyscallInput) : Bool :=
  match injectedArm i.sysno.toNat with
  | some a => !familyMayFail cfg a.family
  | none => false

/-- LPS `Run.v:1544` `spurious_refusal_cfg`: a refusal of a family that may not fail without
cause, at a call where the spec also admits a non-refusal. Exact by construction: a wrong
errno list can only lose filtering. -/
def spuriousRefusalCfg (spec : Sys SyscallEffect) (cfg : SpuriousCfg) : RefusalFilter :=
  fun i m eff =>
    injectedFamilyOff cfg i = true ∧ refusalB i m eff.ret = true ∧
      ∃ eff' m' evs', spec i m (.ok eff' m' evs') ∧ refusalB i m eff'.ret = false

/-- LPS `Run.v:1558` `refusal_decided`. -/
def RefusalDecided (spec : Sys SyscallEffect) (cfg : SpuriousCfg) (i : SyscallInput)
    (m : Model) : Prop :=
  injectedFamilyOff cfg i = true →
    (∃ eff' m' evs', spec i m (.ok eff' m' evs') ∧ refusalB i m eff'.ret = false) ∨
      ∀ eff' m' evs', spec i m (.ok eff' m' evs') → refusalB i m eff'.ret = true

/-- LPS `Run.v:1164` `run`, over the translated table. -/
def run (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Behavior :=
  runWith isa syscallSpec noFilter img lim en inp

/-- LPS `Run.v:1910` `run_scfg`, over the translated table. -/
def runScfg (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Behavior :=
  runWith isa syscallSpec (spuriousRefusalCfg syscallSpec cfg) img lim en inp

/-- LPS `Run.v:1926` `behavior_equiv`. -/
def BehaviorEquiv (b₁ b₂ : Behavior) : Prop :=
  (∀ tr, b₁.traces tr ↔ b₂.traces tr) ∧ (b₁.errors ↔ b₂.errors) ∧
    (b₁.allErrors ↔ b₂.allErrors) ∧ (b₁.unmodeled ↔ b₂.unmodeled)

/-- LPS `Run.v:1960` `run_nospurious`. -/
def runNospurious (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Behavior :=
  runScfg isa (allocOnlyCfg false) img lim en inp

/-- LPS `Run.v:1970` `run_cfg`. -/
def runCfg (allocMayFail : Bool) (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) :
    Behavior :=
  if allocMayFail then run isa img lim en inp else runNospurious isa img lim en inp

/-! ## Memory budgets (LPS `Run.v:2083-2257`) -/

/-- LPS `Run.v:2086` `budget_refused_at`: the next step is refused for budget. -/
def BudgetRefusedAt (segs : List Segment) (spec : Sys SyscallEffect) (c : Config isa) : Prop :=
  c.model.halted = none ∧
    ((isa.svcPending c.ms = none ∧ ∃ report, isa.step segs c.ms = .ok report ∧
        materializeModelAccesses c.model report.accessed = none) ∨
      ∃ x8, isa.svcPending c.ms = some x8 ∧
        (allocBudgetRefusedB (sysInput isa segs c.ms x8) c.model = true ∨
          ∃ eff model' evs, spec (sysInput isa segs c.ms x8) c.model (.ok eff model' evs) ∧
            model'.halted = none ∧
              materializeModelAccesses model' (syscallEffectAccesses eff) = none))

/-- LPS `Run.v:2244` `run_budget_refused` and `Run.v:2252` `run_scfg_budget_refused`. -/
def RunBudgetRefusedWith (spec : Sys SyscallEffect) (refused : RefusalFilter) (img : Image)
    (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ∃ tr c, Star img.segments spec refused (initConfig isa img en lim inp) tr c ∧
    BudgetRefusedAt isa img.segments spec c

/-- LPS `Run.v:2244` `run_budget_refused`. -/
def RunBudgetRefused (img : Image) (lim : Int) (en : ExecEntry) (inp : ProcInput) : Prop :=
  RunBudgetRefusedWith isa syscallSpec noFilter img lim en inp

/-- LPS `Run.v:2252` `run_scfg_budget_refused`. -/
def RunScfgBudgetRefused (cfg : SpuriousCfg) (img : Image) (lim : Int) (en : ExecEntry)
    (inp : ProcInput) : Prop :=
  RunBudgetRefusedWith isa syscallSpec (spuriousRefusalCfg syscallSpec cfg) img lim en inp

/-! ## Valid entries and inputs (LPS `Run.v:2292-3361`) -/

/-- LPS `Run.v:2292` `valid_sp`. -/
def ValidSp (sp : Word) : Prop := spWindowLo ≤ uns sp ∧ uns sp ≤ spWindowHi ∧ uns sp % 16 = 0
/-- LPS `Run.v:2305` `valid_brk`. -/
def ValidBrk (segs : List Segment) (brk : Word) : Prop :=
  reservedTop (segmentsReserved segs) ≤ uns brk ∧
    uns brk ≤ reservedTop (segmentsReserved segs) + brkAslrMax ∧ uns brk % pageSize = 0
/-- LPS `Run.v:2336` `valid_mmap_base`. -/
def ValidMmapBase (mbase : Word) : Prop :=
  mmapBaseMin ≤ uns mbase ∧ uns mbase ≤ mmapBaseMax ∧ uns mbase % pageSize = 0
/-- LPS `Run.v:2351` `valid_sp_va`. -/
def ValidSpVa (v : VaSize) (sp : Word) : Prop :=
  vaSpWindowLo v ≤ uns sp ∧ uns sp ≤ vaSpWindowHi v ∧ uns sp % 16 = 0
/-- LPS `Run.v:2356` `valid_mmap_base_va`. -/
def ValidMmapBaseVa (v : VaSize) (mbase : Word) : Prop :=
  vaMmapBaseMin v ≤ uns mbase ∧ uns mbase ≤ vaMmapBaseMax v ∧ uns mbase % pageSize = 0

/-- LPS `Run.v:2382` `total_arg_bytes`. -/
def totalArgBytes (args : List (List Byte)) : Int := args.foldr (fun a acc => a.length + 1 + acc) 0


/-- LPS `Run.v:2446` `valid_argv`: 1 to 1024 arguments, at most 2 MiB, each under 128 KiB
and NUL-free; the arguments after `argv[0]` contain no `/` and are not `..`. -/
def ValidArgv (argv : List (List Byte)) : Prop :=
  1 ≤ argv.length ∧ argv.length ≤ 1024 ∧ totalArgBytes argv ≤ 2097152 ∧
    (∀ a ∈ argv, a.length ≤ 131071) ∧ (∀ a ∈ argv, (0 : Byte) ∉ a) ∧
    ∀ a ∈ argv.tail, pathHasSlash a = false ∧ Fs.pathEqb a dotdotPath = false

/-- LPS `Run.v:2457` `valid_envp`. -/
def ValidEnvp (envp : List (List Byte)) : Prop :=
  envp.length ≤ 256 ∧ totalArgBytes envp ≤ 131072 ∧ (∀ e ∈ envp, e.length ≤ 131071) ∧
    ∀ e ∈ envp, (0 : Byte) ∉ e

/-- LPS `Run.v:2541` `entry_stack_span`. -/
def entryStackSpan (argv envp : List (List Byte)) : Int :=
  8 + 8 * argv.length + 8 + 8 * envp.length + 8 + auxvSize + totalArgBytes argv +
    totalArgBytes envp + 7 + 16

/-- LPS `Run.v:2558` `entry_stack_fits_va`. -/
def EntryStackFitsVa (v : VaSize) (sp : Word) (argv envp : List (List Byte)) : Prop :=
  uns sp + entryStackSpan argv envp ≤ vaSpWindowHi v

/-- LPS `Run.v:2635` `valid_entry_va`. -/
def ValidEntryVa (v : VaSize) (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ValidSpVa v en.sp ∧ ValidBrk img.segments en.brk ∧ ValidMmapBaseVa v en.mmapBase ∧
    EntryStackFitsVa v en.sp inp.argv inp.envp

/-- LPS `Run.v:2643` `valid_entry`. -/
def ValidEntry (img : Image) (en : ExecEntry) (inp : ProcInput) : Prop :=
  ValidEntryVa inp.vaSize img en inp

/-- LPS `Run.v:2700` `valid_id`. -/
def ValidId (u : Word) : Prop := uns u < 2 ^ 32 - 1
/-- LPS `Run.v:2703` `valid_creds`. -/
def ValidCreds (inp : ProcInput) : Prop := ValidId inp.uid ∧ ValidId inp.gid
/-- LPS `Run.v:2752` `valid_nofile`. -/
def ValidNofile (n : Word) : Prop := uns n ≤ 2 ^ 31 - 64
/-- LPS `Sys/Uapi.v:808` `sig_kernel_only_mask`. -/
def sigKernelOnlyMask : Word := 262400
/-- LPS `Run.v:2818` `valid_sigmask`: SIGKILL and SIGSTOP are not blocked. -/
def ValidSigmask (inp : ProcInput) : Prop := inp.sigmask &&& sigKernelOnlyMask = 0
/-- LPS `Run.v:2859` `valid_hwcap`. -/
def ValidHwcap (h : Word) : Prop := h = hwcapRv64gc ∨ h = hwcapRv64gcv
/-- LPS `Run.v:2906` `valid_urandom`. -/
def ValidUrandom (inp : ProcInput) : Prop := inp.urandom.Infinite

/-- The conjuncts every `valid_input*` of LPS shares. -/
def ValidInputCore (inp : ProcInput) : Prop :=
  ValidArgv inp.argv ∧ ValidEnvp inp.envp ∧ Fs.ValidFs inp.fs ∧ Fs.KeysRelative inp.imageFs ∧
    ValidCreds inp ∧ ValidNofile inp.nofile ∧ ValidSigmask inp ∧ ValidUrandom inp

/-- The input restrictions a statement is read under: the declared `abort()` stance, the
address-space width and the advertised hardware capabilities. LPS spells out one
`valid_input*` predicate for each combination it uses; each is `ValidInputWith` at one
reading (`Run.v:2973-3361`). -/
structure InputReading where
  abort : Option Bool
  va : Option VaSize
  hwcap : Option Word

/-- The valid inputs under a reading. -/
def ValidInputWith (r : InputReading) (inp : ProcInput) : Prop :=
  ValidInputCore inp ∧
    (match r.hwcap with | some h => inp.hwcap = h | none => ValidHwcap inp.hwcap) ∧
    (match r.abort with | some b => inp.abortTerminal = b | none => True) ∧
    (match r.va with | some v => inp.vaSize = v | none => True)

/-- LPS `Run.v:2973` `valid_input`. -/
def ValidInput : ProcInput → Prop := ValidInputWith ⟨some false, some .sv48, none⟩
/-- LPS `Run.v:3007` `valid_input_abort`: `abort()` is the terminal SIGABRT death. -/
def ValidInputAbort : ProcInput → Prop := ValidInputWith ⟨some true, some .sv48, none⟩
/-- LPS `Run.v:3021` `valid_input_either`. -/
def ValidInputEither : ProcInput → Prop := ValidInputWith ⟨none, some .sv48, none⟩
/-- LPS `Run.v:3075` `valid_input_sv39`. -/
def ValidInputSv39 : ProcInput → Prop := ValidInputWith ⟨some false, some .sv39, none⟩
/-- LPS `Run.v:3084` `valid_input_sv57`. -/
def ValidInputSv57 : ProcInput → Prop := ValidInputWith ⟨some false, some .sv57, none⟩
/-- LPS `Run.v:3093` `valid_input_va_any`. -/
def ValidInputVaAny : ProcInput → Prop := ValidInputWith ⟨some false, none, none⟩
/-- LPS `Run.v:3258` `valid_input_hwcap_rv64gc`: no vector extension advertised. -/
def ValidInputHwcapRv64gc : ProcInput → Prop :=
  ValidInputWith ⟨some false, some .sv48, some hwcapRv64gc⟩
/-- LPS `Run.v:3267` `valid_input_hwcap_rv64gcv`. -/
def ValidInputHwcapRv64gcv : ProcInput → Prop :=
  ValidInputWith ⟨some false, some .sv48, some hwcapRv64gcv⟩
/-- LPS `Run.v:3345` `valid_input_abort_hwcap_rv64gc`. -/
def ValidInputAbortHwcapRv64gc : ProcInput → Prop :=
  ValidInputWith ⟨some true, some .sv48, some hwcapRv64gc⟩
/-- LPS `Run.v:3354` `valid_input_abort_hwcap_rv64gcv`. -/
def ValidInputAbortHwcapRv64gcv : ProcInput → Prop :=
  ValidInputWith ⟨some true, some .sv48, some hwcapRv64gcv⟩

end Silmaril.Process.LPS
