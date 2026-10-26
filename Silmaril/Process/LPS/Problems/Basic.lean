module

public import Silmaril.Process.LPS.Shapes

/-!
# OSS Verify problems, generic over the ISA

OSS Verify (`oss-verify-proofs` @ `98e995d4`) states theorems about the builds of OSS-Fuzz
harnesses: each statement in a harness's `Statements.v` is one shape of `Shapes.v` applied to
the memory images of that harness's builds (`docs/statements.md`). This file is the data of
such a problem, independent of the ISA, and its meaning:

* `Build`: the four builds of a harness (`plain`, `ubsan`, `asan`, `asan-ubsan`,
  `docs/building.md` "The builds");
* `Statement`: which shape of `Shapes.v` a statement applies, with the budget pair, the
  environment reading, the exit set and the sanitizer build it names. Its constructors are
  exactly the shapes of `Shapes.v` (the seven agreement forms in `AgreeShape`);
* `Harness`: the ISA-independent facts of one harness (`harness.yaml`): its name, entry
  point, driver input, input distribution (`Distribution.v`), its statements and the ones
  the release proves;
* `Problem`: a harness together with an ISA and the memory image of each build *on that
  ISA*. `Problem.denote?` is the statement, built only from the definitions of
  `Silmaril.Process.LPS.Shapes`.

With the LPS RISC-V machine and the riscv64 images, `Problem.denote?` is OSS Verify's statement
(the shapes are `rfl`-equal to the LPS definitions, `Shapes.lean`). With
`Machines.x86Ext` and x86-64 images of builds made the same way it is an x86-64 statement:
the shapes, budgets, readings, exit sets and distribution are shared, and the machine and
the bytes differ. It is not yet the x86-64 statement with exactly the same meaning, because
the `Shapes` run the reference (asm-generic numbered) syscall table and `x86Ext` keeps
riscv-flavoured kernel parameters:

* `x86Ext` uses the default `addressSpace` (LPS's riscv64 Sv48 constants), so it admits a
  mapping in the last page below `2^47` that x86-64 Linux (`TASK_SIZE = 0x7ffffffff000`)
  refuses;
* `x86Ext` has `reportsAccesses = false`, so a run fails closed while a lazy
  (`MAP_NORESERVE`) reservation exists, which the ASan builds make;
* `x86Ext` renumbers x86-64 calls onto the reference table, which is right only for calls
  whose argument and structure layout is the same on both ISAs.

`Machines.x86ExtNative` with `NativeX86.extendedSyscallSpec` (`Machines.X86NativeLaunch`)
removes the first two, but the `Shapes` are stated over the reference `run`, not over a
run with a supplied syscall table, so they cannot use it yet.

A statement with a missing piece has *no* Lean proposition here: `Problem.denote?` is `none`
on it. Two pieces can be missing: the image of a build the statement names (`Problem.images`),
and the input distribution (`Distribution.v`, not translated: it is built from LPS
`MeasureLib`) of a bound statement (`_disagrees_at_most`). Such a statement stays in
`Harness.statements` as data, but it is neither provable nor refutable in Lean, so no Lean
theorem can contradict, or claim, upstream's statement through it. In particular it does not
denote `False` (`denote?_ne_some_of_untranslated`): upstream's bound statement holds at
`b = 1`, so `False` would contradict a true statement.
-/

@[expose] public section

namespace Silmaril.Process.LPS.Problems

open Silmaril.Process.LPS Silmaril.Process.LPS.Shapes

/-- The builds of a harness (`docs/building.md`, "The builds"). -/
inductive Build where
  | plain
  | ubsan
  | asan
  | asanUbsan
  deriving DecidableEq, Repr

/-- The build's name in `harness.yaml` and `index/binaries.tsv`. -/
def Build.name : Build → String
  | .plain => "plain"
  | .ubsan => "ubsan"
  | .asan => "asan"
  | .asanUbsan => "asan-ubsan"

/-- Whether a build links the AddressSanitizer runtime. -/
def Build.hasAsan : Build → Bool
  | .asan | .asanUbsan => true
  | _ => false

/-- The budget pairs of `Shapes.v:55-62`. -/
inductive BudgetChoice where
  /-- `Budgets.Standard`: 16 GiB plain, 512 GiB sanitizer. -/
  | standard
  /-- `Budgets.Asan`: 2 GiB plain, 512 GiB sanitizer. -/
  | asan
  deriving DecidableEq, Repr

def BudgetChoice.budgets : BudgetChoice → Budgets
  | .standard => Budgets.standard
  | .asan => Budgets.asan

/-- The environment readings of `Shapes.v:76-81`. -/
inductive EnvChoice where
  | mayFail
  | allocForcedOnly
  | forcedOnly
  deriving DecidableEq, Repr

def EnvChoice.cfg : EnvChoice → SpuriousCfg
  | .mayFail => Env.mayFail
  | .allocForcedOnly => Env.allocForcedOnly
  | .forcedOnly => Env.forcedOnly

/-- The exit sets of `Shapes.v:98-107`, and an explicit list for problems that are not OSS
Verify harnesses (the x86 probe corpus, `Problems.X86Probes`): the halting shapes take any
exit set (`Shapes.haltsWithinBudget`, `Shapes.haltsMayFail`), the published statements use
the two named ones. -/
inductive ExitChoice where
  | any
  | okOrRefused
  | listed (codes : List Word)
  deriving DecidableEq, Repr

def ExitChoice.codes : ExitChoice → List Word
  | .any => Exits.any
  | .okOrRefused => Exits.okOrRefused
  | .listed codes => codes

/-- The seven agreement shapes of `Shapes.v:123-245` (`docs/statements.md`, the variant
table): no reading, an environment reading (`agrees_in`), `abort()` read as SIGABRT, and
the RV64GC hardware-capability restriction. -/
inductive AgreeShape where
  | agrees
  | agreesIn (env : EnvChoice)
  | abortModelled
  | inAbortModelled (env : EnvChoice)
  | rv64gc
  | abortModelledRv64gc
  | inRv64gc (env : EnvChoice)
  deriving DecidableEq, Repr

/-- The meaning of an agreement shape: the `Shapes` definition it names. -/
def AgreeShape.denote (isaP isaS : UserIsa) (limP limS : Int) (plain san : Image) :
    AgreeShape → Prop
  | .agrees => Shapes.agrees isaP isaS limP limS plain san
  | .agreesIn env => Shapes.agreesIn isaP isaS env.cfg limP limS plain san
  | .abortModelled => Shapes.agreesAbortModelled isaP isaS limP limS plain san
  | .inAbortModelled env => Shapes.agreesInAbortModelled isaP isaS env.cfg limP limS plain san
  | .rv64gc => Shapes.agreesRv64gc isaP isaS limP limS plain san
  | .abortModelledRv64gc => Shapes.agreesAbortModelledRv64gc isaP isaS limP limS plain san
  | .inRv64gc env => Shapes.agreesInRv64gc isaP isaS env.cfg limP limS plain san

/-- One statement of a harness's `Statements.v`: a shape of `Shapes.v` with its parameters.
The plain build is implicit where a shape compares two builds. -/
inductive Statement where
  /-- `<san>_agrees`: `agrees*` on the plain and `san` images, at the budget pair. -/
  | agrees (san : Build) (budgets : BudgetChoice) (shape : AgreeShape)
  /-- `<b>_halts`: `halts_within_budget (budgets).lim_source exits`. -/
  | haltsWithinBudget (b : Build) (budgets : BudgetChoice) (exits : ExitChoice)
  /-- `<b>_halts_may_fail`: `halts_may_fail exits`. -/
  | haltsMayFail (b : Build) (exits : ExitChoice)
  /-- `<san>_disagrees_at_most b`: `disagrees_at_most` (or `_rv64gc`) under the harness's
  distribution. -/
  | disagreesAtMost (san : Build) (env : EnvChoice) (rv64gc : Bool)
  /-- `<san>_agreement_decidable`: `agreement_decidable` (or `_rv64gc`). -/
  | agreementDecidable (san : Build) (env : EnvChoice) (rv64gc : Bool)
  deriving DecidableEq, Repr

/-- The builds a statement names. -/
def Statement.builds : Statement → List Build
  | .agrees san .. => [.plain, san]
  | .haltsWithinBudget b .. => [b]
  | .haltsMayFail b _ => [b]
  | .disagreesAtMost san .. => [.plain, san]
  | .agreementDecidable san .. => [.plain, san]

/-- Whether the statement needs the input distribution (`Distribution.v`). -/
def Statement.needsDistribution : Statement → Bool
  | .disagreesAtMost .. => true
  | _ => false

/-- The type of a statement: a bound statement takes its bound first
(`Definition <name> (b : Q) : Prop`, `docs/statements.md`). -/
def Statement.Sort : Statement → Type
  | .disagreesAtMost .. => ℚ → Prop
  | _ => Prop

/-- The driver input of a harness: the input file is `[u16 config word][config bytes][u32
allocation mask][payload]`, and the driver exits with status 2 without calling the harness on
a wrong argument count, a missing or unreadable file, a file shorter than its 6-byte header,
or one of `maxInput` bytes or more (`Statements.v` SUBJECT, `docs/statements.md`). This is
documentation of the binary, not a premise: every statement quantifies over every valid
process input. -/
structure DriverInput where
  argv0 : String
  inputFile : String
  headerBytes : Nat := 6
  maxInput : Nat := 64 * 2 ^ 20
  deriving DecidableEq, Repr

/-- The ISA-independent facts of one harness (`projects/<project>/<harness>/harness.yaml`). -/
structure Harness where
  project : String
  harness : String
  /-- The function the driver calls, normally `LLVMFuzzerTestOneInput`. -/
  entry : String
  driver : DriverInput
  /-- `Distribution.v`, where the harness has one. -/
  distribution : Option Distribution
  /-- The statements of `Statements.v`, by name. -/
  statements : List (String × Statement)
  /-- The statements the release proves (`index/PROOFS.md`). -/
  proved : List String

/-- The statements that need the distribution where the harness has none: untranslated on
every problem of the harness (`Problem.isUntranslated`). -/
def Harness.untranslated (h : Harness) : List (String × Statement) :=
  h.statements.filter fun s => s.2.needsDistribution && h.distribution.isNone

/-- A harness on one ISA: the machine, and the memory image of each build of it on that ISA
(`Images.v`; `none` where the build is absent). -/
structure Problem where
  harness : Harness
  isa : UserIsa
  images : Build → Option Image

namespace Problem

variable (p : Problem)

/-- `disagrees_at_most` (or `_rv64gc`) under the distribution `d`. -/
def boundAt (isa : UserIsa) (env : EnvChoice) (rv64gc : Bool) (d : Distribution)
    (plain san : Image) (bound : ℚ) : Prop :=
  if rv64gc then Shapes.disagreesAtMostRv64gc isa env.cfg d.w d.M plain san bound
  else Shapes.disagreesAtMost isa env.cfg d.w d.M plain san bound

/-- `k` at the image of `b`, or `none` where the build has no image. -/
def withImage {α : Type _} (b : Build) (k : Image → α) : Option α :=
  (p.images b).map k

/-- `k` at the plain image and the image of `san`, or `none` where one is missing. -/
def withImages {α : Type _} (san : Build) (k : Image → Image → α) : Option α :=
  (p.images .plain).bind fun plain => p.withImage san (k plain)

/-- The meaning of a statement about this problem, through `Shapes` only, or `none` where the
statement is *untranslated*.

`denote? s = some P`: `P` is the statement. With the problem's images upstream's images and
its machine upstream's, `P` is upstream's statement, so a proof of `P` proves it and a proof
of `¬ P` refutes it.

`denote? s = none` (`denote?_eq_none_iff`): the statement is listed as data but has no Lean
proposition, neither provable nor refutable, because a piece of it is missing:

* a bound statement of a harness whose distribution is unknown (`distribution = none`,
  `Distribution.v` not translated). No proposition replaces the missing distribution: neither
  `False` (upstream's holds at `b = 1`) nor the bound for every distribution (which at
  `b = 1` need not hold);
* a statement about a build with no image. -/
def denote? : (s : Statement) → Option s.Sort
  | .agrees san budgets shape =>
    p.withImages san fun plain sanImg =>
      shape.denote p.isa p.isa budgets.budgets.limSource budgets.budgets.limTarget plain sanImg
  | .haltsWithinBudget b budgets exits =>
    p.withImage b fun img =>
      Shapes.haltsWithinBudget p.isa budgets.budgets.limSource exits.codes img
  | .haltsMayFail b exits =>
    p.withImage b fun img => Shapes.haltsMayFail p.isa exits.codes img
  | .disagreesAtMost san env rv64gc =>
    p.harness.distribution.bind fun d =>
      p.withImages san fun plain sanImg bound => boundAt p.isa env rv64gc d plain sanImg bound
  | .agreementDecidable san env rv64gc =>
    p.withImages san fun plain sanImg =>
      if rv64gc then Shapes.agreementDecidableRv64gc p.isa env.cfg plain sanImg
      else Shapes.agreementDecidable p.isa env.cfg plain sanImg

/-- Whether the statement is untranslated: it needs the distribution and the harness has none,
or it names a build without an image. -/
def isUntranslated (s : Statement) : Bool :=
  (s.needsDistribution && p.harness.distribution.isNone) ||
    s.builds.any fun b => (p.images b).isNone

theorem withImage_eq_none_iff {α : Type _} (b : Build) (k : Image → α) :
    p.withImage b k = none ↔ p.images b = none := by
  simp [withImage]

theorem withImages_eq_none_iff {α : Type _} (san : Build) (k : Image → Image → α) :
    p.withImages san k = none ↔ p.images .plain = none ∨ p.images san = none := by
  unfold withImages withImage
  cases p.images .plain <;> simp

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
  · cases p.images .plain <;> cases p.images san <;> simp

/-- An untranslated statement denotes no proposition: in particular not `False`, nor the
bound for every distribution. -/
theorem denote?_ne_some_of_untranslated {s : Statement} (h : p.isUntranslated s = true)
    (P : s.Sort) : p.denote? s ≠ some P := by
  rw [(p.denote?_eq_none_iff s).2 h]; simp

/-- Without a distribution, a bound statement is untranslated, whatever the images. -/
theorem denote?_disagreesAtMost_of_none (h : p.harness.distribution = none) (san : Build)
    (env : EnvChoice) (rv64gc : Bool) : p.denote? (.disagreesAtMost san env rv64gc) = none := by
  simp [denote?, h]

/-! ### Every other statement means what it meant

Where the images a statement names are present (and, for a bound statement, the distribution),
`denote?` is `some` of the same proposition the former total `Problem.denote` gave, before
untranslated statements were split off (the case bodies are unchanged; the 651 generated
`<name>_eq` are `rfl`). -/

section Translated

variable {p} {san b : Build} {plain sanImg img : Image}

theorem denote?_agrees (hp : p.images .plain = some plain) (hs : p.images san = some sanImg)
    (budgets : BudgetChoice) (shape : AgreeShape) :
    p.denote? (.agrees san budgets shape) = some
      (shape.denote p.isa p.isa budgets.budgets.limSource budgets.budgets.limTarget plain
        sanImg) := by
  simp only [denote?, withImages, withImage, hp, hs]
  rfl

theorem denote?_haltsWithinBudget (h : p.images b = some img) (budgets : BudgetChoice)
    (exits : ExitChoice) :
    p.denote? (.haltsWithinBudget b budgets exits) =
      some (Shapes.haltsWithinBudget p.isa budgets.budgets.limSource exits.codes img) := by
  simp only [denote?, withImage, h]
  rfl

theorem denote?_haltsMayFail (h : p.images b = some img) (exits : ExitChoice) :
    p.denote? (.haltsMayFail b exits) = some (Shapes.haltsMayFail p.isa exits.codes img) := by
  simp only [denote?, withImage, h]
  rfl

theorem denote?_agreementDecidable (hp : p.images .plain = some plain)
    (hs : p.images san = some sanImg) (env : EnvChoice) (rv64gc : Bool) :
    p.denote? (.agreementDecidable san env rv64gc) = some
      (if rv64gc then Shapes.agreementDecidableRv64gc p.isa env.cfg plain sanImg
        else Shapes.agreementDecidable p.isa env.cfg plain sanImg) := by
  simp only [denote?, withImages, withImage, hp, hs]
  rfl

/-- With a distribution, a bound statement is the bound at it. -/
theorem denote?_disagreesAtMost {d : Distribution} (hd : p.harness.distribution = some d)
    (hp : p.images .plain = some plain) (hs : p.images san = some sanImg) (env : EnvChoice)
    (rv64gc : Bool) :
    p.denote? (.disagreesAtMost san env rv64gc) =
      some (fun bound => boundAt p.isa env rv64gc d plain sanImg bound) := by
  simp only [denote?, withImages, withImage, hd, hp, hs]
  rfl

end Translated

/-- Every image of the problem is well formed (`Images.v` `<build>_wf`): the anti-vacuity
check OSS Verify proves of each image by computation. -/
def ImagesWf : Prop := ∀ b img, p.images b = some img → ImageWf p.isa img

/-- Every statement names only builds the problem has images of. -/
def Scoped : Prop :=
  ∀ s ∈ p.harness.statements, ∀ b ∈ s.2.builds, (p.images b).isSome = true

/-- The statements of the harness that have no Lean proposition on this problem. -/
def untranslated : List (String × Statement) :=
  p.harness.statements.filter fun s => p.isUntranslated s.2

end Problem

/-! ## Launch shape

A decidable, ISA-independent part of image well-formedness that is cheap enough to check by
`decide +kernel` on a full image: some segment is mapped, the entry point lies in an
executable segment, the segments are ordered and disjoint, the program-header table is
published, and a valid initial break exists (`imageBrkSatisfiable`, LPS `Equivalence.v:555`).
`ImageWf` adds the ISA's instruction fetch at the entry point and the readability of the
program-header table (`imagePhdrsReadable`, decided separately below).

`Segment.readable`, `writable` and `executable` are `String.contains`, which does not reduce
in the kernel; `Segment.hasPerm` reads the letters through `String.toList`, which does, and
`contains_eq_hasPerm` says the two agree. -/

/-- `perms` holds the letter `c`, through `String.toList`. -/
def _root_.Silmaril.Process.LPS.Segment.hasPerm (c : Char) (s : Segment) : Bool :=
  s.perms.toList.contains c

theorem _root_.Silmaril.Process.LPS.Segment.contains_eq_hasPerm (c : Char) (s : Segment) :
    s.perms.contains c = s.hasPerm c := by
  simp [Segment.hasPerm, String.contains_char_eq]

theorem _root_.Silmaril.Process.LPS.Segment.readable_eq (s : Segment) :
    s.readable = s.hasPerm 'r' :=
  s.contains_eq_hasPerm 'r'

theorem _root_.Silmaril.Process.LPS.Segment.executable_eq (s : Segment) :
    s.executable = s.hasPerm 'x' :=
  s.contains_eq_hasPerm 'x'

/-- The entry point lies in an executable segment. -/
def entryInExecutable (img : Image) : Bool :=
  img.segments.any fun s => s.hasPerm 'x' && decide (s.base ≤ img.initPc) &&
    decide (img.initPc < s.base + s.size)

theorem entryInExecutable_eq (img : Image) :
    entryInExecutable img = img.segments.any fun s => s.executable &&
      decide (s.base ≤ img.initPc) && decide (img.initPc < s.base + s.size) := by
  simp only [entryInExecutable, Segment.executable_eq]

/-- Segments are pairwise disjoint and listed in increasing address order (`elf-snapshot`
refuses overlapping segments). -/
def segmentsOrdered : List Segment → Bool
  | a :: b :: rest => decide (a.base + a.size ≤ b.base) && segmentsOrdered (b :: rest)
  | _ => true

/-- The launch shape of an image. -/
def LaunchShape (img : Image) : Prop :=
  img.segments ≠ [] ∧ entryInExecutable img = true ∧ segmentsOrdered img.segments = true ∧
    0 < img.phdrs.num ∧ 0 < img.phdrs.ent ∧ imageBrkSatisfiable img.segments = true

instance (img : Image) : Decidable (LaunchShape img) := by
  unfold LaunchShape; infer_instance

/-- `memoryRead` with the readable test through `Segment.hasPerm`. -/
def memoryReadK (segs : List Segment) (addr : Word) (n : Nat) : Option (List Byte) :=
  match findSegment segs (uns addr) n with
  | some seg =>
    if seg.hasPerm 'r' then
      let off := (uns addr - seg.base).toNat
      (List.range n).mapM fun k => seg.byteAt (off + k)
    else none
  | none => none

theorem memoryRead_eq_K : memoryRead = memoryReadK := by
  funext segs addr n
  unfold memoryRead memoryReadK
  cases findSegment segs (uns addr) n <;> simp [Segment.readable_eq]

/-- `imagePhdrsReadable` through `memoryReadK`. -/
def imagePhdrsReadableK (segs : List Segment) (ph : PhdrInfo) : Bool :=
  decide (0 < ph.num) && decide (0 < ph.ent) &&
    (memoryReadK segs (zw ph.addr) (ph.num * ph.ent)).isSome

theorem imagePhdrsReadable_eq_K : imagePhdrsReadable = imagePhdrsReadableK := by
  funext segs ph
  simp only [imagePhdrsReadable, imagePhdrsReadableK, memoryRead_eq_K]

end Silmaril.Process.LPS.Problems
