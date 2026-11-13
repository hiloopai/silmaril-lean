module

public import Silmaril.Compiler.Contract.Defs
public import Silmaril.Cerberus.Ail.Reject.Defs
public import Silmaril.Cerberus.Frontend.Parse.Defs
public import Silmaril.Cerberus.Frontend.Desugar.Defs
public import Silmaril.Cerberus.Frontend.Typing.Defs
public import Silmaril.Compiler.C.Asm.Defs
public import Silmaril.Compiler.C.ToMir.Defs
public import Silmaril.Compiler.Target.Backends.Defs
public import Silmaril.Compiler.Target.RenameCheck.Defs
public import Silmaril.Compiler.Mir.LinkCorrect.Defs
public import Silmaril.Compiler.Mir.Pass.Defs
public import Silmaril.Compiler.Mir.CSE.Defs
public import Silmaril.Compiler.Mir.ConstProp.Defs
public import Silmaril.Compiler.Mir.DeadCode.Defs
public import Silmaril.Compiler.Mir.LoadForward.Defs
public import Silmaril.Compiler.Mir.DeadCall.Defs
public import Silmaril.Compiler.Mir.JumpThread.Defs
public import Silmaril.Compiler.Mir.StrengthReduce.Defs
public meta import Silmaril.Compiler.Target.ObjectContract.Defs
/-! # The stage registry of `ccomp`

Every stage of the compiler that the driver (`Silmaril/Compile/C/Main.lean`) runs is a
function `Registry.Stage.key` here, with one row in `rows`: its key, what it does, and
the name of the theorem that validates it (`none` while it is trusted). This mirrors the
pass registry of the formalized Binaryen (`Silmaril/Wasm/Binaryen/PassRegistry.lean`).

**Validated.** A row is validated when its theorem exists (the double backticks make
a missing name fail to elaborate), proves the frozen contract of its key
(`Silmaril/Compile/Contract.lean`: `Contract.key Stage.key`, or `Contract.key` for a
proposition), is sorry-free and uses only the standard axioms. A validator counts like
a proof: make the stage run the transformation and a proved checker, and prove the
contract for the checked stage.

**Registered.** The evaluator follows the constants the executable's `main` uses: it
stops at each `Registry.Stage.*` function (a stage of the pipeline, which must have a
row) and reports any other use of compiler code (`Silmaril.Compile.{C,Mir,Target}`,
`Silmaril.Machine`, `Silmaril.X86`, `Silmaril.RiscV`, the Lean frontend) as an
unregistered stage. So a new pass is added here as a new `Stage` function and row, and
the driver calls it through the registry.

The evaluator reports `trusted_unvalidated` (stages, required or used, with no valid
theorem) and `validated_stages` (rows with a contract and a valid theorem).

## Adding or validating a stage

1. Define the stage function as `Registry.Stage.key` and call it from the driver (or
   from `backend` below).
2. Add the row `⟨"key", "what it does", none⟩`.
3. To validate it: prove `Contract.key Stage.key` (ask for a contract if the key has
   none) in a module the driver imports, and set the row's theorem.
-/

@[expose] public section

namespace Silmaril.Compile.Registry

open Silmaril.Machine
open Silmaril.Cerberus

/-- One registered stage. -/
structure Row where
  /-- The key: `Stage.key` is its function and `Contract.key` its contract. -/
  key : String
  /-- What the stage does. -/
  stage : String
  /-- The theorem that validates it: a proof of its contract (`none`: trusted). -/
  proof : Option Lean.Name

/-- What Cerberus's parser sees: the text without its final newline. -/
def cppText (b : ByteArray) : ByteArray :=
  if b.size > 0 && b[b.size - 1]! == '\n'.toUInt8 then b.extract 0 (b.size - 1) else b

/-- The Mir-to-Mir passes `Stage.mirOpt` runs, in order, each with its proof of
`Contract.mirPass` (directly or through a proved checker with fallback). The driver calls
`Stage.mirOpt` between `lower` and `link`.

* `constProp`: constant and copy propagation, folding, constant branches, from block
  entry facts that an unverified fixpoint computes across blocks and a proved check
  validates per function (block-local when the check fails; `Mir.ConstProp`, a lock-step
  simulation);
* `strengthReduce`: `c := 2^k` followed by `a * c`, `a /u c` or `a %u c` (64-bit) becomes
  `c := k; a << c`, `c := k; a >>u c` or `c := 2^k - 1; a & c` when `c` is dead after it,
  under a checked liveness certificate, the function unchanged when the check fails
  (`Mir.StrengthReduce`, a lock-step simulation with frames that agree on live registers);
* `cse`: block-local common-subexpression elimination of pure integer unary and
  non-faulting binary operations, with up to 32 facts (`Mir.CSE`, equal-frame
  lock-step simulation);
* `jumpThread`: jumps and branches retargeted past the blocks that only jump (no
  instruction, a `jump` terminator), every block kept (`Mir.JumpThread`, a lock-step
  simulation from the output to the input);
* `deadCode`: deletion of dead register operations under a checked liveness certificate,
  the function unchanged when the check fails (`Mir.DeadCode`);
* `loadForward`: block-local full-width store-to-load forwarding and redundant-load
  elimination (`Mir.LoadForward`, a simulation with equal frames and memory through
  `Mir.MemoryFuncPass`);
* `deadCall`: deletion of the calls to symbols that no unit defines from the blocks a
  checked reachability shows unreachable (the `link_error` idiom), every other
  instruction and every defined symbol's reference kept (`Mir.DeadCall`). -/
def mirPasses : List Mir.Pass := [
  ⟨"constProp", Mir.ConstProp.run, Mir.ConstProp.correct⟩,
  ⟨"strengthReduce", Mir.StrengthReduce.run, Mir.StrengthReduce.correct⟩,
  Mir.CSE.pass,
  ⟨"jumpThread", Mir.JumpThread.run, Mir.JumpThread.correct⟩,
  ⟨"deadCode", Mir.DeadCode.run, Mir.DeadCode.correct⟩,
  Mir.LoadForward.pass,
  ⟨"deadCall", Mir.DeadCall.run, Mir.DeadCall.correct⟩]

namespace Stage

/-- Preprocessed C → preprocessed C: make every GNU `asm` safe to drop, or reject the
first one that is not (`C.Asm.lower`). It runs before either frontend (the Lean one or,
with `--ail-from-oracle`, Cerberus), since both drop `asm` statements. -/
def asm (text : ByteArray) : Except String ByteArray :=
  match C.Asm.lower text with
  | .ok t => .ok t
  | .error (p, why) => .error s!"{p.file}:{p.line}: unsupported: {why}"

/-- Preprocessed C → typed Ail in Lean, as Cerberus's pipeline does (`Cabs.Main.frontend`
at level `tail`): the Cabs parser (`Cerberus.Frontend.parse`), `Frontend.desugar` (its
symbols under the MD5 `Ail.fileDigest` of the text) and `Frontend.typecheck` .
The error is `STAGE: MESSAGE`. -/
def frontend (text : ByteArray) : Except String Ail.TypedProgram :=
  let run : Except Ail.Reject Ail.TypedProgram := do
    let unit ← (Frontend.parse (cppText text)).mapError Ail.Reject.ofCabs
    Frontend.typecheck (← Frontend.desugar (Ail.fileDigest text) unit)
  run.mapError fun r => s!"{r.stage}: {r.message}"

/-- C → Mir: lower the definitions reachable from `main` (`C.compileReachableUnits`)
and prepend the process runtime unit (`Target.unit`). With `strict`, lower every
definition for the separate-compilation check (`-c`), without a runtime unit.
Both paths use the same float mode for the whole build; soft-float is the default
until `x86Native` is validated (ideas 567-570). -/
def lower (sources : Array C.SourceUnit) (nativeFloat : Bool := false)
    (strict : Bool := false) : Except String (Array Mir.Unit) := do
  let opts : C.LowerOptions := { float := if nativeFloat then .native else .soft }
  if strict then
    return ← sources.mapM fun s => (C.compileUnit s.tag s.prog opts).mapError fun e => s!"unsupported: {e}"
  let units ← match C.compileReachableUnits sources ["main"] opts with
    | .ok us => pure us
    | .error e => throw s!"unsupported: {e}"
  let some main := (units.flatMap (·.funcs)).find? (·.name == "main")
    | throw "undefined reference to main"
  return #[Target.unit main.params.length main.results] ++ units

/-- Mir → Mir: run the registered passes `mirPasses` in order (`Mir.Pass.runAll`). -/
def mirOpt : Array Mir.Unit → Array Mir.Unit := Mir.Pass.runAll mirPasses

/-- Mir → Lir: resolve the symbols of the units into one Lir program (`Mir.link`), then
check the result against the independent Mir semantics (`Mir.LinkCheck.check`, proved
sound in `Mir.LinkCorrect.check_sound`) and reject a link that fails the check. -/
def link (units : Array Mir.Unit) : Except String Mir.Linked :=
  match Mir.link Target.layout units with
  | .ok l =>
    if Mir.LinkCheck.check Target.layout Target.layout.dataBase units l then .ok l
    else .error "link: the linked program failed the link check (Mir.LinkCheck)"
  | .error e => .error e.message

/-- Renumber the virtual registers: the most used share the 7 register homes
(`RegAlloc.renumber 7`), checked by a liveness certificate, the program unchanged when
the check fails (`RegAlloc.renumberChecked 7`). -/
def renumber : Lir.Prog Nat → Lir.Prog Nat := Target.RegAlloc.renumberChecked 7

/-- Spill every virtual register from 7 on into a stack slot (`firstK 7`). -/
def spill : Lir.Prog Nat → Lir.Prog (Fin 9) := Lir.Alloc.spill (Lir.Alloc.firstK 7)

/-- The verified x86-64 code generator (run as `compileX86Fast`, row `layout`). -/
def codegen : ∀ {P : Type}, X86.Backend.Assign P → Lir.Prog P → Nat →
    Except (List X86.Backend.Error) X86.Backend.Image :=
  @X86.Backend.compile

/-- Native scalar SSE2 code generation, unvalidated for now. `none` means
there are no float ops, so the caller must use the proved code generator. Intended
refinement: `X86Native.compile` on `X86.Float.Machine`, with the default MXCSR;
the integer chunks reuse the existing simulation and each float sequence implements
`Lir.FOp.eval`. -/
def x86Native (q : Lir.Prog (Fin 9)) :
    Option (Except (List X86.Backend.Error) (ByteArray × Array Nat)) :=
  Target.nativeCodeX86 q

/-- Wrap code and the initial memory image in an ELF relocatable object. The verified
backend supplies an image; the native emitter supplies encoded bytes and entry offsets.
Both representations use the same object writer and memory layout. -/
def object (l : Mir.Linked) (q : Lir.Prog (Fin 9))
    (img : X86.Backend.Image ⊕ (ByteArray × Array Nat)) : ByteArray :=
  let code : Target.Code := match img with
    | .inl img =>
      ⟨Target.toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩
    | .inr (bytes, entries) => ⟨bytes, entries⟩
  Target.object .x86_64 l code

/-- The RISC-V backend (spill, `RiscV.Backend.compile`, object), not on the evaluated
x86-64 path. -/
def rv64 (l : Mir.Linked) : Except String ByteArray := Target.compile .rv64 l

end Stage

/-- The x86-64 backend as the driver runs it. -/
def backendX86 (l : Mir.Linked) : Except String ByteArray :=
  let q := Stage.spill (Stage.renumber l.prog)
  match Stage.x86Native q with
  | some (.error es) => .error s!"x86-64 native-float backend: {repr (es.take 5)}"
  | some (.ok img) => .ok (Stage.object l q (.inr img))
  | none =>
    match Stage.codegen (X86.Backend.Assign.fin 9 (by decide)) q 0 with
    | .error es => .error s!"x86-64 backend: {repr (es.take 5)}"
    | .ok img => .ok (Stage.object l q (.inl img))

/-- The backend of the driver: linked Lir to an object file. -/
def backend : Target.Arch → Mir.Linked → Except String ByteArray
  | .x86_64 => backendX86
  | .rv64 => Stage.rv64

/-- The registered x86-64 backend is the previous `Target.compile`. -/
theorem backend_eq_compile (arch : Target.Arch) : backend arch = Target.compile arch := by
  funext l
  cases arch
  · simp only [backend, backendX86, Target.compile, Target.codeX86, Stage.renumber,
      Stage.spill, Stage.x86Native, Stage.codegen, Stage.object]
    cases Target.nativeCodeX86
        (Lir.Alloc.spill (Lir.Alloc.firstK 7) (Target.RegAlloc.renumberChecked 7 l.prog)) with
    | none =>
      cases X86.Backend.compile (X86.Backend.Assign.fin 9 (by decide))
        (Lir.Alloc.spill (Lir.Alloc.firstK 7) (Target.RegAlloc.renumberChecked 7 l.prog)) 0 <;> rfl
    | some r =>
      cases r with
      | error es => rfl
      | ok img => cases img; rfl
  · rfl

/-- The Lir program of a link, printed (`ccomp --emit-lir`). -/
def showLir (l : Mir.Linked) : String := toString (repr l.prog)

/-! ## Proofs of the contracts -/

namespace Proof

theorem renumber : Contract.renumber Stage.renumber :=
  Target.RegAlloc.renumberChecked_refines 7

theorem spill : Contract.spill Stage.spill := fun _ =>
  Lir.Alloc.spill_refines (Lir.Alloc.firstK_valid 7)

theorem codegen : Contract.codegen @Stage.codegen := @X86.Backend.compile_refines

/-- **The object stage's round trip**: the ELF
reader (`Formats.ELF.Object.readObject`) gives back what `Stage.object` writes, the
`.text` code bytes, the `.rodata.ccomp` memory image and the `FUNC` and startup symbols
(`Target.objectSections`, `Target.objectSymbols`), for an object under 4 GiB with NUL-free
function names and 64-bit offsets (`ObjectCorrect.readObject_object`). -/
theorem objectRoundTrip (l : Mir.Linked) (q : Lir.Prog (Fin 9)) (img : X86.Backend.Image)
    (h : Target.ObjectCorrect.ObjectInputs l
      ⟨Target.toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩)
    (hsize : (Stage.object l q (.inl img)).size < 2 ^ 32) :
    Formats.ELF.readObject (Target.ObjectCorrect.toBits (Stage.object l q (.inl img))) =
      some (Target.ObjectCorrect.expected 62 0
        (Target.objectSections l
          ⟨Target.toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩)
        (Target.objectSymbols l
          ⟨Target.toBytes img.code, ((List.range q.funcs.length).map img.layout.func).toArray⟩)) :=
  Target.ObjectCorrect.readObject_object .x86_64 h hsize

/-- The emitted object satisfies the frozen ELF contract, including its symbols. -/
theorem object : Contract.object Stage.object :=
  Target.ObjectContract.object_contract _ fun _ _ x => by
    cases x with
    | inl _ => rfl
    | inr p => cases p; rfl

/-- The registered Mir passes, run in order, refine their input: each proves
`Contract.mirPass`, which holds for the identity and is closed under composition
(`Mir.Pass.runAll_correct`). -/
theorem mirOpt : Contract.mirOpt Stage.mirOpt := Mir.Pass.runAll_correct mirPasses

/-- The checked link refines the independent Mir semantics (`Mir.LinkCorrect`). -/
theorem link : Contract.link Stage.link := by
  intro us l h memSize hm _
  unfold Stage.link at h
  split at h
  · rename_i l' _
    split at h
    · rename_i hc
      cases h
      exact Mir.LinkCorrect.check_sound _ _ _ _ hc memSize hm
    · cases h
  · cases h

end Proof

/-- **The stage registry.** -/
def rows : List Row := [
  ⟨"asm", "preprocessed C → preprocessed C: GNU asm made safe to drop, or rejected \
    (C.Asm.lower); before either frontend", none⟩,
  ⟨"frontend", "preprocessed C → typed Ail in Lean (Cabs parser, desugaring and typing, \
    the Cerberus port); --ail-from-oracle takes Cerberus's typed Ail instead (not a stage then)", none⟩,
  ⟨"lower", "typed Ail → Mir units (reachable definitions plus runtime, or strict -c; \
    native/soft float mode)", none⟩,
  ⟨"mirOpt", "Mir units → Mir units: the registered Mir passes in order (mirPasses: \
    constant and copy propagation, strength reduction by powers of two, block-local \
    common-subexpression elimination, jump threading, checked dead-code elimination, \
    block-local full-width load forwarding, dead calls to undefined symbols in unreachable \
    blocks)", some ``Proof.mirOpt⟩,
  ⟨"link", "Mir units → one Lir program and memory image (Mir.link), checked against \
    the independent Mir semantics (Mir.LinkCheck)", some ``Proof.link⟩,
  ⟨"renumber", "virtual register renumbering by liveness (RegAlloc.renumber 7), checked by \
    a liveness certificate with the identity as fallback (RegAlloc.renumberChecked 7)",
    some ``Proof.renumber⟩,
  ⟨"spill", "spilling onto 7 register homes (Lir.Alloc.spill (firstK 7))",
    some ``Proof.spill⟩,
  ⟨"codegen", "Lir → x86-64 machine code (X86.Backend.compile)", some ``Proof.codegen⟩,
  ⟨"x86Native", "Lir with float ops → scalar SSE2 code (Target.X86Native.compile); \
    unvalidated for now; used only for programs containing float ops", none⟩,
  ⟨"layout", "tabulated layout, the executed X86.Backend.compile (compileX86Fast, @[csimp])",
    some ``Silmaril.Compile.Target.compile_eq_compileX86Fast⟩,
  ⟨"object", "code and memory image → ELF relocatable object (Target.object, ELF writer)",
    some ``Proof.object⟩,
  ⟨"rv64", "the RISC-V backend (not on the evaluated x86-64 path)", none⟩]

end Silmaril.Compile.Registry
