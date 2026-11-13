module

public import Silmaril.Compiler.Driver.Options.Defs
public import Silmaril.Cerberus.Ail.Codec.Defs
public import Silmaril.Cerberus.Frontend.Parse.Defs
public import Silmaril.Compiler.C.ToMir.Defs
public import Silmaril.Compiler.Target.Backends.Defs
public import Silmaril.Compiler.Registry.Defs
/-! # The pure core of `ccomp`

Everything `ccomp` does between reading its inputs and writing its outputs, with no IO:

* `compileTU : Options → ByteArray → Except Diag ByteArray` (also `Silmaril.Compile.C.compileTU`):
  one preprocessed translation unit (the bytes of a `.i` file) to the bytes of an ELF
  relocatable object;
* `linkObjects : Options → List LinkUnit → Except Diag Linked`: ccomp objects (and the C
  library) to the object of the whole program, which the system linker combines with the startup
  code `crt0` (trusted, `tools/ccomp/runtime/crt0-x86_64.S`) into a static executable.

The driver (`Silmaril.Compile.C.Main`) is a thin IO shell around these: it reads files, runs the
preprocessor (`Silmaril.Compile.Driver.Preprocess`) and, with `--ail-from-oracle`, Cerberus for
the typed Ail (after `asmText`); then calls the core; then `as`/`ld`.

## Objects are typed Ail (link-time compilation)

A ccomp object is an ELF relocatable file whose only content is the non-allocated section
`.ccomp.ail`: the unit's typed Ail as a `cerb-oracle --level tail` document. `compileTU` checks
the unit through the middle stage (`Registry.Stage.lower`, strict), so that errors are reported
at compile time, and the link compiles all units together, because Lir has no external calls
(every call is resolved when the units are linked into one Lir program). Both use the float
mode of the options (`--float=soft`, the default, or `--float=native`), one for the whole build;
under `--float=soft` no Lir float instruction is produced, so the backend never takes the
unvalidated native-float stage `Registry.Stage.x86Native`.

## The intended theorem (a template for "`Bytes → Option Bytes`, provably a C compiler")

Let `beh` be the observable behaviours of an executable (the exit status, `stdout`, and the
signal of `abort`, as produced by the startup code from the Lir behaviour), and `C⟦src⟧ᵢ` the
set of behaviours that the C11 semantics (Cerberus Core or the Ail semantics of the Cerberus port, with
undefined behaviour as "any behaviour") allows for the translation unit `src` under the
implementation choices `ᵢ = implChoices o` (LP64, plain `char` signed, Cerberus's concrete
memory layouts, `-std`, the predefined macros having been applied by preprocessing).

    theorem compileTU_correct (o : Options) (src obj : ByteArray)
        (h : compileTU o src = .ok obj) (exe : ByteArray)
        (hl : linkExecutable o [obj] = .ok exe) :
        beh exe ⊆ C⟦src⟧_(implChoices o)

with `linkExecutable` = `linkObjects` followed by the (modelled) system link with `crt0`.
Its proof composes: the `asm` rewrite (`Registry.Stage.asm`), the frontend's agreement with
Cerberus (parse, then the Cerberus port's Cabs → Ail),
`compileUnit`'s correctness at the convention observing `main`'s result, `stdout` and
`exit`/`abort` (`docs/projects/cerberus.md`), `Mir.link`'s definitional semantics, the backend theorems
`Lir.Alloc.spill_refines` and `X86.Backend.compile_refines` (proved), the ELF writer's round
trip, and a loader statement relating crt0 to `Env.load`. A pure `Bytes → Option Bytes` C
compiler is then `fun src => (compileTU o src >>= fun obj => linkExecutable o [obj]).toOption`
(with a Lean preprocessor in front for unpreprocessed C).
-/

@[expose] public section

namespace Silmaril.Compile.Driver

open Silmaril.Cerberus Ail.Codec
open Silmaril.Compile.C (SourceUnit)

/-- The target of the options. -/
def targetArch (o : Options) : Target.Arch :=
  match o.target.getD .x86_64 with
  | .x86_64 => .x86_64
  | .rv64 => .rv64

/-- The implementation-defined choices the options fix (the parameter `ᵢ` of the intended
theorem). Only the target varies today; the rest is ccomp's one implementation. -/
structure ImplChoices where
  arch : Target.Arch
  /-- LP64 integer layouts of `Silmaril.Cerberus.Mem.Concrete.integerLayout` -/
  lp64 : Bool := true
  plainCharSigned : Bool := true
  std : Std := .c11

def implChoices (o : Options) : ImplChoices := { arch := targetArch o, std := o.std.getD .c11 }

/-! ## Translation units -/

/-- Preprocessed C → preprocessed C (`Registry.Stage.asm`): every GNU `asm` made safe to drop,
or the first one that is not rejected. It runs before either frontend (the Lean one, or Cerberus
with `--ail-from-oracle`), since both drop `asm` statements. -/
def asmText (src : ByteArray) : Except Diag ByteArray :=
  match Registry.Stage.asm src with
  | .ok t => .ok t
  | .error e => .error (.reject e)

/-- The Lean frontend: preprocessed C to typed Ail (`asmText`, then `Registry.Stage.frontend`:
`Frontend.parse`, `Frontend.desugar` and `Frontend.typecheck` of the Cerberus port). -/
def frontend (_o : Options) (src : ByteArray) : Except Diag Ail.TypedProgram := do
  match Registry.Stage.frontend (← asmText src) with
  | .ok p => .ok p
  | .error e => .error (.reject e)

/-- The typed-Ail document of a program of the Lean frontend (what a `-c` object stores). -/
def ailDocument (prog : Ail.TypedProgram) : String :=
  printTailDocument (.document Cabs.Codec.cerberusCommit Cabs.Codec.cerberusImpl prog)

/-- Decode a typed-Ail document (`cerb-oracle --level tail`, or a ccomp object's section). -/
def decodeAil (name doc : String) : Except Diag Ail.TypedProgram :=
  match readTailDocument doc with
  | .error e => .error (.usage s!"{name}: not a typed-Ail document: {e}")
  | .ok (.reject _ _ stage _ msg) => .error (.reject s!"{name}: {stage}: {msg}")
  | .ok (.document _ _ prog) => .ok prog

/-- The ccomp object of a typed-Ail program: check the unit through the middle stage (strict,
in the float mode of the options), then wrap its document `doc` (computed only when the check
passes) in the `.ccomp.ail` section. -/
def ailObject (o : Options) (prog : Ail.TypedProgram) (doc : Unit → String) :
    Except Diag ByteArray := do
  if let .error e := Registry.Stage.lower #[{ tag := "u", prog }] o.nativeFloat true then
    throw (.reject e)
  return Formats.ELF.Write.writeRelocatable (targetArch o).machine 0
    [{ name := ".ccomp.ail", flags := 0, align := 1, data := (doc ()).toUTF8 }] []

/-- The ccomp object of a typed-Ail document (`.ail` inputs, `--ail-from-oracle`). -/
def docObject (o : Options) (name doc : String) : Except Diag ByteArray := do
  (ailObject o (← decodeAil name doc) fun _ => doc).mapError
    fun d => { d with message := s!"{name}: {d.message}" }

/-- **The pure compiler of one translation unit**: preprocessed C (the bytes of a `.i` file)
to an ELF object. The intended theorem is in the module doc. -/
def compileTU (o : Options) (src : ByteArray) : Except Diag ByteArray := do
  let prog ← frontend o src
  ailObject o prog fun _ => ailDocument prog

/-! ## Objects and archives -/

/-- The typed Ail held by a ccomp object, if it is one. -/
def objectAil (b : ByteArray) : Option String := do
  let le (off n : Nat) : Nat := (List.range n).foldr (fun i acc => acc * 256 + b[off + i]!.toNat) 0
  if b.size < 64 || b[0]! != 0x7f || b[1]! != 0x45 then none
  let shoff := le 0x28 8
  let shnum := le 0x3c 2
  let shstr := le 0x3e 2
  let sh (i : Nat) := shoff + 64 * i
  let strOff := le (sh shstr + 24) 8
  let name (i : Nat) : String := Id.run do
    let mut s := ""
    let mut j := strOff + le (sh i) 4
    while j < b.size && b[j]! != 0 do
      s := s.push (Char.ofNat b[j]!.toNat); j := j + 1
    return s
  let i ← (List.range shnum).find? fun i => name i == ".ccomp.ail"
  let off := le (sh i + 24) 8
  let size := le (sh i + 32) 8
  String.fromUTF8? (b.extract off (off + size))

/-- The members of a Unix `ar` archive (the common format of GNU `ar`, with the `//` long-name
table; the symbol tables `/` and `/SYM64/` are skipped), or `none` if it is not one. -/
def arMembers (b : ByteArray) : Option (List (String × ByteArray)) := do
  if b.size < 8 || String.fromUTF8? (b.extract 0 8) != some "!<arch>\n" then none
  let field (off n : Nat) : String :=
    ((String.fromUTF8? (b.extract off (off + n))).getD "").trimAscii.toString
  let mut pos := 8
  let mut longNames : ByteArray := .empty
  let mut out : List (String × ByteArray) := []
  for _ in [0:b.size] do
    if pos + 60 > b.size then break
    let name := field pos 16
    let size ← (field (pos + 48) 10).toNat?
    let data := b.extract (pos + 60) (pos + 60 + size)
    if name == "//" then longNames := data
    else if name == "/" || name == "/SYM64/" then pure ()
    else
      let n := if name.startsWith "/" then
          match (name.drop 1).toString.toNat? with
          | some k =>
            let rest := longNames.extract k longNames.size
            let s := (String.fromUTF8? rest).getD ""
            ((s.splitOn "/\n").head?.getD "")
          | none => name
        else (name.dropEndWhile (· == '/')).toString
      out := out ++ [(n, data)]
    pos := pos + 60 + size + size % 2
  return out

/-! ## The link -/

/-- One typed-Ail unit of a link. Weak units (the C library) yield to strong definitions. -/
structure LinkUnit where
  name : String
  prog : Ail.TypedProgram
  weak : Bool := false

structure Linked where
  lir : Mir.Linked
  /-- the ELF object of the whole program -/
  object : ByteArray

/-- Lower the typed-Ail units (`Registry.Stage.lower`): the definitions reachable from `main`
(the process runtime's only reference into C), after weak resolution, with the runtime unit, in
the float mode of the options (one mode for the whole build). -/
def lowerUnits (o : Options) (units : List LinkUnit) : Except Diag (Array Mir.Unit) := do
  let sources : Array SourceUnit :=
    (units.zipIdx.map fun (u, i) => { tag := s!"u{i}", prog := u.prog, weak := u.weak }).toArray
  match Registry.Stage.lower sources o.nativeFloat with
  | .ok us => return us
  | .error e => throw (.reject e)

/-- Optimize the Mir units (`Registry.Stage.mirOpt`: the registered Mir passes in order). -/
def optimizeMir (mirUnits : Array Mir.Unit) : Array Mir.Unit := Registry.Stage.mirOpt mirUnits

/-- Link the Mir units (`Registry.Stage.link`, `Mir.link`). -/
def linkMir (mirUnits : Array Mir.Unit) : Except Diag Mir.Linked :=
  match Registry.Stage.link mirUnits with
  | .ok l => .ok l
  | .error e => .error (.reject s!"link: {e}")

/-- The backend (`Registry.backend`): spilling, the verified backend, the object. -/
def backend (o : Options) (linked : Mir.Linked) : Except Diag ByteArray :=
  match Registry.backend (targetArch o) linked with
  | .ok b => .ok b
  | .error e => .error (.reject s!"unsupported: {e}")

/-- The linked Lir program, printed (`--emit-lir`). -/
def showLir (l : Mir.Linked) : String := Registry.showLir l

/-- **The pure link**: typed-Ail units to the object of the whole program. -/
def linkObjects (o : Options) (units : List LinkUnit) : Except Diag Linked := do
  let linked ← linkMir (optimizeMir (← lowerUnits o units))
  return { lir := linked, object := ← backend o linked }

end Silmaril.Compile.Driver

namespace Silmaril.Compile.C

/-- **The pure C compiler of one translation unit** (`Silmaril.Compile.Driver.compileTU`):
preprocessed C bytes to ELF object bytes, no IO. The driver calls the `Driver` name (driver
code, for the evaluator's stage registry); this is the same function. -/
abbrev compileTU : Driver.Options → ByteArray → Except Driver.Diag ByteArray := Driver.compileTU

theorem compileTU_eq : compileTU = Driver.compileTU := rfl

end Silmaril.Compile.C
