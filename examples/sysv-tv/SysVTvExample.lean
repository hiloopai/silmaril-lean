module

public import ProjectSelfTest
public import Silmaril.Project.Shapes.C.Thms
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.Shapes.C.Defs
public meta import Silmaril.X86.Bir9.Defs

/-!
# Worked example: one C function, two builds, the System V translation-validation shapes

`examples/sysv-tv/max2/max2.c` defines `int max2(int a, int b)`. It was compiled with gcc 14.2.0
at `-O0` and `-O2` (`examples/sysv-tv/max2/build.sh`, a pinned container image; the receipt
`RECEIPTS.sha256` has the hashes). The objects are registered artifacts, read here as values.
The rows (`docs/projects/sysv-tv.md` explains the shapes):

| row | shape | verdict |
|---|---|---|
| `silmaril.sysv_tv.max2.{o0,o2}_obj_value.parses` | the two objects, read as bytes | proved (`silmaril_decide`) |
| `silmaril.sysv_tv.max2.o0.code` | `elf.object_fn`: the `-O0` object defines `max2` with the bytes `O0.code` | proved (kernel) |
| `silmaril.sysv_tv.max2.o2.code` | the same at `-O2` | proved (kernel) |
| `silmaril.sysv_tv.max2.elaborates` | `c.elaborates_to`: the C function elaborates to `cfn` | open (`Task.elaborates`); its first conjunct, the elaborator's output, is proved (`elab_ok`, `cbv`); the procedure's shape is checked by compiled evaluation |
| `silmaril.sysv_tv.max2.o2.lifts` | `sysv.lifts.open9`: the Bir9 block `O2.block` is a lift of the `-O2` code | open (`Task.o2_lifts`) |
| `silmaril.sysv_tv.max2.o2.ir_refines` | `c.ir_refines`: that block corresponds to `max2` | open (`Task.o2_ir_refines`) |
| `silmaril.sysv_tv.max2.o0.compiles_to` | `c.compiles_to.open9`: the `-O0` code implements `max2` | open (`Task.o0_compiles_to`) |
| `silmaril.sysv_tv.max2.o2.compiles_to` | the same at `-O2` | proved from the two `-O2` rows above (`o2_compiles_to_of`), so open with them |
| `silmaril.sysv_tv.max2.builds` | `c.compiles_to.builds`: both builds implement `max2` | proved from the per-build rows (`builds_of`), so open with them |

Same source, two builds: the C side (`cfn`, its elaboration row) is shared; each build
has its own placed code and its own rows. The `-O0` build is checked against C directly; the
`-O2` build goes through its lift, and `CompilesTo.of_lift` composes the two rows.
-/

namespace SysVTvExample

open Silmaril.Cerberus
open Silmaril.Project.Shapes
open Silmaril.Project.Shapes.C
open Silmaril.Project.Shapes.SysV (bir9 Bir9Fn)
open Silmaril.X86.SystemV.CApi (Signature Scalar)

@[expose] public section

/-! ## The C side, shared by both builds -/

/-- The C source, verbatim (`examples/sysv-tv/max2/max2.c`). -/
def cText : String :=
  "/* The worked example of the System V translation-validation shapes\n   (docs/projects/sysv-tv.md): one C function, compiled at -O0 and -O2. */\nint max2(int a, int b)\n{\n  if (a > b)\n    return a;\n  return b;\n}\n"

/-- `int max2(int, int)`: two `int` arguments, an `int` result. -/
def sig : Signature := ⟨[.int32, .int32], some .int32⟩

set_option maxRecDepth 100000 in
/-- Its typed Ail: the output of the Lean Cerberus frontend, quoted. -/
def ail : Ail.TypedProgram := ail_program% "($tuple ($none) (sigma ($list ($tuple (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 3 (SD_Id ($str \"max2\"))) ($tuple ($loc_region ($str \"\") 3 5 ($str \"\") 3 9) (Attrs ($list)) (Decl_function ($false) ($tuple (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 1 ($str \"\") 3 4))) (Basic (Integer (Signed (Int_)))))) ($list ($tuple (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 10 ($str \"\") 3 13))) (Basic (Integer (Signed (Int_))))) ($false)) ($tuple (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 17 ($str \"\") 3 20))) (Basic (Integer (Signed (Int_))))) ($false))) ($false) ($false) ($false))))) ($list) ($list ($tuple (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 3 (SD_Id ($str \"max2\"))) ($tuple ($loc_region ($str \"\") 3 1 ($str \"\") 8 2) 4 (Attrs ($list)) ($list (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 1 (SD_ObjectAddress ($str \"a\"))) (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 2 (SD_ObjectAddress ($str \"b\")))) (statement ($loc_region ($str \"\") 4 1 ($str \"\") 8 2) (desug_info ($false) ($none)) (Attrs ($list)) (AilSblock ($list) ($list (statement ($loc_region ($str \"\") 5 3 ($str \"\") 6 14) (desug_info ($false) ($none)) (Attrs ($list)) (AilSif (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list) ($loc_region ($str \"\") 5 7 ($str \"\") 5 12) (AilEbinary (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list) ($loc_region ($str \"\") 5 7 ($str \"\") 5 8) (AilErvalue (AnnotatedExpression (GenLValueType (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 10 ($str \"\") 3 13))) (Basic (Integer (Signed (Int_))))) ($false)) ($list) ($loc_region ($str \"\") 5 7 ($str \"\") 5 8) (AilEident (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 1 (SD_ObjectAddress ($str \"a\"))))))) (Gt) (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list) ($loc_region ($str \"\") 5 11 ($str \"\") 5 12) (AilErvalue (AnnotatedExpression (GenLValueType (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 17 ($str \"\") 3 20))) (Basic (Integer (Signed (Int_))))) ($false)) ($list) ($loc_region ($str \"\") 5 11 ($str \"\") 5 12) (AilEident (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 2 (SD_ObjectAddress ($str \"b\"))))))))) (statement ($loc_region ($str \"\") 6 5 ($str \"\") 6 14) (desug_info ($false) ($none)) (Attrs ($list)) (AilSreturn (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list (Astd ($str \"§6.8.4.1#1\"))) ($loc_region ($str \"\") 6 12 ($str \"\") 6 13) (AilErvalue (AnnotatedExpression (GenLValueType (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 10 ($str \"\") 3 13))) (Basic (Integer (Signed (Int_))))) ($false)) ($list (Astd ($str \"§6.8.4.1#1\"))) ($loc_region ($str \"\") 6 12 ($str \"\") 6 13) (AilEident (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 1 (SD_ObjectAddress ($str \"a\"))))))))) (statement ($loc_region ($str \"\") 5 3 ($str \"\") 6 14) (desug_info ($false) ($none)) (Attrs ($list)) (AilSskip)))) (statement ($loc_region ($str \"\") 7 3 ($str \"\") 7 12) (desug_info ($false) ($none)) (Attrs ($list)) (AilSreturn (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list (Astd ($str \"§6.5.16.1#1, bullet 1\"))) ($loc_region ($str \"\") 7 10 ($str \"\") 7 11) (AilErvalue (AnnotatedExpression (GenLValueType (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 3 17 ($str \"\") 3 20))) (Basic (Integer (Signed (Int_))))) ($false)) ($list (Astd ($str \"§6.5.16.1#1, bullet 1\"))) ($loc_region ($str \"\") 7 10 ($str \"\") 7 11) (AilEident (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 2 (SD_ObjectAddress ($str \"b\"))))))))))))))) ($list) ($list) ($map ($tuple (Identifier ($loc_region ($str \"\") 3 5 ($str \"\") 3 9) ($str \"max2\")) ($tuple (Symbol ($str \"b85860f8e811e8fbcdffc6d680a3c212\") 3 (SD_Id ($str \"max2\"))) (IK_definition)))) ($map) ($map) ($list) ($list) ($list) ($list) ($list) ($map)))"

/-- The typed-Ail document of a program (to compare programs by their printed form). -/
def tailText (p : Ail.TypedProgram) : String := Ail.Codec.printTailDocument (.document "" "" p)

-- C → typed Ail: the frontend, run by compiled evaluation (its typing pass is `partial`), gives
-- exactly the quoted `ail`.
#guard (FrontendAil cText).toOption.map tailText == some (tailText ail)

/-- An empty file (only to make `cfn` total; the elaboration is checked to succeed below). -/
def emptyFile : Codec.FileBindings := ⟨none, .normal, [], [], [], [], [], [], [], [], []⟩

/-- The elaborated file. -/
def elaborated : Codec.FileBindings := ((ElabAil ail).toOption).getD emptyFile

#guard (ElabAil ail).toOption.isSome

/-- The procedure `max2` of the elaborated file: its symbol and body. -/
def proc : Option (Sym × Core.Dynamics.EE) :=
  match procedureNamed elaborated "max2" with
  | some (s, .procedure _ _ _ _ body) => some (s, body)
  | _ => none

#guard proc.isSome

/-- The parameter objects of `max2`, as the file's function information records them. -/
def params : List (Sym × Ctype) :=
  match proc with
  | some (s, _) =>
    match elaborated.funInfo.find? (fun e => e.1.key == s.key) with
    | some (_, info) => info.2.2.2.1.filterMap fun (o, t) => o.map (·, t)
    | none => []
  | none => []

#guard params.length == 2

/-- **`max2` as Cerberus Core**: the elaborated file, its parameters and its body. -/
def cfn : CFn sig where
  file := elaborated.toFile
  params := params
  body := match proc with
    | some (_, body) => body
    | none => .mk [] (.pure (.mk [] () (.val .unit)))

/-! ## Build `-O0` -/

namespace O0

/-- The `.text` bytes of `max2` in `O0/max2.o` (offset 0): the `-O0` frame (`push %rbp`, the
arguments stored at `-4(%rbp)`, `-8(%rbp)`, the compare and branch, `pop %rbp; ret`). -/
def code : List (BitVec 8) :=
  [0x55, 0x48, 0x89, 0xe5, 0x89, 0x7d, 0xfc, 0x89, 0x75, 0xf8, 0x8b, 0x45, 0xfc, 0x3b, 0x45, 0xf8,
    0x7e, 0x05, 0x8b, 0x45, 0xfc, 0xeb, 0x03, 0x8b, 0x45, 0xf8, 0x5d, 0xc3]

/-- Placed at `0x401000`, entered at offset 0. -/
def placement : Placement := ⟨0x401000, code, 0⟩

/-- The build: gcc 14.2.0 `-O0`; it writes 16 bytes below the entry `rsp` (the saved `rbp`
and the two red-zone slots). -/
def build : Build := ⟨"gcc 14.2.0 -O0", placement, 16⟩

end O0

/-! ## Build `-O2` -/

namespace O2

/-- The `.text` bytes of `max2` in `O2/max2.o`: `cmp %esi,%edi; mov %esi,%eax;
cmovge %edi,%eax; ret`. -/
def code : List (BitVec 8) :=
  [0x39, 0xf7, 0x89, 0xf0, 0x0f, 0x4d, 0xc7, 0xc3]

/-- Placed at `0x401000`, entered at offset 0. -/
def placement : Placement := ⟨0x401000, code, 0⟩

/-- The build: gcc 14.2.0 `-O2`; it writes no stack. -/
def build : Build := ⟨"gcc 14.2.0 -O2", placement, 0⟩

/-- The code decoded by the model's decoder (`Silmaril.X86.Ext.decode`), as a Bir9 listing
(`fuel` bounds the number of instructions). -/
def listingOf : Nat → List (BitVec 8) → Option (List (Silmaril.X86.Bir9.LInstr × Nat))
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, bytes => do
    let (i, len) ← Silmaril.X86.Ext.decode bytes
    if len = 0 then none else
    let rest ← listingOf fuel (bytes.drop len)
    pure ((.ext i, len) :: rest)

/-- The listing of the `-O2` code. -/
def listing : List (Silmaril.X86.Bir9.LInstr × Nat) := (listingOf 16 code).getD []

#guard listing.length == 4

/-- **The lifted IR function**: the Bir9 block of the listing (`Silmaril.X86.Bir9.liftBlock`,
whose soundness is `Silmaril.X86.Bir9.liftBlock_sound`). -/
def block : Silmaril.X86.Bir9.Block :=
  (Silmaril.X86.Bir9.liftBlock listing).getD ⟨[], [], .entry, .rip, []⟩

#guard (Silmaril.X86.Bir9.liftBlock listing).isSome

/-- The Bir9 leaf function of the `-O2` build. -/
def birFn : Bir9Fn := ⟨sig, block, 0⟩

end O2

end

end SysVTvExample

/-! ## The rows -/

silmaril value silmaril.sysv_tv.max2.o0_obj_value : bytes := "examples/sysv-tv/max2/O0/max2.o"
silmaril value silmaril.sysv_tv.max2.o2_obj_value : bytes := "examples/sysv-tv/max2/O2/max2.o"

-- The bytes: tied to the registered objects by the kernel.
silmaril instance silmaril.sysv_tv.max2.o0.code := silmaril.shapes.elf.object_fn
  (obj := silmaril.sysv_tv.max2.o0_obj_value) (fn := "max2") (code := SysVTvExample.O0.code)
silmaril instance silmaril.sysv_tv.max2.o2.code := silmaril.shapes.elf.object_fn
  (obj := silmaril.sysv_tv.max2.o2_obj_value) (fn := "max2") (code := SysVTvExample.O2.code)

-- C to Core, shared by both builds.
silmaril instance silmaril.sysv_tv.max2.elaborates := silmaril.shapes.c.elaborates_to
  (ail := SysVTvExample.ail) (name := "max2") (F := SysVTvExample.cfn)

-- Build -O0: x86 to C directly.
silmaril instance silmaril.sysv_tv.max2.o0.compiles_to := silmaril.shapes.c.compiles_to.open9
  (p := SysVTvExample.O0.placement) (frame := 16) (F := SysVTvExample.cfn)

-- Build -O2: x86 to IR (a Bir9 block), IR to C, and their composition.
silmaril instance silmaril.sysv_tv.max2.o2.lifts := silmaril.shapes.sysv.lifts.open9
  (p := SysVTvExample.O2.placement) (frame := 0) (I := Silmaril.Project.Shapes.SysV.bir9)
  (f := SysVTvExample.O2.birFn)
silmaril instance silmaril.sysv_tv.max2.o2.ir_refines := silmaril.shapes.c.ir_refines
  (I := Silmaril.Project.Shapes.SysV.bir9) (f := SysVTvExample.O2.birFn) (F := SysVTvExample.cfn)
silmaril instance silmaril.sysv_tv.max2.o2.compiles_to := silmaril.shapes.c.compiles_to.open9
  (p := SysVTvExample.O2.placement) (frame := 0) (F := SysVTvExample.cfn)

-- Same source, both builds.
silmaril instance silmaril.sysv_tv.max2.builds := silmaril.shapes.c.compiles_to.builds
  (M := Silmaril.X86.Open9.isa) (F := SysVTvExample.cfn)
  (builds := [SysVTvExample.O0.build, SysVTvExample.O2.build])

namespace SysVTvExample

/-- **The `-O0` object defines `max2` with `O0.code`.** -/
@[answers "silmaril.sysv_tv.max2.o0.code" thm] public theorem o0_code :
    silmaril.sysv_tv.max2.o0.code :=
  Silmaril.Project.Shapes.SysV.ObjectFn.of_blob 0 (Silmaril.Project.Shapes.blob_of_decode rfl rfl)
    (by decide +kernel)

/-- **The `-O2` object defines `max2` with `O2.code`.** -/
@[answers "silmaril.sysv_tv.max2.o2.code" thm] public theorem o2_code :
    silmaril.sysv_tv.max2.o2.code :=
  Silmaril.Project.Shapes.SysV.ObjectFn.of_blob 0 (Silmaril.Project.Shapes.blob_of_decode rfl rfl)
    (by decide +kernel)

@[solves "silmaril.sysv_tv.max2.o0_obj_value.parses"] public theorem o0_parses :
    silmaril.sysv_tv.max2.o0_obj_value.parses := by
  silmaril_decide

@[solves "silmaril.sysv_tv.max2.o2_obj_value.parses"] public theorem o2_parses :
    silmaril.sysv_tv.max2.o2_obj_value.parses := by
  silmaril_decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
attribute [local cbv_eval] Silmaril.Cerberus.Elaboration.Expressions.expression.eq_def
  List.mergeSort_pair List.mergeSort_nil List.mergeSort_singleton in
/-- **The elaborator accepts `max2`'s typed Ail** and gives `elaborated` (kernel-checked: `cbv`
evaluates the elaborator). The first conjunct of the `elaborates` row. -/
public theorem elab_ok : Silmaril.Project.Shapes.C.ElabAil ail = .ok elaborated := by
  cbv

/-- Both placements can be entered for every argument tuple (the first conjunct of the
`compiles_to` and `lifts` rows). -/
public theorem o0_enterable : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open9.isa
    O0.placement sig 16 :=
  Silmaril.Project.Shapes.SysV.Enterable.of_fits (fun _ => trivial) (by decide) (by decide)
    (by decide)

public theorem o2_enterable : Silmaril.Project.Shapes.SysV.Enterable Silmaril.X86.Open9.isa
    O2.placement sig 0 :=
  Silmaril.Project.Shapes.SysV.Enterable.of_fits (fun _ => trivial) (by decide) (by decide)
    (by decide)

/-! ### Open rows, frozen as `Task` statements -/

/-- Open: C to Core (checked by compiled evaluation above; a kernel proof evaluates the
elaborator, as `cbv` can). -/
public def Task.elaborates : Prop := silmaril.sysv_tv.max2.elaborates
/-- Open: the `-O0` code implements `max2`. -/
public def Task.o0_compiles_to : Prop := silmaril.sysv_tv.max2.o0.compiles_to
/-- Open: the Bir9 block is a lift of the `-O2` code. -/
public def Task.o2_lifts : Prop := silmaril.sysv_tv.max2.o2.lifts
/-- Open: the Bir9 block corresponds to `max2`. -/
public def Task.o2_ir_refines : Prop := silmaril.sysv_tv.max2.o2.ir_refines

/-- **The `-O2` row from its lift and its correspondence** (the composition theorem). -/
public theorem o2_compiles_to_of (hl : Task.o2_lifts) (hr : Task.o2_ir_refines) :
    silmaril.sysv_tv.max2.o2.compiles_to :=
  Silmaril.Project.Shapes.C.CompilesTo.of_lift hl hr

/-- **Both builds, from the per-build rows.** -/
public theorem builds_of (h0 : Task.o0_compiles_to) (h2 : silmaril.sysv_tv.max2.o2.compiles_to) :
    silmaril.sysv_tv.max2.builds := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact h0
  · exact h2

/-- **Both builds, from the open rows.** -/
public theorem builds_of_tasks (h0 : Task.o0_compiles_to) (hl : Task.o2_lifts)
    (hr : Task.o2_ir_refines) : silmaril.sysv_tv.max2.builds :=
  builds_of h0 (o2_compiles_to_of hl hr)

end SysVTvExample
