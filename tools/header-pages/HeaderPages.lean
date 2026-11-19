import Lean
import Silmaril.Data.Layout.Header.Defs
import Silmaril.Data.Layout.Header.Demo.Defs
-- loaded at run time (`demoModules`) to check the layout links: imported here so that building
-- header-pages builds them
import Silmaril.Data.Layout.Header.Demo.Thms
import Silmaril.Data.Layout.Header.Demo.Decoys
import Silmaril.Data.Layout.Bitfield.Defs
import Silmaril.Machine.Abi.Conformance.Defs
import Silmaril.Machine.Abi.Conformance.Win64.Defs
import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
import Silmaril.Machine.Abi.Conformance.Import.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.Arith.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.Probe.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.ZlibSolo.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.ZlibHosted.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.GlibcString.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.GlibcStdlib.Defs

/-!
# The explorer's Headers tab data (`OUTDIR/headers/index.json`)

For each pinned header: what the subset reader (`Silmaril.Data.Layout.Header.read`) reads or why
it refuses; each prototype's C spelling and qualifiers; what each versioned ABI definition
(`sysvInt`, `win64Int`, `sysvScalar`) lowers it to, with the header's own tag definitions
(`Header.env`: `sysvScalar` classifies small aggregates passed by value from their layout), or the
reason it refuses; the call plan of
`sysvScalar` (where each argument and the result go); and each aggregate's layout under the
System V x86-64 and Microsoft x64 data models (`bitLayout`).

**The clang route.** A header may also have a pinned clang import
(`Data.Layout.Header.Import.Pinned`, associated by `clangOf`; glibc's `string.h` has only this
route). For it: the provenance (`Provenance.parse` of the committed `.prov`), the entry counts,
and per entry its name, kind, location, C declaration (or the import's reason), calling
convention, attributes, symbol and asm label, and per ABI definition the `status`
(`Machine.Abi.Conformance.Import`: claimable, unsupported or internal, with the reason) with the
conventions `clangCcs` names, plus, for a prototype, the same lowering and call plan as on the
subset route. The entries are the generated literals (`Pinned.<Name>.entries`); the JSON
artifact is not read here.

Every value is computed by the definitions that conformance rows and layout theorems use, run
here on the header files and literals; none is a theorem. A view must say so.

**Layout links.** `demo.h` (`layout-demo`) is read from the compiled-in constant
`Header.Demo.demoH` (the file on disk must equal it, else no link). Each of its layouts is linked
to the kernel theorem an explicit table (`demoLinks`) names, and only after `checkEq` accepts it:
loaded from the compiled modules (`importModules`), the theorem's type must be exactly
`@Eq T (layoutOf <pol> <dm> demoEnv <kind> "<tag>") rhs` (and `paddingOf` likewise) with the
table's policy, data model, kind and tag as constants and literals, `rhs` a literal whose decoded
value is the one the page shows, and the proof's axioms the standard three. Otherwise the layout
gets `proof: null` and the reason. `--self-test` checks that every true link is accepted and
that decoys (`Header.Demo.Decoys`, swapped and tampered links) are refused.

    lake env .lake/build/bin/header-pages OUTDIR
    lake env .lake/build/bin/header-pages --self-test
-/

open Lean (Json)
open Silmaril.Data.Layout
open Silmaril.Data.Layout.Header
open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import (Entry Body Fn Got CallConv Attr DeclKind Imported Provenance)

def js (s : String) : Json := Json.str s
def jn (n : Nat) : Json := Json.num n

/-- A pinned header: id, title, the files (name in the include graph, path), the root. -/
structure Src where
  id : String
  title : String
  files : List (String × String)
  root : String
  note : String := ""
  /-- Whether the subset reader is run on `files` (a clang-only header has no files here). -/
  subset : Bool := true
  /-- `demo.h`: read from the compiled-in `Header.Demo.demoH`, its layouts linked (`demoLinks`). -/
  demo : Bool := false

def sources : List Src := [
  { id := "arith", title := "elf-ladder rung 01 arith.h (and the rt.h it includes)",
    files := [("rt.h", "examples/elf-ladder/common/rt.h"), ("arith.h", "examples/elf-ladder/01-leaf-arith/arith.h")],
    root := "arith.h", note := "the header of the leaf-arith conformance rows (their status is in the registry, not here)" },
  { id := "zlib-hosted", title := "zlib 1.3.1 zlib.h checksum excerpt, hosted",
    files := [("zconf.h", "examples/headers/zlib-1.3.1/zconf-hosted.h"), ("zlib.h", "examples/headers/zlib-1.3.1/zlib.h")],
    root := "zlib.h", note := "the header of the shared-library rows" },
  { id := "zlib-solo", title := "zlib 1.3.1 zlib.h checksum excerpt, -DZ_SOLO",
    files := [("zconf.h", "examples/headers/zlib-1.3.1/zconf-solo.h"), ("zlib.h", "examples/headers/zlib-1.3.1/zlib.h")],
    root := "zlib.h", note := "the header of the static zlib-checksums rows" },
  { id := "probe", title := "probe.h (the clang import's probe header)",
    files := [("probe.h", "examples/headers/probe/probe.h")], root := "probe.h",
    note := "exercises what the subset reader refuses" },
  { id := "layout-demo", title := "layout demo: aggregates under two data models",
    files := [("demo.h", "examples/headers/layout/demo.h")], root := "demo.h", demo := true },
  { id := "glibc-string", title := "glibc string.h (the clang import's hosted header)",
    files := [], root := "/usr/include/string.h", subset := false,
    note := "only the clang route: the file is the pinned clang image's, not in this repository" },
  { id := "glibc-stdlib", title := "glibc stdlib.h with alloca.h (the clang import's hosted header)",
    files := [], root := "/usr/include/stdlib.h", subset := false,
    note := "only the clang route, in the pinned configuration (-std=gnu11, default feature set): not the whole stdlib.h API; see the scope report" },
  { id := "glibc-math", title := "glibc math.h, libm (the clang import's hosted header)",
    files := [], root := "/usr/include/math.h", subset := false,
    note := "only the clang route, in the pinned configuration (-std=gnu11, default feature set): not the whole math.h API (488 public names exist only under -D_GNU_SOURCE); see the scope report" }]

/-- The ABI definitions a prototype is lowered by. -/
def abis : List (String × AbiDef) := [("sysvInt", sysvInt), ("win64Int", win64Int), ("sysvScalar", sysvScalar)]

/-- A pinned clang import: its key, the Lean names of its value and literal, the `.prov` text and
the literal entries (`Pinned.<Name>.entries`). -/
structure Artifact where
  key : String
  value : String
  literal : String
  prov : String
  entries : List Entry

open Silmaril.Data.Layout.Header.Import.Pinned in
def artifacts : List Artifact := [
  ⟨"arith", "Pinned.arith", "Pinned.Arith.entries", arithProv, Arith.entries⟩,
  ⟨"probe", "Pinned.probe", "Pinned.Probe.entries", probeProv, Probe.entries⟩,
  ⟨"zlibSolo", "Pinned.zlibSolo", "Pinned.ZlibSolo.entries", zlibSoloProv, ZlibSolo.entries⟩,
  ⟨"zlibHosted", "Pinned.zlibHosted", "Pinned.ZlibHosted.entries", zlibHostedProv, ZlibHosted.entries⟩,
  ⟨"glibcString", "Pinned.glibcString", "Pinned.GlibcString.entries", glibcStringProv,
    GlibcString.entries⟩,
  ⟨"glibcStdlib", "Pinned.glibcStdlib", "Pinned.GlibcStdlib.entries", glibcStdlibProv,
    GlibcStdlib.entries⟩,
  ⟨"glibcMath", "Pinned.glibcMath", "Pinned.GlibcMath.entries", glibcMathProv,
    GlibcMath.entries⟩]

/-- The import of an artifact: its provenance and the literal entries. -/
def Artifact.imported (a : Artifact) : Imported := ⟨.parse a.prov, a.entries, none⟩

/-- **Which clang artifact a header page shows**, and how its input relates to the files the
subset route reads. -/
def clangOf : String → Option (String × String)
  | "arith" => some ("arith", "the same arith.h and rt.h the subset route reads")
  | "probe" => some ("probe", "the same probe.h the subset route reads")
  | "zlib-solo" => some ("zlibSolo", "the full zlib 1.3.1 release zlib.h and its zconf.h, with \
      -DZ_SOLO; the subset route reads a checksum excerpt")
  | "zlib-hosted" => some ("zlibHosted", "the full zlib 1.3.1 release zlib.h and its zconf.h, \
      hosted; the subset route reads a checksum excerpt")
  | "glibc-string" => some ("glibcString", "glibc's string.h in the pinned clang image")
  | "glibc-stdlib" => some ("glibcStdlib", "glibc's stdlib.h (with alloca.h) in the pinned clang image")
  | "glibc-math" => some ("glibcMath", "glibc's math.h (with bits/mathcalls*.h and bits/floatn-common.h) in the pinned clang image")
  | _ => none

/-- The conventions each ABI definition accepts on the import's target
(`x86_64-unknown-linux-gnu`): the System V definitions `sysvCcs` (the default C convention and
`sysv_abi`); the Microsoft x64 definition `ms_abi`, the attribute that selects it there. -/
def clangCcs : String → List CallConv
  | "win64Int" => [.msAbi]
  | _ => sysvCcs

/-- Why an ABI definition accepts the conventions it does on the imports' target. -/
def clangCcsNote : String → String
  | "win64Int" => "every pinned import targets x86_64-unknown-linux-gnu, where the default C \
      convention is System V: only ms_abi declarations follow Microsoft x64 there, so a \
      default-convention function is unsupported under win64Int here. A Windows-target import \
      (where the default is Microsoft x64) is not pinned."
  | _ => "the default C convention and sysv_abi: System V on the imports' target \
      x86_64-unknown-linux-gnu"

def exceptJson {α : Type} (f : α → Json) : Except String α → Json
  | .ok a => Json.mkObj [("ok", f a)]
  | .error e => Json.mkObj [("refused", js e)]

def locText : Silmaril.Machine.SystemV.Abi.Location → String
  | .gp r => (reprStr r).replace "Silmaril.X86.Reg." ""
  | .vector i o => s!"xmm{i}" ++ (if o = 0 then "" else s!"+{o}")
  | .x87 i => s!"st({i})"

def chunksText (cs : List Silmaril.Machine.SystemV.Abi.Chunk) : String :=
  ", ".intercalate (cs.map fun c => s!"{locText c.location}[{c.offset}..{c.offset + c.bytes})")

def planJson (p : Silmaril.Machine.SystemV.Abi.CallPlan) : Json :=
  Json.mkObj [
    ("arguments", Json.arr (p.arguments.toArray.map fun a =>
      js (if a.chunks.isEmpty then (match a.stackOffset with
        | some o => s!"stack [rsp+8+{o}]" | none => "?") else chunksText a.chunks))),
    ("result", js (match p.result with
      | .void => "void" | .direct cs => chunksText cs | .indirect s al => s!"memory (sret, {s} B, align {al})")),
    ("stackSize", jn p.stackSize)]

/-- A constructor's name without its namespace (`Silmaril.C.Api.Scalar.int32` → `int32`). -/
def short (s : String) : String := (s.splitOn ".").getLast!

def sigText (args : List String) (ret : Option String) : String :=
  "(" ++ ", ".intercalate args ++ ") → " ++ ret.getD "void"

/-- A scalar-fragment argument as text: its kind, or an aggregate's size and alignment. -/
def argText : Silmaril.Machine.Abi.SystemV.Scalar.Arg → String
  | .scalar k => short (reprStr k)
  | .agg a _ => s!"{a.name} ({a.size} B, align {a.align}, eightbytes {((reprStr a.eights).replace "Silmaril.Machine.Abi.SystemV.Scalar." "").replace "Silmaril.Machine.SystemV.Abi." ""})"

/-- An integer-fragment lowering: the C API signature, or the refusal. -/
def intLowering (r : Except String Silmaril.Machine.Abi.SystemV.Proto) : Json :=
  exceptJson (fun p => js (sigText (p.signature.arguments.map (short ∘ reprStr)) (p.signature.result.map (short ∘ reprStr)))) r

/-- Each ABI's view of one prototype. -/
def lowerings (env : Env) (cp : CProto) : Json := Json.mkObj <| abis.map fun (name, _) =>
  (name, match name with
    | "sysvScalar" =>
      match lowerScalar Silmaril.Data.Layout.sysvX86_64 env cp with
      | .error e => Json.mkObj [("refused", js e)]
      | .ok p => Json.mkObj [("ok", js (sigText (p.args.map argText) (p.result.map argText))),
          ("plan", exceptJson planJson (p.plan {}))]
    | "win64Int" =>
      match (win64Int.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto) with
      | .error e => Json.mkObj [("refused", js e)]
      | .ok p => Json.mkObj [
          ("ok", js (sigText (p.signature.arguments.map (short ∘ reprStr)) (p.signature.result.map (short ∘ reprStr)))),
          -- Microsoft x64's closed-form plan (`Win64.plan`, the convention's `msPlan`): RCX, RDX,
          -- R8, R9, then 8-byte slots above the 32-byte shadow space; the outgoing area is the
          -- shadow space plus the stack arguments, 16-aligned.
          ("plan", Json.mkObj [("ok", planJson (Silmaril.Machine.Abi.Win64.plan p))]),
          ("planNote", js "Microsoft x64: RCX, RDX, R8, R9, then 8-byte stack slots; the outgoing area includes the 32-byte shadow space")]
    | _ => intLowering (sysvInt.lower env cp : Except String Silmaril.Machine.Abi.SystemV.Proto))

def protoJson (h : Header) (f : String) (cp : CProto) : Json :=
  Json.mkObj [("name", js f), ("c", js (cp.render f)),
    ("quals", match h.quals? f with
      | some q => js (reprStr q) | none => Json.null),
    ("lowering", lowerings h.env cp)]

def slotJson (s : BitSlot) : Json :=
  Json.mkObj [("name", js s.name), ("bitOffset", jn s.off), ("bits", jn s.width)]

/-- The bytes of `[0, size)` that no named member occupies (an unnamed bit-field is not a member
in C), as maximal ranges `[lo, hi)`. A byte a bit-field uses only partly is not padding here. -/
def paddingRanges (slots : List BitSlot) (size : Nat) : List (Nat × Nat) :=
  let used (b : Nat) : Bool := slots.any fun s =>
    s.name != "" && s.width > 0 && s.off < 8 * (b + 1) && 8 * b < s.off + s.width
  let pad := (List.range size).filter fun b => !used b
  (pad.foldl (fun (acc : List (Nat × Nat)) b => match acc with
    | (lo, hi) :: rest => if hi == b then (lo, b + 1) :: rest else (b, b + 1) :: acc
    | [] => [(b, b + 1)]) []).reverse

/-! ## Layout links: exact, checked theorems -/

open Silmaril.Data.Layout.Header.Demo (demoH demoFiles demoEnv layoutOf paddingOf)

/-- The modules the links are read from, loaded at run time (`loadEnv`). -/
def demoModules : Array Lean.Name :=
  #[`Silmaril.Data.Layout.Header.Demo.Thms, `Silmaril.Data.Layout.Header.Demo.Decoys]

/-- The module every linked theorem must be declared in. -/
def demoThmsModule : Lean.Name := `Silmaril.Data.Layout.Header.Demo.Thms

/-- A data model as the page names it: its bit-field policy and data model, as values and as the
constants a linked theorem must name. -/
structure Model where
  key : String
  pol : BitPolicy
  dm : DataModel
  polConst : Lean.Name
  dmConst : Lean.Name

def models : List Model := [
  ⟨"sysvX86_64", .sysv, sysvX86_64, ``BitPolicy.sysv, ``sysvX86_64⟩,
  ⟨"msX64", .ms, msX64, ``BitPolicy.ms, ``msX64⟩]

/-- **A layout table's link** (curated): the aggregate, the data model, and the theorems of its
layout and of its padding counts. Nothing here is trusted: `checkLink` derives every claim from
the theorems' types and the values the page shows. -/
structure LayoutLink where
  kind : Kind
  tag : String
  model : String
  layout : Lean.Name
  padding : Lean.Name

instance : Inhabited LayoutLink := ⟨⟨.struct, "", "", .anonymous, .anonymous⟩⟩

open Silmaril.Data.Layout.Header.Demo in
/-- The theorems of `demo.h`'s layout tables (`Header.Demo.Thms`), by an explicit table. -/
def demoLinks : List LayoutLink := [
  ⟨.struct, "rec", "sysvX86_64", ``rec_sysv, ``rec_sysv_padding⟩,
  ⟨.struct, "rec", "msX64", ``rec_ms, ``rec_ms_padding⟩,
  ⟨.struct, "pt", "sysvX86_64", ``pt_sysv, ``pt_sysv_padding⟩,
  ⟨.struct, "pt", "msX64", ``pt_ms, ``pt_ms_padding⟩,
  ⟨.union, "word", "sysvX86_64", ``word_sysv, ``word_sysv_padding⟩,
  ⟨.union, "word", "msX64", ``word_ms, ``word_ms_padding⟩,
  ⟨.struct, "node", "sysvX86_64", ``node_sysv, ``node_sysv_padding⟩,
  ⟨.struct, "node", "msX64", ``node_ms, ``node_ms_padding⟩,
  ⟨.struct, "pair", "sysvX86_64", ``pair_sysv, ``pair_sysv_padding⟩,
  ⟨.struct, "pair", "msX64", ``pair_ms, ``pair_ms_padding⟩,
  ⟨.struct, "vec2", "sysvX86_64", ``vec2_sysv, ``vec2_sysv_padding⟩,
  ⟨.struct, "vec2", "msX64", ``vec2_ms, ``vec2_ms_padding⟩,
  ⟨.struct, "mixed", "sysvX86_64", ``mixed_sysv, ``mixed_sysv_padding⟩,
  ⟨.struct, "mixed", "msX64", ``mixed_ms, ``mixed_ms_padding⟩]

def kindConst : Kind → Lean.Name
  | .struct => ``Kind.struct
  | .union => ``Kind.union

def aggKindText : Kind → String
  | .struct => "struct"
  | .union => "union"

/-- `fn <pol> <dm> demoEnv <kind> "<tag>"`: constants and a string literal, nothing else. -/
def queryExpr (fn : Lean.Name) (m : Model) (k : Kind) (tag : String) : Lean.Expr :=
  Lean.mkAppN (.const fn []) #[.const m.polConst [], .const m.dmConst [], .const ``demoEnv [],
    .const (kindConst k) [], .lit (.strVal tag)]

def queryText (fn : Lean.Name) (m : Model) (k : Kind) (tag : String) : String :=
  s!"{fn} {m.polConst} {m.dmConst} {``demoEnv} {kindConst k} \"{tag}\""

def tyOption (t : Lean.Expr) : Lean.Expr := .app (.const ``Option [.zero]) t
def tyProd (a b : Lean.Expr) : Lean.Expr := Lean.mkApp2 (.const ``Prod [.zero, .zero]) a b
def tyNat : Lean.Expr := .const ``Nat []
def tySlot : Lean.Expr := .const ``BitSlot []
def tyShape : Lean.Expr := .const ``Shape []
def tySlots : Lean.Expr := .app (.const ``List [.zero]) tySlot
/-- `Option (List BitSlot × Shape)`, `layoutOf`'s type. -/
def tyLayout : Lean.Expr := tyOption (tyProd tySlots tyShape)
/-- `Option (Nat × Nat)`, `paddingOf`'s type. -/
def tyPadding : Lean.Expr := tyOption (tyProd tyNat tyNat)

/-! Literal right-hand sides, decoded structurally: a numeral (`OfNat.ofNat Nat n (instOfNatNat
n)` or a raw literal), a string literal, and applications of `BitSlot.mk`, `Shape.mk`,
`Prod.mk`, `List.cons`/`List.nil` and `Option.some`/`Option.none` at exactly the expected types.
Anything else (a constant, a function application, …) is not decoded. -/

def natLit? (e : Lean.Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ => match e.getAppFn, e.getAppArgs with
    | .const ``OfNat.ofNat [.zero], #[.const ``Nat [], .lit (.natVal n), i] =>
      if i == .app (.const ``instOfNatNat []) (.lit (.natVal n)) then some n else none
    | _, _ => none

def strLit? : Lean.Expr → Option String
  | .lit (.strVal s) => some s
  | _ => none

def slotLit? (e : Lean.Expr) : Option BitSlot :=
  match e.getAppFn, e.getAppArgs with
  | .const ``BitSlot.mk [], #[n, o, w] => do pure ⟨← strLit? n, ← natLit? o, ← natLit? w⟩
  | _, _ => none

def shapeLit? (e : Lean.Expr) : Option Shape :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Shape.mk [], #[s, a] => do pure ⟨← natLit? s, ← natLit? a⟩
  | _, _ => none

partial def listLit? {α : Type} (elem : Lean.Expr) (f : Lean.Expr → Option α) (e : Lean.Expr) :
    Option (List α) :=
  match e.getAppFn, e.getAppArgs with
  | .const ``List.nil [.zero], #[t] => if t == elem then some [] else none
  | .const ``List.cons [.zero], #[t, x, xs] =>
    if t == elem then do pure ((← f x) :: (← listLit? elem f xs)) else none
  | _, _ => none

def pairLit? {α β : Type} (a b : Lean.Expr) (f : Lean.Expr → Option α) (g : Lean.Expr → Option β)
    (e : Lean.Expr) : Option (α × β) :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Prod.mk [.zero, .zero], #[ta, tb, x, y] =>
    if ta == a && tb == b then do pure (← f x, ← g y) else none
  | _, _ => none

def optionLit? {α : Type} (t : Lean.Expr) (f : Lean.Expr → Option α) (e : Lean.Expr) :
    Option (Option α) :=
  match e.getAppFn, e.getAppArgs with
  | .const ``Option.none [.zero], #[t'] => if t' == t then some none else none
  | .const ``Option.some [.zero], #[t', x] => if t' == t then (f x).map some else none
  | _, _ => none

def layoutLit? : Lean.Expr → Option (Option (List BitSlot × Shape)) :=
  optionLit? (tyProd tySlots tyShape) (pairLit? tySlots tyShape (listLit? tySlot slotLit?) shapeLit?)

def paddingLit? : Lean.Expr → Option (Option (Nat × Nat)) :=
  optionLit? (tyProd tyNat tyNat) (pairLit? tyNat tyNat natLit? natLit?)

def runCore {α : Type} (env : Lean.Environment) (x : Lean.CoreM α) : IO α := do
  let (a, _) ← x.toIO { fileName := "<header-pages>", fileMap := default } { env }
  pure a

def standardAxioms : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- **The exact check of one theorem.** `decl` must be a theorem (not an axiom or definition),
without universe parameters, whose type is exactly `@Eq ty (fn <pol> <dm> demoEnv <kind> "<tag>")
rhs` (syntactically, after removing top-level metadata: nothing is unfolded), with `rhs` a
literal (`decode`) equal to `shown`, the value the page shows; whose axioms are among `propext`,
`Classical.choice` and `Quot.sound`; and declared in `Header.Demo.Thms`. Returns the link, or
the reason it is refused. -/
def checkEq {α : Type} [BEq α] (env : Lean.Environment) (decl fn : Lean.Name) (ty : Lean.Expr)
    (decode : Lean.Expr → Option (Option α)) (m : Model) (k : Kind) (tag : String)
    (shown : Option α) : IO (Except String Json) := do
  let some (.thmInfo ti) := env.find? decl | return .error s!"{decl}: not a theorem"
  unless ti.levelParams.isEmpty do return .error s!"{decl}: has universe parameters"
  let .app (.app (.app (.const ``Eq [lvl]) t) lhs) rhs := ti.type.consumeMData
    | return .error s!"{decl}: its type is not an equation"
  unless lvl == .succ .zero && t == ty do return .error s!"{decl}: not an equation in {ty}"
  unless lhs == queryExpr fn m k tag do
    return .error s!"{decl}: its left-hand side is not exactly {queryText fn m k tag}"
  let some v := decode rhs | return .error s!"{decl}: its right-hand side is not a literal"
  unless v == shown do return .error s!"{decl}: its right-hand side is not the value the page shows"
  let axs ← runCore env (Lean.collectAxioms decl)
  unless axs.all standardAxioms.contains do
    return .error s!"{decl}: depends on {axs.toList}, not only propext, Classical.choice and Quot.sound"
  let module := match env.getModuleIdxFor? decl with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  unless module == demoThmsModule do
    return .error s!"{decl}: declared in {if module.isAnonymous then "no module" else module.toString}, not {demoThmsModule}"
  let line ← runCore env do return ((← Lean.findDeclarationRanges? decl).map (·.range.pos.line))
  pure (.ok (Json.mkObj [("decl", js decl.toString), ("module", js module.toString),
    ("file", js (module.toString.replace "." "/" ++ ".lean")),
    ("line", match line with | some l => jn l | none => Json.null),
    ("status", js "proved"),
    ("axioms", Json.arr ((axs.qsort Lean.Name.lt).map (js ·.toString))),
    ("statement", js s!"{queryText fn m k tag} = <the value shown>")]))

/-- The padding counts a page shows for a layout (`paddingBytes`, `paddingBits`). -/
def shownPadding (shown : Option (List BitSlot × Shape)) : Option (Nat × Nat) :=
  shown.map fun (ss, sh) => (paddingBytes ss sh, paddingBits ss sh)

/-- **A layout table's link**: both theorems of `l` checked (`checkEq`) against the aggregate
`kind tag` under `m` and the layout the page shows; the layout theorem's link, with the padding
theorem's under `padding`. -/
def checkLink (env : Lean.Environment) (l : LayoutLink) (m : Model) (k : Kind) (tag : String)
    (shown : Option (List BitSlot × Shape)) : IO (Except String Json) := do
  match ← checkEq env l.layout ``layoutOf tyLayout layoutLit? m k tag shown with
  | .error e => pure (.error e)
  | .ok lj =>
    match ← checkEq env l.padding ``paddingOf tyPadding paddingLit? m k tag (shownPadding shown) with
    | .error e => pure (.error e)
    | .ok pj => pure (.ok (lj.setObjVal! "padding" pj))

/-- Whether `demo.h`'s page may be linked: the file on disk is the compiled-in `demoH`, and the
header's definitions (read from `demoH`) are `demoEnv`. -/
def demoGate (env : Env) (disk : String) : Except String Unit := do
  unless disk == demoH do
    throw "examples/headers/layout/demo.h differs from the compiled-in Header.Demo.demoH; no theorem is linked"
  unless env == demoEnv do throw "the header's definitions are not Header.Demo.demoEnv; no theorem is linked"

/-- Whether the loaded `Header.Demo.Defs` holds the same text as the binary: in the environment the
theorems are read from (`loadEnv`), `demoH` is a definition whose value is exactly the string
literal `text` (the compiled-in `demoH`). Lake does not track `include_str`, so after a partial
or stale build the binary and the loaded oleans could disagree; this refuses every link then. -/
def loadedGate (lenv : Lean.Environment) (text : String) : Except String Unit :=
  match lenv.find? ``demoH with
  | some (.defnInfo d) =>
    if d.value.consumeMData == .lit (.strVal text) then .ok ()
    else .error "the loaded Header.Demo.demoH is not the text compiled into header-pages (stale build?); no theorem is linked"
  | _ => .error "Header.Demo.demoH is not a definition in the loaded environment; no theorem is linked"

/-- The link context of a header page: the loaded environment and the gate. -/
abbrev LinkCtx := Option (Lean.Environment × Except String Unit)

/-- The `proof` of one layout table (`null`, with `proofNote`, when there is none). -/
def proofFor (ctx : LinkCtx) (m : Model) (env : Env) (d : Decl)
    (shown : Option (List BitSlot × Shape)) : IO (List (String × Json)) := do
  let none' (why : String) : List (String × Json) := [("proof", Json.null), ("proofNote", js why)]
  let some (lenv, gate) := ctx
    | return none' "no theorem is registered for this header's layouts: computed, not a theorem"
  if let .error e := gate then return none' e
  let some l := demoLinks.find? fun l => l.kind == d.kind && l.tag == d.tag && l.model == m.key
    | return none' "no theorem is registered for this table"
  -- the page's value is `layoutOf` on `demoEnv` (compiled evaluation), as the theorem states
  unless layoutOf m.pol m.dm demoEnv d.kind d.tag == shown && env == demoEnv do
    return none' "the value shown is not layoutOf on demoEnv"
  match ← checkLink lenv l m d.kind d.tag shown with
  | .ok j => pure [("proof", j)]
  | .error e => pure (none' s!"refused: {e}")

def layoutJson (ctx : LinkCtx) (m : Model) (env : Env) (d : Decl) : IO Json := do
  let r := bitLayout m.pol m.dm env d
  let base := exceptJson (fun (slots, sh) =>
    let pad := paddingRanges slots sh.size
    Json.mkObj [("size", jn sh.size), ("align", jn sh.align),
      ("members", Json.arr (slots.toArray.map slotJson)),
      ("padding", Json.arr (pad.toArray.map fun (lo, hi) => Json.arr #[jn lo, jn hi])),
      -- the library's counts (`Data.Layout.paddingBytes`/`paddingBits`, the definitions the
      -- layout theorems state); the ranges above are this tool's rendering of the same byte
      -- predicate, checked against `paddingBytes` by headers.mjs
      ("paddingBytes", jn (paddingBytes slots sh)),
      ("paddingBits", jn (paddingBits slots sh))]) r
  let fs ← proofFor ctx m env d r.toOption
  pure (fs.foldl (fun j (k, v) => j.setObjVal! k v) base)

def declJson (ctx : LinkCtx) (env : Env) (d : Decl) : IO Json := do
  let mut ls : List (String × Json) := []
  for m in models do ls := ls ++ [(m.key, ← layoutJson ctx m env d)]
  pure (Json.mkObj [("kind", js (aggKindText d.kind)),
    ("tag", js d.tag),
    ("members", Json.arr (d.fields.toArray.map fun fl => Json.mkObj [("name", js fl.name),
      ("type", js (fl.ty.declare "")), ("bits", match fl.bits with | some b => jn b | none => Json.null)])),
    ("layouts", Json.mkObj ls)])

/-! ## The clang route -/

def ccText : CallConv → String
  | .c => "default"
  | .msAbi => "ms_abi"
  | .sysvAbi => "sysv_abi"
  | .regcall => "regcall"
  | .vectorcall => "vectorcall"
  | .other s => s

def attrText : Attr → String
  | .noreturn => "noreturn" | .nonnull => "nonnull" | .format => "format"
  | .deprecated => "deprecated" | .visibility v => s!"visibility({v})" | .asmLabel => "asm label"
  | .pure => "pure" | .const => "const" | .nothrow => "nothrow" | .leaf => "leaf"
  | .builtin => "builtin" | .restrict => "restrict" | .warnUnusedResult => "warn_unused_result"
  | .allocSize => "alloc_size" | .aligned => "aligned" | .weak => "weak" | .alias => "alias"
  | .section => "section" | .used => "used" | .unused => "unused" | .cold => "cold"
  | .returnsTwice => "returns_twice" | .other k => k

def kindText : DeclKind → String
  | .function => "function" | .typedef => "typedef" | .struct => "struct" | .union => "union"
  | .enum => "enum" | .variable => "variable" | .other k => k

def gotJson {α : Type} (f : α → String) : Got α → Json
  | .ok a => Json.mkObj [("ok", js (f a))]
  | .unsupported w => Json.mkObj [("unsupported", js w)]

/-- The reason the import gives for not reading (part of) an entry, if any: a function type
outside `CProto`, a typedef's or variable's type outside `CTy`, a declaration it does not read. -/
def importReason? (e : Entry) : Option String :=
  match e.body with
  | .function f => match f.proto with
    | .unsupported w => some w
    | .ok _ => none
  | .typedef (.unsupported w) | .variable (.unsupported w) _ | .unsupported w => some w
  | _ => none

def statusJson : Status → Json
  | .claimable => Json.mkObj [("status", js "claimable")]
  | .unsupported w => Json.mkObj [("status", js "unsupported"), ("why", js w)]
  | .internal w => Json.mkObj [("status", js "internal"), ("why", js w)]
  | .notFunction => Json.mkObj [("status", js "notFunction")]

def optStr : Option String → Json
  | some s => js s
  | none => Json.null

/-- One entry: what the import reads of it, and its status for each ABI definition (`stat`, from
`table`). A prototype also gets the subset route's lowering and call plan, in `env`. -/
def entryJson (env : Env) (e : Entry) (stat : List (String × Status)) (dup : Bool := false) : Json :=
  let loc := match e.loc with
    | some l => Json.mkObj [("file", js l.file), ("line", jn l.line)]
    | none => Json.null
  let decl : Json := match e.body with
    | .function f => gotJson (fun cp => cp.render e.name) f.proto
    | .typedef t => gotJson (fun t => "typedef " ++ t.declare e.name) t
    | .tag d => Json.mkObj [("ok", js (kindText e.kind ++ " " ++
        (if e.name == "" then "(anonymous)" else e.name) ++ (if d then " { … }" else "")))]
    | .variable t st =>
      gotJson (fun t => (match st with | some x => x ++ " " | none => "") ++ t.declare e.name) t
    | .unsupported w => Json.mkObj [("unsupported", js w)]
  let base := [("name", js e.name), ("kind", js (kindText e.kind)), ("loc", loc),
    ("implicit", Json.bool e.implicit), ("duplicateOfExplicit", Json.bool dup), ("decl", decl),
    ("status", Json.mkObj (stat.map fun (n, s) => (n, statusJson s)))]
  Json.mkObj <| match e.body with
    | .function f => base ++ [("variadic", Json.bool f.variadic), ("cc", js (ccText f.cc)),
        ("attrs", Json.arr (f.attrs.toArray.map (js ∘ attrText))), ("symbol", js f.symbol),
        ("asmLabel", optStr f.asmLabel), ("storage", optStr f.storage),
        ("inline", Json.bool f.inline), ("definition", Json.bool f.definition)] ++
        (match f.proto with
          | .ok cp => [("lowering", lowerings env cp)]
          | .unsupported _ => [])
    | _ => base

def provJson (p : Provenance) : Json :=
  Json.mkObj [("artifact", js p.artifact), ("image", js p.image), ("clang", js p.clang),
    ("target", js p.target), ("std", js p.std), ("cwd", js p.cwd), ("command", js p.command),
    ("defines", Json.arr (p.defines.toArray.map js)),
    ("includes", Json.arr (p.includes.toArray.map js)),
    ("filter", js p.filter), ("filterSha256", js p.filterSha256), ("source", optStr p.source),
    ("inputs", Json.arr (p.inputs.toArray.map fun (f, h) =>
      Json.mkObj [("file", js f), ("sha256", js h)])),
    ("jsonSha256", js p.jsonSha256), ("jsonBytes", jn p.jsonBytes)]

/-- An artifact's clang route: provenance, counts (`abiCounts` from `interface`, `claimable`
and `unsupportedFns`) and every entry with its status per ABI (`table`). -/
def clangJson (a : Artifact) (relation : String) : Json :=
  let imp := a.imported
  let env := imp.header.env
  let tables := abis.map fun (n, A) => (n, (table A (clangCcs n) imp).toArray)
  let es := imp.entries
  Json.mkObj [("artifact", js a.key), ("value", js a.value), ("literal", js a.literal),
    ("relation", js relation), ("provenance", provJson imp.provenance),
    ("counts", Json.mkObj [("total", jn es.length),
      ("functions", jn (es.filter (·.kind == .function)).length),
      ("implicit", jn (es.filter (·.implicit)).length),
      ("unsupported", jn (es.filter fun e => (importReason? e).isSome).length)]),
    ("abiCounts", Json.mkObj (abis.map fun (n, A) => (n, Json.mkObj [
      ("interface", jn (interface A (clangCcs n) imp).length),
      ("claimable", jn (claimable A (clangCcs n) imp).length),
      ("unsupported", jn (unsupportedFns A (clangCcs n) imp).length)]))),
    ("entries", Json.arr (es.toArray.mapIdx fun i e =>
      entryJson env e (tables.map fun (n, t) => (n, (t[i]?.map (·.2)).getD .notFunction))
        -- an implicit entry is an excluded duplicate when the import also has an explicit
        -- function entry of the same name, classified on its own
        (e.implicit && es.any fun e' => !e'.implicit && e'.kind == .function && e'.name == e.name)))]

/-- The recipe's scope report of an artifact (`examples/headers/clang/<name>.scope`, checked byte
for byte by `recipe.sh --check`; not a theorem), if it has one. -/
def scopeOf (a : Artifact) : IO Json := do
  let path := "examples/headers/clang/" ++ ((Provenance.parse a.prov).artifact.replace ".json" ".scope")
  if ← System.FilePath.pathExists path then
    pure (Json.mkObj [("path", js path), ("text", js (← IO.FS.readFile path))])
  else pure Json.null

def clangFor (id : String) : IO Json := do
  match clangOf id with
  | some (k, rel) => match artifacts.find? (·.key == k) with
    | some a => pure ((clangJson a rel).setObjVal! "scope" (← scopeOf a))
    | none => throw (IO.userError s!"header-pages: no artifact {k} for page {id}")
  | none => pure Json.null

def headerJson (lenv : Lean.Environment) (s : Src) : IO Json := do
  let mut disk : Array (String × String) := #[]
  for (n, p) in s.files do disk := disk.push (n, ← IO.FS.readFile p)
  -- `demo.h` is read from the compiled-in `demoH`, the text its theorems are about; the file on
  -- disk is only compared with it (`demoGate`)
  let files := if s.demo then demoFiles else disk.toList
  let base := [("id", js s.id), ("title", js s.title), ("note", js s.note), ("root", js s.root),
    ("files", Json.arr (s.files.toArray.map fun (n, p) => Json.mkObj [("name", js n), ("path", js p)])),
    ("text", if s.demo then js (toString ``demoH) else Json.null),
    ("clang", ← clangFor s.id)]
  if !s.subset then return Json.mkObj (base ++ [("read", Json.null)])
  match read files s.root with
  | .error e => pure (Json.mkObj (base ++ [("read", Json.mkObj [("refused", js e)])]))
  | .ok h =>
    let ctx : LinkCtx := if s.demo then
      some (lenv, loadedGate lenv demoH *> demoGate h.env (((disk.find? (·.1 == "demo.h")).map (·.2)).getD "")) else none
    let aggs ← h.env.toArray.mapM (declJson ctx h.env)
    pure (Json.mkObj (base ++ [("read", Json.mkObj [("ok", Json.bool true)]),
      ("typedefs", Json.arr (h.typedefs.toArray.map fun (n, t) => Json.mkObj [("name", js n), ("type", js (t.declare ""))])),
      ("enums", Json.arr (h.enums.toArray.map fun (t, cs) => Json.mkObj [("tag", js t),
        ("constants", Json.arr (cs.toArray.map fun (c, v) => Json.arr #[js c, js (toString v)]))])),
      ("aggregates", Json.arr aggs),
      ("prototypes", Json.arr (h.protos.toArray.map fun (f, cp) => protoJson h f cp))]))

/-- The modules of the links (`demoModules`), from the build's search path (`lake env`). -/
def loadEnv : IO Lean.Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.importModules (demoModules.map ({ module := · })) {}

/-! ## Self-test: true links accepted, decoys refused -/

/-- An environment with a theorem `HeaderPagesSelfTest.<name>` of type `ty`, proved by `value`
(after adding `HeaderPagesSelfTest.ax : ty` when `value` is `none`): declarations no module
holds, built at run time so that the library needs no axiom. -/
def withTheorem (env : Lean.Environment) (name : String) (ty : Lean.Expr) (value : Option Lean.Expr) :
    IO Lean.Environment := runCore env do
  let thm := `HeaderPagesSelfTest ++ name.toName
  let v ← match value with
    | some v => pure v
    | none =>
      let ax := `HeaderPagesSelfTest ++ (name ++ "_ax").toName
      Lean.addDecl (.axiomDecl { name := ax, levelParams := [], type := ty, isUnsafe := false })
      pure (.const ax [])
  Lean.addDecl (.thmDecl { name := thm, levelParams := [], type := ty, value := v, all := [thm] })
  Lean.getEnv

/-- A decoy: what it is, the environment it is checked in, the link, and the table it is put on
(aggregate, data model, the value shown). -/
structure Decoy where
  what : String
  env : Lean.Environment
  link : LayoutLink := default
  kind : Kind := .struct
  tag : String := "rec"
  model : String := "sysvX86_64"
  shown : Option (Option (List BitSlot × Shape)) := none

def shownOf (m : Model) (k : Kind) (tag : String) : Option (List BitSlot × Shape) :=
  (demoEnv.find? k tag).bind fun d => (bitLayout m.pol m.dm demoEnv d).toOption

def selfTest : IO UInt32 := do
  let env ← loadEnv
  let mut failed := 0
  -- the table covers every aggregate of demo.h under both data models, and each link is accepted
  for d in demoEnv do
    for m in models do
      let some l := demoLinks.find? fun l => l.kind == d.kind && l.tag == d.tag && l.model == m.key
        | IO.eprintln s!"header-pages --self-test: no link for {d.tag} under {m.key}"; failed := failed + 1; continue
      match ← checkLink env l m d.kind d.tag (shownOf m d.kind d.tag) with
      | .ok _ => pure ()
      | .error e => IO.eprintln s!"header-pages --self-test: a true link is refused ({e})"; failed := failed + 1
  let D := `Silmaril.Data.Layout.Header.Demo
  let X := D ++ `Decoys
  let some recSysv := demoLinks.find? fun l => l.tag == "rec" && l.model == "sysvX86_64" | return 1
  let some recThm := env.find? recSysv.layout | return 1
  let some sysv := models.find? (·.key == "sysvX86_64") | return 1
  let recShown := shownOf sysv .struct "rec"
  let tampered (f : List BitSlot × Shape → List BitSlot × Shape) := recShown.map f
  -- run-time theorems: the right statement backed by an axiom; the right statement proved by
  -- `rec_sysv` but declared outside `Header.Demo.Thms`
  let envAx ← withTheorem env "rec_by_axiom" recThm.type none
  let envCopy ← withTheorem env "rec_copy" recThm.type (some (.const recSysv.layout []))
  let decoys0 : List Decoy := [
    { what := "another tag: pt_sysv on rec's table", env, link := { recSysv with layout := D ++ `pt_sysv } },
    { what := "the other data model: rec_ms on rec's System V table", env, link := { recSysv with layout := D ++ `rec_ms } },
    { what := "the other data model's padding: rec_ms_padding", env, link := { recSysv with padding := D ++ `rec_ms_padding } },
    { what := "another tag's padding: pt_sysv_padding", env, link := { recSysv with padding := D ++ `pt_sysv_padding } },
    { what := "another environment with the same slots and shape (Header.recEnv)", env,
      link := { recSysv with layout := X ++ `rec_other_env } },
    { what := "another environment (Header.ptEnv) on pt's table", env, tag := "pt",
      link := { recSysv with tag := "pt", layout := X ++ `pt_other_env, padding := D ++ `pt_sysv_padding } },
    { what := "a tautology about the right constants", env, link := { recSysv with layout := X ++ `rec_refl } },
    { what := "the right equation under a disjunction", env, link := { recSysv with layout := X ++ `rec_or_true } },
    { what := "the right equation flipped", env, link := { recSysv with layout := X ++ `rec_flipped } },
    { what := "a right-hand side that is not a literal (Header.recLayout)", env,
      link := { recSysv with layout := X ++ `rec_rhs_not_literal } },
    { what := "Microsoft policy with the System V data model, on the System V table", env,
      link := { recSysv with layout := X ++ `rec_mixed_model } },
    { what := "Microsoft policy with the System V data model, on the Microsoft table", env, model := "msX64",
      link := { recSysv with model := "msX64", layout := X ++ `rec_mixed_model, padding := D ++ `rec_ms_padding } },
    { what := "another kind: struct word = none on union word's table", env, kind := .union, tag := "word",
      link := { recSysv with kind := .union, tag := "word", layout := X ++ `word_as_struct, padding := D ++ `word_sysv_padding } },
    { what := "the padding theorem as the layout theorem", env, link := { recSysv with layout := D ++ `rec_sysv_padding } },
    { what := "the layout theorem as the padding theorem", env, link := { recSysv with padding := recSysv.layout } },
    { what := "a definition, not a theorem (demoEnv)", env, link := { recSysv with layout := ``demoEnv } },
    { what := "a wrong right-hand side: the size shown is 33", env,
      shown := some (tampered fun (ss, sh) => (ss, { sh with size := 33 })) },
    { what := "a wrong right-hand side: flags shown at bit 9", env,
      shown := some (tampered fun (ss, sh) => (ss.map fun s => if s.name == "flags" then { s with off := 9 } else s, sh)) },
    { what := "a wrong right-hand side: the layout shown as refused", env, shown := some none },
    { what := "the right statement proved from an axiom", env := envAx,
      link := { recSysv with layout := `HeaderPagesSelfTest.rec_by_axiom } },
    { what := "an axiom, not a theorem", env := envAx, link := { recSysv with layout := `HeaderPagesSelfTest.rec_by_axiom_ax } },
    { what := "the right statement declared outside Header.Demo.Thms", env := envCopy,
      link := { recSysv with layout := `HeaderPagesSelfTest.rec_copy } }]
  -- a decoy that names no link is put on rec's System V link
  let decoys := decoys0.map fun d => if d.link.layout.isAnonymous then { d with link := recSysv } else d
  let mut refused := 0
  for d in decoys do
    let some m := models.find? (·.key == d.model) | return 1
    let shown := d.shown.getD (shownOf m d.kind d.tag)
    match ← checkLink d.env d.link m d.kind d.tag shown with
    | .ok _ => IO.eprintln s!"header-pages --self-test: the checker accepted '{d.what}'"; failed := failed + 1
    | .error e => refused := refused + 1; IO.println s!"header-pages --self-test: refused '{d.what}': {e}"
  -- the gate: a file on disk that is not `demoH`, and definitions that are not `demoEnv`
  let gates := [("demo.h on disk differs from demoH", demoGate demoEnv (demoH ++ " ")),
    ("definitions other than demoEnv", demoGate demoEnv.reverse demoH),
    ("loaded demoH differs from the compiled text (stale build)", loadedGate env (demoH ++ " "))]
  for (what, g) in gates do
    match g with
    | .ok _ => IO.eprintln s!"header-pages --self-test: the gate accepted '{what}'"; failed := failed + 1
    | .error e => refused := refused + 1; IO.println s!"header-pages --self-test: refused '{what}': {e}"
  unless loadedGate env demoH matches .ok _ do
    IO.eprintln "header-pages --self-test: the loaded-text gate refuses the loaded demoH"; failed := failed + 1
  unless demoGate demoEnv demoH matches .ok _ do
    IO.eprintln "header-pages --self-test: the gate refuses demoH itself"; failed := failed + 1
  let total := decoys.length + gates.length
  if failed == 0 then
    IO.println s!"header-pages --self-test: ok ({demoLinks.length} links accepted, {refused} of {total} decoys refused)"
    pure 0
  else
    IO.eprintln s!"header-pages --self-test: {failed} failures"; pure 1

def main (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then return ← selfTest
  let [out] := args | IO.eprintln "usage: header-pages OUTDIR | header-pages --self-test"; return 2
  let lenv ← loadEnv
  let mut hs : Array Json := #[]
  for s in sources do hs := hs.push (← headerJson lenv s)
  let j := Json.mkObj [("schema", js "silmaril.header-pages/2"),
    ("note", js "computed by the reader, the ABI definitions' lowering and the layout definitions, run on the header files; not theorems"),
    ("proofNote", js "a layout with a proof is linked to a kernel theorem whose statement header-pages checked exactly: layoutOf (and paddingOf) of that policy, data model, Header.Demo.demoEnv, kind and tag equals the literal the table shows, with only the standard axioms; every other layout is computed, not a theorem"),
    ("clangNote", js "computed by the import's status, interface and lowering definitions, run on the literal entries of each pinned clang import and its .prov; not theorems"),
    ("abis", Json.arr (abis.toArray.map fun (n, A) => Json.mkObj [("name", js n), ("id", js A.id), ("source", js A.source),
      ("clangCcs", Json.arr ((clangCcs n).toArray.map (js ∘ ccText))),
      ("clangCcsNote", js (clangCcsNote n))])),
    ("dataModels", Json.arr #[js "sysvX86_64", js "msX64"]),
    ("headers", Json.arr hs)]
  IO.FS.createDirAll (out ++ "/headers")
  IO.FS.writeFile (out ++ "/headers/index.json") j.pretty
  IO.println s!"header-pages: wrote {out}/headers/index.json ({hs.size} headers)"
  return 0
