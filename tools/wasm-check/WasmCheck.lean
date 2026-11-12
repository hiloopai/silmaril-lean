import Silmaril.Wasm.Auto.Front.Defs
import Silmaril.Wasm.Auto.Bridge.Defs
import tests.wasm.auto.FrontBench.Defs
import tests.wasm.auto.FrontBenchX.Defs
import Silmaril.Wasm.Auto2.VCLib.Thms
import Silmaril.Wasm.Auto2.VCLib2.Thms
import Silmaril.Wasm.Auto2.VCLib3.Thms
import Silmaril.Wasm.Auto2.Summ.Defs
import Silmaril.Wasm.Auto2.Calls.Defs
import Silmaril.Wasm.Auto2.Front2.Defs
import Silmaril.Wasm.Auto2.VCInfer.Defs
import Silmaril.Wasm.Binaryen.Exe.CompactInput
import Silmaril.Wasm.Binaryen.Exe.Encode

/-! `wasm-check`: the front end of `docs/projects/wasm-binaryen-tooling.md` on binary
Core 3.0 modules. I/O glue only: decoding (silmaril-lean's decoder), argument parsing, timing
and printing; the checks are `Silmaril.Wasm.Auto.Front.checkRefinesBase`/`checkEquivBase`/`checkMeets`,
whose `refuted` verdicts are refutations (`Silmaril.Wasm.Auto.Front.Thms`).

```
wasm-check refines IMPL.wasm SPEC.wasm EXPORT [--rel eq|trap] [--random N] [--lean FILE]
wasm-check equiv A.wasm B.wasm EXPORT [--rel eq|trap] [--random N] [--lean FILE]
wasm-check pass A.wasm B.wasm [--random N] [--lean FILE] [--lean-dir DIR] [--chunk K]
                       [--egraph-tv TV.lean] [--egraph-tv-seg FILE] [--wat A.wat B.wat]
wasm-check bench [--random N] [--out DIR] [--vc]
wasm-check vc IMPL.wasm EXPORT CONTRACT [--lean FILE]
wasm-check vc-emit DIR
```

**Contracts (the VC stage).** `bench` runs the reference-function cases that have a proved
contract (`Silmaril.Wasm.Auto2.VCLib.refEntries`) through `Silmaril.Wasm.Auto2.VCBridge.checkMeetsVC`
(differential testing, then the VC stage: `proved` is `ModMeets` at every profile by
`checkMeetsVC_proved`). `vc` checks export `EXPORT` of a binary against a contract of the VC
library (`Silmaril.Wasm.Auto2.VCLib.entries`, by name: `sum`, `max`, `add`, `div10`): it computes the
conditions of the VC generator (`Silmaril.Wasm.Auto2.VCGen`) on the export's code and reports how
many are not proved conditions of the contract; `proved` (none missing, same types) is the total
every-run specification of the export (`Silmaril.Wasm.Auto2.VCBridge.modTSpec_of_vcCheck`), and
`--lean FILE` writes that theorem as a certificate (the binary embedded, `vcCheck` by kernel
evaluation).

Both use the normalising check with memory and callees
(`Silmaril.Wasm.Auto2.VCCheck.vcCheckM`: a condition is accepted if its normal form is `tt` or a
renamed normal form of a proved condition; callees are read from the module and checked against
their own contracts). `vc` searches `Silmaril.Wasm.Auto2.VCLib2.entriesM` (adds `double`, with a
callee, and `load2`, with memory), `proved` is `Silmaril.Wasm.Auto2.VCCheck.modTSpecM_of_vcCheckM`;
`bench` uses `checkMeetsVCN` (`checkMeetsVCN_proved`). `vc-emit DIR` writes the binaries of the
library's demonstration modules (`Silmaril.Wasm.Auto2.VCLib2.demoModules`).

`vc` also searches `Silmaril.Wasm.Auto2.VCLib3.entriesM3` (contracts whose callees read and write
globals, `incr2` and `drain`, a variant over a global, `countdown`, and `dbl`, `add3`, whose
demonstrations differ by linear arithmetic, normalised by `Silmaril.Wasm.Auto2.VCGen.Tm.lin`);
certificates state `ModTSpecM P (entryM3 "NAME") modA j`. `bench --vc` checks the library's
contracts against their demonstration modules and mutants (`Silmaril.Wasm.Auto2.VCLib3.vcBench`,
expected verdicts built in); `vc-emit` also writes these demonstration modules.

**Basic stages and certificates.** The first checks are
`Silmaril.Wasm.Auto.Front.checkRefines`/`checkEquiv` (the basic stages, then the extended summaries
of `Silmaril.Wasm.Auto.Bridge`: memory, globals, conversions, trap guards). `pass --lean` writes one
certificate whose proved exports are checked in chunks of `K`
exports (default 4): one kernel evaluation of `Silmaril.Wasm.Auto.Bridge.checkAmong` per chunk
(each decodes and instantiates both modules once), so that no single evaluation holds every
export's terms; the e-graph side conditions likewise (`liftAmong`). `--lean-dir DIR` writes the
same certificate split into files (`chunk_<c>.lean`, `rest.lean`) for separate Lean processes.
`--wat A.wat B.wat` writes the modules as WAT text (`wat3b!`, `Silmaril.Wasm.Auto2.Wat`: `wat3!`
reading Binaryen's `tuple.make`/`tuple.drop`) instead of embedding the binaries: decoding a binary
in the kernel is the dominant cost (a 2 KB module exceeded 20 GB), while the kernel checks a
module term directly. The certificate is then about the modules of the WAT texts (for the
benchmark, Binaryen's printing of the pinned binaries); that they are the binaries' modules is not
checked by the kernel. `--link a|b|ab` adds, for the named modules,
the module the tool decoded from the binary as a term and a proof by `rfl` that the WAT module is
that term: a kernel-checked cross-check of the two front ends (Binaryen's printer with `wat3b!`,
and the compiled decoder with the derived `Repr`), which holds for Binaryen-written binaries.
`--link-equiv a|b|ab` is the link for the other binaries, whose type
sections Binaryen's printer reorders and merges: the decoded module as a term, a kernel-checked
equivalence of each proved export of the decoded module to the WAT module's (`checkAmong` over
`instK?`, `linkA_<j>`/`linkB_<j>`), the same signatures (`Silmaril.Wasm.Auto2.Link.sigOkAll`), and
each certificate equivalence transferred to the decoded modules (`decA_<j>`, `decB_<j>`,
`decAB_<j>`, by `Silmaril.Proofs.Wasm.Auto2.Link.modEquiv_link`; `Rel.eq` only).

**Kernel form.** Without `--wat`, the modules the tool decoded are stated as Lean terms (their
derived `Repr`; `--embed` embeds the binaries instead), and certificates validate each module once
(`validA`, `validB`) and rewrite every later kernel goal to the validation-free, closed-form
instantiation of `Silmaril.Wasm.Auto2.Kernel` (`--spec-kernel` writes the older form, in which every
kernel evaluation validates and instantiates the modules itself).

**Summaries.** The checks `Silmaril.Wasm.Auto2.Calls.checkRefinesC`/`checkEquivC` run the basic
stages, then summaries with constant-trip loops unrolled and a guard-aware comparison (stage
`equivu`), then the same with calls inlined (stage `equivc`); `pass` proves the exports of these
stages in chunks of `Silmaril.Wasm.Auto2.Summ.checkAmongU` and `Silmaril.Wasm.Auto2.Calls.checkAmongC`.

The full checks are `Silmaril.Wasm.Auto2.Front2.checkRefinesV`/`checkEquivV`, which add stage
`equivv` (the same summaries with a third simplifier, `Silmaril.Wasm.Auto2.Summ2.fnCheckV`) and stage
`vcequiv` (both exports checked against contracts of one functional contract of
`Silmaril.Wasm.Auto2.VCEquiv.eqFuns`: loops whose trip count depends on the inputs). In the default
(kernel) form, `pass` proves every export of the stages `equivu`, `equivc` and `equivv` in chunks
of `Silmaril.Wasm.Auto2.Summ2.checkAmongV`, rewritten by `checkAmongV_eq_K` to the validation-free,
closed-form instance (so modules with data segments are checked in the kernel); `--spec-kernel`
keeps the `checkAmongU`/`checkAmongC` chunks. `vcequiv` exports are proved by
`modEquiv_of_vcEquivAny`.

`pass` checks every function export the two modules share (same name, same index) for
equivalence, as for an optimizer pass (`A` its input, `B` its output), and prints one JSON report
per export and a summary line. `--egraph-tv FILE` (a `wasm-egraph tv` module) and
`--egraph-tv-seg FILE` (a `wasm-egraph tv-seg --func` module: bodies with locals, `select` and
renumbered locals, compared from function entry) add an e-graph stage for the exports the
other stages leave unknown: an export whose side conditions hold (`Bridge.egraphLiftOk`,
`Bridge.egraphFuncOk`) and whose certificate theorem is in the module (`tv_<export name>`)
is proved in the `--lean` certificate (`modEquiv_of_egraph`, `modEquiv_of_funcEquiv`).

`EXPORT` is an index into the function exports or an export name (it must name the same index
in both modules). Prints one JSON report per check, with the stages run and their times.
`--lean FILE` writes a Lean certificate for a `refuted` or `proved` verdict: a module that embeds
both binaries, decodes them, and proves the refutation by kernel evaluation on the verified
interpreter (`refutes_of_cexK`), or the equivalence at every profile by kernel evaluation of the
proving stage (`modEquiv_of_proveStageBase`).
`bench` runs the pinned cases of `Silmaril.Wasm.Auto.FrontBench` and prints a TSV line per case
(name, verdict, expected, milliseconds, ok); with `--out DIR` it also writes the binaries of the
module cases there. Exit code `0` on success (whatever the verdict; for `bench`, when every case
has its expected verdict), `1` when a bench case differs, `2` on a usage, input or decoding
error. -/

namespace Silmaril.Wasm.Auto.Front.Cli

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front Silmaril.Wasm.Auto.FrontBench

/-- The usage message. -/
def usage : String :=
  "usage: wasm-check (refines|equiv) A.wasm B.wasm EXPORT [--rel eq|trap] [--random N]\n" ++
  "                        [--lean FILE] [--spec-kernel] [--embed]\n" ++
  "       wasm-check pass A.wasm B.wasm [--random N] [--lean FILE] [--lean-dir DIR]\n" ++
  "                        [--chunk K] [--wat A.wat B.wat [--link a|b|ab] [--link-equiv a|b|ab]]\n" ++
  "                        [--spec-kernel]\n" ++
  "                        [--embed]\n" ++
  "                        [--egraph-tv TV.lean]\n" ++
  "       wasm-check bench [--random N] [--out DIR] [--vc]\n" ++
  "       wasm-check vc IMPL.wasm EXPORT CONTRACT [--lean FILE]\n" ++
  "       wasm-check vc-emit DIR\n" ++
  "EXPORT is an index into the function exports or an export name; prints JSON reports."

/-- Decode a binary module (standard, or with compact imports). -/
def decode (bytes : ByteArray) : Except String Module :=
  (Silmaril.Wasm.Binaryen.Exe.CompactInput.prepare bytes).map (·.source)

/-- The function exports of a module (name, function index), in order. -/
def funcExports (m : Module) : List (String × Nat) :=
  m.exports.filterMap fun x => match x.index with
    | .func y => some (x.name, y.toNat)
    | _ => none

/-- Resolve a function export given as an index or as a name. -/
def resolveExport (m : Module) (arg : String) : Option Nat :=
  match arg.toNat? with
  | some k => some k
  | none =>
    let fx := funcExports m
    ((List.range fx.length).zip fx).findSome? fun (k, (n, _)) => if n == arg then some k else none

/-- Options. -/
structure Opts where
  rel : Rel := .eq
  random : Nat := 1000
  lean : Option String := none
  leanDir : Option String := none
  wat : Option (String × String) := none
  out : Option String := none
  egraphTv : Option String := none
  egraphTvSeg : Option String := none
  chunk : Nat := 4
  /-- Write certificates in the specification form (every kernel evaluation validates and instantiates
  with the specification's functions) instead of over `Silmaril.Wasm.Auto2.Kernel`. -/
  specKernel : Bool := false
  /-- Embed the binaries in the certificate, decoded in the kernel, instead of
  stating the decoded modules as terms. -/
  embed : Bool := false
  /-- With `--wat`: also state these modules (`a`, `b`) as the tool decoded them from the
  binaries, and prove each WAT module equal to its decoded term by `rfl` (`--link`). -/
  link : List Char := []
  /-- With `--wat`: for these modules (`a`, `b`), the decoded module, a kernel-checked equivalence
  to the WAT module at every proved export, and the certificate's equivalences transferred to the
  decoded modules (`--link-equiv`). -/
  linkEquiv : List Char := []
  /-- `bench --vc`: the VC cases of the library (`Silmaril.Wasm.Auto2.VCLib3.vcBench`) instead of
  the front-end cases. -/
  vcCases : Bool := false

/-- Parse the options. -/
def parseOpts : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--rel" :: "eq" :: rest, o => parseOpts rest { o with rel := .eq }
  | "--rel" :: "trap" :: rest, o => parseOpts rest { o with rel := .trap }
  | "--random" :: n :: rest, o => match n.toNat? with
    | some k => parseOpts rest { o with random := k }
    | none => .error s!"bad --random {n}"
  | "--lean" :: f :: rest, o => parseOpts rest { o with lean := some f }
  | "--lean-dir" :: d :: rest, o => parseOpts rest { o with leanDir := some d }
  | "--wat" :: a :: b :: rest, o => parseOpts rest { o with wat := some (a, b) }
  | "--spec-kernel" :: rest, o => parseOpts rest { o with specKernel := true }
  | "--embed" :: rest, o => parseOpts rest { o with embed := true }
  | "--vc" :: rest, o => parseOpts rest { o with vcCases := true }
  | "--link" :: w :: rest, o =>
    if w.toList.all (fun c => c == 'a' || c == 'b') && !w.isEmpty then
      parseOpts rest { o with link := w.toList }
    else .error s!"bad --link {w} (a, b or ab)"
  | "--link-equiv" :: w :: rest, o =>
    if w.toList.all (fun c => c == 'a' || c == 'b') && !w.isEmpty then
      parseOpts rest { o with linkEquiv := w.toList }
    else .error s!"bad --link-equiv {w} (a, b or ab)"
  | "--out" :: d :: rest, o => parseOpts rest { o with out := some d }
  | "--egraph-tv" :: f :: rest, o => parseOpts rest { o with egraphTv := some f }
  | "--egraph-tv-seg" :: f :: rest, o => parseOpts rest { o with egraphTvSeg := some f }
  | "--chunk" :: n :: rest, o => match n.toNat? with
    | some k => if k > 0 then parseOpts rest { o with chunk := k } else .error "bad --chunk 0"
    | none => .error s!"bad --chunk {n}"
  | x :: _, _ => .error s!"unknown option {x}"

/-- A Lean term for a value (numbers only). -/
def valLean : Val → String
  | .num ⟨.int .i32, b⟩ => s!"Val.i32 {b.toNat}#32"
  | .num ⟨.int .i64, b⟩ => s!"Val.i64 {b.toNat}#64"
  | .num ⟨.float .f32, b⟩ => s!"Val.num ⟨.float .f32, {b.toNat}#32⟩"
  | .num ⟨.float .f64, b⟩ => s!"Val.num ⟨.float .f64, {b.toNat}#64⟩"
  | .vec b => s!"Val.vec {b.toNat}#128"
  | .ref _ => "Val.ref .null"

/-- The imports and the validity theorems of a certificate over `Silmaril.Wasm.Auto2.Kernel`:
each module is validated once (`validA`, `validB`); every later kernel evaluation
uses the validation-free instance `instK?` and closed-form data segments, through the equations
of `Silmaril.Wasm.Auto2.Kernel.Thms`. Empty in the specification form (`--spec-kernel`).
Validation goes through `Silmaril.Wasm.Auto2.Valid2` (`validG?_eq`: control flow, calls,
globals and memory on the structural path; no type comparison per function). -/
def kImport (k : Bool) : String :=
  if k then
    "import Silmaril.Wasm.Auto2.Kernel.Thms\nimport Silmaril.Wasm.Auto2.KernelU.Thms\n" ++
      "import Silmaril.Wasm.Auto2.Valid2.Thms\nimport Silmaril.Wasm.Auto2.Link.Thms\n"
  else ""

/-- The validity theorems of the two modules (see `kImport`). -/
def kValid (k : Bool) : String :=
  if k then
    "theorem validA : (Silmaril.Wasm.Validation.validate? modA).isSome = true := by\n" ++
    "  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]\n  decide +kernel\n\n" ++
    "theorem validB : (Silmaril.Wasm.Validation.validate? modB).isSome = true := by\n" ++
    "  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]\n  decide +kernel\n\n"
  else ""

/-- The proof of `cexK R m₁ m₂ j vs = true` (modules `modA`, `modB`, or swapped with `sym`). -/
def cexProof (k sym : Bool) : String :=
  if k then
    let v := if sym then "validB validA" else "validA validB"
    "(by\n    rw [cexK, Silmaril.Proofs.Wasm.Auto2.Kernel.cexWith_eq_K " ++ v ++ "]\n" ++
      "    decide +kernel)"
  else "(by decide +kernel)"

/-- A Lean list literal of bytes. -/
def bytesLean (bs : ByteArray) : String :=
  "[" ++ ", ".intercalate (bs.toList.map toString) ++ "]"

/-- The header of a certificate: both modules decoded from their binaries (`extra`: more
imports). -/
def certHeader (a b : ByteArray) (extra : List String := []) (k : Bool := false) : String :=
  "import Silmaril.Wasm.Auto.Front.Thms\nimport Silmaril.Wasm.Auto.Bridge.Thms\n" ++
  "import Silmaril.Wasm.Auto2.Calls.Thms\nimport Silmaril.Wasm.Auto2.Front2.Thms\n" ++
  String.join (extra.map fun m => "import " ++ m ++ "\n") ++
  "import Silmaril.Wasm.Binaryen.Exe.CompactInput\n" ++ kImport k ++ "\n" ++
  "/-! Certificate written by `wasm-check`. -/\n\n" ++
  "open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front\n" ++
  "open Silmaril.Wasm.SingleThreaded (profile)\n\n" ++
  "/-- The first module, decoded from its binary. -/\n" ++
  "def modA : Module := match Silmaril.Wasm.Binaryen.Exe.CompactInput.prepare ⟨#" ++
    bytesLean a ++ "⟩ with\n  | .ok m => m.source\n  | .error _ => {}\n\n" ++
  "/-- The second module, decoded from its binary. -/\n" ++
  "def modB : Module := match Silmaril.Wasm.Binaryen.Exe.CompactInput.prepare ⟨#" ++
    bytesLean b ++ "⟩ with\n  | .ok m => m.source\n  | .error _ => {}\n\n" ++ kValid k

/-- A decoded module as a Lean term (its derived `Repr`: constructor applications and literals,
re-elaborated when the certificate is checked). -/
def moduleLean (m : Module) : String := Std.Format.pretty (repr m) 100

/-- The header of a certificate whose modules are stated as **decoded terms**:
the modules the tool decoded (silmaril-lean's decoder, compiled), printed as Lean terms,
so the kernel never decodes a binary. -/
def certHeaderTerm (ma mb : Module) (extra : List String := []) (k : Bool := false) : String :=
  "import Silmaril.Wasm.Auto.Front.Thms\nimport Silmaril.Wasm.Auto.Bridge.Thms\n" ++
  "import Silmaril.Wasm.Auto2.Calls.Thms\nimport Silmaril.Wasm.Auto2.Front2.Thms\n" ++
  String.join (extra.map fun m => "import " ++ m ++ "\n") ++ kImport k ++ "\n" ++
  "/-! Certificate written by `wasm-check` (modules stated as decoded terms). -/\n\n" ++
  "open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front\n" ++
  "open Silmaril.Wasm.SingleThreaded (profile)\n\n" ++
  "/-- The first module, as decoded by the tool. -/\n" ++
  "def modA : Module :=\n" ++ moduleLean ma ++ "\n\n" ++
  "/-- The second module, as decoded by the tool. -/\n" ++
  "def modB : Module :=\n" ++ moduleLean mb ++ "\n\n" ++ kValid k

/-- The header of a certificate whose modules are given as WAT text (`wat3b!`, parsed when the
certificate is elaborated; the kernel then checks only the Module terms, without decoding). -/
def certHeaderWat (ta tb : String) (extra : List String := []) (k : Bool := false) : String :=
  "import Silmaril.Wasm.Auto.Front.Thms\nimport Silmaril.Wasm.Auto.Bridge.Thms\n" ++
  "import Silmaril.Wasm.Auto2.Calls.Thms\nimport Silmaril.Wasm.Auto2.Front2.Thms\n" ++
  String.join (extra.map fun m => "import " ++ m ++ "\n") ++
  "import Silmaril.Wasm.Auto2.Wat.Defs\n" ++ kImport k ++ "\n" ++
  "/-! Certificate written by `wasm-check` (modules given as WAT text). -/\n\n" ++
  "open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front\n" ++
  "open Silmaril.Wasm.SingleThreaded (profile)\n\n" ++
  "/-- The first module, from its WAT text. -/\n" ++
  "def modA : Module := wat3b! r#\"\n" ++ ta ++ "\n\"#\n\n" ++
  "/-- The second module, from its WAT text. -/\n" ++
  "def modB : Module := wat3b! r#\"\n" ++ tb ++ "\n\"#\n\n" ++ kValid k

/-- The link of a WAT-stated module to the binary (`--link`): the module the tool decoded from
the binary (silmaril-lean's decoder, compiled), as a term, and a proof by `rfl` that the WAT
module is that term. It holds when Binaryen's printing is faithful to the binary (for
Binaryen-written binaries; Binaryen reorders and merges the type section of
other binaries, and the `rfl` then fails). -/
def linkThms (name : String) (m : Module) : String :=
  s!"/-- `{name}` as decoded from its binary by the tool. -/\n" ++
  s!"def {name}Dec : Module :=\n" ++ moduleLean m ++ "\n\n" ++
  s!"/-- The WAT module `{name}` is the decoded binary. -/\n" ++
  s!"theorem {name}_link : {name} = {name}Dec := rfl\n\n"

/-- The theorem of a proved export `j`: equivalence (hence refinement) at every profile. -/
def provedThm (rel : Rel) (j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto2.Calls.modEquiv_of_proveStageC (m₁ := modA) (m₂ := modB) (j := {j}) " ++
  "(by decide +kernel) _ P\n\n"

/-- A Lean list literal of Booleans. -/
def boolsLean (bs : List Bool) : String := "[" ++ ", ".intercalate (bs.map toString) ++ "]"

/-- A Lean literal of an integer type list. -/
def tysLean (ts : List IntType) : String :=
  "[" ++ ", ".intercalate (ts.map fun t => match t with | .i32 => ".i32" | .i64 => ".i64") ++ "]"

/-- A Lean list literal of naturals. -/
def natsLean (ns : List Nat) : String := "[" ++ ", ".intercalate (ns.map toString) ++ "]"

/-- The decoded module `{name}Dec` and its validity (`--link-equiv`). -/
def linkDecHead (name : String) (m : Module) : String :=
  s!"/-- `{name}` as decoded from its binary by the tool. -/\n" ++
  s!"def {name}Dec : Module :=\n" ++ moduleLean m ++ "\n\n" ++
  s!"theorem valid{name.drop 3}Dec : (Silmaril.Wasm.Validation.validate? {name}Dec).isSome = true := by\n" ++
  "  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]\n  decide +kernel\n\n"

/-- The link of side `X` (`A`: `modADec ≈ modA`; `B`: `modB ≈ modBDec`) on the exports `js`:
one kernel evaluation of `checkAmong` and the signatures, then one equivalence per export. -/
def linkEquivThms (X : String) (js : List Nat) : String :=
  let (m₁, m₂, v₁, v₂) := if X == "A" then ("modADec", "modA", "validADec", "validA")
    else ("modB", "modBDec", "validB", "validBDec")
  s!"theorem link{X} : Silmaril.Wasm.Auto.Bridge.checkAmong {m₁} {m₂} {natsLean js} =\n    " ++
    boolsLean (js.map fun _ => true) ++ " := by\n" ++
    s!"  rw [Silmaril.Proofs.Wasm.Auto2.Kernel.checkAmongX_eq_K {v₁} {v₂}]\n  decide +kernel\n\n" ++
  s!"theorem sig{X} : Silmaril.Wasm.Auto2.Link.sigOkAll {m₁} {m₂} {natsLean js} = true := by\n" ++
    "  decide +kernel\n\n" ++
  String.join ((List.range js.length).zip js |>.map fun (i, j) =>
    s!"theorem link{X}_{j} (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P {m₁} {m₂} {j} :=\n" ++
    s!"  Silmaril.Wasm.Auto.Bridge.modEquiv_of_checkAmong (js := {natsLean js}) (i := {i}) " ++
    s!"(Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl\n    (by rw [link{X}]; rfl)\n\n")

/-- The signatures of two modules on the exports `js` (`theorem {name}`). -/
def sigThm (name m₁ m₂ : String) (js : List Nat) : String :=
  s!"theorem {name} : Silmaril.Wasm.Auto2.Link.sigOkAll {m₁} {m₂} {natsLean js} = true := by\n" ++
    "  decide +kernel\n\n"

/-- The certificate's equivalence `t` at export `j` transferred to decoded modules through the
links (`sides`: `a`, `b` or both). -/
def decThms (sides : List Char) (j : Nat) (t : String) : String :=
  let sig (n : String) := s!"(Silmaril.Proofs.Wasm.Auto2.Link.sigOkK_of_all {n} (by decide))"
  let lk := "Silmaril.Proofs.Wasm.Auto2.Link.modEquiv_link"
  let a := sides.contains 'a'
  let b := sides.contains 'b'
  (if a then
    s!"theorem decA_{j} (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P modADec modB {j} :=\n" ++
    s!"  {lk} validADec validA validB {sig "sigA"} {sig "sigAB"}\n" ++
    s!"    (linkA_{j} P) ({t} P)\n\n" else "") ++
  (if b then
    s!"theorem decB_{j} (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P modA modBDec {j} :=\n" ++
    s!"  {lk} validA validB validBDec {sig "sigAB"} {sig "sigB"}\n" ++
    s!"    ({t} P) (linkB_{j} P)\n\n" else "") ++
  (if a && b then
    s!"theorem decAB_{j} (P : Numerics.Profile) : ModEquiv Rel.eq.toProp P modADec modBDec {j} :=\n" ++
    s!"  {lk} validADec validB validBDec {sig "sigADB"} {sig "sigB"}\n" ++
    s!"    (decA_{j} P) (linkB_{j} P)\n\n" else "")

/-- The shared fact of chunk `c` of a `pass` certificate: the function-level stages on the
exports `js`, each module instantiated once. -/
def chunkThm (c : Nat) (js : List Nat) (k : Bool := false) : String :=
  s!"theorem chunk_{c} : Silmaril.Wasm.Auto.Bridge.checkAmong modA modB {natsLean js} =\n    " ++
    boolsLean (js.map fun _ => true) ++ " := by\n" ++
    (if k then "  rw [Silmaril.Proofs.Wasm.Auto2.Kernel.checkAmongX_eq_K validA validB]\n" else "") ++
    "  decide +kernel\n\n"

/-- The theorem of export `j`, entry `i` of chunk `c` (exports `js`). -/
def provedChunkThm (rel : Rel) (c : Nat) (js : List Nat) (i j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto.Bridge.modEquiv_of_checkAmong (js := {natsLean js}) (i := {i}) " ++
  s!"(Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl\n    (by rw [chunk_{c}]; rfl)\n\n"

/-- The shared fact of chunk `c` of the `equivu` stage: the unrolled summaries and the
guard-aware check on the exports `js`, each module instantiated once. -/
def chunkUThm (c : Nat) (js : List Nat) (k : Bool := false) : String :=
  s!"theorem chunkU_{c} : Silmaril.Wasm.Auto2.Summ.checkAmongU Silmaril.Wasm.Auto2.Summ.defFuel modA modB {natsLean js} =\n    " ++
    boolsLean (js.map fun _ => true) ++ " := by\n" ++
    (if k then "  rw [Silmaril.Proofs.Wasm.Auto2.KernelU.checkAmongU_eq_K validA validB]\n" else "") ++
    "  decide +kernel\n\n"

/-- The theorem of export `j` proved by the `equivu` stage, entry `i` of chunk `c`. -/
def provedChunkUThm (rel : Rel) (c : Nat) (js : List Nat) (i j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto2.Summ.modEquiv_of_checkAmongU (js := {natsLean js}) (i := {i}) " ++
  s!"(Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl\n    (by rw [chunkU_{c}]; rfl)\n\n"

/-- The shared fact of chunk `c` of the `equivc` stage (calls inlined). -/
def chunkCThm (c : Nat) (js : List Nat) (k : Bool := false) : String :=
  s!"theorem chunkC_{c} : Silmaril.Wasm.Auto2.Calls.checkAmongC Silmaril.Wasm.Auto2.Summ.defFuel modA modB {natsLean js} =\n    " ++
    boolsLean (js.map fun _ => true) ++ " := by\n" ++
    (if k then "  rw [Silmaril.Proofs.Wasm.Auto2.KernelU.checkAmongC_eq_K validA validB]\n" else "") ++
    "  decide +kernel\n\n"

/-- The theorem of export `j` proved by the `equivc` stage, entry `i` of chunk `c`. -/
def provedChunkCThm (rel : Rel) (c : Nat) (js : List Nat) (i j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto2.Calls.modEquiv_of_checkAmongC (js := {natsLean js}) (i := {i}) " ++
  s!"(Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl\n    (by rw [chunkC_{c}]; rfl)\n\n"

/-- The shared fact of chunk `c` of the stages `equivu`, `equivc`, `equivv`: the
summaries with unrolled loops and inlined calls and the check with the third simplifier, each
module instantiated once; over `Silmaril.Wasm.Auto2.Kernel` when `k` (`checkAmongV_eq_K`). -/
def chunkVThm (c : Nat) (js : List Nat) (k : Bool) : String :=
  s!"theorem chunkV_{c} : Silmaril.Wasm.Auto2.Summ2.checkAmongV Silmaril.Wasm.Auto2.Summ.defFuel modA modB {natsLean js} =\n    " ++
    boolsLean (js.map fun _ => true) ++ " := by\n" ++
    (if k then "  rw [Silmaril.Wasm.Auto2.Summ2.checkAmongV_eq_K validA validB]\n" else "") ++
    "  decide +kernel\n\n"

/-- The theorem of export `j` proved by chunk `c` of `checkAmongV`, entry `i`. -/
def provedChunkVThm (rel : Rel) (c : Nat) (js : List Nat) (i j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto2.Summ2.modEquiv_of_checkAmongV (js := {natsLean js}) (i := {i}) " ++
  s!"(Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl\n    (by rw [chunkV_{c}]; rfl)\n\n"

/-- The theorem of export `j` proved by stage `vcequiv` (functional contracts). -/
def vcEquivThm (rel : Rel) (j : Nat) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  "  Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquivAny (Silmaril.Wasm.Auto.Bridge.rel_refl _)\n" ++
  s!"    (L := Silmaril.Wasm.Auto2.VCEquiv.eqFuns) (j := {j}) (by decide +kernel)\n\n"

/-- The certificate theorems of an export proved at stage `st` (`refines`/`equiv`, one export). -/
def stageThms (rel : Rel) (st : String) (j : Nat) (k : Bool) : String :=
  if st == "vcequiv" then vcEquivThm rel j
  else if st == "equivu" || st == "equivc" || st == "equivv" then
    chunkVThm 0 [j] k ++ provedChunkVThm rel 0 [j] 0 j
  else chunkThm 0 [j] k ++ provedChunkThm rel 0 [j] 0 j

/-- The shared fact of the e-graph lifts on the exports `js`. -/
def liftsAmongThm (js : List Nat) (ls : List (Option (List IntType))) (k : Bool := false) :
    String :=
  let lit := "[" ++ ", ".intercalate (ls.map fun o => match o with
    | some ts => "some " ++ tysLean ts
    | none => "none") ++ "]"
  s!"theorem lifts : Silmaril.Wasm.Auto.Bridge.liftAmong modA modB {natsLean js} =\n    " ++ lit ++
    " := by\n" ++
    (if k then "  rw [Silmaril.Proofs.Wasm.Auto2.Kernel.liftAmong_eq_K validA validB]\n" else "") ++
    "  decide +kernel\n\n"

/-- The theorem of export `j` (entry `i` of the lifts), lifted from the e-graph certificate
`cert` on its bodies. -/
def liftedAmongThm (rel : Rel) (js : List Nat) (i j : Nat) (cert : String) (k : Bool := false) :
    String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem lifted_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  "  Silmaril.Wasm.Auto.Bridge.modEquiv_of_egraph (Silmaril.Wasm.Auto.Bridge.rel_refl _)\n" ++
  s!"    (Silmaril.Wasm.Auto.Bridge.egraphLiftOk_of_liftAmong (js := {natsLean js}) (i := {i}) rfl " ++
  "(by rw [lifts]; rfl))\n" ++
  (if k then
    "    (by rw [Silmaril.Proofs.Wasm.Auto2.Kernel.fnBody?_eq_K validA]; kernel_rfl)\n" ++
    s!"    (by rw [Silmaril.Proofs.Wasm.Auto2.Kernel.fnBody?_eq_K validB]; kernel_rfl) {cert}\n\n"
  else s!"    (by kernel_rfl)\n    (by kernel_rfl) {cert}\n\n")

/-- The theorem of export `j`, from the function-entry certificate `cert` (`wasm-egraph tv-seg
--func`) on its bodies. -/
def segThm (rel : Rel) (j : Nat) (cert : String) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  s!"theorem seg_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  "  Silmaril.Wasm.Auto.Bridge.modEquiv_of_funcEquiv (Silmaril.Wasm.Auto.Bridge.rel_refl _)\n" ++
  s!"    (by decide +kernel) (by kernel_rfl) (by kernel_rfl) {cert}\n\n"

/-- The `FuncEquiv` theorems of a `wasm-egraph tv-seg --func` module, with its namespace and
the module name derived from the path. -/
def tvSegTheorems (path : String) : IO (String × String × List String) := do
  let src ← IO.FS.readFile path
  let lines := src.splitOn "\n"
  let ns := (lines.findSome? fun l =>
    if l.startsWith "namespace " then some (l.drop 10).trimAscii.toString else none).getD ""
  let names := lines.filterMap fun l =>
    if l.startsWith "theorem " && (l.splitOn "ESeg.FuncEquiv").length > 1 then
      some ((((l.drop 8).toString).splitOn " ").headD "")
    else none
  let modName := ((path.dropEnd 5).toString.replace "/" ".")
  return (modName, ns, names)

/-- Split a list into chunks of `k` (`k > 0`). -/
def chunks {α : Type} (k : Nat) (l : List α) : List (List α) :=
  if _h : l.isEmpty || k == 0 then [] else l.take k :: chunks k (l.drop k)
termination_by l.length
decreasing_by
  simp only [Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff, not_or] at _h
  have := List.length_pos_iff.mpr _h.1
  simp only [List.length_drop]
  omega

/-- The theorem names of an e-graph translation-validation module (`wasm-egraph tv --lean`), in
order, with its namespace, and the module name derived from the path. -/
def tvTheorems (path : String) : IO (String × String × List String) := do
  let src ← IO.FS.readFile path
  let lines := src.splitOn "\n"
  let ns := (lines.findSome? fun l =>
    if l.startsWith "namespace " then some (l.drop 10).trimAscii.toString else none).getD ""
  let names := lines.filterMap fun l =>
    if l.startsWith "theorem " then
      some ((((l.drop 8).toString).splitOn " ").headD "")
    else none
  let modName := ((path.dropEnd 5).toString.replace "/" ".")
  return (modName, ns, names)

/-- The theorem of a refuted export `j`. -/
def refutedThm (kind : String) (rel : Rel) (j : Nat) (vs : List Val) (sym : Bool)
    (k : Bool := false) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  let stmt := if kind == "equiv" then "ModEquiv" else "ModRefines"
  let vsL := "[" ++ ", ".intercalate (vs.map valLean) ++ "]"
  let proof := if sym then
      s!"not_modEquiv_of_cexK_symm (vs := {vsL}) {cexProof k true}"
    else if kind == "equiv" then s!"not_modEquiv_of_cexK (vs := {vsL}) {cexProof k false}"
    else s!"refutes_of_cexK (vs := {vsL}) {cexProof k false}"
  s!"theorem refuted_{j} : ¬ {stmt} {relName}.toProp (profile Silmaril.Wasm.Verify.refOracle) " ++
    s!"modA modB {j} :=\n  {proof}\n\n"

/-- The Lean certificate of a refutation. -/
def certificate (kind : String) (rel : Rel) (hdr : String) (j : Nat) (vs : List Val)
    (sym : Bool) (k : Bool := false) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  let stmt := if kind == "equiv" then "ModEquiv" else "ModRefines"
  let vsL := "[" ++ ", ".intercalate (vs.map valLean) ++ "]"
  let proof := if sym then
      s!"not_modEquiv_of_cexK_symm (vs := {vsL}) {cexProof k true}"
    else if kind == "equiv" then s!"not_modEquiv_of_cexK (vs := {vsL}) {cexProof k false}"
    else s!"refutes_of_cexK (vs := {vsL}) {cexProof k false}"
  hdr ++
  s!"theorem refuted : ¬ {stmt} {relName}.toProp (profile Silmaril.Wasm.Verify.refOracle) modA modB {j} :=\n" ++
  s!"  {proof}\n"

/-- Time an action in milliseconds. -/
def timed {α : Type} (act : IO α) : IO (α × Nat) := do
  let t₀ ← IO.monoMsNow
  let a ← act
  let t₁ ← IO.monoMsNow
  return (a, t₁ - t₀)

/-- Force a report (so that timing measures its computation). -/
def evalReport (r : Unit → Report) : IO Report := do
  let r := r ()
  -- `toJson` forces every field.
  let _ := r.toJson.length
  return r

/-- A Lean term for a candidate of `Silmaril.Wasm.Auto2.VCInfer`. -/
def candLean : Option Silmaril.Wasm.Auto2.VCInfer.Cand → String
  | none => "none"
  | some c => s!"(some ⟨{c.t}, {c.n}, {c.a}, {c.guard}⟩)"

/-- A side of stage `vcinfer` as JSON. -/
def sideJson : Silmaril.Wasm.Auto2.VCInfer.Side → String
  | .lib i => "{\"lib\":" ++ toString i ++ "}"
  | .inferred none _ => "{\"inferred\":\"no loop\"}"
  | .inferred (some c) _ =>
    "{\"inferred\":{\"template\":" ++ toString c.t ++ ",\"n\":" ++ toString c.n ++
      ",\"acc\":" ++ toString c.a ++ ",\"guard\":" ++ toString c.guard ++ "}}"

/-- The contract `e` of one side of stage `vcinfer` (`code`: the name of its function's term)
and the proof that it is derived from `I`. -/
def sideLean (I : Silmaril.Wasm.Auto2.VCInfer.InferFun) (e code : String) :
    Silmaril.Wasm.Auto2.VCInfer.Side → String × String
  | .lib i =>
    (s!"/-- The library contract `{e}`. -/\n" ++
      s!"def {e} : Silmaril.Wasm.Auto2.VCBridge.VcEntry := Silmaril.Wasm.Auto2.VCInfer.libEntry {I.leanName} {i}\n\n",
     s!"(Silmaril.Wasm.Auto2.VCInfer.derives_libEntry {I.leanName} {i})")
  | .inferred c fn =>
    (s!"/-- The code of the export, as decoded by the tool. -/\ndef {code} : Func :=\n" ++
      Std.Format.pretty (repr fn) 100 ++ "\n\n" ++
      s!"/-- The inferred contract `{e}`: its conditions are proved by `vcgen4` and the fixed tactic. -/\n" ++
      s!"def {e} : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=\n" ++
      s!"  Silmaril.Wasm.Auto2.VCInfer.inferEntry {I.leanName} {candLean c} {code}\n" ++
      s!"    (by show Silmaril.Wasm.Auto2.VCGen.AllValid {I.fnsName} _; {I.tactic})\n\n",
     "(.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)")

/-- The certificate theorems of stage `vcinfer` for export `j`. -/
def inferThms (rel : Rel) (j : Nat) (I : Silmaril.Wasm.Auto2.VCInfer.InferFun)
    (s₁ s₂ : Silmaril.Wasm.Auto2.VCInfer.Side) : String :=
  let relName := match rel with | .eq => "Rel.eq" | .trap => "Rel.trap"
  let (dA, hA) := sideLean I "eA" "codeA" s₁
  let (dB, hB) := sideLean I "eB" "codeB" s₂
  "set_option maxRecDepth 100000\n\n" ++ dA ++ dB ++
  s!"theorem check_{j} : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith eA eB modA modB {j} = true := by\n" ++
  "  decide +kernel\n\n" ++
  s!"theorem proved_{j} (P : Numerics.Profile) : ModEquiv {relName}.toProp P modA modB {j} :=\n" ++
  s!"  Silmaril.Wasm.Auto2.VCInfer.modEquiv_of_infer (e₁ := eA) (e₂ := eB)\n" ++
  s!"    (Silmaril.Wasm.Auto.Bridge.rel_refl _) {I.leanName} {hA} {hB} check_{j}\n"

/-- `refines` and `equiv`. -/
def runPair (kind : String) (pa pb exp : String) (o : Opts) : IO UInt32 := do
  let ba ← IO.FS.readBinFile pa
  let bb ← IO.FS.readBinFile pb
  let (ma, mb) ← match decode ba, decode bb with
    | .ok ma, .ok mb => pure (ma, mb)
    | .error e, _ => do IO.eprintln s!"wasm-check: cannot decode {pa}: {e}"; return 2
    | _, .error e => do IO.eprintln s!"wasm-check: cannot decode {pb}: {e}"; return 2
  let some ja := resolveExport ma exp | do
    IO.eprintln s!"wasm-check: no function export {exp} in {pa}"; return 2
  let some jb := resolveExport mb exp | do
    IO.eprintln s!"wasm-check: no function export {exp} in {pb}"; return 2
  if ja != jb then
    IO.eprintln s!"wasm-check: export {exp} has index {ja} in {pa} and {jb} in {pb}"
    return 2
  let identical := ba == bb
  let (r, ms) ← timed <| evalReport fun _ =>
    if kind == "equiv" then Silmaril.Wasm.Auto2.Front2.checkEquivV o.rel ma mb ja o.random identical
    else Silmaril.Wasm.Auto2.Front2.checkRefinesV o.rel ma mb ja o.random identical
  -- Stage `vcinfer`: a search for inferred contracts, run only on
  -- an unknown verdict; its result is a candidate whose certificate (`--lean`) is the proof.
  let (inf, msI) ← timed (pure (if r.verdict == .unknown then
      Silmaril.Wasm.Auto2.VCInfer.inferPair? Silmaril.Wasm.Auto2.VCInfer.inferFuns ma mb ja else none))
  let infJ := match inf with
    | some (I, s₁, s₂) => ",\"vcinfer\":{\"fun\":\"" ++ I.F.name ++ "\",\"a\":" ++ sideJson s₁ ++
        ",\"b\":" ++ sideJson s₂ ++ ",\"status\":\"candidate (proved by the certificate)\"}"
    | none => ""
  IO.println ("{\"check\":\"" ++ kind ++ "\",\"export\":" ++ toString ja ++ ",\"report\":" ++
    r.toJson ++ ",\"stages\":[{\"stage\":\"identical\",\"result\":" ++ toString identical ++
    "},{\"stage\":\"difftest\",\"ms\":" ++ toString ms ++ "},{\"stage\":\"vcinfer\",\"ms\":" ++
    toString msI ++ "}]" ++ infJ ++ "}")
  let kk := !o.specKernel
  let hdr := if o.embed then certHeader ba bb [] kk else certHeaderTerm ma mb [] kk
  if let some f := o.lean then
    match r.reason with
    | .counterexample vs _ _ =>
      -- For `equiv`, the counterexample may come from the reverse direction.
      let sym := kind == "equiv" && !cexWith runC o.rel ma mb ja vs
      IO.FS.writeFile f (certificate kind o.rel hdr ja vs sym kk)
    | .stage st =>
      if o.specKernel && st != "vcequiv" && st != "equivv" then
        IO.FS.writeFile f (hdr ++ provedThm o.rel ja)
      else IO.FS.writeFile f (hdr ++ stageThms o.rel st ja kk)
    | _ =>
      if let some (I, s₁, s₂) := inf then
        let hdrI := if o.embed then certHeader ba bb ["Silmaril.Wasm.Auto2.VCInfer.Thms"] kk
          else certHeaderTerm ma mb ["Silmaril.Wasm.Auto2.VCInfer.Thms"] kk
        IO.FS.writeFile f (hdrI ++ inferThms o.rel ja I s₁ s₂)
  return 0

/-- `pass`: every shared function export, for equivalence. -/
def runPass (pa pb : String) (o : Opts) : IO UInt32 := do
  let ba ← IO.FS.readBinFile pa
  let bb ← IO.FS.readBinFile pb
  let (ma, mb) ← match decode ba, decode bb with
    | .ok ma, .ok mb => pure (ma, mb)
    | .error e, _ => do IO.eprintln s!"wasm-check: cannot decode {pa}: {e}"; return 2
    | _, .error e => do IO.eprintln s!"wasm-check: cannot decode {pb}: {e}"; return 2
  let fa := funcExports ma
  let fb := funcExports mb
  let kk := !o.specKernel
  let mut nP := 0
  let mut nR := 0
  let mut nU := 0
  let mut total := 0
  let mut thms := ""
  let mut proved : List Nat := []
  let mut provedU : List Nat := []
  let mut provedC : List Nat := []
  let mut provedV : List Nat := []
  let mut provedVC : List Nat := []
  let mut unknowns : List Nat := []
  for k in List.range fa.length do
    let name := (fa.getD k ("", 0)).1
    if (fb[k]?.map (·.1)) != some name then
      IO.println ("{\"export\":" ++ toString k ++ ",\"name\":\"" ++ name ++
        "\",\"skipped\":\"not at the same index in both modules\"}")
      continue
    let (r, ms) ← timed <| evalReport fun _ =>
      Silmaril.Wasm.Auto2.Front2.checkEquivV o.rel ma mb k o.random (ba == bb)
    total := total + ms
    match r.verdict with
    | .proved => nP := nP + 1
    | .refuted => nR := nR + 1
    | .unknown => nU := nU + 1
    IO.println ("{\"export\":" ++ toString k ++ ",\"name\":\"" ++ name ++ "\",\"report\":" ++
      r.toJson ++ ",\"ms\":" ++ toString ms ++ "}")
    match r.reason with
    | .stage st =>
      -- Kernel form: every summary stage in `checkAmongV` chunks (over `instK?`).
      if st == "vcequiv" then provedVC := provedVC ++ [k]
      else if st == "equivv" || (kk && (st == "equivu" || st == "equivc")) then
        provedV := provedV ++ [k]
      else if st == "equivu" then provedU := provedU ++ [k]
      else if st == "equivc" then provedC := provedC ++ [k]
      else proved := proved ++ [k]
    | .counterexample vs _ _ =>
      thms := thms ++ refutedThm "equiv" o.rel k vs (!cexWith runC o.rel ma mb k vs) kk
    | _ => unknowns := unknowns ++ [k]
  -- E-graph lifts: unknown exports whose side conditions hold, with the k-th theorem of the
  -- translation-validation module.
  let mut nL := 0
  let mut liftThms := ""
  let mut extra : List String := []
  let mut liftedK : List Nat := []
  if let some tv := o.egraphTv then
    let (modName, ns, names) ← tvTheorems tv
    -- The theorem of export `k`: `tv_<export name>` if there is one, else the `k`-th theorem
    -- when the module has one theorem per export.
    let thmOf := fun (k : Nat) =>
      let byName := "tv_" ++ (fa.getD k ("", 0)).1
      if names.contains byName then some byName
      else if names.length == fa.length then names[k]? else none
    -- Side conditions of the unknown exports that have a translation-validation theorem.
    let cand := unknowns.filter fun k => (thmOf k).isSome
    let la := Silmaril.Wasm.Auto.Bridge.liftAmong ma mb cand
    for (i, k) in (List.range cand.length).zip cand do
      if let (some (some _), some n) := (la[i]?, thmOf k) then
        nL := nL + 1
        liftedK := liftedK ++ [k]
        liftThms := liftThms ++ liftedAmongThm o.rel cand i k (ns ++ "." ++ n) kk
    if nL > 0 then
      extra := [modName]
      liftThms := liftsAmongThm cand la kk ++ liftThms
  -- E-graph certificates with locals (`wasm-egraph tv-seg --func`): unknown exports not lifted
  -- above whose side conditions hold, with their `tv_<export name>` theorem.
  let mut nS := 0
  let mut segK : List Nat := []
  if let some tv := o.egraphTvSeg then
    let (modName, ns, names) ← tvSegTheorems tv
    for k in unknowns do
      let byName := "tv_" ++ (fa.getD k ("", 0)).1
      let liftedHere := liftedK.contains k
      if !liftedHere && names.contains byName &&
          (Silmaril.Wasm.Auto.Bridge.funcLift? ma mb k).isSome then
        nS := nS + 1
        segK := segK ++ [k]
        liftThms := liftThms ++ segThm o.rel k (ns ++ "." ++ byName)
    if nS > 0 then
      extra := extra ++ [modName]
  IO.println ("{\"summary\":{\"exports\":" ++ toString fa.length ++ ",\"proved\":" ++
    toString nP ++ ",\"refuted\":" ++ toString nR ++ ",\"unknown\":" ++ toString nU ++
    ",\"egraphLifts\":" ++ toString nL ++ ",\"egraphSegLifts\":" ++ toString nS ++
    ",\"ms\":" ++ toString total ++ "}}")
  -- `--link-equiv`: every proved export, with its theorem, that the
  -- summaries of `checkAmong` cover on both decoded modules (checked here on each module
  -- against itself; the kernel checks it against the WAT module).
  let named : List (Nat × String) :=
    ((proved ++ provedU ++ provedC ++ provedV ++ provedVC).map fun j => (j, s!"proved_{j}")) ++
      (liftedK.map fun j => (j, s!"lifted_{j}")) ++ (segK.map fun j => (j, s!"seg_{j}"))
  let named := (named.toArray.qsort (fun x y => x.1 < y.1)).toList
  let lj := named.map (·.1)
  let okA := Silmaril.Wasm.Auto.Bridge.checkAmong ma ma lj
  let okB := Silmaril.Wasm.Auto.Bridge.checkAmong mb mb lj
  let named := ((List.range named.length).zip named).filterMap fun (i, n) =>
    if (!o.linkEquiv.contains 'a' || okA[i]? == some true) &&
        (!o.linkEquiv.contains 'b' || okB[i]? == some true) then some n else none
  let lj := named.map (·.1)
  let linkTail :=
    if o.linkEquiv.isEmpty || o.wat.isNone || o.rel != .eq || lj.isEmpty || !kk then ""
    else
      let la := o.linkEquiv.contains 'a'
      let lb := o.linkEquiv.contains 'b'
      (if la then linkDecHead "modA" ma ++ linkEquivThms "A" lj else "") ++
      (if lb then linkDecHead "modB" mb ++ linkEquivThms "B" lj else "") ++
      sigThm "sigAB" "modA" "modB" lj ++
      (if la && lb then sigThm "sigADB" "modADec" "modB" lj else "") ++
      String.join (named.map fun (j, t) => decThms o.linkEquiv j t)
  if !o.linkEquiv.isEmpty then
    IO.println ("{\"linkEquiv\":{\"sides\":\"" ++ String.ofList o.linkEquiv ++
      "\",\"linked\":" ++ toString lj.length ++ "}}")
  let hdr ← match o.wat with
    | some (wa, wb) => do
      let ta ← IO.FS.readFile wa
      let tb ← IO.FS.readFile wb
      let links := (if o.link.contains 'a' then linkThms "modA" ma else "") ++
        (if o.link.contains 'b' then linkThms "modB" mb else "")
      pure fun (ex : List String) => certHeaderWat ta tb ex kk ++ links
    | none => pure fun (ex : List String) =>
      if o.embed then certHeader ba bb ex kk else certHeaderTerm ma mb ex kk
  if let some f := o.lean then
    -- The proved exports, in chunks of `o.chunk`: one kernel evaluation of `checkAmong` each.
    let mut all := ""
    let cs := chunks o.chunk proved
    for (c, js) in (List.range cs.length).zip cs do
      all := all ++ chunkThm c js kk
      for (i, j) in (List.range js.length).zip js do
        all := all ++ provedChunkThm o.rel c js i j
    let csU := chunks o.chunk provedU
    for (c, js) in (List.range csU.length).zip csU do
      all := all ++ chunkUThm c js kk
      for (i, j) in (List.range js.length).zip js do
        all := all ++ provedChunkUThm o.rel c js i j
    let csC := chunks o.chunk provedC
    for (c, js) in (List.range csC.length).zip csC do
      all := all ++ chunkCThm c js kk
      for (i, j) in (List.range js.length).zip js do
        all := all ++ provedChunkCThm o.rel c js i j
    let csV := chunks o.chunk provedV
    for (c, js) in (List.range csV.length).zip csV do
      all := all ++ chunkVThm c js kk
      for (i, j) in (List.range js.length).zip js do
        all := all ++ provedChunkVThm o.rel c js i j
    for j in provedVC do
      all := all ++ vcEquivThm o.rel j
    IO.FS.writeFile f (hdr extra ++ all ++ thms ++ liftThms ++ linkTail)
  -- The same certificate split into files (one per chunk, one for the rest), checked by separate
  -- Lean processes: no process holds more than one chunk.
  if let some d := o.leanDir then
    IO.FS.createDirAll d
    let cs := chunks o.chunk proved
    for (c, js) in (List.range cs.length).zip cs do
      let mut body := chunkThm c js kk
      for (i, j) in (List.range js.length).zip js do
        body := body ++ provedChunkThm o.rel c js i j
      IO.FS.writeFile s!"{d}/chunk_{c}.lean" (hdr [] ++ body)
    let csU := chunks o.chunk provedU
    for (c, js) in (List.range csU.length).zip csU do
      let mut body := chunkUThm c js kk
      for (i, j) in (List.range js.length).zip js do
        body := body ++ provedChunkUThm o.rel c js i j
      IO.FS.writeFile s!"{d}/chunkU_{c}.lean" (hdr [] ++ body)
    let csC := chunks o.chunk provedC
    for (c, js) in (List.range csC.length).zip csC do
      let mut body := chunkCThm c js kk
      for (i, j) in (List.range js.length).zip js do
        body := body ++ provedChunkCThm o.rel c js i j
      IO.FS.writeFile s!"{d}/chunkC_{c}.lean" (hdr [] ++ body)
    let csV := chunks o.chunk provedV
    for (c, js) in (List.range csV.length).zip csV do
      let mut body := chunkVThm c js kk
      for (i, j) in (List.range js.length).zip js do
        body := body ++ provedChunkVThm o.rel c js i j
      IO.FS.writeFile s!"{d}/chunkV_{c}.lean" (hdr [] ++ body)
    if !provedVC.isEmpty then
      IO.FS.writeFile s!"{d}/vcequiv.lean" (hdr [] ++ String.join (provedVC.map (vcEquivThm o.rel)))
    if thms != "" || liftThms != "" then
      IO.FS.writeFile s!"{d}/rest.lean" (hdr extra ++ thms ++ liftThms)
  return 0

/-- `bench --vc`: the VC library's contracts (memory, callees, globals, arithmetic) against their
demonstration modules and mutants (`Silmaril.Wasm.Auto2.VCLib3.vcBench`), by `vcCheckM`. -/
def runVcBench : IO UInt32 := do
  let mut ok := true
  IO.println "vc-case\tverdict\texpected\tms\tok"
  for (name, m, j, contract, want) in Silmaril.Wasm.Auto2.VCLib3.vcBench do
    match Silmaril.Wasm.Auto2.VCLib3.entriesM3.find? (·.name == contract) with
    | none => IO.eprintln s!"{name}: no contract {contract}"; ok := false
    | some e =>
      let (got, ms) ← timed do
        let b := Silmaril.Wasm.Auto2.VCCheck.vcCheckM e m j
        pure b
      let v := if got then "\"proved\"" else "\"unknown\""
      let w := if want then "\"proved\"" else "\"unknown\""
      let good := got == want
      ok := ok && good
      IO.println s!"{name}/{contract}\t{v}\t{w}\t{ms}\t{good}"
  return if ok then 0 else 1

/-- `bench`. -/
def runBench (o : Opts) : IO UInt32 := do
  if o.vcCases then return (← runVcBench)
  let mut ok := true
  IO.println "case\tverdict\texpected\tms\tok"
  for c in Silmaril.Wasm.Auto.FrontBenchX.allCases do
    let (r, ms) ← timed <| evalReport fun _ => match c.against with
      | .module spec => Silmaril.Wasm.Auto2.Front2.checkRefinesV .eq c.impl spec 0 o.random false
      | .refFn f =>
        -- The VC stage, for the cases with a proved reference contract (same function as `f`).
        match Silmaril.Wasm.Auto2.VCLib.refEntries.lookup c.name with
        | some re => Silmaril.Wasm.Auto2.VCCheck.checkMeetsVCN .eq re c.impl 0 o.random
        | none => checkMeets .eq c.impl 0 f o.random
    let expect := if Silmaril.Wasm.Auto2.VCLib.vcProved.contains c.name then .proved else c.expect
    let v := verdictJson r.verdict
    let e := verdictJson expect
    let good := r.verdict == expect
    ok := ok && good
    IO.println s!"{c.name}\t{v}\t{e}\t{ms}\t{good}"
    if let some d := o.out then
      IO.FS.createDirAll d
      let enc := Silmaril.Wasm.Binaryen.Exe.encodeModule?
      match enc c.impl with
      | .ok bs => IO.FS.writeBinFile s!"{d}/{c.name}.impl.wasm" ⟨bs.toArray⟩
      | .error e => IO.eprintln s!"{c.name}: cannot encode: {e}"
      if let .module spec := c.against then
        match enc spec with
        | .ok bs => IO.FS.writeBinFile s!"{d}/{c.name}.spec.wasm" ⟨bs.toArray⟩
        | .error e => IO.eprintln s!"{c.name}: cannot encode: {e}"
  return if ok then 0 else 1

/-- The certificate of a `vc` verdict: the binary embedded, `vcCheck` by kernel evaluation. -/
def vcCertificate (bs : ByteArray) (contract : String) (j : Nat) : String :=
  "import Silmaril.Wasm.Auto2.VCLib3.Thms\nimport Silmaril.Wasm.Binaryen.Exe.CompactInput\n\n" ++
  "/-! Certificate written by `wasm-check vc`. -/\n\n" ++
  "open Silmaril.Wasm\n\n" ++
  "/-- The module, decoded from its binary. -/\n" ++
  "def modA : Module := match Silmaril.Wasm.Binaryen.Exe.CompactInput.prepare ⟨#" ++
    bytesLean bs ++ "⟩ with\n  | .ok m => m.source\n  | .error _ => {}\n\n" ++
  s!"theorem proved (P : Numerics.Profile) :\n    Silmaril.Wasm.Auto2.VCCheck.ModTSpecM P " ++
  s!"(Silmaril.Wasm.Auto2.VCLib3.entryM3 \"{contract}\") modA {j} :=\n" ++
  "  Silmaril.Wasm.Auto2.VCCheck.modTSpecM_of_vcCheckM (by decide +kernel)\n"

/-- `vc`: an export against a contract of the VC library. -/
def runVc (pa exp contract : String) (o : Opts) : IO UInt32 := do
  let ba ← IO.FS.readBinFile pa
  let ma ← match decode ba with
    | .ok m => pure m
    | .error e => do IO.eprintln s!"wasm-check: cannot decode {pa}: {e}"; return 2
  let some j := resolveExport ma exp | do
    IO.eprintln s!"wasm-check: no function export {exp} in {pa}"; return 2
  let some e := Silmaril.Wasm.Auto2.VCLib3.entriesM3.find? (·.name == contract) | do
    let names := ", ".intercalate (Silmaril.Wasm.Auto2.VCLib3.entriesM3.map (·.name))
    IO.eprintln s!"wasm-check: no contract {contract} ({names})"; return 2
  let ((n, miss, ok), ms) ← timed do
    let n := ((Silmaril.Wasm.Auto2.VCCheck.vcCondsM? e ma j).map List.length).getD 0
    let miss := Silmaril.Wasm.Auto2.VCCheck.vcMissingM e ma j
    let ok := Silmaril.Wasm.Auto2.VCCheck.vcCheckM e ma j
    -- Force the values (timing).
    let _ := toString n ++ toString miss ++ toString ok
    pure (n, miss, ok)
  let missJson := match miss with
    | some k => toString k
    | none => "null"
  let verdict := if ok then "proved" else "unknown"
  IO.println ("{\"check\":\"vc\",\"export\":" ++ toString j ++ ",\"contract\":\"" ++ contract ++
    "\",\"conditions\":" ++ toString n ++ ",\"missing\":" ++ missJson ++ ",\"verdict\":\"" ++
    verdict ++ "\",\"ms\":" ++ toString ms ++ "}")
  if ok then
    if let some f := o.lean then IO.FS.writeFile f (vcCertificate ba contract j)
  return 0

/-- `vc-emit`: the binaries of the VC library's demonstration modules. -/
def runVcEmit (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  let mut rc : UInt32 := 0
  for (n, m) in Silmaril.Wasm.Auto2.VCLib2.demoModules ++ Silmaril.Wasm.Auto2.VCLib3.demoModules3 ++
      Silmaril.Wasm.Auto2.VCLib3.demoModules3G do
    match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
    | .ok bs =>
      IO.FS.writeBinFile s!"{dir}/{n}.wasm" ⟨bs.toArray⟩
      IO.println s!"{dir}/{n}.wasm"
    | .error e => IO.eprintln s!"{n}: cannot encode: {e}"; rc := 1
  return rc

/-- The command line. -/
def run (args : List String) : IO UInt32 := do
  try
    match args with
    | ["vc-emit", dir] => runVcEmit dir
    | "vc" :: pa :: exp :: contract :: rest =>
      match parseOpts rest {} with
      | .ok o => runVc pa exp contract o
      | .error e => IO.eprintln s!"wasm-check: {e}\n{usage}"; return 2
    | "bench" :: rest =>
      match parseOpts rest {} with
      | .ok o => runBench o
      | .error e => IO.eprintln s!"wasm-check: {e}\n{usage}"; return 2
    | kind :: pa :: pb :: exp :: rest =>
      if kind == "pass" then
        match parseOpts (exp :: rest) {} with
        | .ok o => return (← runPass pa pb o)
        | .error e => IO.eprintln s!"wasm-check: {e}\n{usage}"; return 2
      if kind != "refines" && kind != "equiv" then
        IO.eprintln usage; return 2
      match parseOpts rest {} with
      | .ok o => runPair kind pa pb exp o
      | .error e => IO.eprintln s!"wasm-check: {e}\n{usage}"; return 2
    | "pass" :: pa :: pb :: rest =>
      match parseOpts rest {} with
      | .ok o => runPass pa pb o
      | .error e => IO.eprintln s!"wasm-check: {e}\n{usage}"; return 2
    | _ => IO.eprintln usage; return 2
  catch e =>
    IO.eprintln s!"wasm-check: {e}"
    return 2

end Silmaril.Wasm.Auto.Front.Cli

/-- The `wasm-check` entry point. -/
def main (args : List String) : IO UInt32 :=
  Silmaril.Wasm.Auto.Front.Cli.run args
