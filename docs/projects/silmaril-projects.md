# Silmaril projects

A silmaril project separates *that* something is formalized (a problem about a value read from
a file) from *how* it is formalized (formats, specs, models, proofs). It declares its
**artifacts** (files, by content hash), the **values** read from them under **formats**, the
**problems** about them, their **answers** (proofs) and the **DAG** that groups the problems.
`sil project` checks all of it, writes one canonical SQLite database and a static page that
explores it.

| Piece | Where |
| --- | --- |
| Lean framework: records, the `silmaril` command, values and formats, the attribute forms | `Silmaril.Project.Defs` (`Silmaril/Project/`) |
| Format adapters over silmaril's parsers (S-expressions, Wasm, WAT, ELF, JSON) | `Silmaril.Project.Formats.Defs`, laws in `….Thms` |
| Standard shapes: formats and values, ELF executables, x86-64 functions, command-line programs | `Silmaril.Project.Shapes.{Format,Elf,X86,Cli}.Defs`, lemmas in `….Thms` |
| The CLI `sil project` (Rust) | `tools/silmaril-project/` |
| The records-file JSON Schema | [`docs/schemas/silmaril-records.v0.2.schema.json`](../schemas/silmaril-records.v0.2.schema.json) |
| The explorer page | [silmaril-projects-explore.md](silmaril-projects-explore.md) |
| The end-to-end self-test | `examples/project/` (`make project-check`) |

The format is young (`v0.1`/`v0.2` schemas) and will change.

## Quick start

1. **Install `sil project`.** In a silmaril-lean checkout, `make project-tool` builds the Rust CLI
   and stages `build/bin/sil` and `build/bin/silmaril-project` (the same program under its
   standalone name); put `build/bin` on your `PATH`. `cargo install --locked --path
   tools/silmaril-project` installs `silmaril-project` alone.
2. **Make a Lake package that requires silmaril.** Copy silmaril-lean's `lean-toolchain`. The
   first build also builds silmaril's dependencies, Mathlib among them, which takes long.
   `lakefile.toml`:
   ```toml
   name = "hello"
   defaultTargets = ["Hello"]

   [[require]]
   name = "silmaril"
   git = "https://github.com/hiloopai/silmaril-lean.git"
   rev = "<a silmaril-lean commit, 40 hex digits>"

   [[lean_lib]]
   name = "Hello"
   needs = ["records", "data"]       # rebuild Hello when a records or data file changes

   [[input_dir]]
   name = "records"
   path = "silmaril"
   filter = { extension = ["toml"] }
   text = true

   [[input_dir]]
   name = "data"
   path = "data"
   ```
3. **Two data files.** `data/greeting.txt` is `hello, world` (13 bytes with the newline), and
   `data/config.sexp` is `(port 8080)`.
4. **Start the project and register the files:**
   ```
   $ sil project init
   wrote silmaril.toml (sid 6e6b27ed26920a0205f6c77488dbc29152de648ed61fcd1df1a667a5581ba107)
   wrote silmaril/artifacts.toml (no artifacts yet: `sil project artifacts add PATH`)
   wrote silmaril/records.toml (a commented example; `silmaril load "silmaril/records.toml"` reads it)
   $ sil project artifacts add data/greeting.txt --name hello.blobs.greeting
   hello.blobs.greeting: (none) -> bafkr4idchjkgbwcbw3i4cpiib2cvadqaip6uxjfixkobvknu63qneerhnq
   wrote silmaril/artifacts.toml (1 artifacts)
   $ sil project artifacts add data/config.sexp --name hello.blobs.config
   hello.blobs.config: (none) -> bafkr4iawijwsks43axipou6slowpwzdqiffbuwzooxvqjwxjymgw4qkbjq
   wrote silmaril/artifacts.toml (2 artifacts)
   ```
5. **Records and statements.** Replace `silmaril/records.toml` (the values):
   ```toml
   schema = "silmaril.records.v0.2"

   [[value]]
   name = "hello.greeting"
   format = "bytes"
   source = "data/greeting.txt"    # a registry path, a CID or a registry name

   [[value]]
   name = "hello.config"
   format = "sexp"                 # a family: read through its default, sexp.text
   source = "hello.blobs.config"
   ```
   `silmaril/dag.toml` (an instance, the root group):
   ```toml
   schema = "silmaril.records.v0.2"
   root = "hello.all"

   [[instance]]
   name = "hello.small.five"
   of = "hello.small"
   args = { n = 5 }
   expect = "CSA"

   [[group]]
   name = "hello.all"
   title = "Check the hello project"
   children = ["hello.greeting.short", "hello.config.pair", "hello.small", "hello.small.five"]
   ```
   `Hello.lean` (the statements and proofs):
   ```lean
   import Silmaril.Project.Defs
   import Silmaril.Project.Formats.Defs             -- the format adapters: sexp, wasm, wat, elf

   open Silmaril.Formats

   silmaril artifacts "silmaril/artifacts.toml"
   silmaril load "silmaril/records.toml"            -- values first: statements are about them

   /-- The number of items of a list (`none` for an atom). -/
   def items? : SExp String → Option Nat
     | .list n _ => some n
     | .atom _ => none

   silmaril problem hello.greeting.short about hello.greeting : fun b => b.length < 16
     := by silmaril_decide
   silmaril problem hello.config.pair about hello.config : fun s => items? s = some 2
     := by silmaril_decide

   @[problem "hello.small" (title := "Small numbers")] def small (n : Nat) : Prop := n < 3
   @[answers "hello.small" sat] theorem small_sat : ∃ n, small n := ⟨0, by unfold small; decide⟩
   @[answers "hello.small" csa] theorem small_csa : ∃ n, ¬ small n := ⟨3, by unfold small; decide⟩

   silmaril load "silmaril/dag.toml"                -- then the structure over the statements

   @[answers "hello.small.five" uns] theorem small_five : ¬ hello.small.five := by
     show ¬ 5 < 3; decide
   ```
6. **Check, dump, explore:**
   ```
   $ sil project lint                   # the records files and the registry, without Lean
   ok: 2 records file(s), 4 table(s); silmaril/artifacts.toml: 2 artifact(s), locked
   $ sil project dump                   # lake build --wfail Hello, then #silmaril_dump
   building Hello with `lake build --wfail Hello` (the first build of the dependencies can take long; `--no-build` skips this step)…
   elaborating the dump driver (`#silmaril_dump`)…
   wrote .lake/silmaril/dump.json (34 records, 5 problems, 5 solutions)
   $ sil project check                  # registries, records vs dump, DAG, statuses
   summary: 6 problems (6 local), 1 groups, 20 records, 9 edges, 2 artifacts
   verdicts: 4 holds, 2 fails, 0 unknown (all 6 problems); 4 holds, 2 fails, 0 unknown (6 local)
   root: hello.all
   predicate hello.small (arity 1): status contingent [CSA SAT], verdict fails
   group hello.all: [hello.greeting.short=THM, hello.config.pair=THM, hello.small=contingent, hello.small.five=UNS]
   sql sha256: 03bd8f95b3114bd6e276e928d12939c1553fadf4ad2b250f7695a08e23d0ce25
   $ sil project sqlite && sil project explore   # .lake/silmaril/{project.sqlite,explore.html}
   ```
   The sid, and so the `sql sha256`, differ in your project: `init` draws a random sid.

A **status** is what is proved (SZS: THM, SAT, UNS, CSA, `contingent` for SAT and CSA, OPN);
a **verdict** is whether the problem holds. `hello.small` (`∀ n, n < 3`) is SAT and CSA, so it
fails. The six problems include the obligations `hello.greeting.parses` and
`hello.config.parses`. If a proof fails, `dump` prints Lean's messages; with `b.length < 8` in
`hello.greeting.short`:

```
✖ [2143/2145] Building Hello (1.1s)
error: Hello.lean:15:8: silmaril_decide: the property is false on this artifact
  problem: `hello.greeting.short`
  value: `hello.greeting` (`data/greeting.txt`, read as `bytes`)
  property:
  fun b => b.length < 8
The artifact does not parse, or its value does not satisfy the property.
The kernel evaluated the goal to `false`, so no proof exists: fix the artifact or the statement, or refute the problem.
Error:   × `lake build --wfail Hello` failed (its messages are above)
```

`examples/project/ProjectSelfTest.lean` with `silmaril/selftest.toml` is a larger example: one
construct per layer, and values read as Wasm and ELF.

## What a project is

1. a **Lean project on Git** (a Lake package),
2. a **`silmaril.toml`** with a project sid, and an artifact registry `silmaril/artifacts.toml`,
3. **records**: the project's structure (values, judgements, instances, groups, …) in TOML
   files under `silmaril/`, which Lean reads with `silmaril load`,
4. **Lean modules** with the definitions, the statements and the proofs.

The rule: **data goes in TOML, terms go in Lean.** A record whose fields are names, titles,
references to constants or small argument tuples is TOML; anything with binders, notation, a
tactic or a proof is Lean. Every TOML table is the same record as a `silmaril <kind> …` Lean
command (both give identical records), but TOML is the default: tools read it without Lean, and
one schema describes it.

A Lake package without a `silmaril.toml` and without records (Mathlib, for example) is a valid
project that declares nothing. silmaril-lean is itself a project: its `silmaril.toml` gives the
records of `Silmaril.Project` (the artifact type `blob`, the formats, the shapes) their sid when
another project imports them.

## Words

| Word | Meaning | Written as |
|---|---|---|
| blob | bytes, identified by their CID; a path is only where the blob was found | `blob : ArtifactType` |
| artifact | a blob in the registry `silmaril/artifacts.toml`, keyed by CID | `[[artifact]]` |
| derivation | how artifacts are built: a recipe, its inputs, the toolchain, a receipt | `[[derivation]]` |
| format | a named parser `Bytes → Option V`, with an optional printer | `Format blob V`, `[[format]]` |
| family | a format name prefix with a default, e.g. `sexp` → `sexp.text` | `[[format_default]]` |
| value | a **named** artifact read under a format; problems are about values | `[[value]]`, Lean: `@[value "n" …]` on a certificate |
| model, spec | a semantics (a class of models), and a predicate on a value type | `[[model]]`, `[[spec]]` |
| problem | a named `P : α₀ → … → αₙ₋₁ → Prop`; arity 0 is a closed `Prop` | Lean: `@[problem "n" (k := v)*]`, `silmaril problem` |
| answer | a theorem establishing one SZS status of a problem (THM, SAT, UNS, CSA) | Lean: `@[answers "n" thm]` |
| instance | a problem obtained by fixing arguments of another | `[[instance]]` |
| room | sentences, models and satisfaction; a sentence is a predicate over models | `[[room]]`, Lean: `silmaril problem … in` |
| group | a DAG node whose result is the vector of its children's verdicts | `[[group]]` |
| sid | a 256-bit silmaril identifier, written as 64 lowercase hex digits | `sid = "…"` |

## Records files

```toml
schema = "silmaril.records.v0.2"
root = "demo.all"                   # optional: the project's root group

[defaults.judgement]                # optional: keys every [[judgement]] below gets unless it sets them
model = "demo.models.reader"
spec = "demo.specs.greets"

[[judgement]]                       # = silmaril judgement demo.greets (expect := "THM") (title := "…")
name = "demo.greets"
expect = "THM"
title = "The demo greets the world"
```

`silmaril load "PATH"` reads one file, or every `*.toml` below a directory (sorted by path,
skipping the artifact registry). The path is relative to the package root (the directory of
`lakefile.toml`, also when a library has a `srcDir`). Within one load, the tables run **kind by
kind** in the order below, then project-defined kinds, then `root`, so a group may come before
its children in the file. Lean statements can only use what was loaded before them: load values
first and the DAG after the statements, as in the quick start.

| kind | keys (**required**) | Lean checks and fills |
|---|---|---|
| `artifact_type` | **name**, **decl**, doc, sid | `decl : ArtifactType` |
| `format` | **name**, **decl**, base, doc, sid | `decl : Format T V`; fills `input`, `value_type`, `printer` |
| `format_default` | **name** (the family), **format**, sid | the format is `<family>.…` |
| `format_law` | name, **format**, **law** (`roundtrip`, `sound`), **proof**, rel | the proof's type |
| `value` | **name**, **format**, **source**, sources = `[{format, source}]`, doc, sid | reads the bytes; defines `N`, `N.parses`, `N.agrees.k` |
| `model`, `spec` | **name**, **decl**, doc, sid; a spec also model, format | |
| `room` | **name**, **decl**, doc, sid | `decl : Room`; fills `sen`, `mod` |
| `instance` | **name**, **of**, **args**, and the judgement keys | defines the instance and its edge |
| `tasks` | **module**, **prefix**, and the judgement keys except `expect` | every `Task.x : Prop` of the module as the open problem `prefix.x` |
| `judgement` | **name**, model, spec, values, artifacts, expect, title, doc, sid | the problem exists, the values are registered |
| `detached` | **name**, reason | |
| `decomposition`, `refutation_route` | name, and exactly one of proof, module | the theorem is `c₁ → … → p` / `¬c → ¬p` |
| `group` | **name**, children, title, doc, sid | |
| `children` | **name**, **children** | |

Lean resolves three spellings; every other key is the record field as written:

- `decl`, `proof` and `rel` name **Lean constants**, resolved like identifiers in a command
  (the current namespace and `open`s apply); `module` names an imported module.
- A value's `source` is a CID (`bafkr…`), a registry path, or a registry name.
- An instance's `args` fix arguments by binder name or by 0-based position
  (`args = { n = 5 }`, `args = { 1 = 0 }`). An argument is a name (a constant, or a registered
  value, which makes the instance `X.Satisfies (fun v => …)`), an integer, a boolean,
  `{ str = "…" }` or an application `["Nat.succ", 2]`. A term with binders or notation is a
  Lean definition (then named), or a Lean `silmaril instance` command.

Every kind also takes **`meta`**, a table of tool-only data: where the record was converted from,
notes, measurements. Lean skips it (it is not a record field and is not in the dump), lint only
checks that it is a table, and `sil project check` does not compare it. Artifact entries and
derivations in the registry take a `meta` table in the same sense.

**The schema** lives once, in `tools/silmaril-project/src/project/schema/records.rs` (kinds,
keys, types and docs). `sil project lint` checks files against it, `sil project schema` prints it
as JSON Schema (committed as
[silmaril-records.v0.2.schema.json](../schemas/silmaril-records.v0.2.schema.json), for editors),
and Lean's reader mirrors only the kind order (a Rust test compares the two). A project-defined
kind, with its own Lean `@[silmaril_kind k]` handler, is listed in `silmaril.toml` as
`kinds = ["segment"]`; lint does not check its tables.

**Errors** point at the TOML. Lean reports them on the `silmaril load` line as
`silmaril/dag.toml:12:1: silmaril judgement: no problem "demo.x" is declared or imported` (a
bad constant points at its value, `…:5:8:`), and the other tables still run. `sil project lint`
reports unknown kinds and keys (with `did you mean` hints), bad types, missing required keys and
duplicate names, with `path:line:col`, before any build.

**Rebuilds.** Lake does not see the files a module reads: the records files, the registry and
every artifact a value reads. Declare them as an `[[input_dir]]` or `[[input_file]]` in the
`needs` of the library whose modules load them, as in the quick start. Filter the records
directory to the TOML files, so that reports written next to the records do not rebuild the
project. Lake mixes a library's `needs` into the trace of **every** module of that library, and
if two libraries' globs match a module, one library's `needs` are silently ignored. So give the
modules that read files a library of their own, and keep statements and proofs that read no
file in another: editing a title or a doc then rebuilds only the loading modules (silmaril-lean
does this with its `ProjectSelfTest` library). `sil project check` still catches a stale build:
every named record of every records file must be in the dump with the same `title`, `doc`,
`expect`, `reason` and `children` (rule R11), which also catches a file nobody loads, and it
warns about a file Lean reads that Lake does not track (W2).

## Values

A `[[value]]` (or the command `silmaril value N : F := src (| F' := src')*`) generates:

- `N : Value V`, where `V` is the value type of format `F`;
- the problem `N.parses` (*the bytes parse*), an explicit obligation, never an assumption;
- for each extra source: a value `N.alt.k` and the problem `N.agrees.k` (both denote the same
  value).

The source must be in the package's registry; Lean reads the bytes with `include_bytes` and
checks the size. Statements talk about a value through `N.Parses`, `N.Satisfies P`
(∃ v, the parse is `some v` and `P v`), `N.Is v` (a certificate) and `N.Agrees M`.

A **certificate** is a Lean declaration, so it takes the attribute form: `@[value]` on what the
file parses to declares the value (exactly as `[[value]]`) plus the problem `N.is` (`N.Is c`)
and the proved edge `N.is → N.parses`:

```lean
@[value "demo.hello" (format := bytes) (source := "data/hello.txt")]
def hello : Silmaril.Formats.Bytes := ⟨⟨#[0x68, 0x69, 0x0a]⟩⟩
@[solves "demo.hello.is"] theorem hello_is : demo.hello.is := by silmaril_decide
```

State facts about `c` and move them to the value with `Value.satisfies_of_is`, or both ways
with `Value.Is.satisfies_iff` (`x.Is c → (x.Satisfies P ↔ P c)`); `Value.Satisfies.mono`
weakens the property. A value without a certificate stays a `[[value]]` table.

`silmaril problem N about X : P := proof` states the problem `X.Satisfies P` and adds the proved
route `¬ X.parses → ¬ N`, the edges to `X`'s obligations and, with a proof, the solutions of `N`
and of `X.parses`. Leave out `:= proof` for an open problem.

`silmaril_decide` closes such a goal (and a certificate `N.is`) with one kernel evaluation of the
parser, as a `Bool`. It is cheap only on small files: in the kernel, `Array`, `ByteArray` and
`String` are lists and only `Nat` arithmetic is accelerated. The examples in
`examples/project-formats/` (a 632-byte ELF executable, small Wasm, WAT and S-expression files)
take seconds. For a big file, prove `N.Is v` once and use `Value.satisfies_of_is`. Compiled
evaluation (`#eval`) is not a kernel fact.

## Problems over arguments, answers and rooms

Where a Lean declaration exists, its record is an **attribute** on it: `@[problem]` on the
statement, `@[answers]` on the proof. The fields `(key := value)` are the problem's judgement
(`expect`, `title`, `doc`, `model`, `spec`, `values`, `artifacts`, `sid`), the same keys as a
`[[judgement]]` table; `(expect := thm)` may be an identifier.

```lean
/-- Addition is commutative. -/
@[problem "demo.add.comm" (expect := thm) (title := "Addition commutes")]
def addComm (a b : Nat) : Prop := a + b = b + a                      -- any arity
@[answers "demo.add.comm" thm]
theorem addComm_thm : ∀ a b, addComm a b := Nat.add_comm
-- thm: ∀ x⃗, P x⃗   sat: ∃ x⃗, P x⃗   uns: ∀ x⃗, ¬ P x⃗   csa: ∃ x⃗, ¬ P x⃗  (arity 0: @[solves]/@[refutes])

@[problem "demo.logic.p" (room := demo.rooms.prop)] def p : Formula := …   -- a sentence of a room
@[conjecture "demo.small_bound" (title := "…")]                       -- = (expect := OPN)
def smallBound : Prop := ∀ n, small n → n ≤ 2
```

Without a declaration, the command forms define one:

```lean
silmaril problem demo.even := Demo.even                              -- an existing definition
silmaril problem demo.square (title := "Squares") := fun n : Nat => ∃ k, k * k = n   -- a term
silmaril conjecture demo.small_bound (title := "…") : ∀ n, small n → n ≤ 2   -- def Task.demo.small_bound, OPN
silmaril problem demo.logic.q in demo.rooms.prop := …                -- a sentence of a room
```

- `@[problem "N"]` without fields on a closed `Prop` is exactly silmaril's `@[problem "N"]`
  (`Silmaril.Problems.Basic`; the project framework routes the syntax to its own handler, which
  calls silmaril's at arity 0), so code written for `Silmaril.Problems` keeps working. At arity
  `n > 0` it adds a `predicate` record. `@[predicate "N"]` is the older spelling; it also adds a
  `predicate` record at arity 0.
- Instance arguments: a registered value given for a binder of type `Value V` is the value; for
  a binder of type `V`, the instance is `X.Satisfies (fun v => …)`. Implicit binders that the
  other arguments determine are inferred.
- Every binder is an argument at its position, named unless Lean made it inaccessible. Answers
  quantify over all of them, and a literal `⟨w₀, …, h⟩` proof records its witnesses.
- Statuses move along instance edges: THM and UNS down to the instance, SAT and CSA up. A solved
  closed instance is SAT of the general problem, a refuted one CSA.
- A **room** is silmaril's `Silmaril.Logic.Institution.Room` (sentences, a category of models,
  satisfaction). `silmaril room R := decl` registers one; a sentence `φ` of `R` is the problem
  `fun M => Silmaril.Project.Room.Problem R φ M`, so THM is validity, SAT satisfiability, UNS
  unsatisfiability and CSA a countermodel (`Silmaril.Project.Room.Thms`).
- Fields before `:=` (`title`, `expect`, `doc`, `sid`) become the problem's judgement.

## Formats

```lean
silmaril format sexp.text := Silmaril.Project.Formats.sexp (doc := "UTF-8 Lisp-style S-expressions …")
silmaril format_default sexp := sexp.text
silmaril format_law wasm.binary.core sound := Silmaril.Project.Formats.wasm_sound
  (rel := Silmaril.Project.Formats.WasmRel)
```

A format is `def myFormat : Format blob MyAst` (a `parse` and optionally a `print`), registered
next to its definition. Format names are global across the imported projects: a project may add
names but not redefine imported ones. `import Silmaril.Project.Defs` registers `bytes`;
`import Silmaril.Project.Formats.Defs` registers the adapters below, thin wrappers over
silmaril's parsers. Their laws and examples are in `Silmaril.Project.Formats.Thms`, over the
files in `examples/project-formats/` (`build.sh` rebuilds the ELF files bit for bit and checks
them against `RECEIPTS.sha256`):

| name (family default in bold) | value | printer | law |
|---|---|---|---|
| `bytes` | the bytes (identity) | yes | `roundtrip` |
| **`sexp.text`**, `sexp.canonical` | S-expressions (UTF-8 Lisp style; Rivest canonical) | yes | `roundtrip` |
| `sexp.wat` | WAT lexed to an S-expression document (Core 3.0 profile) | no | `sound` |
| **`wat.sexp`** | WAT to the Core 3.0 module AST, supported fragment | yes | `sound` |
| **`wasm.binary.core`** | Core 3.0 module AST | yes | `sound` |
| **`elf.elf64le`** | ELF64 relocatable objects | no | none |
| `elf.exec-x86` | x86-64 fixed-address executables, to checked load records | no | `sound` |
| **`json.rfc8259`** | RFC 8259 JSON to the ordered wire AST (`Silmaril.Formats.JsonWire`): UTF-16 strings, members in order with duplicates, exact decimals | yes | none |

Known gaps: shared libraries fit neither ELF format; `json.rfc8259` has no law (no round-trip
theorem for its printer, no proof against an independent grammar); `wat.sexp` covers the supported fragment;
`wasm.binary.core` has no `roundtrip` law (the printer is sound and printing then parsing can
only return the printed module, `wasm_print_parse`). `example.wat` and `example.wasm` are
equivalent conditional on a re-encoding fact checked by evaluation (`ExampleWatEncodes`), since
the kernel does not reduce the encoder.

## Standard problem shapes

Do not restate a standard fact as a problem of your own: silmaril registers each kind of fact
once, as a **shape** (an open problem over arguments), and a project fills in a **row**, an
instance for its own artifact, and proves it. Every project then states the same fact the same
way, the shape collects SAT evidence from every solved row, and the transfer lemmas prove the
rows. The shapes are `Silmaril.Project.Shapes.{Format,Elf,X86,Cli}.Defs` (lemmas in `….Thms`).
An indented name is a named instance of the shape above it, with some arguments fixed:

| shape | Lean (`Silmaril.Project.Shapes.…`) | statement | transfer lemmas |
|---|---|---|---|
| `silmaril.shapes.format.parses` | `Parses {V} (F : Format blob V) (b : Bytes)` | `b` parses under `F` | `parses_iff` |
| `silmaril.shapes.format.agree` | `Agree {V} (F G : Format blob V) (a b : Bytes)` | `a` under `F` and `b` under `G` are one value of the data model `V` | `agree_iff` |
| `silmaril.shapes.value.satisfies` | `Satisfies {V} (X : Value V) (P : V → Prop)` | `X` parses to a `v` with `P v` | `satisfies_iff`, `Satisfies.parses` |
| `silmaril.shapes.elf.loads` | `Loads (L : Loader) {V} (exe : Value V) (perms : String) (addr : Nat) (code : List (BitVec 8))` | the loader `L` accepts `exe`, and a segment with permissions `perms` holds exactly `code` at `addr` | `loads_x86_iff`, `Loads.x86_of_check`, `Loads.x86_of_blob` |
| &nbsp;&nbsp;`….loads.x86` | `L := Loader.x86` | the same with the LPS x86-64 loader of `elf.exec-x86` | |
| `silmaril.shapes.elf.entry` | `Entry (L : Loader) {V} (exe : Value V) (addr : Nat)` | `L` accepts `exe` and its entry point is `addr` | `Entry.x86_of_blob`, `Entry.x86_of_satisfies` |
| &nbsp;&nbsp;`….entry.x86` | `L := Loader.x86` | | |
| `silmaril.shapes.elf.fn_contract` | `ElfFn (L : Loader) (M : Model) {V} (exe : Value V) (addr : Nat) (code : List Byte) (S : FnContract.Spec MState)` | `exe` loads `code` at `addr` (`rx`); `S` is tied to those bytes and that `rip` range: every entry state of `S` has `code` at `addr` and `rip` in `[addr, addr + code.length)` (`EntersCode`), though `S.entry` may assume more memory than the ELF provides (data, stack, other code); some System V entry state meets `S.entry` (`Nonvacuous`), and `S` holds on `M` | `ElfFn.of_segment`, `AbiFn.elfFn`, `ElfFn.x86_of_blob`, `ElfFn.of_leafSpec`, `ElfFn.not_vacuous` |
| &nbsp;&nbsp;`….fn_contract.x86_open`, `.x86_open9` | `L := Loader.x86`, `M := Open.isa` / `Open9.isa` | | |
| `silmaril.shapes.x86.contract` | `Contract (M : Model) (S : FnContract.Spec MState)` | `S` is totally correct on `M` (`S.Total M`); names no code | `Contract.open9_of_open`, `Contract.str9_of_open9` |
| &nbsp;&nbsp;`….contract.open`, `.open9`, `.str9` | `M := Open.isa` / `Open9.isa` / `Str9.isa` | | |
| `silmaril.shapes.x86.contract_strict` | `ContractStrict (M : Model) (S : FnContract.Spec MState)` | first-return total correctness (`S.Strict M`) | `ContractStrict.contract` |
| `silmaril.shapes.x86.abi_function` | `AbiFn (M : Model) (p : Placement) (S : FnContract.Spec MState)` | every entry state of `S` has the region of `p` loaded and `rip` at the function (`EntersAt`), `S` is not vacuous, and `S` holds on `M` | `AbiFn.of_spec`, `AbiFn.open9_of_open`, `AbiFn.str9_of_open9`, `AbiFn.not_vacuous` |
| &nbsp;&nbsp;`….abi_function.open`, `.open9`, `.str9` | `M := Open.isa` / `Open9.isa` / `Str9.isa` | | |
| `silmaril.shapes.x86.correct` | `Correct (𝓜 : Problems.Class MState) (S : Word → FnContract.Spec MState)` | for every placement `entry`, `S entry` is demonically totally correct on every member of `𝓜` (`Problems.FnCorrect`) | `correct_iff` |
| `silmaril.shapes.x86.correct_loose` | `CorrectLoose (D : Loose.DTable Loose.Listing.LForm) (S : Word → FnContract.Spec MState)` | the same on the down-set of the loose x86-64 top over the listing table `D` | `correctLoose_iff` |
| `silmaril.shapes.cli.help` | `Help (M : Silmaril.Cli.Institution.Model Level.full.sig) (v : HelpVariant)` | the CLI model `M` answers help requests as the variant `v` says (spellings, subcommand paths, extra arguments, exit code, stream, substrings; nothing else happens) | `Help.of_sat`, `Help.ofCommand`, `Help.mono`, `help_via_iff` |
| &nbsp;&nbsp;`….help.{basic,short,loose,wins,either}` | `v :=` a named variant | | |
| `silmaril.shapes.cli.help.subcommands` | `HelpSubcommands M (ps : List (List String))` | `--help` and `-h` at the root and after each path in `ps` | |
| `silmaril.shapes.cli.version` | `Version M (v : VersionVariant)` | `M` answers version requests as `v` says | `Version.of_sat`, `Version.ofCommand`, `Version.mono`, `version_via_iff` |
| &nbsp;&nbsp;`….version.{basic,short}` | `v :=` a named variant | | |
| `silmaril.shapes.cli.version.pinned` | `VersionPinned M (ver : String)` | `--version` prints a text containing `ver` | |

`Contract M S` alone is filled by a spec no state enters. A row about a *function* uses
`elf.fn_contract` or `x86.abi_function`, which add that the spec is entered at the code
(`EntersCode`, `EntersAt`) and is not vacuous; `ElfFn.not_vacuous` checks that the vacuous spec
`vacuousSpec` fills neither, while it fills the weak form `ElfFnWeak` (`Loads ∧ Contract`,
not a shape). An executable's bytes are certified as a `Blob` literal by
`blob_of_decode rfl (by decide +kernel)` (or `rfl` for the right-hand side computed from the
chunks), so the kernel reads the file as one number instead of byte by byte; the example rows
`exampleExec_entry` and `exampleExec_code` (`Silmaril.Project.Shapes.Elf.Thms`) do this for
`examples/project-formats/example-exec.elf`, and `ilog2_abi` (`….X86.Thms`) is a row of
`abi_function.open9`.

A row, from the self-test (`silmaril/selftest.toml`):

```toml
[[instance]]
name = "silmaril.selftest.hello.six_row"
of = "silmaril.shapes.value.satisfies"
args = { X = "silmaril.selftest.hello_toml", P = "ProjectSelfTest.sixBytes" }
```

```lean
abbrev sixBytes (b : Silmaril.Formats.Bytes) : Prop := b.length = 6   -- an abbrev: see below
@[answers "silmaril.selftest.hello.six_row" thm] public theorem hello_six_row :
    silmaril.selftest.hello.six_row := by
  silmaril_decide
```

The arguments of a row are Lean terms, or registered values: a value given for a `Value V`
binder is the value itself, and for a binder of its value type `V` the row becomes
`X.Satisfies (fun v => …)`. Implicit type arguments are inferred from the others. A predicate
passed as an argument must be reducible (an `abbrev`) for `silmaril_decide` to find its
`DecidablePred` instance. To add a shape: a `@[problem "silmaril.shapes.<family>.<name>"
(title := …)]` definition (no `expect`) with a docstring, its transfer lemmas in `Thms`, and a
line in this table.

## Artifacts and provenance: `silmaril/artifacts.toml`

There is one registry per package, the single source of truth for blobs, keyed by CID (a DASL
CIDv1, raw codec, BLAKE3-256, base32 `bafkr4i…`; SHA-256 and the Git blob SHA-1 are aliases).
Add a file with `sil project artifacts add PATH [--name N]`, or edit `paths` and `name` and run
`sil project lock`. `lock` fills `cid`, `size`, `sha256`, `git_sha1` and the CIDs of the files
derivations name, merges entries with one CID and sorts them. Lean imports the registry with
`silmaril artifacts "silmaril/artifacts.toml"`. Put the registry, and every directory whose
blobs `silmaril value` reads, in the `needs` of the library of the modules that read them (see
**Rebuilds** above); then Lake rebuilds them after `lock`. Rule R3 flags a stale copy.

Since `silmaril.artifacts.v0.2` an artifact can say how it is built. From silmaril-lean's own
registry:

```toml
[[artifact]]
name = "silmaril.selftest.exec_elf"
paths = ["examples/project-formats/example-exec.elf"]
derivation = "silmaril.selftest.build.exec_elf"
# cid, size, sha256, git_sha1 written by lock

[[derivation]]
name = "silmaril.selftest.build.exec_elf"
op = "link"                 # compile | link | patch | instrument | lift | segment | generate | fetch | revision-of
status = "reproduced"       # pinned | reproduced (rebuilt bit for bit, with a receipt) | generated
recipe = { path = "examples/project-formats/build.sh", cid = "bafkr4i…" }
toolchain = [{ name = "gcc", version = "13.3.0 (Ubuntu 13.3.0-6ubuntu2~24.04.1)" }, { name = "binutils", version = "2.42" }]
flags = ["-O1", "-static", "-nostdlib", "…"]
environment = { os = "ubuntu-24.04", arch = "x86_64" }
receipt = { path = "examples/project-formats/RECEIPTS.sha256", cid = "bafkr4i…" }

[[derivation.input]]
role = "source"             # source | driver | libc | patch | recipe-input | tool
artifact = "silmaril.selftest.exec_c"
# or: path = "…" | url = "…" + sha256 = "…" | git = { repo = "…", rev = "<40 hex>" }
# an input that is not public: name, sha256 and available = "private:<owner>"
```

`sil project check` checks provenance without the network or a rebuild (rules P1–P6 in
[Reference: provenance rules](#reference-provenance-rules)). Lean ignores derivations. Running a
recipe is a later step; today `examples/project-formats/build.sh` rebuilds and checks its
outputs when run by hand.

## The DAG and statuses

- `sil project check` requires no cycle, existing children, exactly one root, and every problem
  reachable from it or `detached`.
- A **group** has no truth value; its result is its children's verdict vector. Use one when the
  children may disagree, for example one per version of a library. Use a `Prop` root with a
  decomposition when "verified" should be a theorem.
- Statuses are SZS codes (THM, SAT, CSA, UNS, OPN, UNK, and `contingent` for SAT and CSA),
  coarsened to holds (THM), fails (CSA, `contingent`, UNS of a closed problem) and unknown. The
  derived status follows Kleene's three-valued logic over the proved edges. A problem with THM
  and CSA, or UNS and SAT, is a soundness alarm (R10).
- Solutions and answers may depend only on `propext`, `Classical.choice` and `Quot.sound`
  (R5); the database lists each answer's axioms (`answer_axioms`).

## Names and sids

- Names are dotted: segments `[a-z][a-z0-9_-]*` or all digits, at most 200 bytes, with a leading
  `.` reserved (e.g. `demo.lib.v1_3_1.safety`). Legacy `/` ids of `Silmaril.Problems` are
  accepted for problems. In a Lean command, write a name with `-` or all-digit segments as a
  string (`silmaril format "elf.exec-x86" := …`).
- sids are 256-bit, written as 64 lowercase hex digits. The project sid in `silmaril.toml` is
  random (`sil project init`). An object's default sid is
  `BLAKE3.derive_key("silmaril.sid.v0", kind ‖ 0x00 ‖ project_sid ‖ 0x00 ‖ name)`; set
  `sid = "…"` to keep an identity across a rename. An artifact's sid is its BLAKE3 digest.

## `silmaril.toml`

```toml
schema = "silmaril.project.v0.1"
sid = "6e6b27ed…"                  # mandatory; `sil project init` writes a random one
name = "hello"                     # default: lakefile.toml `name`
version = "0.1.0"
description = "A small project"
modules = ["Hello"]                # modules the dump imports; default: the [[lean_lib]] names
roots = ["Hello"]                  # module prefixes that are local; default: first components of `modules`
artifacts = "silmaril/artifacts.toml"   # the default
kinds = ["segment"]                # project-defined record kinds in records files (optional)

[[import]]
package = "silmaril"               # a Lake package in lake-manifest.json; url and rev come from there
```

Projects depend on each other through Lake `require`s. An imported package that declares objects
needs its own `silmaril.toml`; silmaril-lean's is at its repository root.

## `sil project`

```
sil project init      [--dir .]
sil project artifacts add PATH [--name N] [--package P] [--dir .]
sil project lock      [--dir .]
sil project lint      [--dir .] [FILE…]
sil project dump      [--dir .] [--out .lake/silmaril/dump.json] [--lake CMD] [--no-build]
sil project check     [--dir .] [--dump .lake/silmaril/dump.json]
sil project sqlite    [--dir .] [--dump …] [--sql .lake/silmaril/project.sql] [--db .lake/silmaril/project.sqlite] [--httpvfs [--page-size 4096]]
sil project explore   [--dir .] [--db .lake/silmaril/project.sqlite] [--out .lake/silmaril/explore.html]
sil project schema    [--out FILE]
```

`sil project --help` and `sil project <command> --help` describe every argument.

- **`init`** writes `silmaril.toml` with a random sid (the name is the `lakefile.toml` name,
  else the directory's), an empty registry and a commented records file.
- **`artifacts add`** checks the path and the name, hashes the file and writes the registry
  only if all of it succeeds.
- **`lint`** checks the records files (by default every one under `silmaril/`) and the
  registry (parsed, files present, locked) without Lean, with `did you mean` hints for unknown
  kinds and keys. It warns about `children`, `of` and `root` that no records file, local `.lean`
  file (under the package root or a library's `srcDir`) or last dump declares; `check` decides.
- **`dump`** builds the modules with `lake build --wfail` and runs `#silmaril_dump`. It is the
  only subcommand that runs Lean (`--lake`, else `$SIL_LAKE`, else `lake`).
- **`check`** checks the manifest, the registries and their provenance, the records files
  (lint and R11), names, references, sids, the DAG and the statuses. It prints errors,
  warnings, a summary, the root, each group's verdict vector and the SHA-256 of the SQL text.
  Facts the tool checks (digests, sizes) are the `tool` tier, and Lean proofs the `kernel` tier.
- **`sqlite`** writes the canonical SQL text (sorted, with no timestamps or host paths, and the
  lookup indexes of `schema::INDEXES`) and builds the database from it. `--httpvfs` tunes it for
  lazy reads over HTTP ([silmaril-projects-explore.md](silmaril-projects-explore.md)).
- **`explore`** writes the static page over the database.

The generated files (`dump.json`, `project.sql`, `project.sqlite`, `explore.html`) go to
`.lake/silmaril/` by default, which the `.gitignore` of `lake new` already ignores; pass `--out`,
`--sql` or `--db` to put one where you commit it. Everything under `silmaril/` is source.

Files are named `package:path` in messages, e.g. `hello:data/config.sexp does not exist`: the
Lake package (this project's `name`, or a dependency from `lake-manifest.json`) and the path
relative to that package's root. `artifacts add --package P PATH` registers a file of a
dependency.

Every file carries its schema version: `silmaril.project.v0.1`, `silmaril.artifacts.v0.2`
(v0.1 is still read), `silmaril.records.v0.2`, `silmaril.project-dump.v0.1` and
`silmaril.project-db.v0.2` (v0.1 plus the trust tables), and
the core's trust export `silmaril.trust-core.v1` ([trust-db.md](trust-db.md)). All are defined in
`tools/silmaril-project/src/project/schema/`.

## The Lean commands

Each records kind is also a command, `silmaril <kind> [<name>] [:= <main field>] (<key> := <value>)*`,
and the two spellings give the same records:

```lean
silmaril value demo.config : sexp := "data/config.sexp"              -- [[value]]
silmaril value demo.module : wasm := "m.wasm" | wat := "m.wat"       -- two sources, one value
silmaril judgement demo.greets (spec := demo.specs.greets) (expect := "THM")
silmaril instance demo.square.n49 := demo.square (n := 49)
silmaril decomposition := Demo.main_of
silmaril tasks (module := Demo.Open) (prefix := demo.tasks)
silmaril group demo.all (title := "Verify the demo") (children := [demo.main, demo.values])
silmaril root demo.all
```

Use them for a one-off record next to a definition (silmaril's formats do this), or where a
field is a term (`silmaril instance … (M := ⟨fun _ => true⟩)`). `#silmaril` prints the records
of a kind (`#silmaril format`), and `#silmaril_dump "PATH"` writes the dump that `sil project
dump` drives.

## Tests

- `tools/silmaril-project/tests/project/<case>/` holds golden cases (`dump.json` written by hand,
  expected `check.txt` and `project.sql`); `provenance-records` exercises P1–P5, lint and R11.
  After a format change, run `tools/silmaril-project/tests/project/regen.sh` and review
  `git diff`. `cargo test` in `tools/silmaril-project` runs them with the unit tests.
- `examples/project/selftest.sh` (`make project-check`) runs `init` (in a scratch directory),
  then `lock`, `lint`, `dump`, `check`, `sqlite` and `explore` on silmaril-lean's own project,
  and compares the check with `examples/project/check.txt` (`SIL_BLESS=1` rewrites it).
- `make project-lean` (`make check` builds the same modules) builds the framework, the format adapters and
  shapes, and the self-test module with `--wfail`.

## Reference: provenance rules

`sil project check` checks the derivations of the registry without the network or a rebuild:

- P1: the files exist and match their CIDs;
- P2: the names resolve;
- P3: each input has one locator, a URL has its `sha256` and a git input a full commit;
- P4: a `reproduced` derivation's receipt lists every output's sha256;
- P5: no derivation is its own input;
- P6: it prints how many artifacts have a derivation.
