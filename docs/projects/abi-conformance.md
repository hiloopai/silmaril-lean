# ABI conformance as a standard problem

A **conformance** row says that machine code, run on a stated x86-64 *machine model* `M`,
behaves as a conforming callee when it is called the way a versioned ABI requires for the
prototype a C header declares:

- it never gets stuck;
- it returns as the ABI requires, with a result the ABI reads back and a C-level spec allows;
- it writes only the memory it may;
- it keeps the thread pointer;
- in total mode, it returns.

The statement is `Silmaril.Machine.Abi.Conformance.Conforms`. The standard problems are:

- `silmaril.shapes.abi.conforms` (code);
- `silmaril.shapes.elf.abi_conforms` (the function of an ELF file, at every load base);
- the header problems `….header_sat_partial`, `….header_sat_available` and
  `….header_sat_complete` (three distinct coverage levels; only the last is whole-header
  satisfaction).

> **Read every row with these three limits.**
>
> 1. **A row is about a restricted machine model, not real x86.** The standard models `Open`
>    and `Open9` decode an integer subset of x86-64. `sysvInt` is the **INTEGER fragment** of
>    the System V psABI (4- and 8-byte integers and pointers, fixed arity), not the whole
>    psABI: it refuses floating types, aggregates, small integers and varargs.
> 2. **FP, vector and control state are preserved by construction, not proved.** The machine
>    has no SSE, x87, MXCSR or direction-flag instruction; `callModelOf` *copies* that state
>    from entry to return. The return obligations about it (MXCSR, x87 control word, DF, the
>    vector registers) therefore hold by the model's definition. That concrete x86 preserves
>    them is the assumption `Faithful R M` of `Conforms.onRef`, which is **not proved here**.
> 3. **The precondition is part of the claim.** A row holds for the calls its `S.pre`
>    admits, and `enterable` makes every one of them an admitted call, with the caller's bytes on
>    the call's objects (when they avoid the code and its data). The rows of this page
>    have `pre = True` (every argument tuple).

## What a row binds

```lean
structure Conforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop where
  declared : Declares A hdr f p
  extent : c.off + c.len ≤ c.bytes.length
  nonvacuous : ∃ a s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory
  enterable : ∀ a mem, S.pre a mem → (∀ x, S.objects a mem x → c.Outside x) →
    ∃ s, Admit A M p c frame S a s ∧ S.pre a s.machine.memory ∧
      (∀ x, S.objects a s.machine.memory x ↔ S.objects a mem x) ∧
      ∀ x, S.objects a mem x → s.machine.memory.bytes[x]? = mem.bytes[x]?
  safe : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory → NoStuck M s
  progress : mode = .total → ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
    ∀ x, M.Fills s x → (callFrom M s x).Nonempty
  sound : ∀ a s, Admit A M p c frame S a s → S.pre a s.machine.memory →
    ∀ t ∈ callModelOf M s, Good A p frame S a s t
```

| ingredient | definition | content |
| --- | --- | --- |
| ABI and its version | `AbiDef` | `id` and `source` (the versioned document); the data model; `lower` from a C prototype to the ABI's prototype, or an explicit refusal, given the tag definitions of the header (`Header.env`) for by-value structs and unions; a `Convention` (`Entry`, `Return`, `ResultAt`); `argArea` and `owned` (memory the callee gets); `EntryEnv`, the entry environment (below) |
| prototype | `Declares A hdr f p` | the header files parse to a header declaring `f`, and `A.lower` maps its prototype to `p` with the tag definitions of the same header (`hdr.env`): a by-value `struct T` is laid out as that header defines `T` (`sysvScalar_tag_mismatch`). The parsed prototype is a function of the header (`hdr.proto? f`), so it is the exact one: result and parameter types with their signedness and widths. Qualifiers are kept beside it (`hdr.quals? f`, by pointer level); they do not change the lowering. The reader (`Data.Layout.Header.read`) refuses incompatible redeclarations, including differing pointee qualifiers. The check runs by `decide`, so no signature is attached by hand |
| code identity | `Code`, `Placed` | the bytes, the load address, the entry offset, the function's extent, the read-only data, and the image's address ranges. An admitted state has the code and data loaded, `rip` at the entry, and the return address outside the code |
| admissible calls | `Admit` | listed below this table |
| machine | `M : Mach` | a segment machine `M.isa` on its own state `M.σ`; the FFI fields it models (`M.models`, always `.machine`); what a machine state says about them (`M.view`); and its admissible completions (`M.Fills s x`: `x` agrees with `s` on the modelled fields, so its core and memory are `s.machine`'s, and holds anything else hardware may present; every FFI state has one). `M.store s y = overwrite M.models s (M.view y)` writes `y` back: modelled fields from `y`, the others from `s`. An integer machine `I` on `MState` is `Mach.ofInt I`: it models `.machine` only and its one completion of `s` is `s.machine` |
| execution | `callModelOf M` | the **first returns** of `M.isa` from **every** completion of `s`, stored back into `s`; the result is read at the function's own return |
| no stuck state | `safe`, `NoStuck` | from every completion, every state before the return takes a step on `M` |
| call/return | `Good.ret` = `A.conv.Return` | `rip` = the return address, `rsp + 8`, the callee-saved registers, DF clear, x87 mode, the MXCSR control bits (6–15) and x87 control word preserved (MXCSR status flags 0–5 free), the FFI thread pointer |
| result | `Good.result` | some `r` with `A.conv.ResultAt` (excess register bits unspecified) and `S.post a s r t` |
| memory | `Good.frame` | written only inside `S.writes` (caller-visible effects) or `Owned`, which is bounded and admitted: `[rsp − frame, rsp)` for the row's stated `frame` (the red zone is the first 128 of these bytes when `frame ≥ 128`; `frame = 0` owns none), the incoming argument area `[rsp + 8, rsp + 8 + argArea)`, and `A.owned` (the storage of a MEMORY result at RDI under `sysvScalar`; empty for `sysvInt` and `win64Int`). `Stack` makes all of it mapped, readable, writable and apart from the code, data, image and objects. Memory further below `rsp` is not owned |
| thread pointer | `Good.fsBase` | the machine's FS base (what `%fs:` reads) is unchanged; on `Open` and `Open9` no step writes it (`Open.step_fsBase`, `Open9.step_fsBase`) |
| non-vacuity | `nonvacuous`, `enterable` | some admitted call exists; and for **every** argument tuple and caller memory the precondition admits, whose caller-visible objects avoid the code and its read-only data (`Code.Outside`), an admitted call with those arguments, the same objects and the same bytes on them (every buffer content). The rest of that call's memory (code, stack, permissions) is the ABI's, not the caller's: a row says nothing about caller states whose objects overlap the code or its data. A row cannot be non-vacuous through one hand-picked call while its precondition admits others |
| mode | `mode` | `.total`: every admitted call returns, from every completion. `.safe`: partial correctness, divergence allowed, stuck states not |

An admitted call (`Admit`) requires:

- every completion of the entry state live;
- `A.conv.Entry p a s`: the arguments in their registers and stack slots,
  `rsp + 8 ≡ 0 (mod 16)`, the return address, DF clear, x87 mode, `%al` for varargs, and sret;
- the entry environment `A.EntryEnv s.mxcsr s.x87Control`: a predicate on the MXCSR and the
  x87 control word only (its type is its scope). `True` for `sysvInt`, `sysvScalar` and
  `win64Int`: their conventions let a caller enter with any control bits. An ABI requiring the
  default MXCSR control bits (`MXCSR &&& 0xffc0 = 0x1F80`; the sticky status flags are free) is
  a **default-environment subset**, not the full convention, and
  says so in its identity (`AbiDef.defaultEnv`). The environment is never part of a machine;
- the code placed;
- the stack the ABI gives the callee (`Stack`):
  - `frame` bytes below `rsp`, the return address and the argument area;
  - readable and writable;
  - apart from the code, the data, the **image** and the call's **caller-visible objects**
    (`S.objects`);
- the FFI thread pointer equal to the machine's (`fsCoherent`);
- `S.pre a mem`: the C precondition (validity of what pointers point to, no undefined
  behaviour). It is stated on the arguments and memory only, so it cannot pin registers, the
  stack pointer or the entry address.

`CallSpec.abiPure` (every call admitted, any result, nothing caller-visible written) states ABI
conformance of a *pure* function. A function with effects (`memset`) gives its `objects` and
`writes`.

## The machine, real x86, and what is assumed

- **Restricted models.** The standard machines have no SSE, x87, MXCSR or direction-flag
  instruction. Such an instruction is undecodable on them, so code that uses one is stuck.
  Because `safe` excludes stuck states, that code has **no row in either mode**: the row is
  unprovable, not vacuously true.
- **State the integer machine lacks: preserved by construction.** On an integer machine
  (`Mach.ofInt`), `callModelOf` carries the vector, x87, DF, MXCSR and x87-control state
  unchanged (`callModelOf_carried`). The `Return`
  obligations about it hold *by the model*, so a row proves nothing about them for real x86;
  that is `Faithful`'s content.
- **No laundering by the write-back.** `Mach.store` is a definition: a field outside
  `M.models` is carried (`Mach.store_carried`), a modelled field is a function of the machine
  state alone, and `store` is the merge of a very well-behaved lens (`Mach.store_store`,
  `Mach.store_fills`). The laundering lens of the #994 review (clear DF and set x87 mode
  whenever the machine state changed) is the store of no `Mach` (`Lens.launder_not_store`), and
  a machine whose state is fixed by its core and memory models nothing but `.machine`
  (`Lens.models_eq_machine`).
- **Every admissible completion.** State the FFI state does not determine (a time-stamp
  oracle, a hidden profile) is not fixed by the machine: `Admit.live`, `NoStuck`, `callModelOf`
  and `progress` range over every `x` with `M.Fills s x`. On `Mach.ofInt` the only completion is
  `s.machine`, and the definitions are the stage-1 ones (`mem_callModelOf_ofInt`,
  `progress_ofInt_iff`, `noStuck_ofInt_iff`, `live_ofInt_iff`).
- **Faithfulness.** `Faithful R M`, for a reference relation `R` on the whole FFI state, at the
  states `M` reaches from a completion `x` of `s`: where `M` steps from `y` to `y'`, `R` can step
  from `M.store s y` to `M.store s y'` (`fwd`); and where `M` steps from `y`, every step of `R`
  from `M.store s y` is a step `M` takes from a state with the same FFI state, reached from some
  completion of `s` (`bwd`). On `Mach.ofInt` this is the stage-1 statement
  (`faithful_ofInt_iff` for a deterministic `Ref.ofFun r`, `faithful_ofInt_iff_rel`). A step that
  reads hidden state does not make it unsatisfiable: `Lens.tsc`, a machine whose `rdtsc`-like step
  reads a hidden value, is faithful to a reference that may return any value
  (`Lens.tsc_faithful`), while no deterministic reference is (`Lens.tsc_not_faithful_ofFun`).
  `Conforms.onRef` transfers a row to `R`: every first return of `R` is a conforming return,
  and in total mode there is one. For real x86 this is an **assumption** about the model (each decoded instruction
  is executed as `M` says and touches no vector, x87 or control state). It is not proved here;
  the open-machine trust base is described in [x86](../x86.md).
- **External calls.** Behaviour comes only from `M`. On the open machines a call to code that is
  not loaded is stuck. A row about code that calls a library is stated on a machine whose steps
  include the callee contracts (`Silmaril.Elf.Link.Dyn.Proc`), and those contracts are then the
  row's assumptions.
- **Faithfulness is not guarded by the ABI.** `Faithful R M` is restricted to states reached
  from a completion, but quantifies over every FFI state `s`. A hardware reference would need
  it restricted to the states the ABI admits: for example, `Str9`'s string forms assume DF = 0,
  which `Entry` guarantees but which does not hold for arbitrary states. That guarded form is
  future work. The standard instances `Open` and `Open9` have no string forms.
- **Recursive callers.** `Placed.retOutside` admits only callers whose return address lies
  outside the function's bytes.

## Standard ABIs

| `AbiDef` | id | source | supported subset |
| --- | --- | --- | --- |
| `sysvInt` | `x86_64-sysv-psabi@e1ce0983/lp64/integer` | System V AMD64 psABI, x86-psABIs/x86-64-ABI@e1ce098331da5dbd66e1ffc74162380bcc213236, §3.2 | fixed-arity prototypes of 4- and 8-byte integers and pointers, up to 127 parameters; the full `Ffi.Entry`/`Ffi.Return` discipline; the planner `SystemV.Abi.plan` (`intPlan` on this subset); arguments past the sixth on the stack, owned by the callee |
| `sysvScalar` | `x86_64-sysv-psabi@e1ce0983/lp64/scalar-aggregates` | as `sysvInt`, §3.2.3 (classification of INTEGER and SSE scalars and of aggregates and unions into eightbytes, passing on the stack when registers run out, returning of values, the hidden pointer of MEMORY results) | `sysvInt`'s subset plus `float` and `double` (SSE class; sizes from the data model's `floatShape`: 4 bytes is binary32, 8 is binary64), mixed freely, **and structs and unions by value**, classified from their member layout in the header (`objectOf`: the System V layout `bitLayout .sysv`, members' own classes merged into eightbytes by the ABI model's `SystemV.Abi.aggregate`; members may be integers of any width, `_Bool`, enums, pointers, `float`, `double`, named bit-fields, arrays and nested structs and unions). INTEGER eightbytes in RDI…R9 and SSE eightbytes in XMM0–XMM7, counted separately; an aggregate over 16 bytes (MEMORY), or one whose eightbytes do not all find a register, goes whole to 8-byte stack slots in argument order (owned by the callee); result eightbytes in RAX/RDX and XMM0/XMM1, a MEMORY result through the hidden pointer (RDI in, RAX out; the storage is `owned`). The convention is `Machine.Abi.SystemV.Scalar.sysv`, on the same planner (`scalarPlan`, `plan_scalarPlan`) and `Ffi` relations (`Ffi.SretAt`, `resultAt_direct`, `resultAt_indirect`) |
| `win64Int` | `x86_64-ms-x64@cpp-docs-e6106755/llp64/integer` | Microsoft, "x64 calling convention" (learn.microsoft.com/en-us/cpp/build/x64-calling-convention, MicrosoftDocs/cpp-docs@e61067551f92a1c7beaad20c04b9f5ccfd2b5dd6) and "Overview of x64 ABI conventions" (…/x64-software-conventions, cpp-docs@d25e83731f0600bc021bd0b084ad5812b6cfe88f) | `sysvInt`'s C subset under the **LLP64** data model `Data.Layout.msX64` (`long` is 4 bytes, `wchar_t` 2, `long double` 8), with the `Machine.Abi.Win64.win64` convention: RCX, RDX, R8, R9, a 32-byte shadow area, then 8-byte slots at `rsp + 8 + 8i`; result in RAX; no red zone. The callee owns the shadow area and its stack arguments (`argArea = 8 · max n 4`) |

The data model is part of the lowering: the header `long f(long);` declares `f` as
`int32 → int32` under `win64Int` and as `int64 → int64` under `sysvInt` and `sysvScalar`
(`win64Int_lower_examples`). `sysvScalar_lower_examples` shows the planner's placements
(`double f(double, int)`: XMM0, EDI, result in XMM0; a ninth `float` on the stack while a later
`long` still gets RDI). `sysvScalar_aggregate_classes`, `sysvScalar_aggregate_args` and
`sysvScalar_aggregate_results` read structs from header text and show the classes and the
planner's placements: `struct { long a, b; }` in RDI, RSI and returned in RAX, RDX;
`struct { double x, y; }` in XMM0, XMM1; `struct { long a; double b; }` in RDI and XMM0;
`struct { float a, b, c; }` in XMM0 (`a`, `b`) and XMM1 (`c`); a 24-byte struct on the stack
and, as a result, through the hidden pointer (`Return.indirect 24 8`, the arguments then
starting at RSI); after five `long`s, a two-`long` struct on the stack whole while a later
`long` still gets R9.

**`sysvScalar` and the standard machines.** `Open` and `Open9` model no SSE instruction. Code
that reads an XMM argument or writes XMM0 is stuck on them, so it has no `sysvScalar` row
there; a row about floating computation needs a machine with SSE steps (and its `Faithful`
assumption). On the open machines a `sysvScalar` row covers code that receives floating
arguments without touching them.

`lowerInt` (and `lowerWin64Int`) refuse everything else with a message:

- `_Bool`, `char` and `short`;
- floating types (SSE and x87 classes);
- structs and unions passed by value;
- enums;
- varargs.

`lowerScalar` (`sysvScalar`) accepts `float`, `double` and structs and unions by value, and
refuses, with a message (pinned in `SysvScalar.Thms`): `long double` (X87/X87UP: passed in
memory, returned in `%st0`) and `__float128` (SSE/SSEUP) as parameters, results or members;
`__int128` members; as parameters and results `_Bool`, `char`, `short`, enums and arrays; a
struct or union the header does not define (incomplete); zero-length or flexible array
members; unnamed bit-fields of nonzero width; bit-fields in a nested aggregate (`layoutTy`
refuses them); an aggregate with an eightbyte of padding only (NO_CLASS), aligned to more than
8 bytes, or larger than 2^32 bytes; and varargs (the `%al` count and `va_list`). The clang
import records no tag definitions yet, so on that route by-value structs are refused as
incomplete.

## The ELF binding

`Elf.Abi.AbiConforms A M mode hdr f p F b c frame S` combines three facts.

1. **`CodeOf F b f c`.** It requires all of the following:
   - The binding `b` (`.symtab`, or `.dynsym ver` for ld.so's versioned lookup) looks up the
     header's name `f`.
   - The lookup finds a plain function with `st_value` = entry and `st_size` = extent.
   - The symbol entry is an `STT_FUNC` named `f`. `STT_OBJECT`, `NOTYPE` and `GNU_IFUNC` are
     rejected.
   - A read-only executable `PT_LOAD` maps the code bytes, and read-only segments map the data.
   - The code's image is the file's `PT_LOAD` ranges.
2. **`Untouched F c`.** The file is x86-64, and every dynamic relocation has a known width
   (`relocWidth`, from the psABI's relocation table: 4, 8, or 16 for `TLSDESC`; types the
   check does not accept, `SIZE64` among them, are refused) and writes outside
   the code and its data. `COPY` (it writes the symbol's `st_size`), `IRELATIVE` (ld.so runs the
   IFUNC resolver it names), link-time-only and unknown types are refused wherever they are (`not_untouched_copy`, `not_untouched_unknown`), as is a
   file of another machine. A `TLSDESC` 12 bytes below the code is refused
   (`not_untouched_tlsdesc`); the former check, which took every relocation as 8 bytes, accepted
   it (`misses8_tlsdesc`).
3. **Rebased conformance.** The file admits at least one load base, and at **every load base
   the file admits** (`Placement`: `0` for `ET_EXEC`, page-aligned for `ET_DYN`), the rebased
   code (`Code.rebase`) conforms. Without the first part, a file that admits no base would make
   this conjunct vacuous.
   No row claims conformance at the link-time address of a shared object.

## Header satisfaction

A coverage per binary lists the claimed functions and excludes every other declared function
for a reason. Each reason is checked:

| exclusion | checked |
| --- | --- |
| `unsupported` | the ABI's lowering refuses the prototype (`Coverage.check`) |
| `absent` | no symbol table of the file defines the name, in any version (`Elf.Abi.Absent`): an API version gap |
| `unclaimed` | the file does define a function of that name (`Elf.Abi.Present`); the reason text is documentation |

- **`HeaderSatPartial`** / `abi_header_sat_partial` requires:
  - at least one claimed function;
  - the coverage checked against the header;
  - every claimed function conforms.
  It says nothing about the excluded functions, and the claimed and excluded lists are part of
  the statement.
- **`HeaderSatAvailable`** / `abi_header_sat_available` is partial satisfaction with no
  `unclaimed` declaration and every claimed function in `.total` mode: every function of the
  header **the binary provides** conforms. `absent` declarations (checked absent from the file:
  a version gap such as zlib 1.2.11 lacking `crc32_combine_gen` and `crc32_combine_op`, which 1.2.12 added) are allowed and listed with the row.
- **`HeaderSatComplete`** / `abi_header_sat_complete` is available satisfaction with nothing
  `absent`: every declaration is claimed or refused by the ABI's lowering. This is the only
  level that is satisfaction of the whole header (for the surface the ABI expresses).

A partial row is never shown as header satisfaction. `arith_h` is partial, and
`not_available` proves it is not available satisfaction for any implementations.

A header shared by several binaries gives **separate rows per binary**. The header and the
specs are shared values; the file, the binding (with its version) and the code differ.

## Distinct from the shapes that state less

| shape | says | does not say |
| --- | --- | --- |
| `elf.lookup`, `elf.binds`, function tables | a symbol has a value and a size; the bytes there | anything about a C signature or the ABI |
| `Data.Layout` problems | sizes, offsets and padding of C types under a data model | how a value is passed |
| `x86.abi_function`, `elf.fn_contract` | a contract with the System V *entry* and *return* discipline (`AbiEntry`/`AbiReturn`) | the prototype, argument placement, result read-back, control state, owned memory |
| **`abi.conforms`, `elf.abi_conforms`** | the code is a conforming callee for the header's prototype under a versioned ABI, on `M`, with a C-level spec | that a compiler produced it; anything about real x86 without `Faithful` |
| `sysv.implements`, `c.compiles_to` | the code implements a source meaning (translation validation) | — |

## The worked example: `arith.h` and the pinned `leaf-arith`

`examples/elf-ladder/01-leaf-arith/arith.h` and the `rt.h` it includes are read as text. The
code is the pinned gcc 13.3 `-O2` executable `examples/elf-ladder/01-leaf-arith/pinned/leaf-arith`
(SHA-256 `d9cf1e5d…`). The per-part ELF reader reads it as `Silmaril.Elf.Staged.Pinned.LeafArith`.
All rows are on `Open`.

| row | statement | status |
| --- | --- | --- |
| `silmaril.elf.abi.leaf_arith.clamp_i32` | `int clamp_i32(int, int, int)`, `0x4013a0`, 19 bytes; total, frame 0, no precondition, result `clampSpec x lo hi`, nothing written | proved |
| `silmaril.elf.abi.leaf_arith.sat_add_u32` | `u32 sat_add_u32(u32, u32)`, `0x401400`, 29 bytes | proved |
| `silmaril.elf.abi.leaf_arith.gcd_u32` | `u32 gcd_u32(u32, u32)`, `0x401370`, 37 bytes | open: `Task.gcd_conforms`; file facts proved |
| `silmaril.elf.abi.leaf_arith.bswap32_manual` | `u32 bswap32_manual(u32)`, `0x401420`, 5 bytes | open: `Task.bswap_conforms`; file facts proved |
| `silmaril.elf.abi.leaf_arith.arith_h` | **partial** header satisfaction: the two proved functions; 9 declarations absent from every table of the file; the rest present and unclaimed with reasons (`popcount32` uses `imul r32, r/m32, imm32` and `ilog2_u32` uses `bsr`, both outside `Open`) | proved |

### Negative tests (proved)

| theorem | rejects |
| --- | --- |
| `open_mid_not` (with `open_stuck_mid`) | **stuck code on `Open`**: `clamp_i32`'s prototype entered in the middle of an instruction is undecodable, and it conforms in neither mode, for any spec |
| `clamp_rejects_first` | a wrong postcondition ("returns its first argument") |
| `stuck_not` | a machine that cannot step (schema test) |
| `clobber_not` | a return with `rbx` changed (schema test) |
| `unbalanced_not` | a "return" with `rsp` 16 above the entry, which never returns and gets stuck (schema test) |
| `scribble_not` | a write at `rsp − 8` with `frame = 0` (schema test) |
| `wrong_prototype` | `long clamp_i32(long, long, long)` (wrong widths), which is not what `arith.h` declares |
| `wrong_signedness` | `unsigned clamp_i32(int, int, int)` (wrong result signedness) |
| `wrong_header_not` | a header declaring an `unsigned` result: the code conforms to the `int` prototype on no machine, mode or spec |
| `not_available` (two forms) | the partial `arith.h` coverage as available (or complete) header satisfaction |
| `not_headerSatPartial_nil`, `HeaderSatAvailable.total` | header satisfaction with nothing claimed; a `.safe` claim in available (or complete) satisfaction |
| `Elf.Abi.Present.not_absent` | an `absent` exclusion of a function some table of the file defines (any table, any version: `Absent` takes no claimant-chosen selector) |
| `Elf.Abi.LeafArith.not_codeOf_symbol` | `clamp_i32`'s code as the file's `sat_add_u32` (wrong symbol) |
| `Elf.Abi.LeafArith.not_codeOf_bytes` | the code with its entry byte changed (wrong bytes), as any function of the file (`Elf.Abi.not_codeOf_of_bytes`) |
| `Data.Layout.Header.qualifier_redeclaration` | `int f(const char *); int f(char *);` and other redeclarations with differing pointee qualifiers |
| `Elf.Abi.LeafArith.not_codeOf_offset` | an entry that is not the symbol's `st_value` |
| `Elf.Abi.not_abiConforms_of_noPlacement` | any claim, for any spec and machine, on a file that admits no load base |
| header reader (`Data.Layout.Header.Thms`) | conflicting redeclarations and tag redefinitions, `#if`, untagged definitions, flexible arrays, function pointers, K&R declarations, `#pragma pack`, and the other constructs outside the subset |

The schema tests run on small machines given by a step function (`Witness.toy`). They test the
statement, not x86 code.

## How the proofs are made

`conforms_of_strict` turns a first-return function contract (`FnContract.Spec.Strict`, as block
certificates give through `BlockCert.FunCert.strict`) into a row. A first return also rules out
stuck states (`noStuck_of_firstReturn`, since the machine is deterministic).

`Proofs.Machine.Abi.Conformance.SysvInt` has the `sysvInt` lemmas: the entry obligations, a
contract result as a System V return, and the 32-bit read-back. The read-back
(`Ffi.bytes4_inj`, `Ffi.chunk32_iff`) has one copy, in `Machine.SystemV.Abi.Ffi`. The entry and
return lemmas are still restated beside `Machine.Abi.OpenMachine`'s, whose closure cannot be
loaded with the registry's. Follow-up: state them once on any machine whose core and memory are
the state's (as here), in `Machine.SystemV.Abi.Ffi`, and derive the `OpenMachine` forms from it.

## Modules

| module | content |
| --- | --- |
| `Silmaril.Data.Layout.Header` | the header subset reader (`read`), `CProto`, `Header`; tagged struct, union and enum definitions are read into `Header.decls`/`Header.enums` (`Header.env` for layouts). Header satisfaction concerns the prototypes only |
| `Silmaril.Data.Layout.Header.Import`, `Silmaril.Machine.Abi.Conformance.Import` | the clang route: a provenance-tagged import of a pinned clang JSON AST, its cross-check with the subset reader, and coverage and `Declares` from it ([C headers](c-headers.md)) |
| `Silmaril.Machine.Abi.Conformance` | `AbiDef` (with `EntryEnv`, `AbiDef.defaultEnv`), `sysvInt`, `Code`, `FfiField`, `overwrite`, `Mach`, `Mach.store`, `Mach.ofInt`, `callFrom`, `callModelOf`, `CallSpec`, `Admit`, `NoStuck`, `Good`, `Conforms`, `Ref`, `Faithful`, `Coverage`, `HeaderSatPartial`, `HeaderSatAvailable`, `HeaderSatComplete`; `conforms_of_strict`, `Conforms.steps`, `Conforms.onRef`, the lens laws and the `Mach.ofInt` reductions |
| `Silmaril.Machine.Abi.Conformance.Lens` | `launder` (the #994 review's laundering store) and `launder_not_store`; `models_eq_machine`; `tsc`, a machine with hidden state a step reads, and `tsc_faithful`, `tsc_not_faithful_ofFun` |
| `Silmaril.Machine.Abi.Conformance.Win64`, `….SysvScalar` | `win64Int`, `lowerWin64Int` and `sysvScalar`, `kindOf`, `objectOf`, `argOf`, `lowerScalar`, with their lowering examples |
| `Silmaril.Machine.Abi.SystemV.Scalar` | the scalar-and-aggregate vocabulary and convention: `Kind`, `Agg`, `Eights`, `Arg`, `Proto`, `scalarPlan`, `plan_scalarPlan`, `entry_inhabited`, `sysv`, `resultAt_some`, `resultAt_direct`, `resultAt_indirect` |
| `Silmaril.Data.Layout` (`msX64`) | the Microsoft x64 LLP64 data model |
| `Silmaril.Machine.Abi.Conformance.LeafArith` | the example: its header, code, specs, coverage, witness state, test machines, open tasks, proofs and negative tests |
| `Silmaril.X86.Open.FsBase` | `Open.step_fsBase`, `Open9.step_fsBase`: no step writes the FS base (proving `FsBase.Task.openStepKeepsFs`) |
| `Silmaril.Project.Shapes.Abi` | `silmaril.shapes.abi.conforms`, `header_sat_partial`, `header_sat_available`, `header_sat_complete` and their `sysv_int` instances |
| `Silmaril.Elf.Abi`, `Silmaril.Elf.Abi.LeafArith` | `silmaril.shapes.elf.abi_conforms`, `abi_header_sat_partial`, `abi_header_sat_available`, `abi_header_sat_complete`, the rows and the group `silmaril.abi` |
| `Silmaril.X86.Ladder.LeafArith.Realizes` | rung 01's `*_realizes` certificates, split from `LeafArith.Thms` because their proofs import `Silmaril.X86.FnContract.SystemV`, which cannot be loaded together with the `Silmaril.Machine.X86` copies the registry also loads |

## Next

- zlib's checksum functions as rows per binary under one header excerpt:
  - the static `zlib-checksums`, whose total contracts are proved but whose first-return forms
    are open;
  - Ubuntu's `libz.so.1.3`, with versioned bindings and rebasing.
- `Open9` rows.
- System V `long double`, `__int128`, over-aligned and SSEUP aggregates, and varargs; tag
  definitions in the clang import; Microsoft x64 floating arguments (positional XMM0–XMM3) and
  aggregates.
- `sysvScalar` and `win64Int` instances of the registry shapes, and rows for them (a
  `sysvScalar` row about floating computation needs a machine with SSE steps).
- A reference machine for `Faithful`.
- A `Mach` with SSE steps (`Str9L`) that models the vector registers and MXCSR (`models`), with
  its completions (`Fills`); rows on it state their entry environment through the ABI
  (`EntryEnv`), and a default-MXCSR row is a default-environment subset.
- The explorer's prototype and ABI views.
