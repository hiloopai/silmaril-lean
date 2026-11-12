# Institutions from Rust

A Rust program states properties by *calling* an institution's imports. Silmaril's verified checker
answers questions about those calls on the compiled `.wasm`. The same binaries, quoted into Lean,
get kernel-checked theorems in Silmaril's specification institutions.

Curry–Howard reading: an institution's signature (its imports) is a Rust trait; a program generic
over the trait is a program over that vocabulary; a sentence ("`unlock` is never called while
`status` runs", "`assert` never receives `0`", "this module may attest") is a question about
the program's import calls.

## Crates

* `institution/`: the `institution!` macro (no dependencies, `no_std`).
  `pub mod spec = "spec" { fn alarm(); fn assert(cond: i32); }` generates:
  - a trait `spec::Api` (the signature);
  - `spec::Wasm`, the real imports via `#[link(wasm_import_module = "spec")]`, and module-level
    functions calling them (Wasm targets only);
  - `spec::Observer<F>`, which reports each call as a `spec::Event` to a closure. The same
    program then runs natively under unit and property tests.
* `adder-core/` (logic, native tests) and `adder/` (the Wasm module). Exports `add`,
  `checked_add` (calls `spec.alarm` on overflow) and `add_comm` (calls
  `spec.assert(add(a, b) == add(b, a))`).
* `door-lock/` (logic, native tests), `door/` and `door-buggy/` (the Wasm modules). A PIN door
  lock with states `Locked`, `Open` and `Alarm`; three wrong PINs sound the alarm. It is written
  once, generic over two institutions: `spec` (`attest`, `assert`) and `door` (`unlock`, `lock`,
  `alarm`). At the unlock transition it calls `spec.assert(pin == PIN)`, then `spec.attest()`,
  then `door.unlock()`. The modules export `enter(pin)`, `lock()` and `status()`. `door-buggy`
  inverts the PIN comparison.
* `leaf-door-opens/`, `leaf-overflow/`: two Rust "propositions" for the Attest encoding (positive
  logic by "may attest", `docs/projects/wasm-wasi.md`). Each is a module whose only import is
  `env.attest : [] -> []`:
  - "the buggy lock opens for some PIN": `try_pin(pin)` runs the buggy lock and attests when it
    opens;
  - "`checked_add(a, i32::MAX)` overflows for some `a`": `probe(a)`.
* `wasm2lean/`: prints a `.wasm` as WAT (`wasmprinter` 0.240.0, custom sections dropped), and
  writes `Silmaril/Wasm/Examples/RustInst/Defs.lean` quoting each binary with silmaril-lean's `wat3!`.

`.cargo/config.toml` links the Wasm builds with a 1 KiB shadow stack and one 64 KiB page. The
static state then sits at address 1024, which keeps kernel evaluation of the interpreter cheap.

## Run

```sh
rustup target add wasm32-unknown-unknown
(cd ../../.. && nice lake build wasm-verify)   # the checker
./run.sh             # build to wasm32, ask expected.txt's questions, check the Lean quotation is current
cargo test           # native unit and property tests
REGEN=1 ./run.sh     # rewrite Silmaril/Wasm/Examples/RustInst/Defs.lean from this build
(cd ../../.. && nice lake build --wfail Silmaril.Wasm.Examples.RustInst.Thms)
```

`run.sh` exits non-zero if a verdict differs from `expected.txt`, or if the Lean quotation differs
from the binaries just built.

## What is proved, tested, planned

### Checked on the binaries (`wasm-verify`)

The checker's verdicts have soundness theorems in Lean (`docs/projects/wasm-wasi.md`):

* `proved` means the property holds of every play of the module in Silmaril's game semantics, at
  every profile and against every environment;
* `refuted` comes with a concrete play.

The command line decodes the binary with silmaril-lean's decoder at run time.

| Module | Question | Verdict |
| --- | --- | --- |
| `adder` | `spec.alarm` never called while `add` is active | proved, `unreachableFrom` |
| `adder` | `spec.alarm` never called while `add_comm` is active | proved |
| `adder` | `spec.alarm` never called while `checked_add` is active | unknown, `reaches`. It is called on overflow, but the refuter tries only `0,0` and `1,1`. |
| `adder` | `spec.assert` never receives `0` | proved, `guarded`. LLVM folded `a + b == b + a` to `1`. |
| `adder` | `spec.assert` never called | refuted: `add_comm(0, 0)` calls `assert(1)` |
| `door` | `spec.assert` never receives `0` ("the bolt is released only on the right PIN", as the program states it) | **proved**, `guarded` |
| `door_buggy` | the same | **refuted**: the play `enter(0)` calls `spec.assert(0)` |
| both | `door.unlock` / `spec.attest` never called while `status` is active | proved |
| both | `door.unlock` / `door.alarm` never called while `lock` is active | proved |
| `door` | `door.unlock` never called while `enter` is active | unknown, `reaches` |
| `door` | `spec.attest` never called | unknown. The refuter tries `enter(0)` and `enter(1)` only; `1234` opens the door. |
| `leaf_door_opens` | `env.attest` never called | refuted: `try_pin(0)` |
| `leaf_overflow` | `env.attest` never called | refuted: `probe(1)` |

The `proved` for `assert-never-false` on `door` is shallow. LLVM turned
`if pin == PIN { assert(pin == PIN) }` into `assert(1)`, and the checker confirms that the
binary's argument is a non-zero constant. The checker does not decide the temporal properties
below.

### Proved in Lean (`Silmaril/Wasm/Examples/RustInst/Thms.lean`)

The binaries are quoted into Lean by `wasm2lean` and `wat3!`. Every verdict is computed by kernel
evaluation of the verifier (`wasm_check`, `wasm_refute`, `decide +kernel`; no native evaluation).
The headline theorems depend on `propext`, `Classical.choice` and `Quot.sound` only.

```lean
theorem door_assertNeverFalse (P : Profile) :
    Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem P) (progOf door)
      ⟨0, by decide +kernel⟩
theorem doorBuggy_not_assertNeverFalse (nd : Bool) :
    ¬ Models (assertNeverFalse FnType (Behaviour Val)) (wasmSem (Profile.spec nd {}))
      (progOf doorBuggy) ⟨0, doorBuggy_imports⟩
theorem door_neverCallFrom_unlock_status (P : Profile) :
    Models (neverCallFrom FnType (List Val) (Behaviour Val)) (wasmSem P) (progOf door)
      (⟨2, by decide +kernel⟩, ⟨2, door_exports⟩)
theorem rust_and (nd : Bool) :
    MayCall (andM (coreKit (Profile.spec nd {}))
      ((leafOf leafDoorOpens).toAMod (Profile.spec nd {}))
      ((leafOf leafOverflow).toAMod (Profile.spec nd {}))).σ
theorem rust_and_ff (P : Profile) :
    ¬ MayCall (andM (coreKit P) ((leafOf leafDoorOpens).toAMod P) ((leafOf ffMod).toAMod P)).σ
```

The file also proves:

* for the adder: `adder_neverCallFrom_add` and `adder_assertNeverFalse`;
* for the door lock: `door_neverCallFrom_unlock_lock`;
* for the leaves: `leafDoorOpens_attests` and `leafOverflow_attests`, via `attests_of_refuted`
  and the verifier's `check_refuted_sound_spec`;
* `rust_or_ff`.

`rust_and` is the Attest conjunction of two Rust-compiled propositions, linked game-semantically
through the gate module (`Strategy.comp`/`Strategy.pair`, not a linked Core module). By
`mayAttest_and`, it may attest because each leaf may. `rust_and_ff` pairs a Rust leaf with the
hand-written `false` module `ffMod`.

**Trusted, not proved.** The quoted Lean `Module` is the module the binary denotes: `wasmprinter`
and `wat3!` are not checked against silmaril-lean's decoder. The FNV-1a fingerprints in the Defs
module and `run.sh`'s comparison only tie the Lean file to a build. Import and export *indices*
depend on the linker's order, so the theorems name them by number (see the Defs module's WAT).

### Tested natively (`cargo test`, proptest 1.7.0, 256 cases per property)

* `adder-core`:
  - `add` is commutative and associative;
  - the import trace of `add_comm` is exactly `[assert(1)]`;
  - `checked_add` calls `alarm` exactly when the mathematical sum overflows.
* `door-lock`: random sequences of up to 40 export calls (PINs drawn from `1234`, `0`, `1235` and
  any `i32`). The import trace is checked for these temporal properties:
  - `assert` never receives `0`;
  - `attest` is only called right after `assert(1)`, and `unlock` only right after `attest`
    ("the door opens only after the code was checked");
  - after `alarm`, `unlock` never occurs;
  - `unlock` and `lock` alternate, starting with `unlock`.
* `buggy_is_refuted`: with `BUGGY = true`, proptest's `TestRunner` finds a violation of the first
  property and shrinks it to a single wrong PIN, `[Enter(0)]`. That is the checker's
  counterexample.
* `wasm2lean`: custom-section stripping.

The native build is the same source with `Observer` in place of the Wasm imports. Nothing relates
the native and Wasm builds; there is no translation validation.

### Not done

* The temporal trace properties (`unlock` only after `assert(1)`, no `unlock` after `alarm`) are
  tested natively, not proved of the binary. `Silmaril.Wasm.Spec` has LTL/TLA sentences over
  `wasmDivSem`, but the checker decides only `neverCall`, `assertNeverFalse` and
  `neverCallFrom`.
* The refuter makes one export call from the initial store, with arguments all `0` or all `1`,
  and stops at the first import call. So it finds neither `enter(1234)` nor a sequence of calls.
* A whole-module `neverCall` proof for a Rust module needs the import to be present but
  unreachable. The linker removes unreachable code, so the `false` leaf of the Attest examples is
  the hand-written `ffMod`.
* The macro only covers functions returning `()` with scalar arguments. It has no import results
  and no component-model types.
