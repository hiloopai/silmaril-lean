# as-adder: a compiled AssemblyScript export, tested and verified

`assembly/index.ts` is four AssemblyScript functions on `i32`, compiled by `asc` 0.28.20 with
the stub runtime to `wasm/adder.wasm` (113 bytes; `wasm/adder.wat` is the compiler's own text
output, committed for reading).

| Export | AssemblyScript source | Compiled body (from `wasm/adder.wat`) |
| --- | --- | --- |
| `add(a, b)` | `a + b` | `local.get 0; local.get 1; i32.add` |
| `mul(a, b)` | `a * b` | `local.get 0; local.get 1; i32.mul` |
| `max(a, b)` | `a < b ? b : a` | `local.get 1; local.get 0; local.get 0; local.get 1; i32.lt_s; select` |
| `odd(a)` | `a * 2 + 1` | `local.get 0; i32.const 1; i32.shl; i32.const 1; i32.add` |

AssemblyScript `i32` arithmetic wraps modulo 2^32. The module also exports a memory of 0
pages, which no function touches. It has **no imports**: with `--runtime stub` and no
allocation or `abort` call site, `asc` emits neither an allocator nor the usual
`env.abort` import (the build is the same with or without `--noAssert`). Instantiating it
needs no host functions, so the host is closed: the `wasmi` linker in the harness is empty,
and `module.imports().len() == 0` is asserted.

## Build (reproducible)

```sh
./build-wasm.sh   # npx --yes -p assemblyscript@0.28.20 asc assembly/index.ts --runtime stub -O3, then cmp
```

The script rebuilds into a temporary directory and `cmp`s both the `.wasm` and the `.wat`
against the committed files. `sha256(wasm/adder.wasm) =
8441a35f0f1e67eab72da9e017c90b980fe4d45935e51b63e88521089a0901b1` (node v24.21.0).

## What is tested (not proved)

`harness/` (a standalone Cargo crate) embeds the committed `wasm/adder.wasm` with
`include_bytes!` and runs it in the `wasmi` 0.40.0 interpreter.

```sh
cd harness
cargo test                                         # 7 tests, proptest 1.6.0, 10_000 cases each
cargo run --release --bin fuzz -- 5000000 0xc0ffee
```

* `wasm_*` proptests, on the **compiled module**: `add` is commutative and associative, `mul`
  is commutative, `max` is an upper bound attained by an argument, `odd` is odd.
* `wasm_agrees_with_source` (proptest) and `wasm_boundary_cases` (all triples of 9 boundary
  values): a differential test of the compiled exports against `src`, a **hand
  transcription** of `index.ts` into Rust. AssemblyScript cannot be run natively, so unlike
  the Rust demo there is no run of the source itself; `src` is a model of it.
* `fuzz`: a stable-toolchain fuzz loop (SplitMix64, half uniform and half boundary-biased
  inputs) running the same checks. Recorded run: `fuzz: 5000000 cases, seed 0xc0ffee:
  compiled adder.wasm agrees with the transcribed AssemblyScript source`.

Testing samples finitely many inputs and trusts `wasmi`.

## What is proved (Lean kernel, about the committed `.wasm` itself)

Statements: `Silmaril/Wasm/Examples/AsAdder/Thms.lean`; proofs:
`Silmaril/Proofs/Wasm/Examples/AsAdder/`. Build:
`lake build --wfail Silmaril.Wasm.Examples.AsAdder.Thms`. The pattern is the Rust demo's
(`../rust-adder`), reused file for file.

1. **Ingestion.** `tools/wasm-to-lean` prints `Silmaril/Wasm/Examples/AsAdder/Defs.lean` (the
   113 bytes and the decoded `Module` term); the tool is untrusted:

   ```lean
   theorem decode_eq : Decode.decodeModule bytes = .ok module := by kernel_rfl
   theorem encodes : Encodes bytes.data.toList module := Decode.decodeModule_sound decode_eq
   theorem asI_isInstance : ∃ mt, IsInstance module mt asI
   ```

2. **Layout.** `asc` emits the functions in the order `odd, mul, max, add` and exports them as
   `add, mul, max, odd`, so export `j` is the function at address `addrOf j`:
   `addrOf_eq : [addrOf 0, addrOf 1, addrOf 2, addrOf 3] = [3, 1, 2, 0]`,
   `export_names : module.exports.map (·.name) = ["add", "mul", "max", "odd", "memory"]`.

3. **Every export computes what the source says**, at every profile `P` and for every host
   relation (partial and total correctness):

   ```lean
   theorem export_valid (j : Nat) (hj : j < 4) : FSpecValid P host (addrOf j) (exportSpec j)
   theorem export_total (j : Nat) (hj : j < 4) : TFSpecAt P host (addrOf j) (exportSpec j)
   ```

   plus `export_run` (every finished run returns `[i32 v]` with `expected j args = some v` and
   keeps the store), `export_safe` (no run gets stuck or traps) and `export_terminates` (no run
   diverges). `expected` is the source read on `BitVec 32`: `Src.add a b = a + b`,
   `Src.mul a b = a * b`, `Src.max a b = if a.toInt < b.toInt then b else a`,
   `Src.odd a = a * 2 + 1`. The compiled `odd` is `(a << 1) + 1` (`shl_add_one`), and `max`
   is `select` on `i32.lt_s` (`select_ltS`).

4. **The proptest properties, for the compiled exports** (`invoke s 3` is `add`, `1` is `mul`,
   `2` is `max`, `0` is `odd`):

   ```lean
   theorem add_comm_runs ... (x y : BitVec 32)
       (h₁ : Steps P host (invoke s₁ 3 [.i32 x, .i32 y]) c₁) (e₁ : c₁.code = r₁.toAdmin)
       (h₂ : Steps P host (invoke s₂ 3 [.i32 y, .i32 x]) c₂) (e₂ : c₂.code = r₂.toAdmin) :
       r₁ = r₂
   theorem add_assoc_runs ...   -- add(add(x,y),z) and add(x,add(y,z)) return the same result
   theorem mul_comm_runs ...
   theorem max_runs ... : ∃ m, r = .values [.i32 m] ∧ x.toInt ≤ m.toInt ∧ y.toInt ≤ m.toInt ∧ (m = x ∨ m = y)
   theorem odd_runs ... : ∃ m, r = .values [.i32 m] ∧ m = x * 2 + 1 ∧ m.getLsbD 0 = true
   ```

5. **Sessions.** `as_session : Session P asI K asI.store l → ∀ c ∈ l, Correct c`.

All of these depend only on `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`).

**Imports and the host.** The module has no imports, so the instance `asI` has
`imports := []` and the session theorem holds against every environment `K` (there is
nothing for `K` to answer). The Core-run theorems quantify over every `host` relation, which
is never consulted. Had `asc` emitted an `env.abort` import (it does when the code has an
`abort` call site, e.g. an assertion or a bounds check), the instance would have that import
and the theorems would need an assumption about how the environment answers it; this demo
does not handle that case.

**Not proved:** anything about the exported memory (0 pages; no function uses it).
`Src`/`expected` are a hand transcription of `assembly/index.ts`: nothing formally links the
Lean theorems to the `.ts` file, and only the differential test relates the transcription to
the compiled module. There is no translation validation.

## Regenerating the Lean file

```sh
cargo run --manifest-path tools/wasm-to-lean/Cargo.toml -- \
  examples/wasm-demos/as-adder/wasm/adder.wasm --namespace Silmaril.Wasm.Examples.AsAdder \
  --source '`examples/wasm-demos/as-adder/wasm/adder.wasm` (AssemblyScript `asc` 0.28.20, `--runtime stub -O3`, see that directory'"'"'s README)' \
  > Silmaril/Wasm/Examples/AsAdder/Defs.lean
```
