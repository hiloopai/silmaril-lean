# rust-adder: a compiled Rust export, tested and verified

A tiny `no_std` Rust crate (`adder/`) compiled by today's `rustc` to
`wasm32-unknown-unknown`, with the resulting module committed as `wasm/adder.wasm` (124 bytes).

| Export | Rust source | Compiled body (decoded) |
| --- | --- | --- |
| `add(a, b)` | `a.wrapping_add(b)` | `local.get 1; local.get 0; i32.add` |
| `mul(a, b)` | `a.wrapping_mul(b)` | `local.get 1; local.get 0; i32.mul` |
| `max(a, b)` | `if a < b { b } else { a }` | `local.get 0; local.get 1; local.get 0; local.get 1; i32.gt_s; select` |
| `odd(a)` | `a.wrapping_mul(2).wrapping_add(1)` | `local.get 0; i32.const 1; i32.shl; i32.const 1; i32.or` |

(The module also exports its linear memory and defines the `__stack_pointer` global; none of
the four functions touches them.)

## Build (reproducible)

```sh
./build-wasm.sh   # cargo build -p adder --profile wasm --target wasm32-unknown-unknown, then cmp
```

* toolchain: `rustc 1.98.1 (48a229cea 2026-09-01)`, `cargo 1.98.1` (pinned by the repository's
  `rust-toolchain.toml`), target `wasm32-unknown-unknown`;
* profile `wasm` (in `Cargo.toml`): `opt-level = "s"`, `panic = "abort"`, `lto = true`,
  `codegen-units = 1`, `strip = true`;
* `sha256(wasm/adder.wasm) = d45d9378b925adef58a2588c80bbbfb259d327a1fd83499a23492f576a16cffc`.

## What is tested (not proved)

`harness/` embeds the committed `wasm/adder.wasm` with `include_bytes!` and runs it with the
`wasmi` 0.40.0 interpreter.

```sh
cargo test -p adder-harness                        # 7 tests, proptest 1.6.0, 10_000 cases each
cargo run --release -p adder-harness --bin fuzz -- 5000000 0xc0ffee
```

* `source_*` proptests: commutativity and associativity of `add`, commutativity of `mul`,
  `max` is an upper bound attained by an argument, `odd` is odd. These run the **Rust source**
  natively; they are about the compiled module only if one trusts `rustc`'s wasm backend.
* `wasm_agrees_with_source` (proptest) and `wasm_boundary_cases` (all triples of 9 boundary
  values): a differential test of the **compiled** exports against the source, plus
  commutativity and associativity of `add` and oddness of `odd` checked on the compiled module.
* `fuzz`: a stable-toolchain fuzz loop (SplitMix64, half uniform inputs and half
  boundary-biased) running the same differential check; it exits non-zero on the first
  disagreement. Recorded run: `fuzz: 5000000 cases, seed 0xc0ffee: compiled adder.wasm agrees
  with the Rust source`.

Testing samples finitely many inputs and trusts `wasmi`.

## What is proved (Lean kernel, about the committed `.wasm` itself)

1. **Ingestion.** `tools/wasm-to-lean` (Rust, `wasmparser` 0.219.1) prints
   `Silmaril/Wasm/Examples/RustAdder/Defs.lean`: the 124 bytes and the decoded silmaril-lean
   `Module` term. The tool is untrusted:

   ```lean
   theorem decode_eq : Decode.decodeModule bytes = .ok module := by kernel_rfl
   theorem encodes : Encodes bytes.data.toList module := Decode.decodeModule_sound decode_eq
   theorem adderI_isInstance : ∃ mt, IsInstance module mt adderI
   ```

   `decode_eq` runs silmaril-lean's binary decoder in the kernel on the exact bytes;
   `adderI` (the instance after `instantiateOnce?`) equals `Verify.instOf module` by `kernel_rfl`.

2. **Every export computes what the Rust source says**, at **every profile** `P` and for every
   host relation (Silmaril's every-run Hoare logic, `HWP`, partial correctness; `TWP`, total):

   ```lean
   theorem export_valid (j : Nat) (hj : j < 4) : FSpecValid P host j (exportSpec j)
   theorem export_run (j : Nat) (hj : j < 4) {s : Store Nat} (hs : s.funcs = adderStore.funcs)
       {args : List Val} {v : BitVec 32} (hv : expected j args = some v) {c' : Config Nat}
       {r : Result} (hrun : Steps P host (invoke s j args) c') (hc : c'.code = r.toAdmin) :
       r = .values [.i32 v] ∧ c'.store = s
   ```

   where `expected` is the Rust source read on `BitVec 32` (`Src.add a b = a + b`,
   `Src.max a b = if a.toInt < b.toInt then b else a`, `Src.mul a b = a * b`,
   `Src.odd a = a * 2 + 1`). The compiled code is not literally the source: `add`/`mul` swap
   their operands, `max` is `select` on `i32.gt_s`, `odd` is `(a << 1) | 1`; the proofs cover
   that (`select_gtS`, `shl_or_one`). `export_safe`: no run gets stuck or traps.

3. **The proptest properties, for the compiled export:**

   ```lean
   theorem add_comm_runs ... (x y : BitVec 32)
       (h₁ : Steps P host (invoke s₁ 0 [.i32 x, .i32 y]) c₁) (e₁ : c₁.code = r₁.toAdmin)
       (h₂ : Steps P host (invoke s₂ 0 [.i32 y, .i32 x]) c₂) (e₂ : c₂.code = r₂.toAdmin) :
       r₁ = r₂
   theorem add_assoc_runs ... -- add(add(x,y),z) and add(x,add(y,z)) return the same result
   theorem mul_comm_runs ...
   theorem max_runs ... : ∃ m, r = .values [.i32 m] ∧ x.toInt ≤ m.toInt ∧ y.toInt ≤ m.toInt ∧ (m = x ∨ m = y)
   theorem odd_runs ... : ∃ m, r = .values [.i32 m] ∧ m = x * 2 + 1 ∧ m.getLsbD 0 = true
   ```

4. **Sessions.** `adder_session : Session P adderI K adderI.store l → ∀ c ∈ l, Correct c`:
   in every closed-world sequence of export calls on one instance, against every environment
   `K`, every answer is the source's value.

All headline theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. Statements:
`Silmaril/Wasm/Examples/RustAdder/Thms.lean`; proofs: `Silmaril/Proofs/Wasm/Examples/RustAdder/`.

Build: `lake build --wfail Silmaril.Wasm.Examples.RustAdder.Thms`.

**Termination** is proved too: `export_total j : TFSpecAt P host j (exportSpec j)` and
`export_terminates : ¬ Diverges P host (invoke s j args)`, so no run diverges.

**Not proved:** anything about the exported memory or the `__stack_pointer` global (no
function touches them). The source-level proptests
are about the Rust source; the Lean theorems are about the compiled bytes. Nothing relates
the two except the differential test, so there is no translation validation.

`wasm-verify` (`lake build wasm-verify`) decodes the module and lists its exports
(`add`, `max`, `mul`, `odd`) and imports (none). Its properties are about import calls, so for
an import-free module it can only report `importOutOfRange`; it does not check the
arithmetic.

## Regenerating the Lean file

```sh
cargo run --manifest-path tools/wasm-to-lean/Cargo.toml -- \
  examples/wasm-demos/rust-adder/wasm/adder.wasm --namespace Silmaril.Wasm.Examples.RustAdder \
  --source '...' > Silmaril/Wasm/Examples/RustAdder/Defs.lean
```
