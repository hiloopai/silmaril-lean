# c-adder: compiled C exports, tested and verified

A freestanding C file (`src/adder.c`) compiled by today's `clang` to `wasm32`, with the
resulting module committed as `wasm/adder.wasm` (192 bytes).

| Export | C source | Compiled body (decoded) |
| --- | --- | --- |
| `add(a, b)` | `(uint32_t)a + (uint32_t)b` | `local.get 1; local.get 0; i32.add` |
| `mul(a, b)` | `(uint32_t)a * (uint32_t)b` | `local.get 1; local.get 0; i32.mul` |
| `max(a, b)` | `a < b ? b : a` | `local.get 0; local.get 1; local.get 0; local.get 1; i32.gt_s; select` |
| `odd(a)` | `(uint32_t)a * 2u + 1u` | `local.get 0; i32.const 1; i32.shl; i32.const 1; i32.or` |
| `popcount(x)` | Kernighan's loop: `while (x) { x &= x - 1; n++; }` | `local.get 0; i32.popcnt` |
| `gcd(a, b)` | Euclid: `while (b) { t = a % b; a = b; b = t; }` | a `block` (early return when `b = 0`), then a `loop` around `i32.rem_u` |

Two things clang does that a talk can point at: it recognises the popcount loop and replaces it
by the single instruction `i32.popcnt`, and it rotates Euclid's loop (test `b = 0` once up
front, then a do-while loop that keeps `b` in a fresh local).

The module also exports its linear memory (2 pages), defines the `__stack_pointer` global, and
has the one-entry `funcref` table that `wasm-ld` always emits; no function touches any of them.

## Build (reproducible)

```sh
./build-wasm.sh
# clang --target=wasm32 -mcpu=generic -O2 -ffreestanding -nostdlib \
#   -Wl,--no-entry -Wl,--strip-all -o target/adder.wasm src/adder.c, then cmp
```

* toolchain: `Ubuntu clang version 18.1.3 (1ubuntu1)`, `Ubuntu LLD 18.1.3` (`wasm-ld`);
* exports are chosen by `__attribute__((export_name(...)))` in the source;
* `sha256(wasm/adder.wasm) = 56650a65a27e9d30063f20e334622da35859cf1ab9a3163e3af027ed23a5ba43`.

## What is tested (not proved)

`harness/` (Rust) embeds the committed `wasm/adder.wasm` with `include_bytes!` and runs it with
the `wasmi` 0.40.0 interpreter. Its `build.rs` also compiles `src/adder.c` **natively** for the
host (`cc` crate 1.9.0, host C compiler, `-O2`), so the same C source can be run directly.

```sh
cargo test --release                                 # 11 tests, proptest 1.6.0
cargo run --release -p c-adder-harness --bin fuzz -- 5000000 0xc0ffee
```

* `source_*` proptests (10,000 cases each), on the **native build of the C source**:
  commutativity and associativity of `add`, commutativity of `mul`, `max` is an upper bound
  attained by an argument, `odd` is odd, `popcount` equals Rust's `u32::count_ones`, `gcd`
  equals an independent binary-GCD reference (`gcd_ref`) and divides both arguments. These are
  about the `.wasm` only if one trusts clang's wasm backend.
* `wasm_agrees_with_source` (10,000 cases), `wasm_boundary_cases` (all triples of 9 boundary
  values), `wasm_gcd_small` (10,000 cases with arguments below 2000) and `wasm_gcd_fibonacci`
  (consecutive Fibonacci numbers, Euclid's worst case): the **compiled** exports against the
  native build, plus commutativity/associativity of `add`, oddness of `odd`, `popcount` against
  `count_ones`, and `gcd` against `gcd_ref` and for symmetry, all on the compiled module.
* `fuzz`: a stable-toolchain fuzz loop (SplitMix64, half uniform and half boundary-biased
  inputs) running the same differential check; it exits non-zero on the first disagreement.
  Recorded run: `fuzz: 5000000 cases, seed 0xc0ffee: compiled adder.wasm agrees with the
  native C build`.

Testing samples finitely many inputs and trusts `wasmi` and the host C compiler.

## What is proved (Lean kernel, about the committed `.wasm` itself)

Statements: `Silmaril/Wasm/Examples/CAdder/Thms.lean`; proofs:
`Silmaril/Proofs/Wasm/Examples/CAdder/`. Build:
`lake build --wfail Silmaril.Wasm.Examples.CAdder.Thms`. All headline theorems depend only on
`propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no native evaluation).

1. **Ingestion.** `tools/wasm-to-lean` (Rust, `wasmparser` 0.219.1, untrusted) prints
   `Silmaril/Wasm/Examples/CAdder/Defs.lean`: the 192 bytes and the decoded `Module`. Then

   ```lean
   theorem decode_eq : Decode.decodeModule bytes = .ok module := by kernel_rfl
   theorem encodes : Encodes bytes.data.toList module := Decode.decodeModule_sound decode_eq
   theorem adderI_isInstance : ∃ mt, IsInstance module mt adderI
   ```

2. **Every export computes what the C source says, and terminates**, at every profile `P`
   and for every host relation (total correctness, `TWP`; partial correctness follows):

   ```lean
   theorem export_total (j : Nat) (hj : j < 6) : TFSpecAt P host j (exportSpec j)
   theorem export_valid (j : Nat) (hj : j < 6) : FSpecValid P host j (exportSpec j)
   theorem export_terminates ... : ¬ Diverges P host (invoke s j args)
   ```

   `expected` is the C source read on `BitVec 32`: `Src.add a b = a + b`, `Src.mul a b = a * b`,
   `Src.max a b = if a.toInt < b.toInt then b else a`, `Src.odd a = a * 2 + 1`,
   `Src.popcount x = x.cpop`, `Src.gcd a b = BitVec.ofNat 32 (Nat.gcd a.toNat b.toNat)`.

3. **Euclid's loop.** `gcd_twp` proves clang's rotated loop correct with the logic's loop rule
   (`TWP.loop`): invariant "`b ≠ 0` and `gcd a b` is the original gcd", variant `b` (each
   iteration replaces it by `a % b < b`); the `block` returns `a` early when `b = 0`, and
   `i32.rem_u` never traps because its divisor is the loop's non-zero `b`.

4. **The proptest properties, for the compiled exports:**

   ```lean
   theorem add_comm_runs ... : r₁ = r₂     -- runs of add x y and add y x
   theorem add_assoc_runs ... : r₁ = r₂    -- add (add x y) z and add x (add y z)
   theorem mul_comm_runs ... : r₁ = r₂
   theorem max_runs ... : ∃ m, r = .values [.i32 m] ∧ x.toInt ≤ m.toInt ∧ y.toInt ≤ m.toInt ∧ (m = x ∨ m = y)
   theorem odd_runs ... : ∃ m, r = .values [.i32 m] ∧ m = x * 2 + 1 ∧ m.getLsbD 0 = true
   theorem popcount_runs ... : ∃ m, r = .values [.i32 m] ∧ m = x.cpop ∧ m.toNat ≤ 32
   theorem gcd_runs ... : ∃ g, r = .values [.i32 g] ∧ g.toNat = Nat.gcd x.toNat y.toNat ∧
       g.toNat ∣ x.toNat ∧ g.toNat ∣ y.toNat ∧ ∀ d, d ∣ x.toNat → d ∣ y.toNat → d ∣ g.toNat
   theorem gcd_comm_runs ... : r₁ = r₂     -- runs of gcd x y and gcd y x
   ```

5. **Sessions.** `adder_session : Session P adderI K adderI.store l → ∀ c ∈ l, Correct c`.

**Not proved.** `Src.*` is a hand transcription of `src/adder.c`; nothing formally links the
Lean theorems to the C file (no translation validation), only the differential tests relate the
source to the compiled module. In particular `Src.popcount` is "the number of set bits": that
Kernighan's loop computes it is tested, not proved (clang replaced the loop by `i32.popcnt`).
Nothing is proved about the exported memory, the `__stack_pointer` global or the table.

## Regenerating the Lean file

```sh
cargo run --manifest-path tools/wasm-to-lean/Cargo.toml -- \
  examples/wasm-demos/c-adder/wasm/adder.wasm --namespace Silmaril.Wasm.Examples.CAdder \
  --source '`examples/wasm-demos/c-adder/wasm/adder.wasm` (Ubuntu clang 18.1.3, `--target=wasm32 -O2`, see that directory'"'"'s README)' \
  > Silmaril/Wasm/Examples/CAdder/Defs.lean
```
