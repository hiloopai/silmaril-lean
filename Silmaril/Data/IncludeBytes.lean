module

public import Silmaril.Data.IncludeBytes.Types
public meta import Lean.Elab.Term

/-! # Including binary files as `ByteArray` terms

`include_bytes "path"` is the binary analogue of Lean core's `include_str`: it reads the file
at `path`, resolved relative to the directory of the current source file, at elaboration time
and elaborates to a `ByteArray` term denoting its contents.

```
def addWasm : ByteArray := include_bytes "fixtures/add.wasm"
```

It is the first step toward `wat!`-style macros for Wasm-accelerated proofs (#2296): a Wasm
binary can live next to the Lean file that reasons about it instead of being transcribed into
a hex literal.

## Representation

The term is `IncludeBytes.decode 4096 len [c₀, c₁, …]`: `len` is the file size and `cᵢ` is
the natural-number literal whose little-endian base-256 digits are the bytes of the `i`-th
4 KiB chunk of the file (`cᵢ = ∑ⱼ b₄₀₉₆ᵢ₊ⱼ · 256 ^ j`; the last chunk may be shorter). The
length is explicit because trailing zero bytes are invisible in a literal. The alternatives
considered were:

* a hex `String` literal decoded by a Lean function (`ofHex "0061736d…"`, as in #2297). A
  string literal is stored in the `.olean` as UTF-8, two bytes per file byte, and decoding it
  in the kernel goes through `String.toList`, a `Char` per hex digit and a parse per pair.
* a `ByteArray` literal: Lean has none. The kernel knows only `Nat` and `String` literals,
  and `ByteArray.mk #[0x00, 0x61, …]` is a term with one `UInt8` literal (an `OfNat`
  application) per byte, tens of bytes of `.olean` and an `Expr` node per file byte.
* a single `Nat` literal for the whole file. The `.olean` stores literals in binary, so this
  is the most compact (one byte per byte), but it has two quadratic costs. The compiler emits
  a `Nat` literal into C as a decimal string (`lean_cstr_to_nat("2545…")`), and converting a
  big number to decimal is superlinear: a computable 64 KiB include takes 8 s to build and a
  1 MiB one did not finish in 14 minutes. In the kernel, decoding divides the whole literal by
  256 once per byte; `decide +kernel` on a decoded 64 KiB file did not finish in 12 minutes.
* `Nat` literals of 4 KiB each (chosen). Storage stays binary (5 % overhead for the list
  cells and literal headers), C emission is linear in the number of chunks, and the kernel
  only ever divides 4 KiB numbers. GMP accelerates `Nat.div` and `Nat.mod` on literals in the
  kernel, so `decide` and `rfl` work on small files and `decide +kernel` decodes a 64 KiB file
  in under 20 s per goal.

Kernel checking `def x : ByteArray := include_bytes "…"` does not reduce `decode` at all: the
body is `decode` applied to literals, so including a large file costs only the literals.

## Measurements

Lean v4.35.0-rc4, uniformly random test files; sizes in bytes, build time is `lake build` of
the one-definition module. "computable" files also have a `.ir` file and, for chunked
literals, an `.olean.private` holding the compiler's closed terms.

| encoding                        | 64 KiB `.olean` | 1 MiB `.olean` | 1 MiB build    |
|---------------------------------|-----------------|----------------|----------------|
| hex `String`, computable        | 135008          | 2101088        | 2.6 s          |
| one `Nat`, noncomputable        | 69152           | 1052184        | 1.8 s          |
| one `Nat`, computable           | 70048           | 1053088        | > 14 min       |
| 4 KiB chunks, noncomputable     | 73088           | 1109888        | 3.0 s          |
| 4 KiB chunks, computable        | 73992           | 1110784        | 14 s           |
| 1 KiB chunks, computable        | 84744           | 1282816        | 8.6 s          |
| 16 KiB chunks, computable       | 71304           | 1067784        | 40 s           |

For the computable 1 MiB include with 4 KiB chunks, the `.ir` is 1182712 bytes and the
`.olean.private` 460048 bytes, against 2099800 bytes of `.ir` for hex. Evaluating it at run
time (decoding the megabyte and comparing it with the file) takes 1.8 s. A definition used
only in proofs should be `noncomputable`, which skips the compiled copy entirely.

4 KiB balances `.olean` overhead (22 % at 1 KiB, 1.4 % at 16 KiB) against the per-chunk
decimal conversion in C emission (40 s per MiB at 16 KiB).

## Correctness

`decode` is specified by the structural `bytesChunks` and `bytesLE` (`decode_eq`), and
`decode_encode` proves that it inverts the specification encoder `encode`, so
`decode c b.size (encode c b) = b` for every `b` and every chunk size `c > 0`. The
elaborator computes the chunk literals with a divide-and-conquer metaprogram (`encodeRange`,
`O(M(n) log n)` per chunk); it is not proved equal to `encode`, but nothing depends on that:
the term is whatever `decode` makes of the literals, and the examples in
`Silmaril.Data.IncludeBytesExamples` check by `decide` that it is the file.

At run time `bytesLE` is replaced (`@[csimp]`) by the divide-and-conquer `bytesLEFast`, proved
equal.

## Lake dependency tracking

Lake does not see the included file. A module's trace is its source, its imports, its
options and its library's `needs`; editing the file therefore does not rebuild the module
(the same holds for core's `include_str`). Touch the including `.lean` file after changing
the binary, or declare the file as an input of the library in `lakefile.toml`, which mixes
its hash into the trace of every module of that library (Lake fetches a library's `needs` and
`extraDepTargets` before its modules and mixes their traces into each module's trace):

```toml
[[input_file]]
name = "addWasm"
path = "Silmaril/Data/fixtures/add.wasm"

[[lean_lib]]
name = "…"
needs = ["addWasm"]
```

This repository does not declare its fixtures that way: `needs` on the `Silmaril` library
would rebuild every module whenever a fixture changes. Fixtures that change often belong in a
small separate `lean_lib` with its own `needs`.
-/

@[expose] public section

namespace Silmaril.IncludeBytes

/-- The number whose little-endian base-256 digits are `bs` (specification encoder). -/
def ofBytesLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * ofBytesLE bs

theorem ofBytesLE_cons (b : UInt8) (bs : List UInt8) :
    ofBytesLE (b :: bs) = b.toNat + 256 * ofBytesLE bs := rfl

@[simp] theorem bytesLE_zero (n : Nat) : bytesLE 0 n = [] := rfl

theorem bytesLE_succ (k n : Nat) : bytesLE (k + 1) n = UInt8.ofNat n :: bytesLE k (n / 256) :=
  rfl

@[simp] theorem length_bytesLE (k n : Nat) : (bytesLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bytesLE_succ, ih]

/-- The first `a + b` digits are the first `a` digits followed by the next `b`. -/
theorem bytesLE_add (a b n : Nat) :
    bytesLE (a + b) n = bytesLE a (n % 256 ^ a) ++ bytesLE b (n / 256 ^ a) := by
  induction a generalizing n with
  | zero => simp
  | succ a ih =>
    have hdvd : 2 ^ 8 ∣ 256 ^ (a + 1) :=
      ⟨256 ^ a, by show (256 : Nat) ^ (a + 1) = 256 * 256 ^ a; rw [Nat.pow_succ, Nat.mul_comm]⟩
    have hmod : n % 256 ^ (a + 1) % 2 ^ 8 = n % 2 ^ 8 := Nat.mod_mod_of_dvd n hdvd
    have h1 : UInt8.ofNat (n % 256 ^ (a + 1)) = UInt8.ofNat n := by
      rw [← UInt8.ofNat_mod_size (x := n % 256 ^ (a + 1)), hmod, UInt8.ofNat_mod_size]
    have h2 : n % 256 ^ (a + 1) / 256 = n / 256 % 256 ^ a := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ a) 256, Nat.mod_mul_right_div_self]
    have h3 : n / 256 ^ (a + 1) = n / 256 / 256 ^ a := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ a) 256, Nat.div_div_eq_div_mul]
    rw [show a + 1 + b = (a + b) + 1 by omega, bytesLE_succ (a + b), ih, bytesLE_succ a,
      List.cons_append, h1, h2, h3]

/-- `bytesLE` inverts the specification encoder. -/
theorem bytesLE_ofBytesLE : ∀ bs : List UInt8, bytesLE bs.length (ofBytesLE bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hdiv : (b.toNat + 256 * ofBytesLE bs) / 256 = ofBytesLE bs := by omega
    have hmod : (b.toNat + 256 * ofBytesLE bs) % 2 ^ 8 = b.toNat := by
      show (b.toNat + 256 * ofBytesLE bs) % 256 = b.toNat
      omega
    have hbyte : UInt8.ofNat (b.toNat + 256 * ofBytesLE bs) = b := by
      rw [← UInt8.ofNat_mod_size (x := b.toNat + 256 * ofBytesLE bs), hmod, UInt8.ofNat_toNat]
    rw [List.length_cons, ofBytesLE_cons, bytesLE_succ, hbyte, hdiv, bytesLE_ofBytesLE bs]

/-- Divide-and-conquer `bytesLE`: `O(M(n) log n)` instead of `len` big-number divisions.
It replaces `bytesLE` in compiled code (`bytesLE_eq_bytesLEFast`). -/
def bytesLEFast (len n : Nat) : List UInt8 :=
  if len ≤ 64 then bytesLE len n
  else bytesLEFast (len / 2) (n % 256 ^ (len / 2)) ++
    bytesLEFast (len - len / 2) (n / 256 ^ (len / 2))
termination_by len
decreasing_by all_goals omega

theorem bytesLEFast_eq (len : Nat) : ∀ n, bytesLEFast len n = bytesLE len n := by
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro n
    by_cases hl : len ≤ 64
    · rw [bytesLEFast, ite_eq_left hl]
    · rw [bytesLEFast, ite_eq_right hl, ih (len / 2) (by omega), ih (len - len / 2) (by omega),
        ← bytesLE_add, show len / 2 + (len - len / 2) = len by omega]

@[csimp] theorem bytesLE_eq_bytesLEFast : @bytesLE = @bytesLEFast := by
  funext len n
  exact (bytesLEFast_eq len n).symm

/-- Decode a list of chunk literals: each literal holds the next `chunk` bytes of a sequence of
length `len` (little-endian base 256), the last one holding what remains. -/
theorem bytesChunks_nil (chunk len : Nat) : bytesChunks chunk len [] = [] := rfl

theorem bytesChunks_cons (chunk len c : Nat) (cs : List Nat) :
    bytesChunks chunk len (c :: cs) =
      bytesLE (min chunk len) c ++ bytesChunks chunk (len - chunk) cs :=
  rfl

/-- The specification encoder: split `l` into chunks of `chunk` bytes, each read as a
little-endian base-256 number. -/
def encodeChunks (chunk : Nat) (l : List UInt8) : List Nat :=
  if _h : chunk = 0 ∨ l = [] then [] else
    ofBytesLE (l.take chunk) :: encodeChunks chunk (l.drop chunk)
termination_by l.length
decreasing_by
  obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (fun e => _h (Or.inr e))
  have := fun e => _h (Or.inl e)
  simp only [List.length_drop, List.length_cons]
  omega

/-- `bytesChunks` inverts the specification encoder. -/
theorem bytesChunks_encodeChunks {chunk : Nat} (hc : 0 < chunk) (l : List UInt8) :
    bytesChunks chunk l.length (encodeChunks chunk l) = l := by
  suffices ∀ n, ∀ l : List UInt8, l.length = n →
      bytesChunks chunk l.length (encodeChunks chunk l) = l from this _ l rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hl
    rcases l with _ | ⟨b, t⟩
    · rw [encodeChunks, dite_eq_left (Or.inr rfl), bytesChunks_nil]
    · have hne : ¬(chunk = 0 ∨ b :: t = []) := by
        intro h
        rcases h with h | h
        · omega
        · exact List.cons_ne_nil b t h
      have htake : (List.take chunk (b :: t)).length = min chunk (b :: t).length :=
        List.length_take
      have hdrop : (List.drop chunk (b :: t)).length = (b :: t).length - chunk :=
        List.length_drop
      have hlt : (b :: t).length - chunk < n := by
        rw [← hl, List.length_cons]
        omega
      rw [encodeChunks, dite_eq_right hne, bytesChunks_cons, ← htake, bytesLE_ofBytesLE, ← hdrop,
        ih _ hlt _ hdrop, List.take_append_drop]

/-- The specification encoder: the chunk literals of `b`. -/
def encode (chunk : Nat) (b : ByteArray) : List Nat := encodeChunks chunk b.data.toList

theorem decode_eq (chunk len : Nat) (cs : List Nat) :
    (decode chunk len cs).data.toList = bytesChunks chunk len cs := rfl

/-- `decode` inverts `encode`: an included file denotes its bytes. -/
theorem decode_encode {chunk : Nat} (hc : 0 < chunk) (b : ByteArray) :
    decode chunk b.size (encode chunk b) = b := by
  obtain ⟨⟨l⟩⟩ := b
  show ByteArray.mk ⟨bytesChunks chunk l.length (encodeChunks chunk l)⟩ = ByteArray.mk ⟨l⟩
  rw [bytesChunks_encodeChunks hc]

/-- The chunk size used by `include_bytes`, in bytes. -/
meta def chunkSize : Nat := 4096

/-- `ofBytesLE` of the bytes `b[lo:hi]`, by divide and conquer (`O(M(n) log n)`). -/
meta partial def encodeRange (b : ByteArray) (lo hi : Nat) : Nat :=
  if hi ≤ lo then 0
  else if hi - lo ≤ 64 then
    (List.range (hi - lo)).foldr (fun i acc => (b.get! (lo + i)).toNat + 256 * acc) 0
  else
    let mid := (lo + hi) / 2
    encodeRange b lo mid + (encodeRange b mid hi <<< (8 * (mid - lo)))

open Lean in
/-- The term `decode chunk b.size [c₀, c₁, …]` denoting `b`, with chunk literals `cᵢ`. -/
meta def includeExpr (b : ByteArray) (chunk : Nat) : Expr :=
  let nat := mkConst ``Nat
  let n := (b.size + chunk - 1) / chunk
  let cs := (List.range n).foldr (init := mkApp (mkConst ``List.nil [Level.zero]) nat)
    fun i acc =>
      let lit := encodeRange b (i * chunk) (min b.size ((i + 1) * chunk))
      mkApp3 (mkConst ``List.cons [Level.zero]) nat (mkNatLit lit) acc
  mkApp3 (mkConst ``decode) (mkNatLit chunk) (mkNatLit b.size) cs

open Lean Elab Term in
/-- Read the file `path`, resolved relative to the directory of the current Lean file. -/
meta def readRelative (path : String) : TermElabM ByteArray := do
  let ctx ← readThe Lean.Core.Context
  let srcPath := System.FilePath.mk ctx.fileName
  let some srcDir := srcPath.parent
    | throwError "cannot compute parent directory of `{srcPath}`"
  IO.FS.readBinFile (srcDir / path)

open Lean Elab Term in
/--
`include_bytes "path"` is the contents of the file `path`, resolved relative to the directory
of the current Lean file (as for core's `include_str`), as a `ByteArray`. The file is read
at elaboration time; if it cannot be read, elaboration fails.

```
def addWasm : ByteArray := include_bytes "fixtures/add.wasm"
example : addWasm.size = 41 := by decide
```

The term is `Silmaril.IncludeBytes.decode 4096 size [c₀, c₁, …]` with one `Nat` literal per
4 KiB chunk (see the module docstring for why). Lake does not rebuild the module when the
file changes unless the file is declared as an `input_file` that the library `needs`.
-/
elab (name := includeBytes) "include_bytes " path:str : term => do
  return includeExpr (← readRelative path.getString) chunkSize

end Silmaril.IncludeBytes
