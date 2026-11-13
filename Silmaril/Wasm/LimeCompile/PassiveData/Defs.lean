module

public import Silmaril.Wasm.LimeCompile.Preserve.Defs

/-!
# The container for passive data segments: definitions

An earlier step of the container track of the 3.0 → Lime compiler (docs/projects/wasm-wasi.md, "3.0 to Lime
compiler"). The fragment is **Lime1 plus passive data segments and `memory.init`** on memory 0.
Lime1 has neither: its data segments are active, and `memory.init` is a bulk-memory instruction
Lime1 leaves out. The container emulates them with Lime1 code:

* every data segment `y` gets a **helper function** `$init_y : [i32 i32 i32] → []` appended after
  the module's own functions. It holds the segment's bytes as code constants, so neither the
  memory nor the table changes;
* a passive data segment becomes an empty active segment at offset 0 of memory 0. This keeps the
  data index space, and hence the data addresses, the same. An empty active segment writes
  nothing; it only checks `0 ≤ |mem|`;
* `memory.init 0 y` becomes `call $init_y`. Active segments are dropped after instantiation, so
  `$init_y` uses the bytes of `y` if it is passive and no bytes if it is active.

`$init_y` (parameters `i`, `j`, `n`) mirrors Core 3.0's three `memory.init` rules:

```
if (i + n > 65536 · memory.size) or (j + n > |b|) then unreachable   ;; in i64, no overflow
if n ≠ 0 then
  i32.store8 i (b[j])                  ;; b[j]: a chain of `select`s over the constants of b
  call $init_y (i + 1) (j + 1) (n - 1)
```

The bounds are checked in `i64`, so neither sum can overflow, and before any write, as in the
source (`memory.init-oob` traps on an unchanged store). Every byte goes through the same
`i32.store8` as the source's `memory.init-succ` step, so the memories stay equal.

* `chain bs k`: the `select` chain that leaves `b[j]` on the stack (local 1 is `j`);
* `checkCode L`, `copyCode bs h`, `helperBody bs h`: the helper's code;
* `effBytes d`: the bytes `memory.init` can still read after instantiation;
* `rwI`, `rwL`: the rewrite of `memory.init 0 y`;
* `emuModule m`: the Core 3.0 module the container produces (helpers, types, data, bodies);
* **`compile m`**: `emuModule m` read back as Lime1 (`none` outside the fragment), and
  `compileP := limePres compile`, which leaves Lime-only modules unchanged;
* `exM`, `exDrop`: a module in the fragment and one outside it (`data.drop`).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.PassiveData

open Silmaril.Wasm

/-- The index with number `k` (taken modulo `2 ^ 32`). -/
def idx {κ : IndexKind} (k : Nat) : Idx κ := ⟨Fin.ofNat (2 ^ 32) k⟩

/-- `i32.const` of a byte. -/
def byteConst (b : UInt8) : Instr := .intConst .i32 (BitVec.ofNat 32 b.toNat)

/-- **The byte lookup**: with an accumulator on the stack and `j` in local 1, each byte `b` at
position `k` runs `i32.const b; local.get 1; i32.const k; i32.sub; select`. That keeps the
accumulator if `j - k ≠ 0` and replaces it by `b` otherwise. -/
def chain : List UInt8 → Nat → List Instr
  | [], _ => []
  | b :: bs, k =>
    [byteConst b, .localGet (idx 1), .intConst .i32 (BitVec.ofNat 32 k), .intBinOp .i32 .sub,
      .select none] ++ chain bs (k + 1)

/-- `local.get x; i64.extend_i32_u`. -/
def get64 (x : Nat) : List Instr := [.localGet (idx x), .convert (.extend .unsigned)]

/-- The bounds check: trap unless `i + n ≤ 65536 · pages` and `j + n ≤ L`, in `i64`. -/
def checkCode (L : Nat) : List Instr :=
  get64 0 ++ get64 2 ++ [.intBinOp .i64 .add,
    .memorySize (idx 0), .convert (.extend .unsigned), .intConst .i64 65536, .intBinOp .i64 .mul,
    .intRelOp .i64 (.gt .unsigned)] ++
  get64 1 ++ get64 2 ++ [.intBinOp .i64 .add,
    .intConst .i64 (BitVec.ofNat 64 L), .intRelOp .i64 (.gt .unsigned),
    .intBinOp .i32 .or, .if_ .empty [.unreachable] []]

/-- `i32.store8` at memory 0 with the zero memory argument (the store of `memory.init-succ`). -/
def store8I : Instr := .intStore .i32 (some .i8) (idx 0) ⟨0, 0⟩

/-- The `n ≠ 0` branch: store `b[j]` at `i`, then recurse on `i + 1`, `j + 1`, `n - 1`. -/
def stepCode (bs : List UInt8) (h : Nat) : List Instr :=
  [.localGet (idx 0), .intConst .i32 0] ++ chain bs 0 ++ [store8I,
    .localGet (idx 0), .intConst .i32 1, .intBinOp .i32 .add,
    .localGet (idx 1), .intConst .i32 1, .intBinOp .i32 .add,
    .localGet (idx 2), .intConst .i32 1, .intBinOp .i32 .sub,
    .call (idx h)]

/-- The copy: if `n ≠ 0`, one byte and the recursive call. -/
def copyCode (bs : List UInt8) (h : Nat) : List Instr :=
  [.localGet (idx 2), .if_ .empty (stepCode bs h) []]

/-- **The body of `$init_y`** for the bytes `bs`, calling itself at function index `h`. -/
def helperBody (bs : List UInt8) (h : Nat) : List Instr := checkCode bs.length ++ copyCode bs h

/-- The type of every helper, `[i32 i32 i32] → []`. -/
def helperType : V1.FuncType := ⟨[V1.ValType.i32, V1.ValType.i32, V1.ValType.i32], []⟩

/-- The bytes `memory.init` can read after instantiation: a passive segment keeps its bytes, an
active one has been dropped. -/
def effBytes (d : Data) : List UInt8 :=
  match d.mode with
  | .passive => d.bytes.data.toList
  | .active _ _ => []

/-- A data segment as the container emits it: passive becomes empty active at offset 0. -/
def emuData (d : Data) : Data :=
  match d.mode with
  | .passive => ⟨ByteArray.empty, .active (idx 0) [.intConst .i32 0]⟩
  | .active _ _ => d

set_option linter.unusedTactic false in
mutual
/-- The rewrite of one instruction: `memory.init 0 y` becomes `call (base + y)`. -/
def rwI (base : Nat) : Instr → Instr
  | .memoryInit x y => if x.toNat = 0 then .call (idx (base + y.toNat)) else .memoryInit x y
  | .block bt b => .block bt (rwL base b)
  | .loop bt b => .loop bt (rwL base b)
  | .if_ bt b₁ b₂ => .if_ bt (rwL base b₁) (rwL base b₂)
  | .tryTable bt cs b => .tryTable bt cs (rwL base b)
  | i => i
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- The rewrite of an instruction sequence. -/
def rwL (base : Nat) : List Instr → List Instr
  | [] => []
  | i :: is => rwI base i :: rwL base is
termination_by is => sizeOf is
decreasing_by all_goals simp_wf; all_goals omega
end

/-- The function index of the first helper: after every imported and defined function. -/
def helperBase (m : Module) : Nat := m.importedFunctions.length + m.funcs.length

/-- The helper of data segment number `y` of `m`. -/
def helperFunc (m : Module) (y : Nat) (d : Data) : Func :=
  { type := idx m.types.length, locals := [], body := helperBody (effBytes d) (helperBase m + y) }

/-- The rewrite of a function body. -/
def rwFunc (base : Nat) (f : Func) : Func := { f with body := rwL base f.body }

/-- The helpers of all data segments, in order. -/
def helpers (m : Module) : List Func :=
  ((List.range m.data.length).zip m.data).map fun p => helperFunc m p.1 p.2

/-- **The container's Core 3.0 module**: the helper type is appended to the types, the helpers to
the functions, passive segments become empty active ones, and `memory.init 0 y` calls helper
`y`. Imports, exports, globals, memories, tables, elements and start are unchanged. -/
def emuModule (m : Module) : Module :=
  { m with
    types := m.types ++ [helperType.toCoreRec]
    funcs := m.funcs.map (rwFunc (helperBase m)) ++ helpers m
    data := m.data.map emuData }

/-- **The passive-data container compiler**: emulate, check that the element segments are typed
`funcref`, and read back as Lime1 (which fails outside the fragment, e.g. on `data.drop`). -/
def compile (m : Module) : Option Lime1.Module :=
  if Preserve.ElemsCanon (emuModule m) then Lime1.Module.ofCore? (emuModule m) else none

/-- The Lime-preserving variant: Lime-only modules are returned unchanged. -/
def compileP : Preserve.Compiler := Preserve.limePres compile

/-! ## Examples -/

/-- A module with one passive segment `01 02 03` and an exported `f(d)` running
`memory.init 0 0 (d, 0, 3)`. -/
def exM : Module :=
  { types := [V1.FuncType.toCoreRec ⟨[V1.ValType.i32], []⟩]
    memories := [⟨.i32, ⟨1, none⟩⟩]
    funcs := [{ type := idx 0, locals := [], body := [.localGet (idx 0), .intConst .i32 0,
      .intConst .i32 3, .memoryInit (idx 0) (idx 0)] }]
    data := [⟨⟨#[1, 2, 3]⟩, .passive⟩]
    exports := [⟨"f", .func (idx 0)⟩] }

/-- The same module with `data.drop 0` after the copy (outside the fragment). -/
def exDrop : Module :=
  { exM with
    funcs := [{ type := idx 0, locals := [], body := [.localGet (idx 0), .intConst .i32 0,
      .intConst .i32 3, .memoryInit (idx 0) (idx 0), .dataDrop (idx 0)] }] }

end Silmaril.Wasm.LimeCompile.PassiveData
