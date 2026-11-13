module

public import Silmaril.Wasm.Jco.Styles.Wide.Defs
public import Silmaril.Wasm.Jco.Styles.Enc.Defs

/-!
# Spilling more than `MAX_FLAT_PARAMS` flat parameters

`Sig.Ok` of the first fragment excludes signatures with more than `MAX_FLAT_PARAMS = 16` flat
parameters. For those, `canon lift` (`lower_flat_values`, `definitions.py`, `a25fc0b`) stores the
parameters as a tuple in a block from `realloc(0, 0, alignment, size)`. It traps unless the
block is aligned and in bounds, and passes the callee **one `i32` pointer**.

The fragment here: every parameter is a scalar (`bool`, integers, floats, `char`), laid out as in
`Silmaril.Wasm.Jco.Styles.Wide`. Storing a scalar (`store_int` and friends) writes the low bytes
of its flat lowering: a `bool` is 0 or 1, a signed integer is in two's complement, a `char` is its
code point. The result is memory-free and not wide.

* `spillOf ps`: the field types and sizes of a spilled parameter list.
* `lowerSpill`, `canonCallS`: `canon lift` with spilled parameters (and the first fragment
  otherwise).
* **The C convention with many parameters** (FFI style 6): the core function takes all of them
  flat, as a C compiler for a wasm target with no parameter limit does. `Meta.specCallSpill` is
  this convention together with the block that the canonical ABI allocates through `alloc` and
  writes.
* `spillShim md s ts ns`: the adaptor's export shim. It loads each field from the pointer it
  receives (`i32.load8_s`, `i32.load16_u`, `i64.load`, `f32.load`, and so on) and calls the function
  with them. `wrapS md` is `wrap`'s construction with these shims for spilled signatures.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)
open Silmaril.Wasm (NumType)

/-- A scalar parameter type. -/
def scalarParam : PTy → Option ValTy
  | .val t => (scalarSize t).map fun _ => t
  | _ => none

/-- A spilled parameter list: more than `MAX_FLAT_PARAMS` flat parameters, all scalars. -/
def spillOf (ps : List PTy) : Option (List ValTy × List Nat) :=
  if maxFlatParams < (flatParams ps).length then do
    let ts ← ps.mapM scalarParam
    let ns ← ts.mapM scalarSize
    pure (ts, ns)
  else none

/-- The component values of scalar parameters. -/
def PVal.val? : PVal → Option Val
  | .val v => some v
  | _ => none

/-- Whether a scalar type is loaded sign-extended. -/
def signedTy : ValTy → Bool
  | .s8 | .s16 => true
  | _ => false

variable (M : CoreInst)

/-- The canonical spilling of scalar parameters through `realloc`. -/
def lowerSpill (R : List Flat → RM M.St (List Flat)) (ts : List ValTy) (ns : List Nat)
    (vals : List Val) : RM M.St (List Flat) := do
  RM.check (ValTy.checkList ts vals)
  let p ← reallocCall M R 0 0 (tupleAlign ns) (tupleSize ns)
  checkAt M (tupleAlign ns) (tupleSize ns) p
  storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns (ValTy.lowerList ts vals))
  pure [Flat.i32 p]

/-- **`canon lift` with spilled parameters.** -/
def canonCallS (R callee : List Flat → RM M.St (List Flat)) (sig : Sig) (vs : List PVal) :
    RM M.St (Option PVal) :=
  match spillOf sig.params with
  | some (ts, ns) => do
    let vals ← RM.ofOption (vs.mapM PVal.val?)
    let xs ← lowerSpill M R ts ns vals
    let rs ← callee xs
    liftResult M sig.result rs
  | none => canonCall M R callee sig vs

namespace Meta

variable (md : Meta)

/-- A world function with spilled parameters under the C convention: all parameters flat, after
the block the canonical ABI allocates with `alloc(size, align)` and writes. -/
def specCallSpill (sig : Sig) (ts : List ValTy) (ns : List Nat) (vs : List PVal) :
    RM M.St (Option PVal) := do
  let vals ← RM.ofOption (vs.mapM PVal.val?)
  RM.check (ValTy.checkList ts vals)
  let r ← M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)]
  let p ← RM.ofOption (single32? r)
  checkAt M (tupleAlign ns) (tupleSize ns) p
  storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns (ValTy.lowerList ts vals))
  let rs ← M.call sig.name (ValTy.lowerList ts vals)
  liftResult M sig.result rs

/-- **The C convention with spilled parameters** (other functions: `Meta.specCall`). -/
def specS (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig =>
    match spillOf sig.params with
    | some (ts, ns) => md.specCallSpill M sig ts ns vs
    | none => md.specCall M sig vs
  | none => RM.fail

end Meta

/-! ## The wrapper -/

/-- Load fields `j, j + 1, …` from the pointer in local 0. -/
def spillLoads : List ValTy → List Nat → List Nat → List XInstr
  | t :: ts, o :: os, n :: ns =>
    [.base (.localGet 0), .load (t.flat.headD (.int .i32)) n (signedTy t) o] ++ spillLoads ts os ns
  | _, _, _ => []

/-- The export shim of a function with spilled parameters. -/
def spillShim (s : Sig) (ts : List ValTy) (ns : List Nat) : XFn :=
  { params := 1, body := spillLoads ts (fieldOffs 0 ns) ns ++ [.base (.call s.name ts.length)] }

/-- The export shim of a world function, spilling where needed. -/
def exportShimS (md : Meta) (s : Sig) : XFn :=
  match spillOf s.params with
  | some (ts, ns) => spillShim s ts ns
  | none => (exportShim md s).toX

/-- **The wrapper with spilled parameters.** -/
def wrapS (md : Meta) : XComp :=
  { adaptor := ⟨("cabi_realloc", (reallocShim md.alloc).toX) ::
      md.world.map fun s => (s.name, exportShimS md s)⟩
    lifts := (liftsFrom 0 md.world).map fun l => ⟨l.sig, l.callee, l.realloc, .utf8⟩ }

end Silmaril.Wasm.Jco
