module

public import Silmaril.Numeric.Libm.Catalogue.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Binaryen.Behaviour
public import Silmaril.Wasm.Binary.Core.Decode

/-!
# libm problems for WebAssembly modules

What it means for a Wasm module to export a valid `f` at a node of the libm
lattice (`Silmaril.Numeric.Libm.Lattice.Defs`), and to export a valid libm.

A module `m` is instantiated against no imports with silmaril-lean's executable
instantiation (`instantiateOnce?`, which runs the data and element segments; it
agrees with the specification's `$instantiate` on valid modules,
`instantiateDirect?_sound`), and its export `name` is called with the
embedder's `$invoke` under the Core 3.0 small-step semantics at a profile `P`
(`Silmaril.Wasm.Numerics.Profile`), with no host functions (`closedHost`; a libm
module imports nothing). A `double` is passed and returned as an `f64` value
with the same bits, a C `int` as an `i32`.

`FuncImplements P s a N`: the function at address `a` of the store `s`

* returns a `double` on every input (some run of `$invoke` ends in one value);
* never ends otherwise: every run that stops has returned one `double` (no trap,
  no stuck state, no other result shape);
* satisfies the node `N` for every way of resolving its nondeterminism: every
  `impl : α → F64` that picks, for each input, a value that some run returns,
  satisfies `N (Outcome.pure impl)`.

Nodes are per-input properties, so the last clause says that every value any run
can return meets the node. At a deterministic profile there is exactly one such
`impl`. Wasm has no floating-point environment, so only the value nodes apply:
`ExportsValid` asks for `Spec.ValidValues` (the special-case values and the
accuracy node), not for flags or `errno`.

`ExportsValidLibm P m p` is "`m` exports a valid libm at accuracy profile `p`":
one subproblem `ExportsValid P m S (Double.level p S.name)` per function of
`wasmCatalogue`. That catalogue holds every `double` function of
`Double.catalogue` with a scalar C signature: `ldexp` and `scalbn` take a C
`int`, so they are specified on `F64 × BitVec 32` (`Spec.comap`); `frexp` and
`modf` return through a pointer into linear memory and are not included.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.WasmExport

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm
open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## Encodings -/

/-- A `double` as a Wasm `f64` value, bit for bit. -/
def f64v (x : F64) : Val := .num ⟨.float .f64, x.bits.toBitVec⟩

/-- The Wasm arguments of a C argument list. -/
class WasmArgs (α : Type) where
  args : α → List Val

instance : WasmArgs F64 := ⟨fun x => [f64v x]⟩
instance : WasmArgs (F64 × F64) := ⟨fun p => [f64v p.1, f64v p.2]⟩
/-- `(double, int)`, as for `ldexp`. -/
instance : WasmArgs (F64 × BitVec 32) := ⟨fun p => [f64v p.1, Val.i32 p.2]⟩

/-! ## Calling an export -/

/-- The store after instantiating `m` against no imports, and the function address of
its export `name`. `none` if instantiation fails, `m` has a start function, or
`name` is not a function export. -/
def exportFunc? (m : Module) (name : String) : Option (Store Nat × Nat) :=
  match instantiateOnce? ({} : Store Nat) m [] with
  | some (s, f, none) =>
    match f.module.exports.find? (·.name == name) with
    | some ⟨_, .func a⟩ => some (s, a)
    | _ => none
  | _ => none

/-- No host functions. -/
abbrev noHost : HostSemantics Nat := Silmaril.Wasm.Binaryen.closedHost

/-- A run of `$invoke` of the function at `a` in `s` on `args` ends with the values `res`. -/
def Returns (P : Numerics.Profile) (s : Store Nat) (a : Nat) (args res : List Val) : Prop :=
  ∃ s' f', Steps P noHost (invoke s a args) ⟨s', f', vals res⟩

/-- A configuration that cannot step. -/
def Stopped (P : Numerics.Profile) (c : Config Nat) : Prop := ∀ c', ¬ Step P noHost c c'

/-- **The function at `a` implements a `double`-valued C function at node `N`.** -/
def FuncImplements {α : Type} [WasmArgs α] (P : Numerics.Profile) (s : Store Nat) (a : Nat)
    (N : (α → Outcome F64) → Prop) : Prop :=
  (∀ x : α, ∃ y, Returns P s a (WasmArgs.args x) [f64v y]) ∧
  (∀ (x : α) c, Steps P noHost (invoke s a (WasmArgs.args x)) c → Stopped P c →
    ∃ y, c.code = vals [f64v y]) ∧
  ∀ impl : α → F64, (∀ x : α, Returns P s a (WasmArgs.args x) [f64v (impl x)]) →
    N (Outcome.pure impl)

/-- **The export `name` of `m` implements a `double`-valued C function at node `N`.** -/
def Exports {α : Type} [WasmArgs α] (P : Numerics.Profile) (m : Module) (name : String)
    (N : (α → Outcome F64) → Prop) : Prop :=
  ∃ s a, exportFunc? m name = some (s, a) ∧ FuncImplements P s a N

/-! ## The lattice nodes, for a module -/

section Nodes

variable {α : Type} [WasmArgs α] (P : Numerics.Profile) (m : Module) (S : Spec α F64)

/-- (a) The special-case values of Annex F. -/
def ExportsSpecialValues : Prop := Exports P m S.name S.SpecialValues

/-- (b) Within `k` ulps of the exact result on the inputs `D`. -/
def ExportsErrorOn (D : Set α) (k : ℝ) : Prop := Exports P m S.name (S.ErrorOn · D k)

/-- (c) Within `k` ulps of the exact result everywhere. -/
def ExportsErrorGlobal (k : ℝ) : Prop := Exports P m S.name (S.ErrorGlobal · k)

/-- (d) Correctly rounded. -/
def ExportsCorrectlyRounded : Prop := Exports P m S.name S.CorrectlyRounded

/-- (d) Within `n` ulps of the correctly rounded result. -/
def ExportsCRWithin (n : ℝ) : Prop := Exports P m S.name (S.CRWithin · n)

/-- (d) Exact. -/
def ExportsExact : Prop := Exports P m S.name S.Exact

/-- (e) Bit for bit the pure Lean function `ref`. -/
def ExportsBitExact (ref : α → F64) : Prop := Exports P m S.name (BitExact · ref)

/-- (e) Bit for bit the partial pure Lean function `ref`, where it is defined. -/
def ExportsBitExactWhere (ref : α → Option F64) : Prop := Exports P m S.name (BitExactWhere · ref)

/-- **"`m` exports a valid `f` at accuracy `a`"**: the special-case values and the
accuracy node `a` (`Spec.ValidValues`). -/
def ExportsValid (a : Accuracy) : Prop := Exports P m S.name (S.ValidValues · a)

end Nodes

/-! ## Builds: the bytes of a module -/

/-- **The Wasm binary `b` exports `name` at node `N`**, at every deterministic profile (canonical
NaNs; `memory.grow` failures decided by any oracle): `b` decodes (silmaril-lean's binary
decoder) to a module whose export `name` implements `N`. -/
def BuildExports {α : Type} [WasmArgs α] (b : ByteArray) (name : String)
    (N : (α → Outcome F64) → Prop) : Prop :=
  match Binary.Core.Decode.decodeModule b with
  | .ok m => ∀ o, Exports (Numerics.Profile.deterministic o) m name N
  | .error _ => False

/-! ## Checkers for single-instruction functions

Executable recognisers of the function shapes that `Silmaril.Numeric.Libm.Wasm.Thms`
proves bit-exact (`buildExports_unop`, `buildExports_call_binop`). They only read the decoded
module and its instantiation; the theorems turn a `true` answer, obtained by kernel evaluation,
into the node. -/

/-- The store, address and function instance of export `name`. -/
def exportInst? (m : Module) (name : String) : Option (Store Nat × Nat × FuncInst Nat) :=
  (exportFunc? m name).bind fun (s, a) => s.funcs[a]?.map fun fi => (s, a, fi)

/-- The number of parameters and results of a function instance's type. -/
def arity (fi : FuncInst Nat) : Option (Nat × Nat) :=
  match fi.type.expand? with
  | some (.func ps rs) => some (ps.length, rs.length)
  | _ => none

/-- `op` if the body is `local.get 0; f64.op` with no locals. -/
def unopOf (fi : FuncInst Nat) : Option FloatUnOp :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet i, .floatUnOp .f64 op]⟩ => if i.toNat = 0 then some op else none
  | _ => none

/-- `op` if the body is `local.get 0; local.get 1; f64.op` with no locals. -/
def binopOf (fi : FuncInst Nat) : Option FloatBinOp :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet i, .localGet j, .floatBinOp .f64 op]⟩ =>
    if i.toNat = 0 ∧ j.toNat = 1 then some op else none
  | _ => none

/-- `k` if the body is `local.get 0; local.get 1; call k` with no locals. -/
def callOf (fi : FuncInst Nat) : Option FuncIdx :=
  match fi.code with
  | .wasm ⟨_, [], [.localGet i, .localGet j, .call k]⟩ =>
    if i.toNat = 0 ∧ j.toNat = 1 then some k else none
  | _ => none

/-- Export `name` of `m` is `local.get 0; f64.op` of type `[f64] → [f64]`-arity `1 → 1`. -/
def checkUnop (m : Module) (name : String) (op : FloatUnOp) : Bool :=
  match exportInst? m name with
  | some (_, _, fi) => decide (unopOf fi = some op ∧ arity fi = some (1, 1))
  | none => false

/-- Export `name` of `m` forwards its two arguments (`call k`) to a function whose body is
`local.get 0; local.get 1; f64.op`, both of arity `2 → 1`. -/
def checkCallBinop (m : Module) (name : String) (op : FloatBinOp) : Bool :=
  match exportInst? m name with
  | some (s, _, fi) =>
    match callOf fi with
    | some k =>
      match fi.module.funcs[k.toNat]? with
      | some b =>
        match s.funcs[b]? with
        | some gi => decide (binopOf gi = some op ∧ arity fi = some (2, 1) ∧ arity gi = some (2, 1))
        | none => false
      | none => false
    | none => false
  | none => false

/-- `checkUnop` on the module that `b` decodes to. -/
def checkUnopBytes (b : ByteArray) (name : String) (op : FloatUnOp) : Bool :=
  match Binary.Core.Decode.decodeModule b with
  | .ok m => checkUnop m name op
  | .error _ => false

/-- `checkCallBinop` on the module that `b` decodes to. -/
def checkCallBinopBytes (b : ByteArray) (name : String) (op : FloatBinOp) : Bool :=
  match Binary.Core.Decode.decodeModule b with
  | .ok m => checkCallBinop m name op
  | .error _ => false

/-! ## Whole libms -/

/-- A specification on other arguments: `S` read through `g`, for instance `ldexp` on a
C `int` exponent. -/
def _root_.Silmaril.Numeric.Libm.Spec.comap {α β τ : Type} (S : Spec α τ) (g : β → α) :
    Spec β τ where
  name := S.name
  exact := S.exact ∘ g
  special := S.special.map fun c =>
    { name := c.name, applies := c.applies ∘ g, expect := c.expect ∘ g, raises := c.raises,
      errno := c.errno }

/-- The C `int` exponent of `ldexp` and `scalbn`, as an integer. -/
def intArg (p : F64 × BitVec 32) : F64 × ℤ := (p.1, p.2.toInt)

/-- One function of a Wasm libm: its name and its validity problem at each accuracy. -/
structure WasmEntry where
  name : String
  valid : Accuracy → Numerics.Profile → Module → Prop

/-- The entry of a specification. -/
def wasmEntry {α : Type} [WasmArgs α] (S : Spec α F64) : WasmEntry where
  name := S.name
  valid a P m := ExportsValid P m S a

/-- The `double` functions with a scalar C signature: batch 1 without `frexp` and
`modf`, and batch 2. -/
noncomputable def wasmCatalogue : List WasmEntry :=
  [Double.fabs, Double.floor, Double.ceil, Double.trunc, Double.round, Double.rint,
      Double.nearbyint, Double.sqrt].map wasmEntry ++
  [Double.copysign, Double.fmod, Double.remainder, Double.fmin, Double.fmax].map wasmEntry ++
  [wasmEntry (Double.ldexp.comap intArg), wasmEntry (Double.scalbn.comap intArg)] ++
  Double.batch2Unary.map wasmEntry ++ [Double.pow, Double.hypot, Double.atan2].map wasmEntry

/-- **"`m` exports a valid `double` libm at accuracy profile `p`"**: one subproblem per
function of `wasmCatalogue`, at the level `Double.level p` assigns it. -/
def ExportsValidLibm (P : Numerics.Profile) (m : Module) (p : Double.Profile) : Prop :=
  ∀ e ∈ wasmCatalogue, e.valid (Double.level p e.name) P m

/-- **"The Wasm binary `b` exports a valid `double` libm at accuracy profile `p`"**, at every
deterministic profile. -/
def BuildValidLibm (b : ByteArray) (p : Double.Profile) : Prop :=
  match Binary.Core.Decode.decodeModule b with
  | .ok m => ∀ o, ExportsValidLibm (Numerics.Profile.deterministic o) m p
  | .error _ => False

end Silmaril.Numeric.Libm.WasmExport
