module

public import Silmaril.Numeric.Libm.Wasm.Defs
public import Silmaril.Numeric.Libm.Lattice.Thms
import Silmaril.Proofs.Numeric.Libm.Wasm

/-!
# libm problems for Wasm modules: theorems

* `Exports.mono`, `BuildExports.mono`: an export's node weakens along any implication of nodes,
  so every edge of the lattice (`Silmaril.Numeric.Libm.Lattice.Thms`) holds for exports.
* `funcImplements_unop`: at every deterministic profile, a function whose body is
  `local.get 0; f64.op` (no locals, arity `1 → 1`) is bit-exact with `floatUnOp64 op`
  (`F64.abs`, `F64.floor`, `F64.ceil`, `F64.trunc`, `F64.nearest`, `F64.sqrt`, `F64.neg`).
* `funcImplements_call_binop`: a function whose body is `local.get 0; local.get 1; call k`,
  where `k` is `local.get 0; local.get 1; f64.op`, is bit-exact with `floatBinOp64 op`
  (`F64.copySign`, …). This is the shape of Rust's `#[no_mangle]` wrappers.
* `buildExports_unop`, `buildExports_call_binop`: the same for the export of a Wasm binary,
  from a `true` answer of the executable recognisers `checkUnopBytes`/`checkCallBinopBytes`
  (decoding, instantiation and the recognisers run in the kernel).

The proofs (`Silmaril.Proofs.Numeric.Libm.Wasm`) build one run of `$invoke` with silmaril-lean's
existential calculus (`WasmSpec.Computes`, `FuncSpec.of_body`, `wp_call`) and use uniqueness of
normal forms at the deterministic profile (`Silmaril.Wasm.Binaryen.steps_det_nf`) for every
other run. Under `Profile.spec` (nondeterministic NaN payloads) nothing is proved here.
-/

@[expose] public section

namespace Silmaril.Numeric.Libm.WasmExport

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

theorem Exports.mono {α : Type} [WasmArgs α] {P : Numerics.Profile} {m : Module} {name : String}
    {N N' : (α → Outcome F64) → Prop} (h : Exports P m name N) (hN : ∀ i, N i → N' i) :
    Exports P m name N' :=
  Proofs.Numeric.Libm.WasmExport.Exports.mono h hN

theorem BuildExports.mono {α : Type} [WasmArgs α] {b : ByteArray} {name : String}
    {N N' : (α → Outcome F64) → Prop} (h : BuildExports b name N) (hN : ∀ i, N i → N' i) :
    BuildExports b name N' :=
  Proofs.Numeric.Libm.WasmExport.BuildExports.mono h hN

variable {o : GrowKind → Nat → Nat → Nat → Bool}

theorem funcImplements_unop {s : Store Nat} {a : Nat} {fi : FuncInst Nat} {ty : TypeIdx}
    {op : FloatUnOp} {ps rs : Ty (.list .val)} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .floatUnOp .f64 op]⟩)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 1) (hrs : rs.length = 1) :
    FuncImplements (α := F64) (Profile.deterministic o) s a (BitExact · (floatUnOp64 op)) :=
  Proofs.Numeric.Libm.WasmExport.funcImplements_unop hfi hcode he hps hrs

theorem funcImplements_call_binop {s : Store Nat} {a b : Nat} {fi gi : FuncInst Nat}
    {ty ty' : TypeIdx} {k : FuncIdx} {op : FloatBinOp} {ps rs ps' rs' : Ty (.list .val)}
    (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm ⟨ty, [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .call k]⟩)
    (he : Expand fi.type (.func ps rs)) (hps : ps.length = 2) (hrs : rs.length = 1)
    (hk : fi.module.funcs[k.toNat]? = some b) (hgi : s.funcs[b]? = some gi)
    (hcode' : gi.code = .wasm ⟨ty', [], [.localGet ⟨0⟩, .localGet ⟨1⟩, .floatBinOp .f64 op]⟩)
    (he' : Expand gi.type (.func ps' rs')) (hps' : ps'.length = 2) (hrs' : rs'.length = 1) :
    FuncImplements (α := F64 × F64) (Profile.deterministic o) s a
      (BitExact · (fun p => floatBinOp64 op p.1 p.2)) :=
  Proofs.Numeric.Libm.WasmExport.funcImplements_call_binop hfi hcode he hps hrs hk hgi hcode' he'
    hps' hrs'

theorem exports_unop {m : Module} {name : String} {op : FloatUnOp}
    (h : checkUnop m name op = true) :
    Exports (α := F64) (Profile.deterministic o) m name (BitExact · (floatUnOp64 op)) :=
  Proofs.Numeric.Libm.WasmExport.exports_unop h

theorem exports_call_binop {m : Module} {name : String} {op : FloatBinOp}
    (h : checkCallBinop m name op = true) :
    Exports (α := F64 × F64) (Profile.deterministic o) m name
      (BitExact · (fun p => floatBinOp64 op p.1 p.2)) :=
  Proofs.Numeric.Libm.WasmExport.exports_call_binop h

/-- **A Wasm binary whose export `name` is `local.get 0; f64.op` exports `floatUnOp64 op`, bit
for bit**, at every deterministic profile. -/
theorem buildExports_unop {b : ByteArray} {name : String} {op : FloatUnOp}
    (h : checkUnopBytes b name op = true) :
    BuildExports (α := F64) b name (BitExact · (floatUnOp64 op)) :=
  Proofs.Numeric.Libm.WasmExport.buildExports_unop h

/-- **A Wasm binary whose export `name` forwards to `local.get 0; local.get 1; f64.op` exports
`floatBinOp64 op`, bit for bit**, at every deterministic profile. -/
theorem buildExports_call_binop {b : ByteArray} {name : String} {op : FloatBinOp}
    (h : checkCallBinopBytes b name op = true) :
    BuildExports (α := F64 × F64) b name (BitExact · (fun p => floatBinOp64 op p.1 p.2)) :=
  Proofs.Numeric.Libm.WasmExport.buildExports_call_binop h

end Silmaril.Numeric.Libm.WasmExport
