module

public import Silmaril.Wasm.Jco.Styles.EncWrap.Defs
public import Silmaril.Wasm.Jco.Styles.Spill.Defs
public import Silmaril.Wasm.Jco.Styles.Wide.Defs

/-!
# One wrapper covering the FFI styles

The FFI styles of `Silmaril/Wasm/Jco/Styles` are separate variants: `wrapE md enc` (string
encodings), `wrapS md` (spilled parameters) and `wrapW md` (wide results in the multi-value
style). Each has its own adaptor and its own `canon lift`. `wrapU md enc` is **one wrapper
covering all three**. Each world function gets the style it needs:

* a function whose parameters spill (`spillOf`, more than `MAX_FLAT_PARAMS` scalar values) gets
  the spill shim and the spilling `canon lift` (`canonCallS`);
* otherwise a function with a wide result (`wideOf`, a record of scalars) gets the multi-value
  shim, with its parameters lowered at the encoding `enc` (`canonCallWE`). This is a new
  combination: the encoded string parameters and the wide result;
* any other function gets the plain export shim and the encoded `canon lift` (`canonCallE`).

The adaptor's `cabi_realloc` is the copying shim of `wrapE` (`reallocShimX`), which the
`utf16` and `latin1+utf16` encodings need. On the spilling and multi-value paths it is called
only with old pointer `0`, where it is the allocator.

The specification `Meta.specU M enc` dispatches in the same way, to `specCallSpill`,
`specCallMVE` (the multi-value style with encoded parameters) and `specCallE`.

**World imports.** `Silmaril.Wasm.Jco.Styles.Unified.Imports` adds the `canon lower`s of `wrapI`
to `wrapU` (`wrapUI`).

Not combined here: async lifts (`Silmaril/Wasm/Jco/Async`) and resources
(`Silmaril/Wasm/Jco/Resource`) live over other component types. `Silmaril.Wasm.Jco.Styles.Unified.Thms`
says where they meet.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy liftArgs)

/-- The export shim of a world function in the unified wrapper. -/
def exportShimU (md : Meta) (s : Sig) : XFn :=
  match spillOf s.params with
  | some (ts, ns) => spillShim s ts ns
  | none => exportShimW md s

/-- The adaptor of the unified wrapper. -/
def adaptorUOf (md : Meta) : XMod :=
  ⟨("cabi_realloc", reallocShimX md.alloc) :: md.world.map fun s => (s.name, exportShimU md s)⟩

/-- **The unified wrapper** with string encoding `enc`. -/
def wrapU (md : Meta) (enc : StrEnc) : XComp :=
  { adaptor := adaptorUOf md, lifts := (liftsFrom 0 md.world).map (Lift.withEnc enc) }

variable (M : CoreInst)

/-- `canon lift` with a wide result and parameters at the encoding `enc`. -/
def canonCallWE (enc : StrEnc) (R callee : List Flat → RM M.St (List Flat)) (sig : Sig)
    (vs : List PVal) : RM M.St (Option PVal) := do
  let xs ← lowerParamsE M enc R sig.params vs
  let rs ← callee xs
  liftResultW M sig.result rs

/-- **The unified `canon lift`**: spilling, wide results, or the encoded lift. -/
def canonCallU : LiftSem M := fun enc R callee sig vs =>
  match spillOf sig.params with
  | some _ => canonCallS M R callee sig vs
  | none =>
    match wideOf sig.result with
    | some _ => canonCallWE M enc R callee sig vs
    | none => canonCallE M enc R callee sig vs

namespace Meta

variable (md : Meta)

/-- The multi-value style with parameters at the encoding `enc`. -/
def specCallMVE (enc : StrEnc) (sig : Sig) (ts : List ValTy) (ns : List Nat) (vs : List PVal) :
    RM M.St (Option PVal) := do
  let xs ← lowerParamsE M enc (reallocEmuF M md.alloc) sig.params vs
  let rs ← M.call sig.name xs
  let r ← M.call md.alloc [i32n (tupleSize ns), i32n (tupleAlign ns)]
  let p ← RM.ofOption (single32? r)
  storeAll M (fieldWrites p.toNat ts (fieldOffs 0 ns) ns rs)
  RM.check (p.toNat % tupleAlign ns == 0)
  let s ← RM.get
  RM.check (decide (p.toNat + tupleSize ns ≤ (M.mem s).length))
  let v ← RM.ofOption (liftArgs ts rs)
  pure (some (.val (.record v)))

/-- One world function under the unified convention. -/
def specCallU (enc : StrEnc) (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) :=
  match spillOf sig.params with
  | some (ts, ns) => md.specCallSpill M sig ts ns vs
  | none =>
    match wideOf sig.result with
    | some (ts, ns) => md.specCallMVE M enc sig ts ns vs
    | none => md.specCallE M enc sig vs

/-- **The unified convention**: spilled parameters, wide results in the multi-value style, and
the C convention with string encoding `enc` for the rest. -/
def specU (enc : StrEnc) (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig => md.specCallU M enc sig vs
  | none => RM.fail

end Meta

end Silmaril.Wasm.Jco
