module

public import Silmaril.Wasm.Jco.Wrap.Defs
public import Silmaril.Wasm.Jco.Thin.Canon.Defs

/-!
# FFI style: result pointers returned by the module (canonical retptr)

Under the C convention of `Silmaril.Wasm.Jco.Meta` (FFI style 1) a string or `list<u8>` result is
written to a **caller-allocated out-pointer** passed as the last argument. The canonical ABI
instead expects the callee to **return a pointer** to the `(ptr, len)` pair (`MAX_FLAT_RESULTS =
1`). This module adds the variant in between, FFI style 3, the **retptr style**: the module
exports `alloc(size, align)` as in the C convention, takes string and list parameters copied
through `alloc`, and returns result pointers itself.

* `Meta.retCall`, `Meta.retSpec`: the behaviour of a world function under the retptr style.
* `retComp md`: its wrapper. The only adaptor function is `cabi_realloc` (the `realloc` shim of
  `wrap`); every lift calls the module's export **directly** (no export shim).
* `recognizeRet md`: the partial recognizer of the retptr style. It always succeeds; what it
  recognizes is the metadata's claim that the module returns its result pointers. The thin
  wrapper `thinComp md r` applies when the module also exports a canonical `realloc` `r`.
* `retView M md`: the **out-pointer to retptr view** of a C-convention module. Each world
  function with a result in memory is replaced by `alloc(8, 4)`, the call with that out-pointer,
  and returning it, i.e. exactly what the export shim of `wrap` computes.
* `Meta.NoClash md r`: no world function with a result in memory is called `md.alloc` or `r`, so
  the view leaves the allocator and the `realloc` alone. It is decidable.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

variable (M : CoreInst) (md : Meta)

namespace Meta

/-- A world function under the retptr style: copy parameters through `alloc`, call, lift the
results (a result in memory comes back as a pointer to the pair). -/
def retCall (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) := do
  let xs ← md.specParams M sig.params vs
  let rs ← M.call sig.name xs
  liftResult M sig.result rs

/-- **The retptr style**: calling world function `name`. -/
def retSpec (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig => md.retCall M sig vs
  | none => RM.fail

/-- No world function with a result in memory is named `md.alloc` or `r`. -/
def NoClash (r : String) : Bool :=
  md.world.all fun s => !(inMem s.result && (s.name == md.alloc || s.name == r))

end Meta

/-- **The retptr wrapper**: the adaptor holds only `cabi_realloc`; each world function is the
`canon lift` of the module's own export. -/
def retComp : Comp :=
  { adaptor := ⟨[("cabi_realloc", reallocShim md.alloc)]⟩
    lifts := md.world.map fun s => ⟨s, .core s.name, .adapt 0⟩ }

/-- **Retptr recognition** (partial, but total on metadata that declares the retptr style). -/
def recognizeRet (retptr : Bool) : Option Comp := if retptr then some (retComp md) else none

/-- What the export shim of an out-pointer function computes, as a core function. -/
def outAsRet (name : String) (xs : List Flat) : RM M.St (List Flat) := do
  let r ← M.call md.alloc [i32n 8, i32n 4]
  let p ← RM.ofOption (single32? r)
  let _ ← M.call name (xs ++ [Flat.i32 p])
  pure [Flat.i32 p]

/-- The call of the out-pointer to retptr view. -/
def retViewCall (name : String) (xs : List Flat) : RM M.St (List Flat) :=
  match md.world.find? (·.name == name) with
  | some s => if inMem s.result then outAsRet M md name xs else M.call name xs
  | none => M.call name xs

/-- **The out-pointer to retptr view** of a C-convention module. -/
def retView : CoreInst := { M with call := retViewCall M md }

end Silmaril.Wasm.Jco
