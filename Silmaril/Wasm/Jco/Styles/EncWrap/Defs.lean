module

public import Silmaril.Wasm.Jco.Styles.Enc.Defs
public import Silmaril.Wasm.Jco.Styles.Realloc.Defs
public import Silmaril.Wasm.Jco.Thin.Canon.Defs
public import Silmaril.Wasm.Jco.Wrap.Defs

/-!
# FFI styles with a string encoding: the wrapper, the thin wrapper and the C convention

A core module compiled from a language with UTF-16 or Latin-1/UTF-16 strings (FFI style 4,
one variant per `StrEnc`) follows the C convention of `Silmaril.Wasm.Jco.Meta`. Its strings are in
the encoding `enc`, as `(ptr, code units)` (tagged for `latin1+utf16`). The module has only a C
allocator `alloc(size, align)`.

* `wrapE md enc`: the wrapper. The adaptor's `cabi_realloc` is `reallocShimX`, the `realloc`
  that copies an old block, because transcoding shrinks and grows blocks. The export shims are
  those of `wrap`, and every lift has `string-encoding=enc`.
* `Meta.specE M md enc`: the C convention with the encoding `enc`. The caller stores each
  string argument by the canonical algorithm for `enc`, reallocating through `alloc` and a copy
  (`reallocEmuF`). A string result written to the out-pointer is read in the encoding `enc`.
* `thinE md r enc`: the thin wrapper of a module that exports a canonical `realloc` `r`;
  `canonSpecE M world r enc` is its convention (the canonical one with encoding `enc`).
* `Meta.specExact M md enc`: the **exact-copy** C convention. Each string is stored once, in a
  block of exactly its size in the encoding `enc`, allocated by `alloc(bytes, align)` (the
  alignment and bounds are checked as the canonical ABI checks them). `NoShrink enc s` says
  that the canonical algorithm allocates exactly that size for `s` and never calls `realloc`
  again: UTF-16 with `2 × (UTF-8 length)` bytes, or Latin-1 with every character below `2^7`.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat)

/-- The adaptor of the encoded wrapper. -/
def adaptorXOf (md : Meta) : XMod :=
  ⟨("cabi_realloc", reallocShimX md.alloc) :: md.world.map fun s => (s.name, (exportShim md s).toX)⟩

/-- A lift of `wrap` with an encoding. -/
def Lift.withEnc (enc : StrEnc) (l : Lift) : XLift := ⟨l.sig, l.callee, l.realloc, enc⟩

/-- **The wrapper with string encoding `enc`.** -/
def wrapE (md : Meta) (enc : StrEnc) : XComp :=
  { adaptor := adaptorXOf md, lifts := (liftsFrom 0 md.world).map (Lift.withEnc enc) }

/-- **The thin wrapper with string encoding `enc`** and the module's `realloc` `r`. -/
def thinE (md : Meta) (r : String) (enc : StrEnc) : XComp :=
  { lifts := md.world.map fun s => ⟨s, .core s.name, .core r, enc⟩ }

variable (M : CoreInst) (md : Meta)

namespace Meta

/-- A world function under the C convention with encoding `enc`. -/
def specCallE (enc : StrEnc) (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) := do
  let xs ← lowerParamsE M enc (reallocEmuF M md.alloc) sig.params vs
  if inMem sig.result then do
    let r ← M.call md.alloc [i32n 8, i32n 4]
    let o ← RM.ofOption (single32? r)
    let _ ← M.call sig.name (xs ++ [Flat.i32 o])
    liftResultE M enc sig.result [Flat.i32 o]
  else do
    let rs ← M.call sig.name xs
    liftResultE M enc sig.result rs

/-- **The C convention with string encoding `enc`.** -/
def specE (enc : StrEnc) (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig => md.specCallE M enc sig vs
  | none => RM.fail

/-- Store bytes in a fresh block of exactly their size, allocated by `alloc(len, al)`. -/
def exactBytes (al : Nat) (bs : List UInt8) (units : Nat) : RM M.St (List Flat) := do
  RM.check (decide (bs.length ≤ maxStringBytes))
  let r ← M.call md.alloc [i32n bs.length, i32n al]
  let p ← RM.ofOption (single32? r)
  checkAt M al bs.length p
  M.store p.toNat bs
  pure [Flat.i32 p, i32n units]

/-- A string stored by the exact-copy convention. -/
def exactStr : StrEnc → String → RM M.St (List Flat)
  | .utf8, s => md.specBytes M maxStringBytes (utf8 s)
  | .utf16, s => md.exactBytes M 2 (utf16Bytes s) ((utf16Bytes s).length / 2)
  | .latin1Utf16, s =>
    if latin1Prefix s = s.length then md.exactBytes M 2 (latin1Bytes s s.length) s.length
    else md.exactBytes M 2 (utf16Bytes s) ((utf16Bytes s).length / 2 ||| utf16Tag)

/-- One parameter under the exact-copy convention. -/
def exactParam (enc : StrEnc) : PTy → PVal → RM M.St (List Flat)
  | .string, .string s => md.exactStr M enc s
  | t, v => md.specParam M t v

/-- The parameters under the exact-copy convention. -/
def exactParams (enc : StrEnc) : List PTy → List PVal → RM M.St (List Flat)
  | [], [] => pure []
  | t :: ts, v :: vs => do
    let a ← md.exactParam M enc t v
    let b ← exactParams enc ts vs
    pure (a ++ b)
  | _, _ => RM.fail

/-- A world function under the exact-copy convention with encoding `enc`. -/
def specCallExact (enc : StrEnc) (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) := do
  let xs ← md.exactParams M enc sig.params vs
  if inMem sig.result then do
    let r ← M.call md.alloc [i32n 8, i32n 4]
    let o ← RM.ofOption (single32? r)
    let _ ← M.call sig.name (xs ++ [Flat.i32 o])
    liftResultE M enc sig.result [Flat.i32 o]
  else do
    let rs ← M.call sig.name xs
    liftResultE M enc sig.result rs

end Meta

/-- The canonical algorithm stores `s` with one allocation of its exact size. -/
def NoShrink : StrEnc → String → Bool
  | .utf8, _ => true
  | .utf16, s => (utf16Bytes s).length == 2 * (utf8 s).length
  | .latin1Utf16, s => latin1Prefix s == s.length && s.length == (utf8 s).length

/-- Every string argument satisfies `NoShrink`. -/
def NoShrinkArgs (enc : StrEnc) (vs : List PVal) : Prop :=
  ∀ s, PVal.string s ∈ vs → NoShrink enc s = true

/-- **The canonical convention with encoding `enc`** (the module's own `realloc` `r`). -/
def canonSpecE (world : List Sig) (r : String) (enc : StrEnc) (name : String)
    (vs : List PVal) : RM M.St (Option PVal) :=
  match world.find? (·.name == name) with
  | some s => canonCallE M enc (M.call r) (M.call s.name) s vs
  | none => RM.fail

/-- The module's `realloc` `r` behaves as the emulated `realloc` of its allocator. -/
def ReallocEmulates (r : String) : Prop :=
  ∀ a b c d : Nat, M.call r [i32n a, i32n b, i32n c, i32n d] =
    reallocEmuF M md.alloc [i32n a, i32n b, i32n c, i32n d]

end Silmaril.Wasm.Jco
