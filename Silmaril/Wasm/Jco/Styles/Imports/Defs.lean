module

public import Silmaril.Wasm.Jco.Wrap.Defs

/-!
# World imports: `canon lower` through the adaptor

`wrap` of `Silmaril.Wasm.Jco.Wrap` covers worlds with exports only. This module adds **world
imports**. The core module now imports functions, so its behaviour depends on what they do:

* `ICoreInst`: a core instance whose exports' behaviour `call imps name args` is a function of
  the behaviour `imps` of its imports. `ICoreInst.inst M imps` is the `CoreInst` it is with those
  imports; `ICoreInst.ofCore N` is an import-free instance.
* `Host σ`: the host's implementation of the world's imports, on component values.
* `canonLowerWith put h sig`: `canon lower` of the host function `h` at `sig`, following
  `definitions.py` (`a25fc0b`) for the fragment. The flat arguments are lifted (a memory-free
  value by `ValTy.lift`; a string or `list<u8>` from a `(ptr, len)` pair: the bytes are read from
  memory, and a string is decoded as UTF-8, trapping when invalid). Then `h` is called and its
  result lowered: a memory-free result flat, after a type check. A string or `list<u8>` result is
  stored with `put` (a `realloc(0, 0, 1, len)` and a copy), and its `(ptr, len)` pair is written
  to the **return pointer**, the last flat argument (more than `MAX_FLAT_RESULTS = 1` flat
  results). The return pointer must be 4-aligned and in bounds.
* `may_leave`. The reference sets `may_leave = false` while it lowers values, so a `realloc`
  that calls an import traps. The model follows this: every `realloc` (and the C convention's
  copying `alloc`) runs over `M.inst noImports`, the instance whose imports all trap. This also
  makes the definition non-circular. Export shims run with the lowered imports.
* `IMeta`: metadata with world imports. **`wrapI md`** is `wrap md.toMeta` together with, for each
  imported function, a `canon lower` that uses the adaptor's `cabi_realloc`. No import shim is
  needed. The C convention for an import (strings and lists in `M`'s memory as `(ptr, len)`, a
  result in memory written to an out-pointer passed last) **is** the canonical lowering. The
  only difference is the allocator: the host copies a result in memory through `M`'s
  `alloc(len, 1)` (`IMeta.specImports`).
* `IComp.callExport`, `IMeta.spec`: the component's behaviour and the C convention with imports.

Not modelled: imports of interfaces, resources, async; lowering of floats does not canonicalise
NaNs; reentrance (`may_enter`) beyond `may_leave` during lowering.
-/

@[expose] public section

namespace Silmaril.Wasm.Jco

open Silmaril.Wasm.Component (Flat ValTy Val)

/-- Behaviours of a core instance's imports. -/
abbrev Imports (σ : Type) := String → List Flat → RM σ (List Flat)

/-- Imports that all trap. -/
def noImports {σ : Type} : Imports σ := fun _ _ => RM.fail

/-- A core instance whose exports' behaviour depends on its imports. -/
structure ICoreInst where
  St : Type
  mem : St → Mem
  setMem : St → Mem → St
  call : Imports St → String → List Flat → RM St (List Flat)

namespace ICoreInst

/-- The instance with the given imports. -/
abbrev inst (M : ICoreInst) (imps : Imports M.St) : CoreInst := ⟨M.St, M.mem, M.setMem, M.call imps⟩

/-- An instance without imports. -/
abbrev ofCore (N : CoreInst) : ICoreInst := ⟨N.St, N.mem, N.setMem, fun _ => N.call⟩

end ICoreInst

/-- The host's implementation of the world's imports. -/
abbrev Host (σ : Type) := String → List PVal → RM σ (Option PVal)

/-- Little-endian bytes of a `u32`. -/
def le32 (x : BitVec 32) : List UInt8 :=
  [(x.toNat % 256).toUInt8, (x.toNat / 256 % 256).toUInt8, (x.toNat / 65536 % 256).toUInt8,
    (x.toNat / 16777216 % 256).toUInt8]

variable (M : CoreInst)

/-- Lift one flat parameter of an imported function; the rest of the flat arguments. -/
def liftParamC : PTy → List Flat → RM M.St (PVal × List Flat)
  | .val t, xs =>
    match t.lift xs with
    | some (v, r) => pure (.val v, r)
    | none => RM.fail
  | .string, p :: l :: r => do
    let p ← RM.ofOption (asI32? p)
    let l ← RM.ofOption (asI32? l)
    RM.check (decide (l.toNat ≤ maxStringBytes))
    let bs ← M.load p.toNat l.toNat
    let s ← RM.ofOption (decodeUtf8 bs)
    pure (.string s, r)
  | .bytes, p :: l :: r => do
    let p ← RM.ofOption (asI32? p)
    let l ← RM.ofOption (asI32? l)
    let bs ← M.load p.toNat l.toNat
    pure (.bytes bs, r)
  | _, _ => RM.fail

/-- Lift the flat parameters of an imported function (all of them must be used). -/
def liftParamsC : List PTy → List Flat → RM M.St (List PVal)
  | [], [] => pure []
  | [], _ :: _ => RM.fail
  | t :: ts, xs => do
    let (v, r) ← liftParamC M t xs
    let vs ← liftParamsC ts r
    pure (v :: vs)

/-- Write a `(ptr, len)` pair to a 4-aligned return pointer. -/
def writePair (rp : Flat) (pq : List Flat) : RM M.St Unit := do
  let rp ← RM.ofOption (asI32? rp)
  RM.check (rp.toNat % 4 == 0)
  match pq with
  | [p, q] => do
    let p ← RM.ofOption (asI32? p)
    let q ← RM.ofOption (asI32? q)
    M.store rp.toNat (le32 p ++ le32 q)
  | _ => RM.fail

/-- Lower the host's result; `ret` are the flat arguments after the parameters (the return
pointer of a result in memory). -/
def lowerResC (put : Nat → List UInt8 → RM M.St (List Flat)) :
    Option PTy → Option PVal → List Flat → RM M.St (List Flat)
  | none, none, [] => pure []
  | some (.val t), some (.val v), [] => do
    RM.check (t.check v)
    pure (t.lower v)
  | some .string, some (.string s), [rp] => do
    let pq ← put maxStringBytes (utf8 s)
    writePair M rp pq
    pure []
  | some .bytes, some (.bytes bs), [rp] => do
    let pq ← put maxListBytes bs
    writePair M rp pq
    pure []
  | _, _, _ => RM.fail

/-- `canon lower` of a host function, storing results in memory with `put`. -/
def canonLowerWith (put : Nat → List UInt8 → RM M.St (List Flat))
    (h : List PVal → RM M.St (Option PVal)) (sig : Sig) (xs : List Flat) :
    RM M.St (List Flat) := do
  let n := (flatParams sig.params).length
  let vs ← liftParamsC M sig.params (xs.take n)
  let r ← h vs
  lowerResC M put sig.result r (xs.drop n)

/-- A `canon lower` of an imported function, with its `realloc`. -/
structure Lower where
  sig : Sig
  realloc : CRef
  deriving Repr, Inhabited, DecidableEq

/-- A wrapper-style component with world imports: exports as in `Comp`, and lowered imports. -/
structure IComp where
  comp : Comp
  lowers : List Lower
  deriving Repr, Inhabited

/-- WIT metadata with world imports. -/
structure IMeta extends Meta where
  imports : List Sig := []
  deriving Repr, Inhabited

namespace IComp

variable (M : ICoreInst) (H : Host M.St) (c : IComp)

/-- The imports the component gives the core instance: `canon lower`s, with every `realloc`
run over the instance without imports (`may_leave`). -/
def imps : Imports M.St := fun n =>
  match c.lowers.find? (·.sig.name == n) with
  | some lw =>
    canonLowerWith (M.inst noImports)
      (lowerBytes (M.inst noImports) (c.comp.callRef (M.inst noImports) lw.realloc)) (H n) lw.sig
  | none => noImports n

/-- The behaviour of calling the export `name`. -/
def callExport (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match c.comp.lifts.find? (·.sig.name == name) with
  | some l =>
    canonCall (M.inst (c.imps M H)) (c.comp.callRef (M.inst noImports) l.realloc)
      (c.comp.callRef (M.inst (c.imps M H)) l.callee) l.sig vs
  | none => RM.fail

end IComp

/-- **The monadic construction with world imports.** -/
def wrapI (md : IMeta) : IComp :=
  { comp := wrap md.toMeta, lowers := md.imports.map fun s => ⟨s, .adapt 0⟩ }

namespace IMeta

variable (M : ICoreInst) (H : Host M.St) (md : IMeta)

/-- The C convention's imports: `canon lower` with results copied through `alloc(len, 1)` of the
instance without imports. -/
def specImports : Imports M.St := fun n =>
  match md.imports.find? (·.name == n) with
  | some s => canonLowerWith (M.inst noImports) (md.specBytes (M.inst noImports)) (H n) s
  | none => noImports n

/-- A world export under the C convention with imports: parameters copied through `alloc` of
the instance without imports, the out-pointer allocated and the function called with the C
convention's imports. -/
def specCall (sig : Sig) (vs : List PVal) : RM M.St (Option PVal) := do
  let Mi := M.inst (md.specImports M H)
  let xs ← md.specParams (M.inst noImports) sig.params vs
  if inMem sig.result then do
    let r ← Mi.call md.alloc [i32n 8, i32n 4]
    let o ← RM.ofOption (single32? r)
    let _ ← Mi.call sig.name (xs ++ [Flat.i32 o])
    liftResult Mi sig.result [Flat.i32 o]
  else do
    let rs ← Mi.call sig.name xs
    liftResult Mi sig.result rs

/-- **M's behaviour at a world with imports**, under the C convention. -/
def spec (name : String) (vs : List PVal) : RM M.St (Option PVal) :=
  match md.world.find? (·.name == name) with
  | some sig => md.specCall M H sig vs
  | none => RM.fail

/-- `Meta.Conforms` with every choice of imports. -/
def Conforms : Prop := ∀ imps, md.toMeta.Conforms (M.inst imps)

end IMeta

end Silmaril.Wasm.Jco
