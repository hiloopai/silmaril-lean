module

public import Silmaril.Wasm.Verify.Check.Defs
public import Silmaril.Wasm.Verify.Kernel.Defs
public import Silmaril.Wasm.Auto.Bridge.Defs
public import Silmaril.Wasm.Auto.Front.Defs

@[expose] public section

/-!
# Kernel-cheap instantiation of decoded modules

The certificates of `wasm-check` decide statements about `Silmaril.Wasm.Verify.instance? m`
by kernel evaluation (`decide +kernel`, `kernel_rfl`). Measurements
(`docs/projects/wasm-binaryen-tooling.md`) show two costs besides decoding binaries (which `wat3b!` terms avoid):

* **every kernel evaluation validates both modules again**: a certificate of an optimizer run
  evaluates `instance?` in every chunk of exports and every e-graph lift (18 times for the
  Binaryen `-O2` run of the `opt-in` corpus), and validation (`validate?`, silmaril-lean's
  checker) is nearly all of the cost of `instance?` on decoded modules;
* **memory is quadratic in the kernel**: a data segment is copied byte by byte by
  `memoryInitLoop`, each byte by `Memory.store`, whose `ByteArray.copySlice` the kernel reduces
  through `Array.extract.loop` and `Array.push` (`List.concat`); a 24-byte segment into a
  one-page memory did not finish in 44 GB. Comparing two memories (`decide (A.bytes = B.bytes)`
  in `Bridge.sumCheckX`) goes through `Array.isEqv`, which indexes the list at every position
  (a one-page memory exceeded 20 GiB).

This topic gives the same functions with those costs removed, each proved equal to the
specification one (`Silmaril.Wasm.Auto2.Kernel.Thms`):

* `memoryInitLoopK`: `memoryInitLoop` in closed form: one `writeL` of the whole segment into the
  list of bytes (linear, lazy in the part of the memory after the segment) under the same bounds
  checks; outside the fast path (an address range that wraps) it is `memoryInitLoop` itself;
  `tableInitLoopK` is the same for element segments (`tableInitLoop`: one `List.set` of the table
  per element);
* `initDataSegK?`, `initDataListK?`, `initSegmentsK?`, `prepareDirectK?`, `instantiateOnceK?`:
  the segment initialisation and the instantiation with `memoryInitLoopK`
  (`instantiateOnceK?_eq : instantiateOnceK? = instantiateOnce?`);
* `instK? m`: the scalar instance of an import-free module **without validating it**
  (`instK?_eq`: equal to `instance?`'s whenever `validate? m` succeeds, so a certificate proves
  `(validate? m).isSome` once and every later evaluation skips validation; modules with imports
  fall back to `instance?`);
* `bytesEqL`: equality of two byte lists by list recursion (`bytesEqL_eq`), and `sumCheckXK`,
  `checkAmongXK`, `liftAmongK`, `fnBodyK?`, `cexWithK`: the front end's checks over `instK?`
  (`checkAmongX_eq_K`, `liftAmong_eq_K`, `fnBody?_eq_K`, `cexWith_eq_K`).

Memory is thereby **lazy** in the kernel: the memory of an instance is the term
`writeL (List.replicate n 0) off seg`, and the kernel unfolds `List.replicate` only as far as
an access, a bounds check or a comparison reaches. A comparison of two whole memories is linear.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Auto2.Kernel

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Verify.Kernel (writeL lenGe)
open Silmaril.Wasm.Game (ScalarInstance)

variable {H : Type}

/-! ## Data segments in closed form -/

/-- The bytes of a memory after writing `seg` at `i`, as a list (`writeL`). -/
noncomputable def writeSeg (mi : MemInst) (i : Nat) (seg : List UInt8) : ByteArray :=
  ⟨⟨writeL mi.bytes.data.toList i seg⟩⟩

/-- The fast path of `memory.init`: both ranges in bounds, and neither address range wraps. -/
noncomputable def initFast (mi : MemInst) (di : DataInst) (w i j n : Nat) : Bool :=
  lenGe mi.bytes.data.toList (i + n) && lenGe di.bytes.data.toList (j + n) &&
    decide (i + n < 2 ^ w) && decide (j + n < 2 ^ 32)

/-- **`memoryInitLoop` in closed form**: on the fast path, the whole segment is written by one
`writeL` (the result is unchanged when `n = 0`); otherwise `memoryInitLoop` itself. -/
noncomputable def memoryInitLoopK (s : Store H) (f : Frame) (x : MemIdx) (y : DataIdx)
    (a : AddrType) (i : BitVec a.intType.width) (j n : BitVec 32) : Option (Store H) :=
  match s.mem? f x, s.data? f y with
  | some (ma, mi), some (_, di) =>
    if initFast mi di a.intType.width i.toNat j.toNat n.toNat then
      if n.toNat = 0 then some s
      else
        let b := writeSeg mi i.toNat ((di.bytes.data.toList.drop j.toNat).take n.toNat)
        some (s.setMem ma { mi with bytes := b })
    else memoryInitLoop s f x y a i j n
  | _, _ => memoryInitLoop s f x y a i j n

/-! ## Element segments in closed form -/

/-- The fast path of `table.init`: both ranges in bounds, and neither address range wraps. -/
noncomputable def tinitFast (ti : TableInst) (ei : ElemInst) (w i j n : Nat) : Bool :=
  lenGe ti.refs (i + n) && lenGe ei.refs (j + n) && decide (i + n < 2 ^ w) &&
    decide (j + n < 2 ^ 32)

/-- **`tableInitLoop` in closed form**: on the fast path, the whole segment is written by one
`writeL` of the references (the result is unchanged when `n = 0`); otherwise `tableInitLoop`
itself. -/
noncomputable def tableInitLoopK (s : Store H) (f : Frame) (x : TableIdx) (y : ElemIdx)
    (a : AddrType) (i : BitVec a.intType.width) (j n : BitVec 32) : Option (Store H) :=
  match s.table? f x, s.elem? f y with
  | some (ta, ti), some (_, ei) =>
    if tinitFast ti ei a.intType.width i.toNat j.toNat n.toNat then
      if n.toNat = 0 then some s
      else
        some (s.setTable ta
          { ti with refs := writeL ti.refs i.toNat ((ei.refs.drop j.toNat).take n.toNat) })
    else tableInitLoop s f x y a i j n
  | _, _ => tableInitLoop s f x y a i j n

/-- `initElemSeg? evalConst?` with `tableInitLoopK`. -/
noncomputable def initElemSegK? (s : Store H) (f : Frame) (k : Nat) (e : Elem) :
    Option (Store H) :=
  match e.mode with
  | .passive => some s
  | .declarative => elemDrop? s f ⟨Fin.ofNat _ k⟩
  | .active y off =>
    match evalConst? s f off with
    | none => none
    | some (s₁, v) =>
      match v.addr? with
      | none => none
      | some ⟨a, i⟩ =>
        match tableInitLoopK s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 e.init.length) with
        | none => none
        | some s₂ => elemDrop? s₂ f ⟨Fin.ofNat _ k⟩

/-- `initElemList? evalConst?` with `initElemSegK?`. -/
noncomputable def initElemListK? : Store H → Frame → List (Nat × Elem) → Option (Store H)
  | s, _, [] => some s
  | s, f, (k, e) :: es =>
    match initElemSegK? s f k e with
    | none => none
    | some s₁ => initElemListK? s₁ f es

/-- `initDataSeg? evalConst?` with `memoryInitLoopK`. -/
noncomputable def initDataSegK? (s : Store H) (f : Frame) (k : Nat) (d : Data) :
    Option (Store H) :=
  match d.mode with
  | .passive => some s
  | .active y off =>
    match evalConst? s f off with
    | none => none
    | some (s₁, v) =>
      match v.addr? with
      | none => none
      | some ⟨a, i⟩ =>
        match memoryInitLoopK s₁ f y ⟨Fin.ofNat _ k⟩ a i 0 (BitVec.ofNat 32 d.bytes.size) with
        | none => none
        | some s₂ => dataDrop? s₂ f ⟨Fin.ofNat _ k⟩

/-- `initDataList? evalConst?` with `initDataSegK?`. -/
noncomputable def initDataListK? : Store H → Frame → List (Nat × Data) → Option (Store H)
  | s, _, [] => some s
  | s, f, (k, d) :: ds =>
    match initDataSegK? s f k d with
    | none => none
    | some s₁ => initDataListK? s₁ f ds

/-- `initSegments? evalConst?` with `initElemListK?` and `initDataListK?`. -/
noncomputable def initSegmentsK? (s : Store H) (f : Frame) (m : Module) :
    Option (Store H × Frame) :=
  match (initElemListK? s f ((List.range m.elems.length).zip m.elems)).map (·, f) with
  | none => none
  | some (s₁, f₁) => (initDataListK? s₁ f₁ ((List.range m.data.length).zip m.data)).map (·, f₁)

/-- `prepareDirect? evalConst?` (`instantiateDirect?`) with `initSegmentsK?`. -/
noncomputable def prepareDirectK? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × Frame × Option FuncIdx) :=
  match prepare? evalConst? s m xas with
  | none => none
  | some (c, st) =>
    match initSegmentsK? c.store c.frame m with
    | none => none
    | some (s', f') => some (s', f', st)

/-- `instantiateOnce?` with `prepareDirectK?`. -/
noncomputable def instantiateOnceK? (s : Store H) (m : Module) (xas : List ExternAddr) :
    Option (Store H × Frame × Option FuncIdx) :=
  match evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) with
  | none => none
  | some (s₁, _, _) =>
    prepareDirectK? s₁ m.globalResidue (xas ++ globalAddrs s.globals.length m.globals.length)

/-! ## The instance without validation -/

/-- `Silmaril.Wasm.Verify.instImps` with `instantiateOnceK?`. -/
noncomputable def instImpsK (m : Module) (mt : CModuleType) (imps : List Silmaril.Wasm.Game.FnType) :
    Option (CModuleType × ScalarInstance) :=
  match instantiateOnceK? (Silmaril.Wasm.Game.importStore (CExternType.funcs mt.imports)) m
      ((List.range mt.imports.length).map ExternAddr.func) with
  | some (s, f, none) => Silmaril.Wasm.Verify.instFrom mt imps s f
  | _ => none

/-- **The scalar instance of a module, without validation**: for an import-free module, the
instantiation of `instance?` (with `instantiateOnceK?`) on the empty module type; with imports,
`instance?` itself. Equal to `instance?`'s instance when `validate? m` succeeds (`instK?_eq`). -/
noncomputable def instK? (m : Module) : Option ScalarInstance :=
  if m.imports.isEmpty then (instImpsK m ⟨[], []⟩ []).map (·.2)
  else (Silmaril.Wasm.Verify.instance? m).map (·.2)

/-! ## The front end's checks over `instK?` -/

/-- Equality of byte lists by list recursion (`bytesEqL_eq`). -/
noncomputable def bytesEqL (l : List UInt8) : List UInt8 → Bool :=
  List.rec (motive := fun _ => List UInt8 → Bool)
    (fun r => match r with | [] => true | _ :: _ => false)
    (fun a _ ih r => match r with | [] => false | b :: r => Nat.beq a.toNat b.toNat && ih r) l

open Silmaril.Wasm.Auto.Bridge in
/-- `sumCheckX` with the memories compared by `bytesEqL`. -/
noncomputable def sumCheckXK : Option FnSumX → Option FnSumX → Bool
  | some A, some B =>
    A.params == B.params && decide (A.gvals = B.gvals) &&
      (!(usesMem A.final || usesMem B.final) ||
        bytesEqL A.bytes.data.toList B.bytes.data.toList) &&
      guardSub A.final.guards B.final.guards && guardSub B.final.guards A.final.guards &&
      decide (Silmaril.Wasm.Auto.Equiv.canonSlots A.final.stack =
        Silmaril.Wasm.Auto.Equiv.canonSlots B.final.stack)
  | _, _ => false

open Silmaril.Wasm.Auto in
/-- `Bridge.checkAmong` over `instK?` and with `sumCheckXK`. -/
noncomputable def checkAmongXK (m₁ m₂ : Module) (js : List Nat) : List Bool :=
  match instK? m₁, instK? m₂ with
  | some I₁, some I₂ =>
    js.map fun j =>
      Bridge.sumCheck Bridge.discharged (Bridge.fnSumI I₁ j) (Bridge.fnSumI I₂ j) ||
        sumCheckXK (Bridge.fnSumXI I₁ j) (Bridge.fnSumXI I₂ j)
  | _, _ => []

open Silmaril.Wasm.Auto in
/-- `Bridge.liftAmong` over `instK?`. -/
noncomputable def liftAmongK (m₁ m₂ : Module) (js : List Nat) : List (Option (List IntType)) :=
  match instK? m₁, instK? m₂ with
  | some I₁, some I₂ => js.map (Bridge.liftCheckI I₁ I₂)
  | _, _ => []

open Silmaril.Wasm.Auto in
/-- `Bridge.fnBody?` over `instK?`. -/
noncomputable def fnBodyK? (m : Module) (j : Nat) : Option (List IntType × List Instr) :=
  match instK? m with
  | some I => Bridge.fnBodyI I j
  | none => none

open Silmaril.Wasm.Auto.Front in
/-- `Front.cexWith` over `instK?`. -/
noncomputable def cexWithK (run : Runner) (R : Rel) (impl spec : Module) (j : Nat)
    (vs : List Val) : Bool :=
  match instK? impl, instK? spec with
  | some I₁, some I₂ =>
    match paramsOf I₁ j, paramsOf I₂ j with
    | some ps₁, some ps₂ =>
      Silmaril.Wasm.Spec.typedB ps₁ vs && Silmaril.Wasm.Spec.typedB ps₂ vs &&
        match outOf run I₁.store (I₁.addrs.getD j 0) vs,
            outOf run I₂.store (I₂.addrs.getD j 0) vs with
        | some r₁, some r₂ => badPair R r₁ r₂
        | _, _ => false
    | _, _ => false
  | _, _ => false

end Silmaril.Wasm.Auto2.Kernel
