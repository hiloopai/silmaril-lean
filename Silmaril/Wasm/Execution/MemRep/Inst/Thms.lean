module

public import Silmaril.Wasm.Execution.MemRep.Sim.Thms
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce
public import Silmaril.Wasm.Execution.Core.Exec.ExternAddrCheck
public import Silmaril.Wasm.SingleThreaded.Interface
import Silmaril.Proofs.Wasm.Execution.MemRepInst

/-! # Instantiation and the component accessors over a lawful representation

Instantiation and the store accessors of the component engine are generic in the memory
representation (`Store H R`). Reading every memory through `MemRep.toBytes` (`Store.toBytes`)
commutes with each of them:

* constant evaluation (`evalConst?_toBytes`) and `$evalglobals` (`evalGlobals?_toBytes`), at any
  `R`: they never read memory bytes;
* `$allocmodule` (`allocModule?_toBytes`): fresh memories are `MemRep.zeros`, whose bytes are
  zeros at a lawful `R`;
* segment initialisation (`initSegments?_toBytes`): `memory.init` writes through
  `MemRep.store`;
* allocation with segment code (`prepare?_toBytes`), direct instantiation
  (`instantiateDirect?_toBytes`) and single-allocation instantiation (`instantiateOnce?_toBytes`,
  the instantiation of the component engine `core3`);
* the principal type of an external address and the import check (`externAddrType?_toBytes`,
  `externAddrsOk?_toBytes`), at any `R`;
* the accessors of the component engine (`SingleThreaded.allocHost_toBytes`, `memSize?_toBytes`,
  `memAddrType?_toBytes`, `tableAddrType?_toBytes`, `memRead?_toBytes`, `memWrite?_toBytes`,
  `tableFunc?_toBytes`).

Laws are needed only where bytes are read or written. With the step simulation
(`Execution.MemRep.Sim.Thms`), this is every store operation of `Engine.core3`; the engine
simulation is `Engine.Core3K`.
-/

@[expose] public section

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R]

theorem evalConst?_toBytes (s : Store H R) (f : Frame) (e : Expr) :
    (evalConst? s f e).map (fun p => (p.1.toBytes, p.2)) = evalConst? s.toBytes f e :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.evalConst?_toBytes s f e).symm

theorem evalGlobals?_toBytes (s : Store H R) (f : Frame) (gs : List CGlobalType)
    (es : List Expr) :
    (evalGlobals? evalConst? s f gs es).map (fun p => (p.1.toBytes, p.2)) =
      evalGlobals? evalConst? s.toBytes f gs es :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.evalGlobals?_toBytes s f gs es).symm

theorem externAddrType?_toBytes (s : Store H R) (xa : ExternAddr) :
    externAddrType? s.toBytes xa = externAddrType? s xa :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.externAddrType?_toBytes s xa

theorem externAddrsOk?_toBytes (s : Store H R) (xas : List ExternAddr) (xts : List CExternType) :
    externAddrsOk? s.toBytes xas xts = externAddrsOk? s xas xts :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.externAddrsOk?_toBytes s xas xts

variable [LawfulMemRep R]

theorem allocModule?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr)
    (valsG : List Val) (refsT : List Ref) (refsE : List (List Ref)) :
    (allocModule? s m xas valsG refsT refsE).map (fun p => (p.1.toBytes, p.2)) =
      allocModule? s.toBytes m xas valsG refsT refsE :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.allocModule?_toBytes s m xas valsG refsT refsE).symm

theorem initSegments?_toBytes (s : Store H R) (f : Frame) (m : Module) :
    (initSegments? evalConst? s f m).map (fun p => (p.1.toBytes, p.2)) =
      initSegments? evalConst? s.toBytes f m :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.initSegments?_toBytes s f m).symm

theorem prepare?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr) :
    (prepare? evalConst? s m xas).map (fun p => (p.1.toBytes, p.2)) =
      prepare? evalConst? s.toBytes m xas :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.prepare?_toBytes s m xas).symm

theorem instantiateDirect?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr) :
    (instantiateDirect? s m xas).map (fun p => (p.1.toBytes, p.2)) =
      instantiateDirect? s.toBytes m xas :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.instantiateDirect?_toBytes s m xas).symm

/-- **Instantiation commutes with `toBytes`**: single-allocation instantiation on a lawful
representation, read through `toBytes`, is instantiation of the specification store. -/
theorem instantiateOnce?_toBytes (s : Store H R) (m : Module) (xas : List ExternAddr) :
    (instantiateOnce? s m xas).map (fun p => (p.1.toBytes, p.2)) =
      instantiateOnce? s.toBytes m xas :=
  (Silmaril.Proofs.Wasm.Execution.MemRepInst.instantiateOnce?_toBytes s m xas).symm

end Silmaril.Wasm.Execution.Core

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution (MemRep LawfulMemRep)

variable {H R : Type} [MemRep R]

theorem allocHost_toBytes (s : Store H R) (ft : V1.FuncType) (h : H) :
    allocHost s.toBytes ft h = ((allocHost s ft h).1.toBytes, (allocHost s ft h).2) := rfl

theorem memAddrType?_toBytes (s : Store H R) (a : Nat) :
    memAddrType? s.toBytes a = memAddrType? s a :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.memAddrType?_toBytes s a

theorem tableAddrType?_toBytes (s : Store H R) (a : Nat) :
    tableAddrType? s.toBytes a = tableAddrType? s a := rfl

theorem tableFunc?_toBytes (s : Store H R) (t i : Nat) :
    tableFunc? s.toBytes t i = tableFunc? s t i := rfl

variable [LawfulMemRep R]

theorem memSize?_toBytes (s : Store H R) (a : Nat) : memSize? s.toBytes a = memSize? s a :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.memSize?_toBytes s a

theorem memRead?_toBytes (s : Store H R) (a start len : Nat) :
    memRead? s.toBytes a start len = memRead? s a start len :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.memRead?_toBytes s a start len

theorem memWrite?_toBytes (s : Store H R) (a start : Nat) (bs : ByteArray) :
    memWrite? s.toBytes a start bs = (memWrite? s a start bs).map Store.toBytes :=
  Silmaril.Proofs.Wasm.Execution.MemRepInst.memWrite?_toBytes s a start bs

end Silmaril.Wasm.SingleThreaded
