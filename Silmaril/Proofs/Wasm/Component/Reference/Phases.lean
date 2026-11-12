module

public import Silmaril.Proofs.Wasm.Component.Reference.DetRun
public import Silmaril.Proofs.Wasm.Component.Reference.FlatABI
public import Silmaril.Proofs.Wasm.Component.Reference.HostMap

/-!
# The two phases of an export call of `Simple.toRef`

`RefToSpecAll` is proved in two phases, which meet at the machine configuration reached by
instantiating `c.toRef` from the empty store:

* `afterInst P cs fs`: the host in control, the component store with the core store `cs`, one
  component instance and the component functions `fs`, nothing else;
* `liftedFt x`: the resolved function type of the lift of export `x` (parameters labelled
  `a, ax, …`, the first result type, synchronous), and `liftedFuncs addr c`: the lifted
  functions of the exports of `c`, at the core addresses `addr x.core`, with default options,
  in instance `0`;
* `InstPhase`: instantiation of `c.toRef` only reaches `afterInst`, with the core store of the
  module's instance (up to the host type, `Store.mapH`) and the export map
  `exportMap c` (the `i`-th export names function `i`);
* `CallPhase`: every behaviour of a call of the `j`-th function from `afterInst` is an outcome
  of `exportSpec`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Numerics (Profile)

/-- The resolved function type of the lift of export `x`. -/
def liftedFt (x : SimpleExport) : WIT.FuncType Empty RtId :=
  ⟨labels "a" (toClosedList x.ty.params), (toClosedList x.ty.results).head?, false⟩

/-- The lifted functions of the exports of `c`, at the core addresses `addr x.core`. -/
noncomputable def liftedFuncs (P : Profile) (addr : Nat → Nat) (c : Simple) :
    List (CFuncInst (core3P P)) :=
  c.exports.map fun x => .lifted (addr x.core) (liftedFt x) {} ⟨0⟩

/-- The configuration after instantiation: the host in control (in host state `h`), the core
store `cs`, one component instance and the component functions `fs`. -/
noncomputable def afterInstH {σ : Type} (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) (h : σ) : Machine.Config (core3P P) σ :=
  Config.init { core := cs, insts := [{}], funcs := fs } h

/-- The configuration after instantiation, with the host state `()`. -/
noncomputable abbrev afterInst (P : Profile) (cs : (core3P P).Store (CanonHost (core3P P)))
    (fs : List (CFuncInst (core3P P))) : Machine.Config (core3P P) Unit :=
  afterInstH P cs fs ()

/-- The function exports of the root instance: export `i` is function `i`. -/
def exportMap (c : Simple) : List (String × FuncId) :=
  c.exports.mapIdx fun i x => (x.name, ⟨i⟩)

/-- **The instantiation phase**: instantiating `c.toRef` from the empty store has no other
result than the instance whose configuration is `afterInst` with the instance's core store and
the lifted functions, and whose function exports are `exportMap c`. -/
def InstPhase : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : Simple), c.Good → c.Inst →
    ∃ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I ∧ Store.mapH (fun _ => 0) cs = I.store ∧
      ∀ r ∈ instBehaviours prof (refHost P) (initConfig ()) c.toRef [],
        r = .instance (afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩
          (exportMap c)

/-- **The call phase**: every behaviour of calling function `j` from `afterInst` on the
reference images of well-typed values is an outcome of the specification of export `j`. -/
def CallPhase : Prop :=
  ∀ (P : Profile) (prof : ProfileKind) (c : Simple), c.Good → c.FloatFree → c.Arity →
    ∀ (I : Silmaril.Wasm.Game.ScalarInstance) (cs : (core3P P).Store (CanonHost (core3P P))),
      c.mod.IsInst I → Store.mapH (fun _ => 0) cs = I.store →
      ∀ (j : Nat) (hj : j < c.exports.length) (vs : List Silmaril.Wasm.Component.Val),
        ValTy.checkList c.exports[j].ty.params vs = true →
        callBehaviours prof (refHost P)
            (afterInst P cs (liftedFuncs P (fun k => I.addrs.getD k 0) c)) ⟨0⟩ ⟨j⟩
            (vs.map toRefVal) ⊆
          exportSpec P c c.exports[j] vs

end Silmaril.Proofs.Wasm.Component.Reference
