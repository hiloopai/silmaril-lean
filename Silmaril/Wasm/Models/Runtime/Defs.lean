module

public import Silmaril.Wasm.Models.Syntax.Defs
public import Silmaril.Wasm.Execution.Core.Step

/-!
# The runtime invariant of a feature set

Core 3.0 reduces some MVP instructions to 3.0 instructions:

* `call x` becomes `ref.func a; call_ref dt` (an administrative `call_ref` with a runtime type);
* `call_indirect x y` becomes `table.get x; ref.cast (ref null y); call_ref y`;
* `return_call_indirect x y` becomes `table.get x; ref.cast (ref null y); return_call_ref y`;
* `table.copy`/`table.init` become `table.get`/`table.set` steps.

So `Step` does not keep code in `Instr.InFeat S`. The runtime invariant `Rt.InFeat S c` allows
exactly these expansion forms (`Rt.instrB`), constants of every type (parameters, locals and
fields may hold values of any type), and the administrative instructions:

* `Rt.instrB S i`: `Instr.inFeatB S i`, or a constant, or an expansion form of an instruction
  of `S`;
* `Rt.AdmIn S a`, `Rt.CodeIn S l`: administrative code whose instructions pass `Rt.instrB`,
  label continuations `Instr.inFeatB`, and handlers only under `control` (a caught exception
  branches);
* `Rt.StoreIn S s`: every Wasm function of the store has a body of `S` (calls enter them);
* `Rt.HostIn S host`: host calls keep `StoreIn S` and throw only when `S` has exceptions;
  `Rt.HostKeeps host ∧ Rt.HostThrowsIn S host` is a sufficient condition that is monotone in
  `S` (the domain of the restricted charts);
* `Rt.InFeat S c := CodeIn S c.code ∧ StoreIn S c.store`.

`Thms`: `step_rtInFeat` (every profile, every host with `HostIn S`), and the instantiation
link `invoke_rtInFeat`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.Rt

open Silmaril.Wasm Silmaril.Wasm.Execution.Core FeatureSet

/-- An instruction allowed at runtime in code of `S`. -/
def instrB (S : FeatureSet) : Instr → Bool
  | .intConst _ _ | .floatConst _ _ | .vecConst _ => true
  | .callRef y => Instr.inFeatB S (.callRef y) || S.has .callIndirect
  | .returnCallRef y =>
      Instr.inFeatB S (.returnCallRef y) || (S.has .tailCall && S.has .callIndirect)
  | .refCast rt => Instr.inFeatB S (.refCast rt) || S.has .callIndirect
  | .tableGet x => Instr.inFeatB S (.tableGet x) ||
      ((S.has .callIndirect || S.has .bulkMemory) && tblIdxB S x)
  | .tableSet x => Instr.inFeatB S (.tableSet x) || (S.has .bulkMemory && tblIdxB S x)
  | i => Instr.inFeatB S i

mutual
/-- An administrative instruction of `S` at runtime. -/
def AdmIn (S : FeatureSet) : Admin → Prop
  | .plain i => instrB S i = true
  | .ref _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | .label _ cont body => Instr.insInFeatB S cont = true ∧ CodeIn S body
  | .handler _ _ body => S.has .control = true ∧ CodeIn S body
  | .frame _ _ body => CodeIn S body
  | .trap => True

/-- Administrative code of `S` at runtime. -/
def CodeIn (S : FeatureSet) : List Admin → Prop
  | [] => True
  | a :: as => AdmIn S a ∧ CodeIn S as
end

/-- Every Wasm function of the store has a body of `S`. -/
def StoreIn {H : Type} (S : FeatureSet) (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    Instr.insInFeatB S fn.body = true

/-- Host calls keep the store in `S`, and throw only when `S` has exceptions. -/
def HostIn {H : Type} (S : FeatureSet) (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → StoreIn S s →
    StoreIn S s' ∧ ∀ a, r = .throw a → S.has .exn = true

/-- Host calls never change the store's functions (the usual embedder: imports compute and
touch memories, tables and globals). -/
def HostKeeps {H : Type} (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → s'.funcs = s.funcs

/-- Host calls throw only when `S` has exceptions. -/
def HostThrowsIn {H : Type} (S : FeatureSet) (host : HostSemantics H) : Prop :=
  ∀ h s vs s' a, host h s vs (.returned s' (.throw a)) → S.has .exn = true

/-- **The runtime invariant**: the code and the store's functions are of `S`. -/
def InFeat {H : Type} (S : FeatureSet) (c : Config H) : Prop :=
  CodeIn S c.code ∧ StoreIn S c.store

end Silmaril.Wasm.Models.Rt
