module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.InstGlobInit

/-!
# The global-free residue of a Lime1 module, at every store

The component work instantiates a module with globals through its residue `Lime1Inst.residueL`
(the globals turned into trailing global imports), prepared against a store holding the
evaluated globals; it does so from the empty store with no imports (`Lime1Inst.prepare?_residue`).
This module does the same from **any** store and import list:

* `gstore L gis`: `L` with the global instances `gis` appended;
* `gimports imps n k`: `imps` followed by the global addresses `n, …, n + k - 1`;
* **`prepare?_residueG`**: if the module's initializers evaluate to `vals` (in the instance
  `allocate?` uses), preparing the residue against `gstore L (globalInsts l.globals vals)` and
  `gimports imps |L.globals| |l.globals|` is preparing `l` against `L` and `imps`: same store,
  module instance and start code;
* **`importsMatch_residueG`**: the residue's imports match there, given `ImportsMatch L l imps`
  and typed initializers;
* `storeOk_appendGlobals`: Core's `StoreOk` is kept by appending well-typed global instances
  (through Core's store extension `Extend`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.InstG

open Silmaril.Wasm Silmaril.Wasm.Lime1 Silmaril.Wasm.Lime1.Validation
open Silmaril.Wasm.Execution.Runtime (Value ModuleInst GlobalInst ExternVal)
open Silmaril.Proofs.Wasm.Component.Lime1Inst (residueL globalInsts importsMatch_globals
  forall₂_imp_mem)

variable {H : Type}

/-- `L` with the global instances `gis` appended. -/
def gstore (L : Lime1.Execution.Store H) (gis : List GlobalInst) : Lime1.Execution.Store H :=
  { L with globals := L.globals ++ gis }

/-- `imps` followed by the global addresses `n, …, n + k - 1`. -/
def gimports (imps : List ExternVal) (n k : Nat) : List ExternVal :=
  imps ++ (List.range' n k).map fun i => .global ⟨i⟩

theorem importedInstance_gimports (imps : List ExternVal) (n k : Nat) :
    Lime1.Execution.importedInstance (gimports imps n k) =
      { Lime1.Execution.importedInstance imps with
        globals := (Lime1.Execution.importedInstance imps).globals ++
          Lime1.Execution.addresses .global n k } := by
  simp [Lime1.Execution.importedInstance, gimports, List.filterMap_append, List.filterMap_map,
    Lime1.Execution.addresses, List.range'_eq_map_range, Function.comp_def]

/-- **Allocating the residue against the evaluated globals is allocating the module.** -/
theorem allocate?_residueG {L : Lime1.Execution.Store H} {l : Lime1.Module}
    {imps : List ExternVal} {vals : List Value}
    (hvals : l.globals.mapM (fun g => Lime1.Execution.constExpr? L
      { globals := (Lime1.Execution.importedInstance imps).globals } g.init) = some vals) :
    Lime1.Execution.allocate? (gstore L (globalInsts l.globals vals)) (residueL l)
        (gimports imps L.globals.length l.globals.length) =
      Lime1.Execution.allocate? L l imps := by
  simp only [Lime1.Execution.allocate?, importedInstance_gimports, residueL, gstore,
    List.mapM_nil, hvals, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    List.length_nil, List.append_nil, Lime1.Execution.addresses_zero, List.zipWith_nil_left,
    List.length_append]
  rfl

/-- **Preparing the residue against the evaluated globals is preparing the module.** -/
theorem prepare?_residueG {L : Lime1.Execution.Store H} {l : Lime1.Module}
    {imps : List ExternVal} {vals : List Value}
    (hvals : l.globals.mapM (fun g => Lime1.Execution.constExpr? L
      { globals := (Lime1.Execution.importedInstance imps).globals } g.init) = some vals) :
    Lime1.Execution.prepare? (gstore L (globalInsts l.globals vals)) (residueL l)
        (gimports imps L.globals.length l.globals.length) =
      Lime1.Execution.prepare? L l imps := by
  simp only [Lime1.Execution.prepare?, allocate?_residueG hvals]
  rfl

/-! ## The residue's imports match -/

/-- Appending globals keeps a matched external value matched. -/
theorem externMatches_gstore {L : Lime1.Execution.Store H} {gis : List GlobalInst}
    {e : ExternVal} {et : V1.ExternType} (h : Lime1.Execution.ExternMatches L e et) :
    Lime1.Execution.ExternMatches (gstore L gis) e et := by
  cases h with
  | func a fn ft hf ht => exact .func a fn ft hf ht
  | table a t tt hf hl => exact .table a t tt hf hl
  | memory a m mt hf hl => exact .memory a m mt hf hl
  | global a g gt hf ht hm =>
    exact .global a g gt (by
      simp only [gstore]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hf).1]
      exact hf) ht hm

/-- **The residue's imports match** against the evaluated globals. -/
theorem importsMatch_residueG {L : Lime1.Execution.Store H} {l : Lime1.Module}
    {imps : List ExternVal} {vals : List Value} (hi : Lime1.Execution.ImportsMatch L l imps)
    (hT : List.Forall₂ (fun g v => v.type = g.type.value) l.globals vals) :
    Lime1.Execution.ImportsMatch (gstore L (globalInsts l.globals vals)) (residueL l)
      (gimports imps L.globals.length l.globals.length) := by
  have hS : ∀ i, i < l.globals.length →
      (gstore L (globalInsts l.globals vals)).globals[L.globals.length + i]? =
        (globalInsts l.globals vals)[i]? := fun i _ => by
    simp only [gstore]
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  have hm := importsMatch_globals (types := l.types) L.globals.length hT hS
  unfold Lime1.Execution.ImportsMatch
  simp only [residueL, gimports]
  exact List.rel_append (hi.imp fun _ _ ⟨et, h₁, h₂⟩ => ⟨et, h₁, externMatches_gstore h₂⟩) hm

/-- The initializer values have their declared types, when the imports match. -/
theorem vals_typed {L : Lime1.Execution.Store H} {l : Lime1.Module}
    {imps : List ExternVal} {vals : List Value} (hv : ModuleValid l)
    (hi : Lime1.Execution.ImportsMatch L l imps)
    (hvals : l.globals.mapM (fun g => Lime1.Execution.constExpr? L
      { globals := (Lime1.Execution.importedInstance imps).globals } g.init) = some vals) :
    List.Forall₂ (fun g v => v.type = g.type.value) l.globals vals :=
  forall₂_imp_mem (fun g hg _ hgv => constExpr?_typeG (globalsTyped_of_importsMatch hi)
    (hv.globals g hg).typed hgv) (Lime1.Execution.mapM_forall₂ hvals)

/-! ## Core `StoreOk` with appended globals -/

open Silmaril.Wasm.Execution.Core in
/-- A list extended by appending. -/
theorem extendsList_append {α : Type} {R : α → α → Prop} (hR : ∀ x, R x x) (l l' : List α) :
    ExtendsList R l (l ++ l') :=
  ⟨by simp, fun i x h => ⟨x, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1,
    h], hR x⟩⟩

open Silmaril.Wasm.Execution.Core in
/-- Appending globals extends a typed store. -/
theorem extend_appendGlobals {S : Store H} (hS : StoreOk S) (gs : List Silmaril.Wasm.Execution.Core.GlobalInst) :
    Extend S { S with globals := S.globals ++ gs } :=
  let e := Extend.refl hS
  { e with globals := extendsList_append (fun _ => ⟨rfl, .inr rfl⟩) _ _ }

open Silmaril.Wasm.Execution.Core in
/-- Immutable reachability reads no global. -/
theorem immutReachable_appendGlobals {S : Store H} {gs : List Silmaril.Wasm.Execution.Core.GlobalInst}
    {a b : FieldVal} (h : ImmutReachable { S with globals := S.globals ++ gs } a b) :
    ImmutReachable S a b := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | refExn hs hv => exact .refExn hs hv
  | refExtern r => exact .refExtern r

open Silmaril.Wasm.Execution.Core in
/-- A function instance stays typed when globals are appended. -/
theorem funcInstOk_appendGlobals {S : Store H} (hS : StoreOk S)
    {gs : List Silmaril.Wasm.Execution.Core.GlobalInst} {fi : FuncInst H}
    (h : FuncInstOk S fi) : FuncInstOk { S with globals := S.globals ++ gs } fi := by
  cases h with
  | wasm hdt hm hc hf hs => exact .wasm hdt (hm.extend hS (extend_appendGlobals hS gs)) hc hf hs
  | host hdt he hc => exact .host hdt he hc

open Silmaril.Wasm.Execution.Core in
/-- **Appending typed globals keeps Core's `StoreOk`.** -/
theorem storeOk_appendGlobals {S : Store H} (hS : StoreOk S)
    {gs : List Silmaril.Wasm.Execution.Core.GlobalInst}
    (hg : ∀ g ∈ gs, GlobalInstOk { S with globals := S.globals ++ gs } g) :
    StoreOk { S with globals := S.globals ++ gs } := by
  have he := extend_appendGlobals hS gs
  refine ⟨hS.tags, fun gi h => ?_, hS.mems, fun ti h => ?_, fun fi h =>
    funcInstOk_appendGlobals hS (hS.funcs fi h), fun ei h => (hS.elems ei h).extend he ⟨rfl, .inl rfl⟩,
    fun si h => ?_, fun ai h => ?_, fun e h => ?_,
    fun a ha hr => hS.acyclicStructs a ha (immutReachable_appendGlobals hr),
    fun a ha hr => hS.acyclicArrays a ha (immutReachable_appendGlobals hr),
    fun a ha hr => hS.acyclicExns a ha (immutReachable_appendGlobals hr),
    hS.structsClosed, hS.arraysClosed⟩
  · rcases List.mem_append.1 h with h | h
    · exact ⟨(hS.globals gi h).1, (hS.globals gi h).2.extend he⟩
    · exact hg gi h
  · obtain ⟨h₁, h₂, h₃⟩ := hS.tables ti h
    exact ⟨h₁, h₂, fun r hr => (h₃ r hr).extend he⟩
  · obtain ⟨fs, hE, hF⟩ := hS.structs si h
    exact ⟨fs, hE, hF.imp fun _ _ x => x.extend he⟩
  · obtain ⟨ft, hE, hF⟩ := hS.arrays ai h
    exact ⟨ft, hE, fun fv hfv => (hF fv hfv).extend he⟩
  · obtain ⟨ti, ts, h₁, h₂, h₃⟩ := hS.exns e h
    exact ⟨ti, ts, h₁, h₂, ValOk.forall₂_extend he h₃⟩

/-- The Core image of a Lime1 global instance is typed in every store. -/
theorem globalInstOk_toCore {S : Silmaril.Wasm.Execution.Core.Store H} (g : GlobalInst) :
    Silmaril.Wasm.Execution.Core.GlobalInstOk S g.toCore :=
  ⟨.num _, .num _⟩

/-- The Core image of `gstore`. -/
theorem gstore_toCore (L : Lime1.Execution.Store H) (gis : List GlobalInst) :
    (gstore L gis).toCore =
      { L.toCore with globals := L.toCore.globals ++ gis.map GlobalInst.toCore } := by
  simp [gstore, Silmaril.Wasm.Execution.Runtime.Store.toCore]

/-- **`gstore` has a valid Core image** when `L` has. -/
theorem storeOk_gstore {L : Lime1.Execution.Store H} (hL : Silmaril.Wasm.Execution.Core.StoreOk L.toCore)
    (gis : List GlobalInst) : Silmaril.Wasm.Execution.Core.StoreOk (gstore L gis).toCore := by
  rw [gstore_toCore]
  exact storeOk_appendGlobals hL fun g hg => by
    obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
    exact globalInstOk_toCore g'

end Silmaril.Wasm.SpecTec.Sim10.InstG
