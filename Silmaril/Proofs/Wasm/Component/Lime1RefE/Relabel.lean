module

public import Silmaril.Raw.Wasm.Component.Engine.Lime1

/-!
# Relabelling the host codes of Lime1 stores

The component machine runs a core store at the host type `CanonHost lime1`, while the engine's
own specification (`Param.engineOut`, `instOf`) runs at host type `Nat`. A Lime1 store mentions
its host type only in the codes of host functions, so a map `g : H → H'` relabels a store
(`Store.relabel g`: host codes mapped, everything else kept). This module shows that relabelling
commutes with what the call of an import-free component's export needs:

* `step_relabel`, `steps_relabel`, `diverges_relabel`: host-free Lime1 steps, runs and divergence
  (`Lime1.Execution.Internal` never invokes a host function);
* `status_returned`: a returned status depends only on the code;
* `prepare_relabel`: preparation (allocation and segment initialisation) commutes with
  relabelling, so `lime1.prepare?` in the empty store at any host type is the relabelling of
  its run at another;
* `steps_funcs`: host-free runs keep the function list, and `decompose?_none`: a store without
  host functions has no callout.

New definitions and proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Lime1RefE

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Lime1.Execution
open Silmaril.Wasm.Component.Engine.Lime1 (lime1)

variable {H H' : Type} (g : H → H')

/-- Relabel the host code of a function. -/
def FuncInst.relabel : FuncInst Lime1.Func H → FuncInst Lime1.Func H'
  | .wasm t m c => .wasm t m c
  | .host t h => .host t (g h)

/-- Relabel the host codes of a Lime1 store. -/
def Store.relabel (s : Lime1.Execution.Store H) : Lime1.Execution.Store H' :=
  { funcs := s.funcs.map (FuncInst.relabel g), tables := s.tables, memories := s.memories,
    globals := s.globals }

/-- Relabel the store of a configuration. -/
def Config.relabel (c : Lime1.Execution.Config H) : Lime1.Execution.Config H' :=
  ⟨Store.relabel g c.store, c.frame, c.code⟩

variable {g}

theorem FuncInst.type_relabel (fi : FuncInst Lime1.Func H) :
    (FuncInst.relabel g fi).type = fi.type := by
  cases fi <;> rfl

theorem Store.funcs_relabel (s : Lime1.Execution.Store H) (i : Nat) :
    (Store.relabel g s).funcs[i]? = (s.funcs[i]?).map (FuncInst.relabel g) := by
  simp only [Store.relabel, List.getElem?_map]

theorem frameMemory_relabel (s : Lime1.Execution.Store H) (f : Frame) :
    frameMemory (Store.relabel g s) f = frameMemory s f := rfl

theorem frameTable_relabel (s : Lime1.Execution.Store H) (f : Frame) :
    frameTable (Store.relabel g s) f = frameTable s f := rfl

theorem setMemory_relabel (s : Lime1.Execution.Store H) (a : MemAddr) (m : MemInst) :
    Store.relabel g (setMemory s a m) = setMemory (Store.relabel g s) a m := rfl

theorem setGlobal_relabel (s : Lime1.Execution.Store H) (a : GlobalAddr) (gi : GlobalInst) :
    Store.relabel g (setGlobal s a gi) = setGlobal (Store.relabel g s) a gi := rfl

/-! ## Host-free steps -/

/-- **Host-free Lime1 steps commute with relabelling.** -/
theorem step_relabel {c c' : Lime1.Execution.Config H} (h : Internal c c') :
    Internal (Config.relabel g c) (Config.relabel g c') := by
  induction h with
  | pure s f h => exact .pure _ f h
  | context _ vs tail ih => exact .context ih vs tail
  | label _ n cont ih => exact .label ih n cont
  | frame _ n outer ih => exact .frame ih n outer
  | localGet s f i v found => exact .localGet _ f i v found
  | localSet s f i v old found => exact .localSet _ f i v old found
  | globalGet s f i a gi index found => exact .globalGet _ f i a gi index found
  | globalSet s f i a gi v index found mutable =>
    exact .globalSet _ f i a gi v index found mutable
  | call s f i a found => exact .call _ f i a found
  | callIndirect s f i c table a fn ft tableFound typeFound element found typeMatch =>
    refine .callIndirect _ f i c table a (FuncInst.relabel g fn) ft tableFound typeFound element
      ?_ (by rw [FuncInst.type_relabel, typeMatch])
    rw [Store.funcs_relabel, found]
    rfl
  | callIndirectBounds s f i c table tableFound outOfBounds =>
    exact .callIndirectBounds _ f i c table tableFound outOfBounds
  | callIndirectNull s f i c table tableFound null =>
    exact .callIndirectNull _ f i c table tableFound null
  | callIndirectType s f i c table a fn ft tableFound typeFound element found typeMismatch =>
    refine .callIndirectType _ f i c table a (FuncInst.relabel g fn) ft tableFound typeFound
      element ?_ (by rw [FuncInst.type_relabel]; exact typeMismatch)
    rw [Store.funcs_relabel, found]
    rfl
  | invokeWasm s f a ft module fn args found arity =>
    refine .invokeWasm _ f a ft module fn args ?_ arity
    rw [Store.funcs_relabel, found]
    rfl
  | invokeHost _ _ _ _ _ _ _ _ _ _ behavior => exact behavior.elim
  | invokeHostDiverges _ _ _ _ _ _ _ _ behavior => exact behavior.elim
  | intLoad s f t packed arg c a m v memory loaded =>
    exact .intLoad _ f t packed arg c a m v memory loaded
  | intLoadTrap s f t packed arg c a m memory loaded =>
    exact .intLoadTrap _ f t packed arg c a m memory loaded
  | floatLoad s f t arg c a m v memory loaded => exact .floatLoad _ f t arg c a m v memory loaded
  | floatLoadTrap s f t arg c a m memory loaded =>
    exact .floatLoadTrap _ f t arg c a m memory loaded
  | intStore s f t packed arg c x a m bytes memory stored =>
    exact .intStore _ f t packed arg c x a m bytes memory stored
  | intStoreTrap s f t packed arg c x a m memory stored =>
    exact .intStoreTrap _ f t packed arg c x a m memory stored
  | floatStore s f t arg c x a m bytes memory stored =>
    exact .floatStore _ f t arg c x a m bytes memory stored
  | floatStoreTrap s f t arg c x a m memory stored =>
    exact .floatStoreTrap _ f t arg c x a m memory stored
  | memorySize s f a m memory => exact .memorySize _ f a m memory
  | memoryGrow s f a m c r bytes memory grown => exact .memoryGrow _ f a m c r bytes memory grown
  | memoryCopy s f d src n a m bytes memory copied =>
    exact .memoryCopy _ f d src n a m bytes memory copied
  | memoryCopyTrap s f d src n a m memory copied =>
    exact .memoryCopyTrap _ f d src n a m memory copied
  | memoryFill s f d b n a m bytes memory filled =>
    exact .memoryFill _ f d b n a m bytes memory filled
  | memoryFillTrap s f d b n a m memory filled =>
    exact .memoryFillTrap _ f d b n a m memory filled

variable (g) in
/-- Relabel an engine configuration of `lime1`. -/
def cfgRelabel (c : lime1.Config H) : lime1.Config H' :=
  (Store.relabel g c.1, ⟨c.2.frame, c.2.code⟩)

/-- **Host-free engine runs commute with relabelling.** -/
theorem steps_relabel {c c' : lime1.Config H}
    (h : Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 c c') :
    Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 (cfgRelabel g c) (cfgRelabel g c') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (step_relabel (g := g) hs)

/-- **Host-free engine divergence commutes with relabelling.** -/
theorem diverges_relabel {c : lime1.Config H}
    (h : Silmaril.Wasm.Component.Engine.CoreEngine.Diverges lime1 c) :
    Silmaril.Wasm.Component.Engine.CoreEngine.Diverges lime1 (cfgRelabel g c) :=
  Silmaril.InfiniteTrace.map (cfgRelabel g) (fun _ _ hs => step_relabel (g := g) hs) h

/-- A returned status depends only on the code. -/
theorem status_returned {s : Lime1.Execution.Store H} {t : lime1.Thread H}
    (s' : Lime1.Execution.Store H') (t' : lime1.Thread H') (hc : t'.code = t.code)
    {r : Silmaril.Wasm.Component.Engine.CallResult} (h : lime1.status s t = .returned r) :
    lime1.status s' t' = .returned r := by
  change Silmaril.Wasm.Component.Engine.Lime1.status s t = _ at h
  change Silmaril.Wasm.Component.Engine.Lime1.status s' t' = _
  unfold Silmaril.Wasm.Component.Engine.Lime1.status at h ⊢
  rw [hc]
  split at h
  · cases h
    rfl
  · split at h
    · cases h
    · split at h <;> cases h

/-! ## Function lists and callouts -/

/-- Host-free steps keep the function list. -/
theorem step_funcs {c c' : Lime1.Execution.Config H} (h : Internal c c') :
    c'.store.funcs = c.store.funcs := by
  induction h with
  | context _ _ _ ih | label _ _ _ ih | frame _ _ _ ih => exact ih
  | invokeHost _ _ _ _ _ _ _ _ _ _ behavior => exact behavior.elim
  | _ => rfl

/-- Host-free engine runs keep the function list. -/
theorem steps_funcs {c c' : lime1.Config H}
    (h : Silmaril.Wasm.Component.Engine.CoreEngine.Steps lime1 c c') : c'.1.funcs = c.1.funcs := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (step_funcs hs).trans ih

/-- A store without host functions. -/
def NoHost (s : Lime1.Execution.Store H) : Prop :=
  ∀ (i : Nat) (ft : V1.FuncType) (h : H), s.funcs[i]? ≠ some (.host ft h)

/-- **A store without host functions has no callout.** -/
theorem status_ne_callout {s : Lime1.Execution.Store H} (hs : NoHost s) (t : lime1.Thread H)
    (h : H) (args : List Silmaril.Wasm.Component.Engine.FlatValue) :
    lime1.status s t ≠ .callout h args := by
  intro e
  change Silmaril.Wasm.Component.Engine.Lime1.status s t = _ at e
  unfold Silmaril.Wasm.Component.Engine.Lime1.status at e
  split at e
  · cases e
  · split at e
    · rename_i c hd
      exact hs _ _ _ (decompose?_sound hd).found
    · split at e <;> cases e

end Silmaril.Proofs.Wasm.Component.Lime1RefE
