module

public import Silmaril.Compiler.Core.Verified.StoreTask.Defs

/-! # Uninitialized integer locals

Cerberus emits an explicit store of `Unspecified int` after creating a local without
an initializer. This writes unspecified representation bytes; it neither invents a
specified integer nor ends the allocation's lifetime. A later assignment may then
initialize the same live object.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Uninitialized

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches Eval tagsOf)
open Mem.Concrete (LiveInt intType)

variable {file : Program} {labels : Labels}

def stored (m : Mem.Concrete.State) (id addr : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m with lastUsed := some id}

theorem store_int (tags : Mem.Concrete.Tags) (ann vann : List Annot)
    {m : Mem.Concrete.State} {id addr : Int} (live : LiveInt m id addr) :
    Mem.Concrete.storeTyped tags m (intType ann) (.allocated id addr)
      (.unspecified (intType vann)) = .ok ((addr, 4), stored m id addr) := by
  obtain ⟨a, look, base, size, atomic, ro⟩ := live.found
  simp [Mem.Concrete.storeTyped, Mem.Concrete.access_int tags ann live,
    Mem.Concrete.checkWritable, look, ro, Mem.Concrete.represent,
    Mem.Concrete.layout_intType, stored, Mem.Concrete.plainBytes,
    bind, Except.bind, pure, Except.pure]

theorem stored_live {m : Mem.Concrete.State} {id addr : Int} (live : LiveInt m id addr) :
    LiveInt (stored m id addr) id addr := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  unfold stored
  rw [hw]
  exact Locals.liveInt_with live rfl rfl

theorem stored_stdout (m : Mem.Concrete.State) (id addr : Int) :
    (stored m id addr).stdout = m.stdout := by
  simp [stored, Actions.writeRepresentation_stdout]

/-- The actual Core memory step records the unspecified initialization as a write. -/
theorem store_apply (ann vann : List Annot) (k : List Frame)
    {m : Mem.Concrete.State} {id addr : Int} (live : LiveInt m id addr) :
    Reaches file labels
      ⟨.apply (.memory .store) [.ctype (intType ann), .object (.pointer (.allocated id addr)),
        .loaded (.unspecified (intType vann))], k, m⟩
      ⟨.value .unit, .annotations [StoreTask.writeAccess k addr] :: k, stored m id addr⟩ := by
  apply Actions.memory_reaches (name := "Store") (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory,
    store_int _ ann vann live, Mem.Concrete.access_int _ ann live,
    StoreTask.writeAccess, bind, Except.bind, pure, Except.pure]
  rfl

/-- Source syntax of the positive initialization store, over any continuation. -/
theorem store_reaches (ann a1 c1 a2 a3 c3 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (live : LiveInt m id addr) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.store false (Locals.intVal a1 c1) (.mk a2 () (.sym x))
          (.mk a3 () (.val (.loaded (.unspecified (intType c3))))) .na))))) env, k, m⟩
      ⟨.value .unit, .annotations [StoreTask.writeAccess k addr] :: k,
        stored (ReturnConst.focusMemory ann m) id addr⟩ := by
  have eval : Eval file (tagsOf file m) env
      (.inr [Locals.intVal a1 c1, .mk a2 () (.sym x),
        .mk a3 () (.val (.loaded (.unspecified (intType c3))))])
      (.inr [.ctype (intType c1), .object (.pointer (.allocated id addr)),
        .loaded (.unspecified (intType c3))]) :=
    .cons .val (.cons (.sym hx) (.cons .val .nil))
  exact (Locals.action_reaches Locals.request_store eval).trans
    (store_apply c1 c3 k (Locals.liveInt_focus ann live))

end Silmaril.Compile.Core.Verified.Uninitialized
