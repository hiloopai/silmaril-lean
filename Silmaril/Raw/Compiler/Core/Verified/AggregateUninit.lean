module

public import Silmaril.Compiler.Core.Verified.IntSubobject.Defs
public import Silmaril.Compiler.Core.Verified.StoreTask.Defs
/-! # The explicit unspecified store after aggregate creation

Cerberus emits a whole-object unspecified store even for an uninitialized array or
struct. Its bytes impose no constraints on the target memory. This step preserves
`MemRel.Rel` with the *same* target memory, clearing pointer-copy metadata across
the object. It must precede, not replace, subsequent specified subobject stores.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.AggregateUninit

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Mem.Concrete
open MemRel (Obj Placed Rel)

/-- The Core memory after the explicit whole-object unspecified store. -/
def stored (m : State) (o : Obj) : State :=
  {writeRepresentation o.base (plainBytes (List.replicate o.size none)) m with
    lastUsed := some o.id}

/-- Any non-atomic type of the tracked object's exact layout is accessible at its base. -/
theorem access (tags : Tags) {m : State} {lm : Silmaril.Machine.Lir.Memory} {o : Obj}
    (h : Placed m lm o) {ty : Ctype} {l : TypeLayout}
    (hl : typeLayout 64 tags ty = .ok l) (hs : l.size = (o.size : Int)) :
    accessTyped tags m ty (.allocated o.id o.base) = .ok (o.id, o.base, o.size) := by
  obtain ⟨alive, ⟨a, look, base, size, atomic, _⟩, _⟩ := h
  simp [accessTyped, hl, hs, alive, look, base, size, checkAtomic, atomic,
    bind, Except.bind, pure, Except.pure]

/-- The explicit unspecified Store accepts array and struct types as well as scalars. -/
theorem store (tags : Tags) {m : State} {lm : Silmaril.Machine.Lir.Memory} {o : Obj}
    (h : Placed m lm o) {ty vty : Ctype} {l vl : TypeLayout}
    (hl : typeLayout 64 tags ty = .ok l) (hs : l.size = (o.size : Int))
    (hv : typeLayout 64 tags vty = .ok vl) (hvs : vl.size = (o.size : Int)) :
    storeTyped tags m ty (.allocated o.id o.base) (.unspecified vty) =
      .ok ((o.base, o.size), stored m o) := by
  obtain ⟨a, look, _, _, _, ro⟩ := h.found
  simp [storeTyped, access tags h hl hs, checkWritable, look, ro, represent,
    hv, hvs, stored, plainBytes, bind, Except.bind, pure, Except.pure]

/-- Forgetting the object's bytes keeps the relation with unchanged target bytes.
Other objects retain their specified byte values. -/
theorem rel {m : State} {lm : Silmaril.Machine.Lir.Memory} {objs : List Obj} {o : Obj}
    (h : Rel m lm objs) (ho : o ∈ objs) : Rel (stored m o) lm objs := by
  let bs : List Byte := List.replicate o.size none
  have wa := writeRepresentation_allocations o.base (plainBytes bs) m
  have wf := MemRel.writeRepresentation_fields o.base (plainBytes bs) m
  have wb : (stored m o).bytes = writeInt o.base bs m.bytes := by
    simp [stored, bs, writeRepresentation_bytes, plainBytes]
  refine ⟨fun o' ho' => ?_, h.apart, fun o' ho' => ?_, fun o' ho' => ?_⟩
  · obtain ⟨alive, found, fits, bytes, plain⟩ := h.placed o' ho'
    refine ⟨by simpa [stored, bs, wa.2.1] using alive,
      by simpa [stored, bs, wa.1] using found, fits, fun i hi => ?_, fun i hi => ?_⟩
    · rw [wb]
      by_cases eq : o' = o
      · subst o'
        rw [MemRel.read_writeInt_at _ _ _ i (by simpa [bs] using hi)]
        intro v hv
        simp [bs] at hv
      · obtain ⟨_, apart, _⟩ := h.apart_of ho' ho eq
        rw [read_outside_write _ _ _ _ (by simp only [bs, List.length_replicate]; omega)]
        exact bytes i hi
    · by_cases eq : o' = o
      · subst o'
        exact MemRel.pointerBytes_write_inside _ bs m i (by simpa [bs] using hi)
      · obtain ⟨_, apart, _⟩ := h.apart_of ho' ho eq
        change (writeRepresentation o.base (plainBytes bs) m).pointerBytes.lookup _ = none
        rw [MemRel.pointerBytes_write_outside _ _ _ _ (by
          simp only [bs, List.length_replicate]; omega)]
        exact plain i hi
  · simpa [stored, bs, wf.1] using h.below o' ho'
  · simpa [stored, bs, wf.2] using h.fresh o' ho'


/-- The actual whole-object initialization action records its full write footprint. -/
theorem store_apply {file : Dynamics.Program} {labels : Dynamics.Labels} (tags : Tags)
    (k : List Dynamics.Frame) {m : State} {lm : Silmaril.Machine.Lir.Memory} {o : Obj}
    (h : Placed m lm o) {ty vty : Ctype} {l vl : TypeLayout}
    (hl : typeLayout 64 tags ty = .ok l) (hs : l.size = (o.size : Int))
    (hv : typeLayout 64 tags vty = .ok vl) (hvs : vl.size = (o.size : Int))
    (htags : PureEval.tagsOf file m = tags) :
    Interleave.LocalReaches file labels false
      ⟨.apply (.memory .store) [.ctype ty, .object (.pointer (.allocated o.id o.base)),
        .loaded (.unspecified vty)], k, m⟩
      ⟨.value .unit, .annotations [⟨k.findSome? fun f => match f with
        | .excluded n => some n | _ => none, [], true, o.base, o.size⟩] :: k, stored m o⟩ := by
  apply Relation.ReflTransGen.single
  apply Interleave.LocalStep.memory (name := "Store")
  have ht : ({definitions := file.tagDefs, enums := m.enumTypes} : Tags) = tags := htags
  simp [Dynamics.requestAux, Dynamics.awaitsScheduling, Dynamics.memoryRequest, Dynamics.toMemory,
    store tags h hl hs hv hvs, access tags h hl hs, ht,
    bind, Except.bind, pure, Except.pure]
  rfl

end Silmaril.Compile.Core.Verified.AggregateUninit
