module

public import Silmaril.Compiler.Core.Verified.StateExpr.Defs
public import Silmaril.Compiler.Core.Verified.Slots.Defs
public import Silmaril.Compiler.Core.Verified.Uninitialized.Defs

/-! # The memory of several `int` locals

`Inv env m ls ds`: each local `l` of `ls` (its symbol, allocation id and address) is pointed to
by every symbol with its key in `env` and is live in `m`; locals with different keys have
different ids and disjoint four-byte ranges; and a local whose key `q` has a definition
`ds q = some d` (the closed expression it was last assigned, `StateExpr.close`) holds the
`int` `d.val 0` in its slot, with `d.Ok 0`. Locals without a definition are created but not
yet (or no longer) initialised.

The frame rules: reads and location changes keep `Inv` (`Inv.touched`); a store into one local
updates exactly its definition (`Inv.store`, `Inv.uninit`); creating a fresh local in the
startup memory adds it (`Fresh`, `Fresh.create`); killing one local keeps the others live
(`live_killed`). `Inv.locs` gives `StateExpr.Locs` for an expression reading defined locals.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (LiveInt nextIntAddress)
open Locals (Slot stored killed)
open StateExpr (Key Loc Locs LocsP PtsOk values PtsTo)

/-- A source local: its symbol, allocation id and address. -/
structure Local where
  sym : Sym
  id : Int
  addr : Int

/-- The pointer to a local. -/
abbrev ptr (l : Local) : Dynamics.Val := .object (.pointer (.allocated l.id l.addr))

/-- The closed expression of a key, `0` for a key without definition. -/
def defsOf (ds : Key → Option IntExpr.Term) : Key → IntExpr.Term :=
  fun q => (ds q).getD (.lit 0)

/-- Every key a term reads has a definition. -/
def Defined (ds : Key → Option IntExpr.Term) (t : StateExpr.Term) : Bool :=
  t.vars.all fun q => (ds q).isSome

/-- The definitions after assigning `d` to `q`. -/
def update (ds : Key → Option IntExpr.Term) (q : Key) (d : Option IntExpr.Term) :
    Key → Option IntExpr.Term :=
  fun q' => if q' = q then d else ds q'

/-- What the pointer local `l` holds by its static target `t`: the null pointer, or the pointer
to the `int` local of `ls` with the key of `x`. -/
def Holds (m : Mem.Concrete.State) (ls : List Local) (l : Local) : PtsTo → Prop
  | .null => StrMem.PtrNull m l.id l.addr
  | .addr x => ∃ lq ∈ ls, lq.sym.key = x.key ∧ StrMem.PtrObj m l.id l.addr lq.id lq.addr

/-- The pointer locals `ps` next to the `int` locals `ls`: each is a live 8-byte object
(`StrMem.PtrSlot`); their keys, ids and byte ranges are distinct from each other and from the
`int` locals'; the `int` locals are at positive, aligned addresses; and a pointer local with a
target (`pts`) holds it (`Holds`). With no pointer locals this holds trivially (`PInv.empty`),
which is the default of `Inv`. (That the pointer locals' symbols point to them, `PEnv`, is a
fact about the environment, kept apart so that `Inv`'s environment can change alone.) -/
class PInv (m : Mem.Concrete.State) (ls ps : List Local)
    (pts : Key → Option PtsTo) : Prop where
  live : ∀ l ∈ ps, StrMem.PtrSlot m l.id l.addr
  apart : ∀ a ∈ ps, ∀ b ∈ ps, a.sym.key ≠ b.sym.key → a.id ≠ b.id ∧ Slots.Apart a.addr 8 b.addr 8
  sep : ∀ a ∈ ps, ∀ b ∈ ls, a.sym.key ≠ b.sym.key ∧ a.id ≠ b.id ∧ Slots.Apart a.addr 8 b.addr 4
  good : ps ≠ [] → ∀ l ∈ ls, 0 < l.addr ∧ l.addr < 18446744073709551616 ∧ l.addr % 4 = 0
  pts : ∀ r t, pts r = some t → ∃ l ∈ ps, l.sym.key = r ∧ Holds m ls l t

instance PInv.empty (m : Mem.Concrete.State) (ls : List Local) :
    PInv m ls [] (fun _ => none) where
  live := by simp
  apart := by simp
  sep := by simp
  good := fun h => absurd rfl h
  pts := fun _ _ h => by simp at h

/-- The environment and memory of the locals `ls` with definitions `ds`, and of the pointer
locals `ps` with targets `pts` (none by default). -/
structure Inv (env : Env) (m : Mem.Concrete.State) (ls : List Local)
    (ds : Key → Option IntExpr.Term) (ps : List Local := []) (pts : Key → Option PtsTo := fun _ => none) :
    Prop where
  [ptrs : PInv m ls ps pts]
  env : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)
  live : ∀ l ∈ ls, LiveInt m l.id l.addr
  apart : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → a.id ≠ b.id ∧ Slots.Apart a.addr 4 b.addr 4
  defs : ∀ q d, ds q = some d → d.Ok 0 ∧ ∃ l ∈ ls, l.sym.key = q ∧ Slot m l.id l.addr (d.val 0)

/-! ## The pointer objects under memory changes -/

/-- What a memory change keeps of the pointer objects `ps`: their slots and what they hold (an
allocated pointer or the null pointer). -/
def PFrame (ps : List Local) (m m' : Mem.Concrete.State) : Prop :=
  ∀ l ∈ ps, (StrMem.PtrSlot m l.id l.addr → StrMem.PtrSlot m' l.id l.addr) ∧
    (∀ pid paddr, StrMem.PtrObj m l.id l.addr pid paddr → StrMem.PtrObj m' l.id l.addr pid paddr) ∧
    (StrMem.PtrNull m l.id l.addr → StrMem.PtrNull m' l.id l.addr)

theorem PFrame.trans {ps : List Local} {m₁ m₂ m₃ : Mem.Concrete.State} (h₁ : PFrame ps m₁ m₂)
    (h₂ : PFrame ps m₂ m₃) : PFrame ps m₁ m₃ :=
  fun l hl => ⟨fun s => (h₂ l hl).1 ((h₁ l hl).1 s),
    fun _ _ o => (h₂ l hl).2.1 _ _ ((h₁ l hl).2.1 _ _ o), fun o => (h₂ l hl).2.2 ((h₁ l hl).2.2 o)⟩

theorem PFrame.touched (ps : List Local) {m m' : Mem.Concrete.State} (t : LoadTask.Touched m m') :
    PFrame ps m m' := by
  obtain ⟨l, u, rfl⟩ := t
  exact fun _ _ => ⟨fun h => ⟨h.alive, h.alloc, h.below, h.above⟩,
    fun _ _ h => ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes, h.prov, h.range⟩,
    fun h => ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes⟩⟩

theorem PFrame.nextExcluded (ps : List Local) (m : Mem.Concrete.State) (n : Nat) :
    PFrame ps m {m with nextExcluded := n} :=
  fun _ _ => ⟨fun h => ⟨h.alive, h.alloc, h.below, h.above⟩,
    fun _ _ h => ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes, h.prov, h.range⟩,
    fun h => ⟨⟨h.slot.alive, h.slot.alloc, h.slot.below, h.slot.above⟩, h.bytes⟩⟩

theorem PFrame.ofKeeps (ps : List Local) {m m' : Mem.Concrete.State} (k : StrMem.Keeps m m') :
    PFrame ps m m' :=
  fun _ _ => ⟨fun h => h.keeps k, fun _ _ h => h.keeps k, fun h => h.keeps k⟩

theorem ptrSlot_write {m : Mem.Concrete.State} {id addr : Int} (h : StrMem.PtrSlot m id addr)
    (a : Int) (bs : Mem.Concrete.Representation) (u : Option Int) :
    StrMem.PtrSlot {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} id addr := by
  have hw := Mem.Concrete.writeRepresentation_allocations a bs m
  refine ⟨?_, ?_, ?_, ?_⟩
  · show id ∉ (Mem.Concrete.writeRepresentation a bs m).dead
    rw [hw.2.1]; exact h.alive
  · show ∃ x, (Mem.Concrete.writeRepresentation a bs m).allocations.lookup id = some x ∧ _
    rw [hw.1]; exact h.alloc
  · show id < (Mem.Concrete.writeRepresentation a bs m).nextId
    rw [StrMem.wr_nextId]; exact h.below
  · show (Mem.Concrete.writeRepresentation a bs m).lastAddress ≤ addr
    rw [StrMem.wr_lastAddress]; exact h.above

/-- A representation write apart from the pointer objects keeps them. -/
theorem PFrame.write (ps : List Local) (m : Mem.Concrete.State) (a : Int)
    (bs : Mem.Concrete.Representation) (u : Option Int)
    (apart : ∀ l ∈ ps, Slots.Apart l.addr 8 a bs.length) :
    PFrame ps m {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} := by
  intro l hl
  refine ⟨fun h => ptrSlot_write h a bs u, fun pid paddr h => ⟨ptrSlot_write h.slot a bs u, ?_, ?_, h.range⟩,
    fun h => ⟨ptrSlot_write h.slot a bs u, fun i hi => ?_⟩⟩
  · intro i hi
    have := h.bytes i hi
    show Mem.Concrete.readByte (l.addr + i) (Mem.Concrete.writeRepresentation a bs m).bytes = _
    unfold Mem.Concrete.readByte at this ⊢
    rw [StrMem.bytes_write_outside a _ bs m (by rcases apart l hl with h | h <;> omega)]
    exact this
  · intro i hi
    show (Mem.Concrete.writeRepresentation a bs m).pointerBytes.lookup (l.addr + i) = _
    rw [Slots.pointerByte_writeRepresentation bs a _ m (by rcases apart l hl with h | h <;> omega)]
    exact h.prov i hi
  · have := h.bytes i hi
    show Mem.Concrete.readByte (l.addr + i) (Mem.Concrete.writeRepresentation a bs m).bytes = _
    unfold Mem.Concrete.readByte at this ⊢
    rw [StrMem.bytes_write_outside a _ bs m (by rcases apart l hl with h | h <;> omega)]
    exact this

/-- Killing an allocation that is no pointer local's keeps them. -/
theorem PFrame.killed (ps : List Local) (m : Mem.Concrete.State) (id : Int)
    (ne : ∀ l ∈ ps, l.id ≠ id) : PFrame ps m (Locals.killed m id) := by
  intro l hl
  have slot : ∀ {a : Int}, a = l.addr → StrMem.PtrSlot m l.id a → StrMem.PtrSlot (Locals.killed m id) l.id a := by
    intro a _ h
    refine ⟨?_, ?_, h.below, h.above⟩
    · simpa [Locals.killed, ne l hl] using h.alive
    · obtain ⟨x, hx, rest⟩ := h.alloc
      refine ⟨x, ?_, rest⟩
      change (m.allocations.erase id).lookup l.id = some x
      simp only [Map.lookup, Map.erase]
      rw [Finmap.lookup_erase_ne (show MapKey.key l.id ≠ MapKey.key id from ne l hl)]
      exact hx
  exact ⟨slot rfl, fun _ _ h => ⟨slot rfl h.slot, h.bytes, h.prov, h.range⟩, fun h => ⟨slot rfl h.slot, h.bytes⟩⟩

/-- Every symbol with the key of a pointer local points to it. -/
def PEnv (env : Env) (ps : List Local) : Prop :=
  ∀ l ∈ ps, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l)

theorem PInv.frame {m m' : Mem.Concrete.State} {ls ps : List Local}
    {pts : Key → Option PtsTo} (h : PInv m ls ps pts) (f : PFrame ps m m') :
    PInv m' ls ps pts where
  live l hl := (f l hl).1 (h.live l hl)
  apart := h.apart
  sep := h.sep
  good := h.good
  pts r t hr := by
    obtain ⟨l, hl, hk, hh⟩ := h.pts r t hr
    refine ⟨l, hl, hk, ?_⟩
    cases t with
    | null => exact (f l hl).2.2 hh
    | addr q =>
      obtain ⟨lq, hlq, hq, obj⟩ := hh
      exact ⟨lq, hlq, hq, (f l hl).2.1 _ _ obj⟩

/-- `PtsOk` for every term, from `Inv`. -/
theorem PInv.ptsOk {env : Env} {m : Mem.Concrete.State} {ls ps : List Local}
    {pts : Key → Option PtsTo} (h : PInv m ls ps pts)
    (henv : ∀ l ∈ ls, ∀ y : Sym, y.key = l.sym.key → env.lookup y = some (ptr l))
    (penv : PEnv env ps) (t : StateExpr.Term) :
    PtsOk env m pts t := by
  intro r x hr _
  obtain ⟨l, hl, hk, lq, hlq, hq, obj⟩ := h.pts r _ hr
  refine ⟨l.id, l.addr, fun y hy => penv l hl y (hy.trans hk.symm), fun id addr hx => ?_⟩
  have e := (hx lq.sym hq).symm.trans (henv lq hlq lq.sym rfl)
  simp only [ptr, Option.some.injEq, Value.object.injEq, ObjectValue.pointer.injEq,
    Mem.Concrete.Pointer.allocated.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact ⟨obj, (h.good (List.ne_nil_of_mem hl) lq hlq).2.2⟩

/-- `Inv` only depends on the slots and lifetimes of the memory, and on the pointer objects. -/
theorem Inv.mono {env : Env} {m m' : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts)
    (hs : ∀ id addr n, Slot m id addr n → Slot m' id addr n)
    (hl : ∀ id addr, LiveInt m id addr → LiveInt m' id addr) (hp : PFrame ps m m') :
    Inv env m' ls ds ps pts :=
  haveI := h.ptrs.frame hp
  { env := h.env
    live := fun l hl' => hl _ _ (h.live l hl')
    apart := h.apart
    defs := fun q d hd => by
      obtain ⟨ok, l, hl', hk, slot⟩ := h.defs q d hd
      exact ⟨ok, l, hl', hk, hs _ _ _ slot⟩ }

theorem Inv.touched {env : Env} {m m' : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) (t : LoadTask.Touched m m') :
    Inv env m' ls ds ps pts := by
  refine h.mono (fun _ _ _ s => t.slot s) ?_ (PFrame.touched ps t)
  obtain ⟨l, u, rfl⟩ := t
  exact fun _ _ lv => Locals.liveInt_with lv rfl rfl

theorem Inv.focus {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) (ann : List Annot) :
    Inv env (ReturnConst.focusMemory ann m) ls ds ps pts :=
  h.touched (LoadTask.focusMemory_touched ann m)

theorem Inv.nextExcluded {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) (n : Nat) :
    Inv env {m with nextExcluded := n} ls ds ps pts :=
  h.mono (fun _ _ _ s => Slots.slot_nextExcluded s n) (fun _ _ lv => Locals.liveInt_with lv rfl rfl)
    (PFrame.nextExcluded ps m n)

/-- Binding a symbol whose key is no local's keeps `Inv`. -/
theorem Inv.extend {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {x : Sym} {v : Dynamics.Val}
    (fresh : ∀ l ∈ ls, l.sym.key ≠ x.key) :
    Inv (extendEnv [(x, v)] env) m ls ds ps pts :=
  haveI := h.ptrs
  { env := fun l hl y hy => by
      rw [ConvInt.lookup_one_other (by rw [hy]; exact fresh l hl)]
      exact h.env l hl y hy
    live := h.live
    apart := h.apart
    defs := h.defs }

/-- The locals of the definitions a term reads. -/
theorem Inv.locs {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {t : StateExpr.Term}
    (hd : Defined ds t = true) : Locs env m (values (defsOf ds)) t := by
  intro q hq
  have hs : (ds q).isSome = true := List.all_eq_true.mp hd q hq
  obtain ⟨d, hdq⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨ok, l, hl, hk, slot⟩ := h.defs q d hdq
  have hv : values (defsOf ds) q = d.val 0 := by simp [values, defsOf, hdq]
  rw [hv]
  exact ⟨IntExpr.Term.int_of_ok d ok, l.id, l.addr, fun y hy => h.env l hl y (hy.trans hk.symm), slot⟩

/-- What a read through the pointer locals needs. -/
theorem Inv.locsP {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) (penv : PEnv env ps) {t : StateExpr.Term}
    (hd : Defined ds t = true) : LocsP env m (values (defsOf ds)) pts t :=
  ⟨h.locs hd, h.ptrs.ptsOk h.env penv t, fun r t hr => by
    obtain ⟨l, hl, hk, hh⟩ := h.ptrs.pts r _ hr
    refine ⟨l.id, l.addr, fun y hy => penv l hl y (hy.trans hk.symm), ?_⟩
    cases t with
    | null => exact hh
    | addr x => obtain ⟨lq, -, -, obj⟩ := hh; exact ⟨lq.id, lq.addr, obj⟩⟩

/-- The definitions of the keys a term reads are `Ok`. -/
theorem Inv.defs_ok {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {t : StateExpr.Term}
    (hd : Defined ds t = true) : ∀ q ∈ t.vars, (defsOf ds q).Ok 0 := by
  intro q hq
  have hs : (ds q).isSome = true := List.all_eq_true.mp hd q hq
  obtain ⟨d, hdq⟩ := Option.isSome_iff_exists.mp hs
  simpa [defsOf, hdq] using (h.defs q d hdq).1

/-- The pointer a local's symbol evaluates to. -/
theorem Inv.lookup {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) {y : Sym}
    (hy : y.key = l.sym.key) : env.lookup y = some (ptr l) :=
  h.env l hl y hy

/-! ## Stores -/

/-- A store into an `int` local keeps the pointer objects. -/
theorem PInv.stored {m : Mem.Concrete.State} {ls ps : List Local}
    {pts : Key → Option PtsTo} (h : PInv m ls ps pts) {l : Local} (hl : l ∈ ls) (n : Int) :
    PFrame ps m (stored m l.id l.addr n) :=
  PFrame.write ps m l.addr _ _ fun a ha => by
    simpa [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length] using (h.sep a ha l hl).2.2

/-- **A store into one local** updates exactly its definition. -/
theorem Inv.store {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls)
    {d : IntExpr.Term} (ok : d.Ok 0) :
    Inv env (stored m l.id l.addr (d.val 0)) ls (update ds l.sym.key (some d)) ps pts :=
  haveI := h.ptrs.frame (h.ptrs.stored hl (d.val 0))
  { env := h.env
    live := fun l' hl' => Slots.live_stored (h.live l' hl') _ _ _
    apart := h.apart
    defs := fun q d' hd => by
      unfold update at hd
      split at hd
      · rename_i hq
        cases hd
        exact ⟨ok, l, hl, hq.symm, Locals.stored_slot (h.live l hl) _⟩
      · rename_i hq
        obtain ⟨ok', l', hl', hk, slot⟩ := h.defs q d' hd
        have ne : l.sym.key ≠ l'.sym.key := fun e => hq (hk.symm.trans e.symm)
        exact ⟨ok', l', hl', hk, Slots.slot_stored slot _ _ _ (h.apart l hl l' hl' ne).2⟩ }

/-- An unspecified store keeps every disjoint slot. -/
theorem slot_uninit {m : Mem.Concrete.State} {id addr value : Int} (h : Slot m id addr value)
    (wid waddr : Int) (apart : Slots.Apart waddr 4 addr 4) :
    Slot (Uninitialized.stored m wid waddr) id addr value := by
  have len : (Mem.Concrete.plainBytes (List.replicate 4 none)).length = 4 := by
    simp [Mem.Concrete.plainBytes]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m
    unfold Uninitialized.stored
    rw [hw]
    exact Locals.liveInt_with h.live rfl rfl
  · intro i hi
    change (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m).pointerBytes.lookup (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ waddr (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change Mem.Concrete.fetchBytes 4 addr (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ waddr addr 4 m (by rwa [len])]
    exact h.bytes

theorem live_uninit {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (wid waddr : Int) : LiveInt (Uninitialized.stored m wid waddr) id addr := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  unfold Uninitialized.stored
  rw [hw]
  exact Locals.liveInt_with h rfl rfl

/-- An unspecified store into an `int` local keeps the pointer objects. -/
theorem PInv.uninit {m : Mem.Concrete.State} {ls ps : List Local}
    {pts : Key → Option PtsTo} (h : PInv m ls ps pts) {l : Local} (hl : l ∈ ls) :
    PFrame ps m (Uninitialized.stored m l.id l.addr) :=
  PFrame.write ps m l.addr _ _ fun a ha => by
    simpa [Mem.Concrete.plainBytes] using (h.sep a ha l hl).2.2

/-- **An unspecified store** removes exactly the local's definition. -/
theorem Inv.uninit {env : Env} {m : Mem.Concrete.State} {ls : List Local}
    {ds : Key → Option IntExpr.Term} {ps : List Local} {pts : Key → Option PtsTo}
    (h : Inv env m ls ds ps pts) {l : Local} (hl : l ∈ ls) :
    Inv env (Uninitialized.stored m l.id l.addr) ls (update ds l.sym.key none) ps pts :=
  haveI := h.ptrs.frame (h.ptrs.uninit hl)
  { env := h.env
    live := fun l' hl' => live_uninit (h.live l' hl') _ _
    apart := h.apart
    defs := fun q d' hd => by
      unfold update at hd
      split at hd
      · cases hd
      · rename_i hq
        obtain ⟨ok', l', hl', hk, slot⟩ := h.defs q d' hd
        have ne : l.sym.key ≠ l'.sym.key := fun e => hq (hk.symm.trans e.symm)
        exact ⟨ok', l', hl', hk, slot_uninit slot _ _ (h.apart l hl l' hl' ne).2⟩ }

/-! ## Kills -/

/-- Killing another allocation keeps a local live. -/
theorem live_killed {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (other : Int) (ne : id ≠ other) : LiveInt (killed m other) id addr := by
  refine ⟨?_, ?_⟩
  · simpa [killed, ne] using h.alive
  · obtain ⟨a, ha, rest⟩ := h.found
    refine ⟨a, ?_, rest⟩
    change (m.allocations.erase other).lookup id = some a
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (show MapKey.key id ≠ MapKey.key other from ne)]
    exact ha

/-! ## Creation -/

/-- Creating another `int` object keeps a local live. -/
theorem live_created {m : Mem.Concrete.State} {id addr : Int} (h : LiveInt m id addr)
    (pref : Prefix) (ann : List Annot) (fresh : id ≠ m.nextId) :
    LiveInt (Actions.created pref ann m) id addr := by
  let a := Mem.Concrete.nextIntAddress m
  let bs := Mem.Concrete.plainBytes (List.replicate 4 none)
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape a bs m
  have shape : Actions.created pref ann m =
      {m with
        bytes := b
        pointerBytes := pb
        nextId := m.nextId + 1
        lastAddress := a
        allocations := (m.allocations.insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann)} :
            Mem.Concrete.Allocation)).insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann),
            readonlyKind := Mem.Concrete.readonlyKind pref} : Mem.Concrete.Allocation),
        lastUsed := some m.nextId} := by
    unfold Actions.created
    change Mem.Concrete.updateLastAllocation
      {Mem.Concrete.writeRepresentation a bs m with
        nextId := m.nextId + 1, lastAddress := a,
        allocations := m.allocations.insert m.nextId
          ({base := a, size := 4, objectType := some (Mem.Concrete.intType ann)} :
            Mem.Concrete.Allocation), lastUsed := some m.nextId} _ = _
    rw [hw]
    simp [Mem.Concrete.updateLastAllocation]
  refine ⟨?_, ?_⟩
  · rw [shape]; exact h.alive
  · obtain ⟨old, found, rest⟩ := h.found
    refine ⟨old, ?_, rest⟩
    rw [shape]
    simpa only [Map.lookup_insert_of_key_ne _ _ (show MapKey.key id ≠ MapKey.key m.nextId from fresh)]
      using found

/-- The startup memory with the locals `ls` created in order: nothing died, ids below the next
one, every local at or above the last address, which is `4 * ls.length` below `errno`. -/
structure Fresh (m : Mem.Concrete.State) (ls : List Local) : Prop where
  dead : m.dead = []
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr
  last : m.lastAddress = StartupReach.errnoAddr - 4 * ls.length

theorem Fresh.nextIntAddress {m : Mem.Concrete.State} {ls : List Local} (h : Fresh m ls) :
    nextIntAddress m = m.lastAddress - 4 := by
  simp only [Mem.Concrete.nextIntAddress, h.last, StartupReach.errnoAddr]
  omega

end Silmaril.Compile.Core.Verified.StateMem
