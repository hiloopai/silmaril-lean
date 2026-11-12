module

public import Silmaril.Compiler.Core.Verified.Slots.Defs
public import Silmaril.Cerberus.Mem.TySlots.Defs
/-! # Core memory actions on integer locals of every supported type

The `int` lemmas of `Actions`, `Locals` and `Slots` for a local of any supported integer type
`ity` (`supported`: plain `char`, `signed`/`unsigned` `char`, `short`, `int`, `long`,
`long long`): a `width ity`-byte, `width ity`-aligned object of the concrete memory
(`Mem.TySlots`). `TSlot m id addr w n`: the live object of `w` bytes at `addr` holds the
integer `n`. The Core `create(Ivalignof(T), T)`, `load(T, p)` and `kill(T, p)` as runs of the
machine (`create_reaches`, `load_reaches`, `kill_reaches`), the store transition
(`store_apply`), and the frame rules: a store, a creation or a kill of one object keeps every
disjoint slot (`slot_stored`, `slot_created`, `slot_killed`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyActions

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf argState)
open ReturnConst (focusMemory)
open Mem.Concrete (tyType LiveSz PlainSz InRange nextAddress)
open Slots (Apart)

variable {file : Program} {labels : Labels}

/-! ## The supported types -/

/-- The integer types of the fragment: fixed widths, bounds those of the representation, and
conversions that wrap (`_Bool`, enumerations and the wide character types are left out). -/
def supported : IntegerType → Bool
  | .char => true
  | .signed b | .unsigned b => match b with
    | .ichar | .short | .int | .long | .longLong => true
    | _ => false
  | _ => false

/-- The width in bytes. -/
def width : IntegerType → Nat
  | .char => 1
  | .signed b | .unsigned b => match b with
    | .ichar => 1
    | .short => 2
    | .int => 4
    | _ => 8
  | _ => 8

/-- The signedness (plain `char` is signed). -/
def signed : IntegerType → Bool
  | .char => true
  | .signed _ => true
  | _ => false

theorem layout_of {ity : IntegerType} (h : supported ity = true) :
    Mem.Concrete.integerLayout ity = some (width ity, signed ity) := by
  cases ity with
  | signed b => cases b <;> simp_all [supported, width, signed, Mem.Concrete.integerLayout,
      Mem.Concrete.baseWidth]
  | unsigned b => cases b <;> simp_all [supported, width, signed, Mem.Concrete.integerLayout,
      Mem.Concrete.baseWidth]
  | _ => simp_all [supported, width, signed, Mem.Concrete.integerLayout]

theorem width_cases {ity : IntegerType} (h : supported ity = true) :
    width ity = 1 ∨ width ity = 2 ∨ width ity = 4 ∨ width ity = 8 := by
  cases ity with
  | signed b => cases b <;> simp_all [supported, width]
  | unsigned b => cases b <;> simp_all [supported, width]
  | _ => simp_all [supported, width]

theorem width_pos {ity : IntegerType} (h : supported ity = true) : 0 < width ity := by
  rcases width_cases h with e | e | e | e <;> omega

theorem width_le {ity : IntegerType} (h : supported ity = true) : width ity ≤ 8 := by
  rcases width_cases h with e | e | e | e <;> omega

/-- The bounds of a supported type: those of its representation. -/
def bounds (ity : IntegerType) : Int × Int :=
  Mem.Concrete.representationBounds (width ity) (signed ity)

theorem registeredBounds {ity : IntegerType} (h : supported ity = true) (tags : Mem.Concrete.Tags) :
    Mem.Concrete.registeredIntegerBounds tags ity = some (bounds ity) := by
  cases ity with
  | signed b => cases b <;> simp_all [supported, width, signed, bounds,
      Mem.Concrete.registeredIntegerBounds, Mem.Concrete.registeredInteger,
      Mem.Concrete.integerBounds, Mem.Concrete.integerLayout, Mem.Concrete.baseWidth,
      Mem.Concrete.representationBounds]
  | unsigned b => cases b <;> simp_all [supported, width, signed, bounds,
      Mem.Concrete.registeredIntegerBounds, Mem.Concrete.registeredInteger,
      Mem.Concrete.integerBounds, Mem.Concrete.integerLayout, Mem.Concrete.baseWidth,
      Mem.Concrete.representationBounds]
  | _ => simp_all [supported, width, signed, bounds, Mem.Concrete.registeredIntegerBounds,
      Mem.Concrete.registeredInteger, Mem.Concrete.integerBounds, Mem.Concrete.integerLayout,
      Mem.Concrete.representationBounds]

/-- A value of the type: in its bounds. -/
def Fits (ity : IntegerType) (n : Int) : Prop := InRange (width ity) (signed ity) n

/-! ## Slots -/

/-- The live `w`-byte object at `addr` holds the integer `n`. -/
structure TSlot (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) : Prop where
  live : LiveSz m id addr w
  plain : PlainSz m addr w
  bytes : Mem.Concrete.fetchBytes w addr m.bytes = Mem.Concrete.encodeInteger w n

theorem liveSz_with {m m' : Mem.Concrete.State} {id addr : Int} {w : Nat} (h : LiveSz m id addr w)
    (hd : m'.dead = m.dead) (ha : m'.allocations = m.allocations) : LiveSz m' id addr w := by
  obtain ⟨alive, found⟩ := h
  exact ⟨by rw [hd]; exact alive, by rw [ha]; exact found⟩

theorem liveSz_focus {m : Mem.Concrete.State} {id addr : Int} {w : Nat} (ann : List Annot)
    (h : LiveSz m id addr w) : LiveSz (focusMemory ann m) id addr w := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]; exact liveSz_with h rfl rfl

theorem slot_focus {m : Mem.Concrete.State} {id addr n : Int} {w : Nat} (ann : List Annot)
    (h : TSlot m id addr w n) : TSlot (focusMemory ann m) id addr w n := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  obtain ⟨live, plain, bytes⟩ := h
  rw [hl]
  exact ⟨liveSz_with live rfl rfl, plain, bytes⟩

theorem slot_nextExcluded {m : Mem.Concrete.State} {id addr n : Int} {w : Nat}
    (h : TSlot m id addr w n) (k : Nat) : TSlot {m with nextExcluded := k} id addr w n :=
  ⟨liveSz_with h.live rfl rfl, h.plain, h.bytes⟩

theorem Touched.slot {m m' : Mem.Concrete.State} (h : LoadTask.Touched m m') {id addr n : Int}
    {w : Nat} (s : TSlot m id addr w n) : TSlot m' id addr w n := by
  obtain ⟨l, u, rfl⟩ := h
  exact ⟨liveSz_with s.live rfl rfl, s.plain, s.bytes⟩

theorem Touched.live {m m' : Mem.Concrete.State} (h : LoadTask.Touched m m') {id addr : Int}
    {w : Nat} (s : LiveSz m id addr w) : LiveSz m' id addr w := by
  obtain ⟨l, u, rfl⟩ := h
  exact liveSz_with s rfl rfl

/-! ## Create -/

/-- The memory after `create` of an `ity` object. -/
def created (pref : Prefix) (ann : List Annot) (ity : IntegerType) (m : Mem.Concrete.State) :
    Mem.Concrete.State :=
  Mem.Concrete.updateLastAllocation
    { Mem.Concrete.writeRepresentation (nextAddress m (width ity))
        (Mem.Concrete.plainBytes (List.replicate (width ity) none)) m with
      nextId := m.nextId + 1
      lastAddress := nextAddress m (width ity)
      allocations := m.allocations.insert m.nextId
        ({base := nextAddress m (width ity), size := width ity,
          objectType := some (tyType ann ity)} : Mem.Concrete.Allocation)
      lastUsed := some m.nextId }
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}

theorem create_apply (pref : Prefix) (ann : List Annot) {ity : IntegerType}
    (hs : supported ity = true) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextAddress m (width ity)) :
    Reaches file labels
      ⟨.apply (.memory (.create pref)) [.object (.integer (width ity)), .ctype (tyType ann ity)], k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextAddress m (width ity))))), k,
        created pref ann ity m⟩ :=
  Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest,
      Mem.Concrete.allocate_ty (layout_of hs) (width_pos hs) _ ann m hpos, created])

theorem created_stdout (pref : Prefix) (ann : List Annot) (ity : IntegerType) (m : Mem.Concrete.State) :
    (created pref ann ity m).stdout = m.stdout := by
  simp [created, Actions.updateLastAllocation_stdout, Actions.writeRepresentation_stdout]

theorem created_live (pref : Prefix) (ann : List Annot) (ity : IntegerType) (m : Mem.Concrete.State)
    (hdead : m.nextId ∉ m.dead) :
    LiveSz (created pref ann ity m) m.nextId (nextAddress m (width ity)) (width ity) := by
  refine ⟨?_, ?_⟩
  · simp [created, Locals.updateLastAllocation_dead, Locals.writeRepresentation_dead, hdead]
  · let A : Mem.Concrete.Allocation :=
      { base := nextAddress m (width ity), size := width ity, objectType := some (tyType ann ity)
        readonlyKind := Mem.Concrete.readonlyKind pref }
    refine ⟨A, ?_, rfl, rfl, rfl, rfl⟩
    simp [created, Mem.Concrete.updateLastAllocation]
    rfl

theorem created_lastAddress (pref : Prefix) (ann : List Annot) (ity : IntegerType)
    (m : Mem.Concrete.State) : (created pref ann ity m).lastAddress = nextAddress m (width ity) := by
  simp [created, Locals.updateLastAllocation_lastAddress]

theorem created_dead (pref : Prefix) (ann : List Annot) (ity : IntegerType) (m : Mem.Concrete.State) :
    (created pref ann ity m).dead = m.dead := by
  simp [created, Locals.updateLastAllocation_dead, Locals.writeRepresentation_dead]

theorem created_nextId (pref : Prefix) (ann : List Annot) (ity : IntegerType) (m : Mem.Concrete.State) :
    (created pref ann ity m).nextId = m.nextId + 1 := by
  unfold created Mem.Concrete.updateLastAllocation
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape (nextAddress m (width ity))
    (Mem.Concrete.plainBytes (List.replicate (width ity) none)) m
  rw [hw]
  split
  · rfl
  · split <;> rfl

theorem nextAddress_focus (ann : List Annot) (m : Mem.Concrete.State) (w : Nat) :
    nextAddress (focusMemory ann m) w = nextAddress m w := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]; rfl

theorem focus_nextId (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).nextId = m.nextId := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem focus_dead (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).dead = m.dead := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem focus_lastAddress (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).lastAddress = m.lastAddress := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

theorem focus_stdout (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).stdout = m.stdout := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]

/-- The next address is aligned below the last one: the new object ends at or below it. -/
theorem nextAddress_le (m : Mem.Concrete.State) {w : Nat} (hw : 0 < w) :
    nextAddress m w + w ≤ m.lastAddress := by
  unfold nextAddress
  have := Int.emod_nonneg (m.lastAddress - w) (show (w : Int) ≠ 0 by omega)
  omega

theorem nextAddress_ge (m : Mem.Concrete.State) {w : Nat} (hw : 0 < w) :
    m.lastAddress - 2 * w < nextAddress m w := by
  unfold nextAddress
  have := Int.emod_lt_of_pos (m.lastAddress - w) (show (0 : Int) < w by omega)
  omega

/-- `ity`, as an operand. -/
abbrev tyVal (a c : List Annot) (ity : IntegerType) : PE :=
  .mk a () (.val (.ctype (.mk c (.basic (.integer ity)))))

theorem eval_tyVal (tags : Mem.Concrete.Tags) (env : Env) (a c : List Annot) (ity : IntegerType) :
    Eval file tags env (.inl (tyVal a c ity)) (.inl (.ctype (tyType c ity))) := .val

theorem alignof_ty (tags : Mem.Concrete.Tags) (c : List Annot) {ity : IntegerType}
    (hs : supported ity = true) :
    primitive (.ctor .ivAlignof) [.ctype (tyType c ity)] tags =
      .ok (.object (.integer (width ity))) := by
  have hl := Mem.Concrete.layout_tyType (layout_of hs) tags c
  unfold tyType at hl ⊢
  simp [primitive, Mem.Concrete.alignment, hl, integer, bind, Except.bind, pure, Except.pure]

/-- `create(Ivalignof(T), T)`. -/
theorem create_reaches (ann a1 a2 a3 c1 c2 : List Annot) (l : Loc) (u : Unit) (pref : Prefix)
    {ity : IntegerType} (hs : supported ity = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextAddress m (width ity)) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.create (.mk a1 () (.ctor .ivAlignof [tyVal a2 c1 ity])) (tyVal a3 c2 ity) pref))))) env, k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextAddress m (width ity))))), k,
        created pref c2 ity (focusMemory ann m)⟩ := by
  have hev : Eval file (tagsOf file m) env
      (.inr [.mk a1 () (.ctor .ivAlignof [tyVal a2 c1 ity]), tyVal a3 c2 ity])
      (.inr [.object (.integer (width ity)), .ctype (tyType c2 ity)]) :=
    .cons (.ctor (.cons (eval_tyVal _ env a2 c1 ity) .nil) (alignof_ty _ c1 hs))
      (.cons (eval_tyVal _ env a3 c2 ity) .nil)
  refine (Locals.action_reaches Locals.request_create hev).trans ?_
  rw [← nextAddress_focus ann m, ← focus_nextId ann m]
  exact create_apply pref c2 hs k _ (by rw [nextAddress_focus]; exact hpos)

/-! ## Store -/

/-- The memory after a store of `n` into the `w`-byte object at `addr`. -/
def stored (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) : Mem.Concrete.State :=
  {Mem.Concrete.writeRepresentation addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w n)) m with lastUsed := some id}

theorem stored_stdout (m : Mem.Concrete.State) (id addr : Int) (w : Nat) (n : Int) :
    (stored m id addr w n).stdout = m.stdout := by
  simp [stored, Actions.writeRepresentation_stdout]

theorem stored_slot {m : Mem.Concrete.State} {id addr : Int} {w : Nat} (h : LiveSz m id addr w)
    (n : Int) : TSlot (stored m id addr w n) id addr w n := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w n)) m
  have hlen : (Mem.Concrete.encodeInteger w n).length = w := Mem.Concrete.encodeInteger_length w n
  refine ⟨?_, ?_, ?_⟩
  · unfold stored; rw [hw]; exact liveSz_with h rfl rfl
  · intro i hi
    exact Locals.plain_write _ addr m i (by omega)
  · have := Locals.fetch_write (Mem.Concrete.encodeInteger w n) addr m
    rw [hlen] at this
    exact this

theorem live_stored {m : Mem.Concrete.State} {id addr : Int} {v : Nat} (h : LiveSz m id addr v)
    (wid waddr : Int) (w : Nat) (value : Int) : LiveSz (stored m wid waddr w value) id addr v := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape waddr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w value)) m
  unfold stored
  rw [hw]
  exact liveSz_with h rfl rfl

/-- The frame rule for an integer store. -/
theorem slot_stored {m : Mem.Concrete.State} {id addr value : Int} {v : Nat}
    (h : TSlot m id addr v value) (wid waddr : Int) (w : Nat) (wvalue : Int)
    (apart : Apart waddr w addr v) :
    TSlot (stored m wid waddr w wvalue) id addr v value := by
  have len : (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w wvalue)).length = w := by
    simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]
  refine ⟨live_stored h.live _ _ _ _, ?_, ?_⟩
  · intro i hi
    change (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w wvalue)) m).pointerBytes.lookup
        (addr + i) = none
    rw [Slots.pointerByte_writeRepresentation _ waddr (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)]
    exact h.plain i hi
  · change Mem.Concrete.fetchBytes v addr (Mem.Concrete.writeRepresentation waddr
      (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger w wvalue)) m).bytes = _
    rw [Slots.fetchBytes_writeRepresentation _ waddr addr v m (by rwa [len])]
    exact h.bytes

@[simp] theorem intType_ty (ann : List Annot) (ity : IntegerType) :
    Dynamics.intType (tyType ann ity) = some ity := rfl

@[simp] theorem unatomic_ty (ann : List Annot) (ity : IntegerType) :
    Mem.Concrete.unatomic (tyType ann ity) = tyType ann ity := rfl

/-- `store(T, p, Specified n)` into a live `T` object. -/
theorem store_apply (ann : List Annot) {ity : IntegerType} (hs : supported ity = true)
    (k : List Frame) {m : Mem.Concrete.State} {id addr : Int}
    (h : LiveSz m id addr (width ity)) {n : Int} (hn : Fits ity n) :
    ∃ xs, Reaches file labels
      ⟨.apply (.memory .store) [.ctype (tyType ann ity), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))], k, m⟩
      ⟨.value .unit, .annotations xs :: k, stored m id addr (width ity) n⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .store) [.ctype (tyType ann ity), .object (.pointer (.allocated id addr)),
        .loaded (.specified (.integer n))], k, m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory,
    Mem.Concrete.store_ty (layout_of hs) _ ann h hn,
    Mem.Concrete.access_ty (layout_of hs) _ ann h, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  exact ⟨_, Actions.memory_reaches (by intro o h; cases h) hr⟩

/-! ## Load -/

theorem load_apply (ann : List Annot) {ity : IntegerType} (hs : supported ity = true)
    (k : List Frame) {m : Mem.Concrete.State} {id addr n : Int}
    (slot : TSlot m id addr (width ity) n) (hn : Fits ity n) :
    ∃ xs, Reaches file labels
      ⟨.apply (.memory .load) [.ctype (tyType ann ity), .object (.pointer (.allocated id addr))], k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), .annotations xs :: k,
        {m with lastUsed := some id}⟩ := by
  obtain ⟨r, hr⟩ : ∃ r, request file labels
      ⟨.apply (.memory .load) [.ctype (tyType ann ity), .object (.pointer (.allocated id addr))], k,
        m⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, fromMemory,
    Mem.Concrete.load_ty (layout_of hs) _ ann slot.live slot.plain hn slot.bytes,
    Mem.Concrete.access_ty (layout_of hs) _ ann slot.live, bind,
    Except.bind, pure, Except.pure] at hr'
  subst hr'
  exact ⟨_, Actions.memory_reaches (by intro o h; cases h) hr⟩

/-- `load(T, p)` of the slot holding `n`. -/
theorem load_reaches (ann a1 a2 c1 : List Annot) (l : Loc) (u : Unit) (p : Sym)
    {ity : IntegerType} (hs : supported ity = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr n : Int} (hp : env.lookup p = some (.object (.pointer (.allocated id addr))))
    (hn : Fits ity n) (slot : TSlot m id addr (width ity) n) :
    ∃ xs, Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.load (tyVal a1 c1 ity) (.mk a2 () (.sym p)) .na))))) env, k, m⟩
      ⟨.value (.loaded (.specified (.integer n))), .annotations xs :: k,
        {focusMemory ann m with lastUsed := some id}⟩ := by
  have hev : Eval file (tagsOf file m) env (.inr [tyVal a1 c1 ity, .mk a2 () (.sym p)])
      (.inr [.ctype (tyType c1 ity), .object (.pointer (.allocated id addr))]) :=
    .cons (eval_tyVal _ env a1 c1 ity) (.cons (.sym hp) .nil)
  obtain ⟨xs, hld⟩ := load_apply (file := file) (labels := labels) c1 hs k (slot_focus ann slot) hn
  exact ⟨xs, (Locals.action_reaches Locals.request_load hev).trans hld⟩

/-! ## Kill -/

theorem kill_apply (ann : List Annot) {ity : IntegerType} (hs : supported ity = true)
    (k : List Frame) {m : Mem.Concrete.State} {id addr : Int} (h : LiveSz m id addr (width ity)) :
    Reaches file labels
      ⟨.apply (.memory (.kill (tyType ann ity))) [.object (.pointer (.allocated id addr))], k, m⟩
      ⟨.value .unit, k, Locals.killed m id⟩ :=
  Actions.memory_reaches (name := "Kill") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest,
      Mem.Concrete.kill_ty (layout_of hs) _ ann h, Locals.killed, bind, Except.bind, pure,
      Except.pure])

/-- `kill(T, x)` of a live `T` object. -/
theorem kill_reaches (ann a2 c1 : List Annot) (l : Loc) (u : Unit) (x : Sym)
    {ity : IntegerType} (hs : supported ity = true)
    (env : Env) (k : List Frame) (m : Mem.Concrete.State)
    {id addr : Int} (hx : env.lookup x = some (.object (.pointer (.allocated id addr))))
    (live : LiveSz m id addr (width ity)) :
    Reaches file labels
      ⟨.effectExpr (.mk ann (.action (.mk .pos (.mk l u
        (.kill (.static (tyType c1 ity)) (.mk a2 () (.sym x))))))) env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  have hev : Eval file (tagsOf file m) env (.inr [.mk a2 () (.sym x)])
      (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym hx) .nil
  exact (Locals.action_reaches Locals.request_kill hev).trans
    (kill_apply c1 hs k (liveSz_focus ann live))

theorem killed_stdout (m : Mem.Concrete.State) (id : Int) : (Locals.killed m id).stdout = m.stdout :=
  rfl

/-- Killing a different allocation keeps a live object. -/
theorem live_killed {m : Mem.Concrete.State} {id addr : Int} {w : Nat} (h : LiveSz m id addr w)
    (other : Int) (ne : id ≠ other) : LiveSz (Locals.killed m other) id addr w := by
  refine ⟨?_, ?_⟩
  · simpa [Locals.killed, ne] using h.alive
  · obtain ⟨a, ha, rest⟩ := h.found
    refine ⟨a, ?_, rest⟩
    change (m.allocations.erase other).lookup id = some a
    simp only [Map.lookup, Map.erase]
    rw [Finmap.lookup_erase_ne (show MapKey.key id ≠ MapKey.key other from ne)]
    exact ha

/-- Killing a different allocation keeps a slot. -/
theorem slot_killed {m : Mem.Concrete.State} {id addr value : Int} {w : Nat}
    (h : TSlot m id addr w value) (other : Int) (ne : id ≠ other) :
    TSlot (Locals.killed m other) id addr w value :=
  ⟨live_killed h.live other ne, h.plain, h.bytes⟩

/-- Creating another object keeps a live object. -/
theorem live_created {m : Mem.Concrete.State} {id addr : Int} {w : Nat} (h : LiveSz m id addr w)
    (pref : Prefix) (ann : List Annot) (ity : IntegerType) (fresh : id ≠ m.nextId) :
    LiveSz (created pref ann ity m) id addr w := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape (nextAddress m (width ity))
    (Mem.Concrete.plainBytes (List.replicate (width ity) none)) m
  refine ⟨?_, ?_⟩
  · rw [created_dead]; exact h.alive
  · obtain ⟨old, found, rest⟩ := h.found
    refine ⟨old, ?_, rest⟩
    unfold created Mem.Concrete.updateLastAllocation
    rw [hw]
    simp only [Map.lookup_insert]
    simp only [Map.lookup_insert_of_key_ne _ _ (show MapKey.key id ≠ MapKey.key m.nextId from fresh)]
    exact found

theorem updateLastAllocation_pointerBytes (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).pointerBytes = s.pointerBytes := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · rfl
  · split <;> rfl

theorem updateLastAllocation_bytes (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).bytes = s.bytes := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · rfl
  · split <;> rfl

/-- Allocating another object keeps every disjoint slot. -/
theorem slot_created {m : Mem.Concrete.State} {id addr value : Int} {v : Nat}
    (h : TSlot m id addr v value) (pref : Prefix) (ann : List Annot) (ity : IntegerType)
    (fresh : id ≠ m.nextId) (apart : Apart (nextAddress m (width ity)) (width ity) addr v) :
    TSlot (created pref ann ity m) id addr v value := by
  let bs := Mem.Concrete.plainBytes (List.replicate (width ity) none)
  let a := nextAddress m (width ity)
  have len : bs.length = width ity := by simp [bs, Mem.Concrete.plainBytes]
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape a bs m
  have hpb : (created pref ann ity m).pointerBytes = pb := by
    unfold created
    rw [updateLastAllocation_pointerBytes]
    show (Mem.Concrete.writeRepresentation a bs m).pointerBytes = pb
    rw [hw]
  have hb : (created pref ann ity m).bytes = b := by
    unfold created
    rw [updateLastAllocation_bytes]
    show (Mem.Concrete.writeRepresentation a bs m).bytes = b
    rw [hw]
  refine ⟨live_created h.live pref ann ity fresh, ?_, ?_⟩
  · intro i hi
    rw [hpb]
    have hp := Slots.pointerByte_writeRepresentation bs a (addr + i) m (by
      rw [len]
      rcases apart with h | h
      · right; omega
      · left; omega)
    rw [hw] at hp
    exact hp.trans (h.plain i hi)
  · rw [hb]
    have hb' := Slots.fetchBytes_writeRepresentation bs a addr v m (by rwa [len])
    rw [hw] at hb'
    exact hb'.trans h.bytes

end Silmaril.Compile.Core.Verified.TyActions
