module

public import Silmaril.Compiler.Core.Verified.StateMem.Defs
public import Silmaril.Compiler.Core.Verified.Globals.Defs

/-! # Locals of a struct type wrapping one `int`

A struct type wrapping an `int` (`isWrap`: `IntWrap.wraps`) has the size and alignment of an `int`,
so its `create`, the store of `Unspecified` that declares it (`T s;`) and its `kill` are the memory
transitions of an `int` local: the same slot, the same bytes. Only the allocation records the
struct type (`createdAs`, where `int` creation is `Actions.created`).

`createAny`, `uninitWrap`, `killAny` recognise these actions for both kinds of locals;
`createAny_reaches` gives what the block proofs use of a creation (`Created`), `killAny_reaches`
the memory after a kill (`Locals.killed`), `uninitWrap_reaches` that after the declaration
(`Uninitialized.stored`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.WrapObj

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Eval tagsOf Reaches)
open ReturnLit (Eff)
open ReturnConst (focusMemory)
open Mem.Concrete (Tags typeLayout nextIntAddress LiveInt)
open Locals (Slot)

/-! ## Memory -/

/-- `T` wraps an `int` (at most `IntWrap.depth` levels). -/
def isWrap (defs : Map Sym (Loc × TagDefinition)) (T : Sym) : Bool :=
  (IntWrap.wraps defs IntWrap.depth T).isSome

theorem layout {tags : Tags} {T : Sym} (h : isWrap tags.definitions T = true) (ann : List Annot) :
    ∃ ms, typeLayout 64 tags (.mk ann (.struct T)) = .ok ⟨4, 4, ms⟩ := by
  obtain ⟨⟨f, ty⟩, hw⟩ := Option.isSome_iff_exists.mp h
  exact ⟨_, IntWrap.wraps_layout rfl IntWrap.depth hw 64 (by decide) ann⟩

theorem access {tags : Tags} {T : Sym} (h : isWrap tags.definitions T = true) (ann : List Annot)
    {s : Mem.Concrete.State} {id addr : Int} (live : LiveInt s id addr) :
    Mem.Concrete.accessTyped tags s (.mk ann (.struct T)) (.allocated id addr) = .ok (id, addr, 4) := by
  obtain ⟨ms, hl⟩ := layout h ann
  obtain ⟨alive, a, look, base, size, atomic, _⟩ := live
  simp [Mem.Concrete.accessTyped, hl, alive, look, base, size, Mem.Concrete.checkAtomic, atomic,
    bind, Except.bind, pure, Except.pure]

theorem kill {tags : Tags} {T : Sym} (h : isWrap tags.definitions T = true) (ann : List Annot)
    {s : Mem.Concrete.State} {id addr : Int} (live : LiveInt s id addr) :
    Mem.Concrete.killTyped tags s (.mk ann (.struct T)) (.allocated id addr) =
      .ok ((), { s with
        allocations := s.allocations.erase id
        dead := id :: s.dead
        lastUsed := some id }) := by
  obtain ⟨alive, a, look, base, size, atomic, ro⟩ := live
  simp [Mem.Concrete.killTyped, access h ann ⟨alive, a, look, base, size, atomic, ro⟩, look, base,
    bind, Except.bind, pure, Except.pure]

theorem store_unspecified {tags : Tags} {T T' : Sym} (h : isWrap tags.definitions T = true)
    (h' : isWrap tags.definitions T' = true) (ann vann : List Annot) {m : Mem.Concrete.State}
    {id addr : Int} (live : LiveInt m id addr) :
    Mem.Concrete.storeTyped tags m (.mk ann (.struct T)) (.allocated id addr)
      (.unspecified (.mk vann (.struct T'))) = .ok ((addr, 4), Uninitialized.stored m id addr) := by
  obtain ⟨ms, hl⟩ := layout h' vann
  obtain ⟨a, look, base, size, atomic, ro⟩ := live.found
  simp [Mem.Concrete.storeTyped, access h ann live, Mem.Concrete.checkWritable, look, ro,
    Mem.Concrete.represent, hl, Uninitialized.stored, Mem.Concrete.plainBytes,
    bind, Except.bind, pure, Except.pure]

theorem alignof {tags : Tags} {T : Sym} (h : isWrap tags.definitions T = true) (c : List Annot) :
    primitive (.ctor .ivAlignof) [.ctype (.mk c (.struct T))] tags = .ok (.object (.integer 4)) := by
  obtain ⟨ms, hl⟩ := layout h c
  simp [primitive, Mem.Concrete.alignment, hl, integer, bind, Except.bind, pure, Except.pure]

/-- The memory after the creation of a 4-byte, 4-aligned object of type `ty`. -/
def createdAs (pref : Prefix) (ty : Ctype) (m : Mem.Concrete.State) : Mem.Concrete.State :=
  Mem.Concrete.updateLastAllocation
    { Mem.Concrete.writeRepresentation (nextIntAddress m)
        (Mem.Concrete.plainBytes (List.replicate 4 none)) m with
      nextId := m.nextId + 1
      lastAddress := nextIntAddress m
      allocations := m.allocations.insert m.nextId
        ({base := nextIntAddress m, size := 4, objectType := some ty} : Mem.Concrete.Allocation)
      lastUsed := some m.nextId }
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}

theorem allocate {tags : Tags} {T : Sym} (h : isWrap tags.definitions T = true) (ann : List Annot)
    (s : Mem.Concrete.State) (hpos : 0 < nextIntAddress s) :
    Mem.Concrete.allocateTyped tags s 4 (.mk ann (.struct T)) =
      .ok (.allocated s.nextId (nextIntAddress s),
        { Mem.Concrete.writeRepresentation (nextIntAddress s)
            (Mem.Concrete.plainBytes (List.replicate 4 none)) s with
          nextId := s.nextId + 1
          lastAddress := nextIntAddress s
          allocations := s.allocations.insert s.nextId
            ({base := nextIntAddress s, size := 4, objectType := some (.mk ann (.struct T))} :
              Mem.Concrete.Allocation)
          lastUsed := some s.nextId }) := by
  obtain ⟨ms, hl⟩ := layout h ann
  unfold nextIntAddress at hpos ⊢
  have hn : ¬ (s.lastAddress - 4 - (s.lastAddress - 4) % 4 ≤ 0) := by omega
  simp only [Mem.Concrete.allocateTyped, hl, bind, Except.bind, pure, Except.pure]
  rw [ite_eq_right_of_eq_false _ _ (by simp), ite_eq_right_of_eq_false _ _ (by simpa using hn)]
  rw [show (4 : Int).toNat = 4 from rfl]
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape
    (s.lastAddress - 4 - (s.lastAddress - 4) % 4) (Mem.Concrete.plainBytes (List.replicate 4 none)) s
  simp only [hw]

/-! ## What a creation keeps -/

/-- What the block proofs use of the memory `m₁` after creating a local in `m`. -/
structure Created (m m₁ : Mem.Concrete.State) : Prop where
  live : ∀ {id addr : Int}, LiveInt m id addr → id ≠ m.nextId → LiveInt m₁ id addr
  fresh : m.nextId ∉ m.dead → LiveInt m₁ m.nextId (nextIntAddress m)
  held : ∀ {id addr n : Int}, Globals.Held m id addr n → Globals.Held m₁ id addr n
  last : m₁.lastAddress = nextIntAddress m
  dead : m₁.dead = m.dead
  next : m₁.nextId = m.nextId + 1
  stdout : m₁.stdout = m.stdout

theorem created_int (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    Created m (Actions.created pref ann m) where
  live h f := StateMem.live_created h pref ann f
  fresh := Locals.created_live pref ann m
  held h := Globals.held_created pref ann h
  last := Locals.created_lastAddress pref ann m
  dead := Locals.created_dead pref ann m
  next := Globals.created_nextId pref ann m
  stdout := Actions.created_stdout pref ann m

theorem createdAs_shape (pref : Prefix) (ty : Ctype) (m : Mem.Concrete.State) :
    ∃ b pb, createdAs pref ty m =
      {m with
        bytes := b
        pointerBytes := pb
        nextId := m.nextId + 1
        lastAddress := nextIntAddress m
        allocations := (m.allocations.insert m.nextId
          ({base := nextIntAddress m, size := 4, objectType := some ty} :
            Mem.Concrete.Allocation)).insert m.nextId
          ({base := nextIntAddress m, size := 4, objectType := some ty,
            readonlyKind := Mem.Concrete.readonlyKind pref} : Mem.Concrete.Allocation),
        lastUsed := some m.nextId} := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape (nextIntAddress m)
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  refine ⟨b, pb, ?_⟩
  unfold createdAs
  rw [hw]
  simp [Mem.Concrete.updateLastAllocation]

theorem created_wrap (pref : Prefix) (ty : Ctype) (m : Mem.Concrete.State) :
    Created m (createdAs pref ty m) := by
  obtain ⟨b, pb, shape⟩ := createdAs_shape pref ty m
  refine ⟨fun {id addr} h fresh => ?_, fun hdead => ?_, fun {id addr n} h => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [shape]; exact h.alive
    · obtain ⟨old, found, rest⟩ := h.found
      refine ⟨old, ?_, rest⟩
      rw [shape]
      simpa only [Map.lookup_insert_of_key_ne _ _ (show MapKey.key id ≠ MapKey.key m.nextId from
        fresh)] using found
  · refine ⟨?_, ?_⟩
    · rw [shape]; exact hdead
    · let A : Mem.Concrete.Allocation :=
        { base := nextIntAddress m, size := 4, objectType := some ty
          readonlyKind := Mem.Concrete.readonlyKind pref }
      refine ⟨A, ?_, rfl, rfl, rfl, rfl⟩
      rw [shape]
      simp only [Map.lookup_insert]
      rfl
  · obtain ⟨slot, below, above⟩ := h
    have hne : id ≠ m.nextId := by omega
    let W := Mem.Concrete.writeRepresentation (nextIntAddress m)
      (Mem.Concrete.plainBytes (List.replicate 4 none)) m
    have hW : Slot W id addr n := Globals.slot_write slot _ _
      (by simp [Mem.Concrete.plainBytes, nextIntAddress]; omega)
    obtain ⟨al, hal⟩ := Globals.updateLastAllocation_eq
      { W with
        nextId := m.nextId + 1
        lastAddress := nextIntAddress m
        allocations := m.allocations.insert m.nextId
          ({base := nextIntAddress m, size := 4, objectType := some ty} : Mem.Concrete.Allocation)
        lastUsed := some m.nextId }
      fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}
    have hlook := Globals.updateLastAllocation_lookup
      { W with
        nextId := m.nextId + 1
        lastAddress := nextIntAddress m
        allocations := m.allocations.insert m.nextId
          ({base := nextIntAddress m, size := 4, objectType := some ty} : Mem.Concrete.Allocation)
        lastUsed := some m.nextId }
      (fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}) rfl hne
    refine ⟨?_, ?_, ?_⟩
    · unfold createdAs
      refine Globals.slot_of hW ?_ ?_ ?_ ?_
      · rw [hal]
      · rw [hlook]
        simp only
        rw [Map.lookup_insert_of_key_ne _ _ hne, (Mem.Concrete.writeRepresentation_allocations _ _ m).1]
      · intro i _; rw [hal]
      · rw [hal]
    · unfold createdAs; rw [hal]; simp only; omega
    · unfold createdAs; rw [hal]; simp only [nextIntAddress]; omega
  · rw [shape]
  · rw [shape]
  · rw [shape]
  · unfold createdAs
    simp [Actions.updateLastAllocation_stdout, Actions.writeRepresentation_stdout]

/-! ## Actions -/

variable {file : Program} {labels : Labels}

theorem create_apply (pref : Prefix) (ann : List Annot) {T : Sym}
    (h : isWrap file.tagDefs T = true) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) :
    Reaches file labels
      ⟨.apply (.memory (.create pref)) [.object (.integer 4), .ctype (.mk ann (.struct T))], k, m⟩
      ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), k,
        createdAs pref (.mk ann (.struct T)) m⟩ :=
  Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest,
      allocate (tags := ⟨file.tagDefs, m.enumTypes⟩) h ann m hpos, createdAs])

/-- `create(Ivalignof(T), T')`, `T` and `T'` wrappers. -/
def createWrap (file : Program) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.create (.mk _ () (.ctor .ivAlignof
      [.mk _ () (.val (.ctype (.mk _ (.struct T))))]))
      (.mk _ () (.val (.ctype (.mk _ (.struct T'))))) _)))) =>
      isWrap file.tagDefs T && isWrap file.tagDefs T'
  | _ => false

/-- The creation of an `int` local or of a wrapper local. -/
def createAny (file : Program) (e : Eff) : Bool := Locals.createInt e || createWrap file e

theorem createAny_reaches {e : Eff} (h : createAny file e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) :
    ∃ ann m₁, Created (focusMemory ann m) m₁ ∧ Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value (.object (.pointer (.allocated (focusMemory ann m).nextId (nextIntAddress m)))), k, m₁⟩ := by
  unfold createAny at h
  have h' := Bool.or_eq_true_iff.mp h
  clear h
  rcases h' with h | h
  · unfold Locals.createInt at h
    split at h
    · rename_i ann l u a1 a2 c1 a3 c2 pref
      exact ⟨ann, _, created_int pref c2 _,
        Locals.create_reaches ann a1 a2 a3 c1 c2 l u pref env k m hpos⟩
    · cases h
  · unfold createWrap at h
    split at h
    · rename_i ann l u a1 a2 c1 T a3 c2 T' pref
      simp only [Bool.and_eq_true] at h
      obtain ⟨hT, hT'⟩ := h
      have hev : Eval file (tagsOf file m) env
          (.inr [.mk a1 () (.ctor .ivAlignof [.mk a2 () (.val (.ctype (.mk c1 (.struct T))))]),
            .mk a3 () (.val (.ctype (.mk c2 (.struct T'))))])
          (.inr [.object (.integer 4), .ctype (.mk c2 (.struct T'))]) :=
        .cons (.ctor (.cons .val .nil) (alignof (tags := tagsOf file m) hT c1)) (.cons .val .nil)
      refine ⟨ann, _, created_wrap pref (.mk c2 (.struct T')) (focusMemory ann m),
        (Locals.action_reaches Locals.request_create hev).trans ?_⟩
      rw [← Locals.nextIntAddress_focus ann m]
      exact create_apply pref c2 hT' k _ (by rw [Locals.nextIntAddress_focus]; exact hpos)
    · cases h

theorem kill_apply (ann : List Annot) {T : Sym} (h : isWrap file.tagDefs T = true) (k : List Frame)
    {m : Mem.Concrete.State} {id addr : Int} (live : LiveInt m id addr) :
    Reaches file labels
      ⟨.apply (.memory (.kill (.mk ann (.struct T)))) [.object (.pointer (.allocated id addr))], k, m⟩
      ⟨.value .unit, k, Locals.killed m id⟩ :=
  Actions.memory_reaches (name := "Kill") (by intro o h; cases h) (by
    simp [request, requestAux, awaitsScheduling, memoryRequest,
      kill (tags := ⟨file.tagDefs, m.enumTypes⟩) h ann live, Locals.killed,
      bind, Except.bind, pure, Except.pure])

/-- `kill(T, x)`, `T` a wrapper. -/
def killWrap (file : Program) (x : Sym) : Eff → Bool
  | .mk _ (.action (.mk .pos (.mk _ _ (.kill (.static (.mk _ (.struct T))) (.mk _ () (.sym x')))))) =>
      decide (x'.key = x.key) && isWrap file.tagDefs T
  | _ => false

/-- The kill of an `int` local or of a wrapper local. -/
def killAny (file : Program) (x : Sym) (e : Eff) : Bool := Locals.killInt x e || killWrap file x e

theorem killAny_reaches {x : Sym} {e : Eff} (h : killAny file x e = true) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : ∀ y : Sym, y.key = x.key → env.lookup y = some (.object (.pointer (.allocated id addr))))
    (live : LiveInt m id addr) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, k, Locals.killed (focusMemory ann m) id⟩ := by
  unfold killAny at h
  have h' := Bool.or_eq_true_iff.mp h
  clear h
  rcases h' with h | h
  · unfold Locals.killInt at h
    split at h
    · rename_i ann l u c1 a2 x'
      exact ⟨ann, Locals.kill_reaches ann a2 c1 l u x' env k m (hx x' (of_decide_eq_true h)) live⟩
    · cases h
  · unfold killWrap at h
    split at h
    · rename_i ann l u c1 T a2 x'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      have hev : Eval file (tagsOf file m) env (.inr [.mk a2 () (.sym x')])
          (.inr [.object (.pointer (.allocated id addr))]) := .cons (.sym (hx x' h.1)) .nil
      exact ⟨ann, (Locals.action_reaches Locals.request_kill hev).trans
        (kill_apply c1 h.2 k (Locals.liveInt_focus ann live))⟩
    · cases h

theorem store_apply (ann vann : List Annot) {T T' : Sym} (h : isWrap file.tagDefs T = true)
    (h' : isWrap file.tagDefs T' = true) (k : List Frame) {m : Mem.Concrete.State} {id addr : Int}
    (live : LiveInt m id addr) :
    Reaches file labels
      ⟨.apply (.memory .store) [.ctype (.mk ann (.struct T)), .object (.pointer (.allocated id addr)),
        .loaded (.unspecified (.mk vann (.struct T')))], k, m⟩
      ⟨.value .unit, .annotations [StoreTask.writeAccess k addr] :: k,
        Uninitialized.stored m id addr⟩ := by
  apply Actions.memory_reaches (name := "Store") (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory,
    store_unspecified (tags := ⟨file.tagDefs, m.enumTypes⟩) h h' ann vann live,
    access (tags := ⟨file.tagDefs, m.enumTypes⟩) h ann live,
    StoreTask.writeAccess, bind, Except.bind, pure, Except.pure]
  rfl

/-- `T x;` for a wrapper `T`: the store of `Unspecified(T)`. -/
def uninitWrap (file : Program) : Eff → Option Sym
  | .mk _ (.action (.mk .pos (.mk _ _ (.store false
      (.mk _ () (.val (.ctype (.mk _ (.struct T)))))
      (.mk _ () (.sym x))
      (.mk _ () (.val (.loaded (.unspecified (.mk _ (.struct T')))))) .na)))) =>
      if isWrap file.tagDefs T = true ∧ isWrap file.tagDefs T' = true then some x else none
  | _ => none

theorem uninitWrap_reaches {e : Eff} {x : Sym} (h : uninitWrap file e = some x) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) {id addr : Int}
    (hx : env.lookup x = some (.object (.pointer (.allocated id addr)))) (live : LiveInt m id addr) :
    ∃ ann, Reaches file labels ⟨.effectExpr e env, k, m⟩
      ⟨.value .unit, .annotations [StoreTask.writeAccess k addr] :: k,
        Uninitialized.stored (focusMemory ann m) id addr⟩ := by
  unfold uninitWrap at h
  split at h
  · rename_i ann l u a1 c1 T a2 x' a3 c3 T'
    split at h
    · rename_i hc
      cases h
      have eval : Eval file (tagsOf file m) env
          (.inr [.mk a1 () (.val (.ctype (.mk c1 (.struct T)))), .mk a2 () (.sym x),
            .mk a3 () (.val (.loaded (.unspecified (.mk c3 (.struct T')))))])
          (.inr [.ctype (.mk c1 (.struct T)), .object (.pointer (.allocated id addr)),
            .loaded (.unspecified (.mk c3 (.struct T')))]) :=
        .cons .val (.cons (.sym hx) (.cons .val .nil))
      exact ⟨ann, (Locals.action_reaches Locals.request_store eval).trans
        (store_apply c1 c3 hc.1 hc.2 k (Locals.liveInt_focus ann live))⟩
    · cases h
  · cases h

end Silmaril.Compile.Core.Verified.WrapObj
