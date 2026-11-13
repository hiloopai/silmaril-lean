module

public import Silmaril.Compiler.Core.Verified.ReturnExpr.Defs

/-! # Startup with `int` globals

Cerberus elaborates a file-scope `int x = n;` (and the tentative `int x;`, with `n = 0`) to the
global definition

```
let strong a = create(Ivalignof(int), int) in
  let strong t = bound(pure(n)) in store(int, a, conv_loaded_int(int, t)) ; pure(a)
```

and the Core dynamics runs the definitions in file order before `main` (`Dynamics.initial`,
the `.globals` control), binding each global's symbol to the pointer its initialiser returns.
`initial_reaches_body`: for a file whose definitions are all of this form
(`inits file = some gs`), the dynamics reaches `main`'s body with an environment in which
every global `x` of `gs` points to a live `int` object holding its initialiser (`Slot`), under
one annotation frame, with empty stdout. The objects are never killed: the `errno` startup
allocates below them and writes only its own object.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Globals

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.PureEval (Reaches next_reaches Eval tagsOf)
open ReturnConst (focusMemory)
open ReturnLit (Eff NoBoundary ReturnLabel saveFree noBoundary_cons)
open ConvInt (isConvLoadedInt IsInt)
open Locals (Slot createInt)
open Mem.Concrete (LiveInt IntRange PlainAt nextIntAddress)

variable {file : Program} {labels : Labels}

/-! ## Memory facts -/

/-- Pointer-copy metadata outside the written range is unchanged. -/
theorem pointerBytes_write_outside (bs : Mem.Concrete.Representation) (a c : Int)
    (s : Mem.Concrete.State) (h : c < a ∨ a + bs.length ≤ c) :
    (Mem.Concrete.writeRepresentation a bs s).pointerBytes.lookup c = s.pointerBytes.lookup c := by
  induction bs generalizing a with
  | nil => rfl
  | cons x bs ih =>
    obtain ⟨b, prov⟩ := x
    have hne : MapKey.key c ≠ MapKey.key a := by
      change c ≠ a
      rcases h with h | h
      · omega
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
    have h' : c < a + 1 ∨ a + 1 + bs.length ≤ c := by
      rcases h with h | h
      · left; omega
      · right; simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega
    have := ih (a + 1) h'
    cases prov with
    | none =>
      simp only [Mem.Concrete.writeRepresentation, Map.lookup, Map.erase] at this ⊢
      rw [Finmap.lookup_erase_ne hne]
      exact this
    | some pr =>
      simp only [Mem.Concrete.writeRepresentation]
      rw [Map.lookup_insert_of_key_ne _ _ hne]
      exact this

/-- A slot carries over to a memory with the same lifetime, allocation and bytes there. -/
theorem slot_of {m m' : Mem.Concrete.State} {id addr v : Int} (h : Slot m id addr v)
    (hd : m'.dead = m.dead) (ha : m'.allocations.lookup id = m.allocations.lookup id)
    (hp : ∀ i : Nat, i < 4 → m'.pointerBytes.lookup (addr + i) = m.pointerBytes.lookup (addr + i))
    (hb : Mem.Concrete.fetchBytes 4 addr m'.bytes = Mem.Concrete.fetchBytes 4 addr m.bytes) :
    Slot m' id addr v := by
  obtain ⟨⟨alive, found⟩, plain, bytes⟩ := h
  exact ⟨⟨by rw [hd]; exact alive, by rw [ha]; exact found⟩,
    fun i hi => by rw [hp i hi]; exact plain i hi, by rw [hb]; exact bytes⟩

/-- A write below a slot keeps it. -/
theorem slot_write {m : Mem.Concrete.State} {id addr v : Int} (h : Slot m id addr v) (a : Int)
    (bs : Mem.Concrete.Representation) (hab : a + bs.length ≤ addr) :
    Slot (Mem.Concrete.writeRepresentation a bs m) id addr v := by
  have hw := Mem.Concrete.writeRepresentation_allocations a bs m
  refine slot_of h hw.2.1 (by rw [hw.1]) (fun i _ => pointerBytes_write_outside bs a _ m
    (.inr (by omega))) ?_
  rw [Mem.Concrete.writeRepresentation_bytes]
  exact Mem.Concrete.fetch_disjoint 4 addr a _ _ (.inr (by simp; omega))

theorem updateLastAllocation_eq (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    ∃ al, Mem.Concrete.updateLastAllocation s f = {s with allocations := al} := by
  unfold Mem.Concrete.updateLastAllocation
  split
  · exact ⟨s.allocations, rfl⟩
  · split
    · exact ⟨s.allocations, rfl⟩
    · exact ⟨_, rfl⟩

theorem updateLastAllocation_lookup (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) {j id : Int} (hj : s.lastUsed = some j)
    (hne : id ≠ j) :
    (Mem.Concrete.updateLastAllocation s f).allocations.lookup id = s.allocations.lookup id := by
  unfold Mem.Concrete.updateLastAllocation
  rw [hj]
  dsimp only
  split
  · rfl
  · exact Map.lookup_insert_of_key_ne _ _ hne

/-- What a global's object satisfies: its slot, an id already allocated, and an address at or
above the last allocation. -/
structure Held (m : Mem.Concrete.State) (id addr n : Int) : Prop where
  slot : Slot m id addr n
  below : id < m.nextId
  above : m.lastAddress ≤ addr

theorem held_loc {m : Mem.Concrete.State} {id addr n : Int} (l : Loc) (h : Held m id addr n) :
    Held {m with currentLocation := l} id addr n :=
  ⟨slot_of h.slot rfl rfl (fun _ _ => rfl) rfl, h.below, h.above⟩

theorem held_lastUsed {m : Mem.Concrete.State} {id addr n : Int} (u : Option Int)
    (h : Held m id addr n) : Held {m with lastUsed := u} id addr n :=
  ⟨slot_of h.slot rfl rfl (fun _ _ => rfl) rfl, h.below, h.above⟩

theorem held_focus {m : Mem.Concrete.State} {id addr n : Int} (ann : List Annot)
    (h : Held m id addr n) : Held (focusMemory ann m) id addr n := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]; exact held_loc l h

/-- Creating an `int` object keeps the objects above it. -/
theorem held_created {m : Mem.Concrete.State} {id addr n : Int} (pref : Prefix) (ann : List Annot)
    (h : Held m id addr n) : Held (Actions.created pref ann m) id addr n := by
  obtain ⟨slot, below, above⟩ := h
  have hne : id ≠ m.nextId := by omega
  let W := Mem.Concrete.writeRepresentation (nextIntAddress m)
    (Mem.Concrete.plainBytes (List.replicate 4 none)) m
  have hW : Slot W id addr n := slot_write slot _ _ (by simp [Mem.Concrete.plainBytes, nextIntAddress]; omega)
  obtain ⟨al, hal⟩ := updateLastAllocation_eq
    { W with
      nextId := m.nextId + 1
      lastAddress := nextIntAddress m
      allocations := m.allocations.insert m.nextId
        ({base := nextIntAddress m, size := 4, objectType := some (Mem.Concrete.intType ann)} :
          Mem.Concrete.Allocation)
      lastUsed := some m.nextId }
    fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}
  have hlook := updateLastAllocation_lookup
    { W with
      nextId := m.nextId + 1
      lastAddress := nextIntAddress m
      allocations := m.allocations.insert m.nextId
        ({base := nextIntAddress m, size := 4, objectType := some (Mem.Concrete.intType ann)} :
          Mem.Concrete.Allocation)
      lastUsed := some m.nextId }
    (fun a => {a with readonlyKind := Mem.Concrete.readonlyKind pref}) rfl hne
  refine ⟨?_, ?_, ?_⟩
  · unfold Actions.created
    refine slot_of hW ?_ ?_ ?_ ?_
    · rw [hal]
    · rw [hlook]
      simp only
      rw [Map.lookup_insert_of_key_ne _ _ hne, (Mem.Concrete.writeRepresentation_allocations _ _ m).1]
    · intro i _; rw [hal]
    · rw [hal]
  · unfold Actions.created; rw [hal]; simp only; omega
  · unfold Actions.created; rw [hal]; simp only [nextIntAddress]; omega

/-- A store into an object below keeps the objects above it. -/
theorem held_stored {m : Mem.Concrete.State} {id addr n : Int} (j a v : Int) (ha : a + 4 ≤ addr)
    (h : Held m id addr n) : Held (Locals.stored m j a v) id addr n := by
  obtain ⟨slot, below, above⟩ := h
  refine ⟨Locals.slot_lastUsed _ (slot_write slot _ _ ?_), ?_, ?_⟩
  · simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]; omega
  · simp only [Locals.stored]
    rw [(Mem.Concrete.writeRepresentation_shape _ _ m).choose_spec.choose_spec]
    exact below
  · simp only [Locals.stored]
    rw [(Mem.Concrete.writeRepresentation_shape _ _ m).choose_spec.choose_spec]
    exact above

theorem updateLastAllocation_nextId (s : Mem.Concrete.State)
    (f : Mem.Concrete.Allocation → Mem.Concrete.Allocation) :
    (Mem.Concrete.updateLastAllocation s f).nextId = s.nextId := by
  obtain ⟨al, h⟩ := updateLastAllocation_eq s f
  rw [h]

theorem created_nextId (pref : Prefix) (ann : List Annot) (m : Mem.Concrete.State) :
    (Actions.created pref ann m).nextId = m.nextId + 1 := by
  simp [Actions.created, updateLastAllocation_nextId]

/-- What a store keeps. -/
theorem stored_same (m : Mem.Concrete.State) (j a v : Int) :
    (Locals.stored m j a v).nextId = m.nextId ∧ (Locals.stored m j a v).lastAddress = m.lastAddress ∧
      (Locals.stored m j a v).dead = m.dead ∧ (Locals.stored m j a v).stdout = m.stdout := by
  obtain ⟨b, pb, h⟩ := Mem.Concrete.writeRepresentation_shape a
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 v)) m
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Locals.stored, h]

/-- What a focus keeps. -/
theorem focus_same (ann : List Annot) (m : Mem.Concrete.State) :
    (focusMemory ann m).nextId = m.nextId ∧ (focusMemory ann m).lastAddress = m.lastAddress ∧
      (focusMemory ann m).dead = m.dead ∧ (focusMemory ann m).stdout = m.stdout := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m
  rw [hl]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem nextIntAddress_bounds (m : Mem.Concrete.State) :
    m.lastAddress - 7 ≤ nextIntAddress m ∧ nextIntAddress m + 4 ≤ m.lastAddress := by
  unfold nextIntAddress; omega

/-! ## One global definition -/

/-- `create(Ivalignof(int), int)` with the facts the globals need. -/
theorem createInt_held {e : Eff} (h : createInt e = true) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m', m'.stdout = m.stdout ∧ m'.nextId = m.nextId + 1 ∧ m'.lastAddress = nextIntAddress m ∧
      m'.dead = m.dead ∧ LiveInt m' m.nextId (nextIntAddress m) ∧
      (∀ id addr n, Held m id addr n → Held m' id addr n) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))), k, m'⟩ := by
  unfold createInt at h
  split at h
  · rename_i _ ann l u a1 a2 c1 a3 c2 pref
    obtain ⟨lf, hf⟩ := Locals.focusMemory_eq ann m
    have hlive := Locals.created_live pref c2 (focusMemory ann m) (by rw [hf]; exact hdead)
    have hreach := Locals.create_reaches (file := file) (labels := labels) ann a1 a2 a3 c1 c2 l u
      pref env k m hpos
    rw [Locals.nextIntAddress_focus] at hlive
    rw [hf] at hlive hreach
    refine ⟨_, by rw [Actions.created_stdout], by rw [created_nextId], ?_, ?_, hlive, ?_, hreach⟩
    · rw [Locals.created_lastAddress]; rfl
    · rw [Locals.created_dead]
    · intro id addr n hh
      exact held_created pref c2 (held_loc lf hh)
  · cases h

/-- `let strong a = create(Ivalignof(int), int) in let strong t = bound(pure(n)) in
store(int, a, conv_loaded_int(int, t)) ; pure(a)`: an `int` global initialised by `n`. -/
def initInt (file : File Codec.wireModel Unit Unit) : Eff → Option Int
  | .mk _ (.sseq (.mk _ (.base (some a, _))) cr
      (.mk _ (.sseq (.mk _ (.base (some t, _)))
        (.mk _ (.bound (.mk _ (.pure (.mk _ () (.val (.loaded (.specified (.integer n)))))))))
        (.mk _ (.sseq (.mk _ (.base (none, _)))
          (.mk _ (.action (.mk .pos (.mk _ _ (.store false
            (.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))))
            (.mk _ () (.sym a'))
            (.mk _ () (.call (.sym s) [.mk _ () (.val (.ctype (.mk _ (.basic (.integer (.signed .int)))))),
              .mk _ () (.sym t')])) .na)))))
          (.mk _ (.pure (.mk _ () (.sym a''))))))))) =>
      if createInt cr = true ∧ a'.key = a.key ∧ a''.key = a.key ∧ t'.key = t.key ∧ t.key ≠ a.key ∧
          isConvLoadedInt file s = true ∧ -2147483648 ≤ n ∧ n ≤ 2147483647 then some n else none
  | _ => none

/-- A recognised initialiser returns a fresh `int` object holding `n`, below every earlier
object, and leaves its store's annotation frame. -/
theorem initInt_reaches {e : Eff} {n : Int} (h : initInt file e = some n) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) (hpos : 0 < nextIntAddress m)
    (hdead : m.nextId ∉ m.dead) :
    IntRange n ∧ ∃ m' xs, m'.stdout = m.stdout ∧ m'.nextId = m.nextId + 1 ∧
      m'.lastAddress = nextIntAddress m ∧ m'.dead = m.dead ∧
      Held m' m.nextId (nextIntAddress m) n ∧
      (∀ id addr v, Held m id addr v → Held m' id addr v) ∧
      Reaches file labels ⟨.effectExpr e env, k, m⟩
        ⟨.value (.object (.pointer (.allocated m.nextId (nextIntAddress m)))),
          .annotations xs :: k, m'⟩ := by
  unfold initInt at h
  split at h
  · rename_i _ ann pann a ty cr sann tpann t tty bann ann' pann' n' cann upann uty stann l u a1 c1
      a2 a' a3 s a4 c3 a5 t' rann pann'' a''
    split at h
    · rename_i cond
      obtain ⟨hcr, ha', ha'', ht', hta, hs, lo, hi⟩ := cond
      cases h
      refine ⟨⟨lo, hi⟩, ?_⟩
      let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
      let v : Val := .loaded (.specified (.integer n))
      let PA : EE := .mk rann (.pure (.mk pann'' () (.sym a'')))
      let ST : EE := .mk stann (.action (.mk .pos (.mk l u (.store false
        (.mk a1 () (.val (.ctype (.mk c1 (.basic (.integer (.signed .int)))))))
        (.mk a2 () (.sym a'))
        (.mk a3 () (.call (.sym s) [.mk a4 () (.val (.ctype (.mk c3 (.basic (.integer (.signed .int)))))),
          .mk a5 () (.sym t')])) .na))))
      let C : EE := .mk cann (.sseq (.mk upann (.base (none, uty))) ST PA)
      let B : EE := .mk sann (.sseq (.mk tpann (.base (some t, tty)))
        (.mk bann (.bound (.mk ann' (.pure (.mk pann' () (.val (.loaded (.specified (.integer n))))))))) C)
      obtain ⟨m₁, out₁, id₁, last₁, dead₁, live₁, keep₁, hcreate⟩ := createInt_held (file := file)
        (labels := labels) hcr env (.strongBind (.mk pann (.base (some a, ty))) B env :: k) m hpos hdead
      let env₁ := extendEnv [(a, ptr)] env
      let env₂ := extendEnv [(t, v)] env₁
      let m₂ := focusMemory ann' m₁
      have hx₂ : env₂.lookup a' = some ptr := by
        rw [ConvInt.lookup_one_other (by rw [ha']; exact fun e => hta e.symm)]
        exact ConvInt.lookup_one ha'
      have ht₂ : env₂.lookup t' = some v := ConvInt.lookup_one ht'
      have live₂ : LiveInt m₂ m.nextId (nextIntAddress m) := Locals.liveInt_focus ann' live₁
      obtain ⟨xs, hst⟩ := Locals.store_reaches (file := file) (labels := labels) stann a1 a2 a3 a4 a5
        c1 c3 l u a' s t' hs env₂ (.strongBind (.mk upann (.base (none, uty))) PA env₂ :: k) m₂
        hx₂ ht₂ ⟨lo, hi⟩ live₂
      let m₃ := Locals.stored (focusMemory stann m₂) m.nextId (nextIntAddress m) n
      have hpa : env₂.lookup a'' = some ptr := by
        rw [ConvInt.lookup_one_other (by rw [ha'']; exact fun e => hta e.symm)]
        exact ConvInt.lookup_one ha''
      obtain ⟨l', hpure⟩ := LoadTask.pure_sym_local (file := file) (labels := labels) (wc := false)
        rann pann'' a'' env₂ hpa (.annotations xs :: k) m₃
      obtain ⟨sn₃, sl₃, sd₃, so₃⟩ := stored_same (focusMemory stann m₂) m.nextId (nextIntAddress m) n
      obtain ⟨fn₃, fl₃, fd₃, fo₃⟩ := focus_same stann m₂
      obtain ⟨fn₂, fl₂, fd₂, fo₂⟩ := focus_same ann' m₁
      have bnd := nextIntAddress_bounds m
      refine ⟨{m₃ with currentLocation := l'}, xs, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change m₃.stdout = m.stdout
        rw [so₃, fo₃, fo₂, out₁]
      · change m₃.nextId = m.nextId + 1
        rw [sn₃, fn₃, fn₂, id₁]
      · change m₃.lastAddress = nextIntAddress m
        rw [sl₃, fl₃, fl₂, last₁]
      · change m₃.dead = m.dead
        rw [sd₃, fd₃, fd₂, dead₁]
      · refine held_loc l' ⟨Locals.stored_slot (Locals.liveInt_focus stann live₂) n, ?_, ?_⟩
        · rw [sn₃, fn₃, fn₂, id₁]; omega
        · rw [sl₃, fl₃, fl₂, last₁]
      · intro id addr w hh
        refine held_loc l' (held_stored _ _ _ (by have := hh.above; omega)
          (held_focus stann (held_focus ann' (keep₁ id addr w hh))))
      · refine (ReturnConst.sequence_reaches file labels ann _ cr B env k m).trans ?_
        refine hcreate.trans ?_
        refine (ReturnLit.bind_reaches pann a ty ptr B env k m₁).trans ?_
        refine (ReturnConst.sequence_reaches file labels sann _ _ C env₁ k m₁).trans ?_
        refine (ReturnLit.boundLit_reaches bann ann' pann' n env₁ _ m₁).trans ?_
        refine (ReturnLit.bind_reaches tpann t tty v C env₁ k m₂).trans ?_
        refine (ReturnConst.sequence_reaches file labels cann _ ST PA env₂ k m₂).trans ?_
        refine hst.trans ?_
        refine (Locals.annotations_bind_reaches xs upann uty .unit PA env₂ k m₃).trans ?_
        exact Interleave.reaches_of_local file labels hpure
    · cases h
  · cases h

/-! ## The global definitions -/

/-- The global definitions of a file, in the order `Dynamics.initial` runs them. -/
def definitions (file : File Codec.wireModel Unit Unit) : List (Sym × Eff) :=
  file.globs.filterMap fun (sym, decl) => match decl with
    | .definition _ e => some (sym, e)
    | .declaration _ => none

/-- Every definition is an `int` initialised by a literal: the globals and their values. -/
def inits (file : File Codec.wireModel Unit Unit) : List (Sym × Eff) → Option (List (Sym × Int))
  | [] => some []
  | (x, e) :: ds => (initInt file e).bind fun n => (inits file ds).map fun gs => (x, n) :: gs

/-- Frames that are all annotation frames. -/
def AnnOnly (k : List Frame) : Prop := ∀ f ∈ k, ∃ xs, f = .annotations xs

theorem annOnly_cons {xs : List Access} {k : List Frame} (h : AnnOnly k) :
    AnnOnly (.annotations xs :: k) := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact ⟨xs, rfl⟩
  · exact h f hf

theorem globalResult_reaches (xs : List Access) (x : Sym) (ds : List (Sym × EE)) (args : List String)
    (env : Env) (ls : Labels) (v : Val) (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.value v, .annotations xs :: .globalResult x ds args env ls :: k, m⟩
      ⟨.globals ds args (env.insert x v), .annotations xs :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

theorem global_reaches (x : Sym) (e : EE) (ds : List (Sym × EE)) (args : List String) (env : Env)
    (k : List Frame) (m : Mem.Concrete.State) :
    Reaches file labels ⟨.globals ((x, e) :: ds) args env, k, m⟩
      ⟨.effectExpr e env, .globalResult x ds args env (Map.ofList (saves e).reverse) :: k, m⟩ := by
  apply next_reaches (by intro o h; cases h)
  simp [request, requestAux, awaitsScheduling]

/-- The global definitions run in order: each global points to its object, which holds its
value. -/
theorem globals_reaches (args : List String) : ∀ (ds : List (Sym × EE)) (gs : List (Sym × Int)),
    inits file ds = some gs → (ds.map fun d => d.1.key).Nodup →
    ∀ (env : Env) (k : List Frame) (m : Mem.Concrete.State),
    AnnOnly k → m.dead = [] → 8 * (ds.length + 1) < m.lastAddress →
    ∃ env' m' k', m'.stdout = m.stdout ∧ m'.dead = [] ∧ 8 < m'.lastAddress ∧ AnnOnly k' ∧
      (∀ x v, (∀ d ∈ ds, d.1.key ≠ x.key) → env.lookup x = some v → env'.lookup x = some v) ∧
      (∀ id addr v, Held m id addr v → Held m' id addr v) ∧
      (∀ x n, (x, n) ∈ gs → IntRange n ∧ ∃ id addr,
        env'.lookup x = some (.object (.pointer (.allocated id addr))) ∧ Held m' id addr n) ∧
      Reaches file labels ⟨.globals ds args env, k, m⟩ ⟨.globals [] args env', k', m'⟩
  | [], gs, h, _, env, k, m, hk, hdead, room => by
    simp only [inits, Option.some.injEq] at h
    subst h
    exact ⟨env, m, k, rfl, hdead, by simp at room; omega, hk, fun _ _ _ h => h, fun _ _ _ h => h,
      by simp, .refl⟩
  | (x, e) :: ds, gs, h, nd, env, k, m, hk, hdead, room => by
    simp only [inits] at h
    cases hn : initInt file e with
    | none => simp [hn] at h
    | some n =>
      cases hgs : inits file ds with
      | none => simp [hn, hgs] at h
      | some gs' =>
        simp only [hn, hgs, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have nd' : (ds.map fun d => d.1.key).Nodup := (List.nodup_cons.mp nd).2
        have fresh : ∀ d ∈ ds, d.1.key ≠ x.key := by
          intro d hd e'
          exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨d, hd, e'⟩)
        have bnd := nextIntAddress_bounds m
        simp only [List.length_cons] at room
        obtain ⟨hr, m₁, xs, out₁, id₁, last₁, dead₁, new₁, keep₁, hinit⟩ :=
          initInt_reaches (file := file) (labels := labels) hn env
            (.globalResult x ds args env (Map.ofList (saves e).reverse) :: k) m (by omega)
            (by rw [hdead]; simp)
        let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
        obtain ⟨env', m', k', out, dead', room', hk', look, keep, held, reach⟩ :=
          globals_reaches args ds gs' hgs nd' (env.insert x ptr) (.annotations xs :: k) m₁
            (annOnly_cons hk) (by rw [dead₁, hdead]) (by rw [last₁]; omega)
        refine ⟨env', m', k', by rw [out, out₁], dead', room', hk', ?_, ?_, ?_, ?_⟩
        · intro y w hy hw
          refine look y w (fun d hd => hy d (List.mem_cons_of_mem _ hd)) ?_
          rw [Map.lookup_insert_of_key_ne _ _ (fun h' => hy (x, e) List.mem_cons_self h'.symm)]
          exact hw
        · intro id addr w hh
          exact keep id addr w (keep₁ id addr w hh)
        · intro y w hy
          rcases List.mem_cons.mp hy with hy | hy
          · cases hy
            exact ⟨hr, m.nextId, nextIntAddress m, look x ptr fresh (by simp),
              keep _ _ _ new₁⟩
          · exact held y w hy
        · exact (global_reaches x e ds args env k m).trans (hinit.trans
            ((globalResult_reaches xs x ds args env _ ptr k m₁).trans reach))

/-! ## Startup -/

/-- `.globals []` enters `main`, under any frames. -/
theorem enter_main_reaches (args : List String) (env : Env) (k : List Frame)
    (m : Mem.Concrete.State) {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    Reaches file labels ⟨.globals [] args env, k, m⟩ ⟨.startup (.effectExpr body env), k, m⟩ := by
  refine .trans (StartupReach.step_reaches (r := .next (.enterMain args env) k)
    (by intro o; simp) ?_ .next) ?_
  · simp [request, requestAux, awaitsScheduling]
  refine StartupReach.step_reaches (r := .next (.startup (.effectExpr body env)) k)
    (by intro o; simp) ?_ .next
  simp [request, requestAux, awaitsScheduling, main, decl]

/-- The `errno` startup from any memory with room below its last allocation: it keeps every
object above, and drops the frames below it. -/
theorem startup_errno_held (c : Control) (k : List Frame) (m : Mem.Concrete.State)
    (hpos : 0 < nextIntAddress m) (hdead : m.nextId ∉ m.dead) :
    ∃ m' xs, m'.stdout = m.stdout ∧ (∀ id addr v, Held m id addr v → Held m' id addr v) ∧
      Reaches file labels ⟨.startup c, k, m⟩ ⟨c, [.annotations xs], m'⟩ := by
  let ptr : Val := .object (.pointer (.allocated m.nextId (nextIntAddress m)))
  let m₁ := Actions.created (.other "errno") [] m
  have live₁ : LiveInt m₁ m.nextId (nextIntAddress m) := Locals.created_live _ _ m hdead
  have hcreate : Reaches file labels ⟨.startup c, k, m⟩ ⟨.value ptr, [.startupStore c], m₁⟩ :=
    Actions.memory_reaches (name := "Create") (by intro o h; cases h) (by
      simp only [request, requestAux, awaitsScheduling, memoryRequest]
      simp only [show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
        integer, Mem.Concrete.allocate_int _ [] m hpos]
      simp [bind, Except.bind, pure, Except.pure, m₁, Actions.created, ptr])
  obtain ⟨r, hr⟩ : ∃ r, request file labels ⟨.value ptr, [.startupStore c], m₁⟩ = r := ⟨_, rfl⟩
  have hr' := hr
  simp [request, requestAux, awaitsScheduling, memoryRequest, toMemory, objectMemory, ptr,
    show Ctype.mk [] (.basic (.integer (.signed .int))) = Mem.Concrete.intType [] from rfl,
    Mem.Concrete.store_int _ [] live₁ (show IntRange 0 by unfold IntRange; omega),
    Mem.Concrete.access_int _ [] live₁, bind, Except.bind, pure, Except.pure] at hr'
  subst hr'
  let m₂ := Locals.stored m₁ m.nextId (nextIntAddress m) 0
  have hstore : Reaches file labels ⟨.value ptr, [.startupStore c], m₁⟩
      ⟨.value .unit, [.annotations [⟨none, [], true, nextIntAddress m, 4⟩], .startupEnter c], m₂⟩ :=
    Actions.memory_reaches (by intro o h; cases h) hr
  refine ⟨{m₂ with currentLocation := .other "Driver.drive"}, [⟨none, [], true, nextIntAddress m, 4⟩],
    ?_, ?_, hcreate.trans (hstore.trans ?_)⟩
  · change m₂.stdout = m.stdout
    rw [(stored_same m₁ _ _ _).2.2.2, Actions.created_stdout]
  · intro id addr v hh
    exact held_loc _ (held_stored _ _ _ (by have := hh.above; have := nextIntAddress_bounds m; omega)
      (held_created _ _ hh))
  · exact Straight.update_reaches (by intro o h; cases h) (by simp [request, requestAux, awaitsScheduling])

/-- **Startup with `int` globals.** From the initial state of a file whose global definitions are
`int` objects initialised by literals (`gs`), with distinct symbols, whose `main` is a procedure
without parameters, the dynamics reaches `main`'s body in an environment where every global
points to its object, which holds its value, under one annotation frame, with empty stdout. -/
theorem initial_reaches_body (file : Program) (enums : Map Sym IntegerType) (args : List String)
    {gs : List (Sym × Int)} (hgs : inits file (definitions file) = some gs)
    (nd : ((definitions file).map fun d => d.1.key).Nodup)
    (room : 8 * ((definitions file).length + 1) < 281474976710655)
    {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {body : EE}
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [] body)) :
    ∃ s m env xs, initial file enums args = .ok (s, Map.ofList (saves body).reverse) ∧
      m.stdout = "" ∧
      (∀ x n, (x, n) ∈ gs → IntRange n ∧ ∃ id addr,
        env.lookup x = some (.object (.pointer (.allocated id addr))) ∧ Slot m id addr n) ∧
      Reaches file (Map.ofList (saves body).reverse) s ⟨.effectExpr body env, [.annotations xs], m⟩ := by
  let labels : Labels := Map.ofList (saves body).reverse
  let m₀ : Mem.Concrete.State := {enumTypes := enums}
  obtain ⟨env, m₁, k₁, out₁, dead₁, room₁, -, -, -, held₁, reach₁⟩ :=
    globals_reaches (file := file) (labels := labels) args (definitions file) gs hgs nd ∅ [] m₀
      (by simp [AnnOnly]) rfl (by show (8 : Int) * _ < 281474976710655; omega)
  have bnd := nextIntAddress_bounds m₁
  obtain ⟨m₂, xs, out₂, keep₂, reach₂⟩ := startup_errno_held (file := file) (labels := labels)
    (.effectExpr body env) k₁ m₁ (by omega) (by rw [dead₁]; simp)
  refine ⟨_, m₂, env, xs, ?_, by rw [out₂, out₁], ?_,
    reach₁.trans ((enter_main_reaches args env k₁ m₁ main decl).trans reach₂)⟩
  · simp [initial, definitions, main, decl]
    refine ⟨?_, rfl⟩
    congr 1
  · intro x n hx
    obtain ⟨hr, id, addr, look, hh⟩ := held₁ x n hx
    exact ⟨hr, id, addr, look, (keep₂ id addr n hh).slot⟩

end Silmaril.Compile.Core.Verified.Globals
