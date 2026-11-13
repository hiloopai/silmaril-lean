module

public import Silmaril.Compiler.Core.Verified.ArgvReloc.Defs
public import Silmaril.Compiler.Core.Verified.LoadTask.Defs
public import Silmaril.Compiler.Core.Verified.Argc.Defs

/-! # The argument objects of `main(argc, argv)` under reads

`ArgvReloc` describes the startup objects of `main(argc, argv)` through the loads that read them.
Reading `argv[i][j]` in the body loads the `argv` parameter object, a slot of the pointer array and
a character of a string; each typed load may mark allocations as exposed (`exposeRead`, for bytes
that carry pointer provenance) and records the last used allocation. `Reads m m'` is what such
loads (and changes of the current location) leave: the same bytes, pointer metadata, lifetimes
and output, and the same base, size and atomicity of every allocation.

`Objs m args idV V idA B qs`: the `argv` parameter object `idV` at `V` holds the array
`idA` at `B`, whose slots hold the strings `qs` of `args` (then the null pointer); `Objs.reads`
keeps it under `Reads`, and `initial_reaches_body_mem` gives it at the start of `main`'s body.
`load_slot`, `load_null` and `load_charAt` are the typed loads of a slot and of a character, at
any annotations of the C types (the program's types carry locations).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Core.StartupArgs
open Mem.Concrete (Tags Pointer MemoryValue loadTyped accessTyped typeLayout fetchBytes encodeInteger)

/-! ## Reads -/

/-- What loads leave of a memory. -/
structure Reads (m m' : Mem.Concrete.State) : Prop where
  bytes : m'.bytes = m.bytes
  ptrs : m'.pointerBytes = m.pointerBytes
  dead : m'.dead = m.dead
  stdout : m'.stdout = m.stdout
  enums : m'.enumTypes = m.enumTypes
  last : m'.lastAddress = m.lastAddress
  next : m'.nextId = m.nextId
  allocs : ∀ id r, m.allocations.lookup id = some r → ∃ r', m'.allocations.lookup id = some r' ∧
    r'.base = r.base ∧ r'.size = r.size ∧ r'.atomic = r.atomic ∧ r'.readonly = r.readonly

theorem Reads.refl (m : Mem.Concrete.State) : Reads m m :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl⟩⟩

theorem Reads.trans {m₁ m₂ m₃ : Mem.Concrete.State} (h₁ : Reads m₁ m₂) (h₂ : Reads m₂ m₃) :
    Reads m₁ m₃ := by
  refine ⟨h₂.bytes.trans h₁.bytes, h₂.ptrs.trans h₁.ptrs, h₂.dead.trans h₁.dead,
    h₂.stdout.trans h₁.stdout, h₂.enums.trans h₁.enums, h₂.last.trans h₁.last, h₂.next.trans h₁.next,
    fun id r hr => ?_⟩
  obtain ⟨r', h', b', s', a', o'⟩ := h₁.allocs id r hr
  obtain ⟨r'', h'', b'', s'', a'', o''⟩ := h₂.allocs id r' h'
  exact ⟨r'', h'', b''.trans b', s''.trans s', a''.trans a', o''.trans o'⟩

theorem Reads.of_touched {m m' : Mem.Concrete.State} (h : LoadTask.Touched m m') : Reads m m' := by
  obtain ⟨l, u, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl⟩⟩

theorem Reads.lastUsed {m m' : Mem.Concrete.State} (h : Reads m m') (u : Option Int) :
    Reads m {m' with lastUsed := u} :=
  ⟨h.bytes, h.ptrs, h.dead, h.stdout, h.enums, h.last, h.next, h.allocs⟩

theorem Reads.location {m m' : Mem.Concrete.State} (h : Reads m m') (l : Loc) :
    Reads m {m' with currentLocation := l} :=
  ⟨h.bytes, h.ptrs, h.dead, h.stdout, h.enums, h.last, h.next, h.allocs⟩

theorem Reads.focus {m m' : Mem.Concrete.State} (h : Reads m m') (ann : List Annot) :
    Reads m (ReturnConst.focusMemory ann m') := by
  obtain ⟨l, hl⟩ := Locals.focusMemory_eq ann m'
  rw [hl]; exact h.location l

/-- Marking one allocation exposed. -/
theorem Reads.expose (s : Mem.Concrete.State) (id : Int) (a : Mem.Concrete.Allocation)
    (ha : s.allocations.lookup id = some a) :
    Reads s {s with allocations := s.allocations.insert id {a with exposed := true}} := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun j r hr => ?_⟩
  by_cases e : j = id
  · subst e
    rw [ha] at hr
    cases hr
    exact ⟨_, Map.lookup_insert _ _ _, rfl, rfl, rfl, rfl⟩
  · refine ⟨r, ?_, rfl, rfl, rfl, rfl⟩
    rw [Map.lookup_insert_of_key_ne _ _ e]
    exact hr

theorem Reads.foldl {α : Type} (f : Mem.Concrete.State → α → Mem.Concrete.State)
    (hf : ∀ s x, Reads s (f s x)) : ∀ (l : List α) (s : Mem.Concrete.State), Reads s (l.foldl f s)
  | [], s => Reads.refl s
  | x :: xs, s => (hf s x).trans (Reads.foldl f hf xs (f s x))

theorem Reads.exposeReadBytes (s : Mem.Concrete.State) (addr : Int) (size : Nat) :
    Reads s (Mem.Concrete.exposeReadBytes s addr size) := by
  unfold Mem.Concrete.exposeReadBytes
  refine Reads.foldl _ (fun s i => ?_) _ s
  split
  · exact Reads.refl s
  · split
    · exact Reads.refl s
    · rename_i id _ a ha
      exact Reads.expose s _ a ha

theorem Reads.exposeRead : ∀ (fuel : Nat) (tags : Tags) (s : Mem.Concrete.State) (ty : Ctype)
    (addr : Int), Reads s (Mem.Concrete.exposeRead fuel tags s ty addr)
  | 0, _, s, _, _ => by simp only [Mem.Concrete.exposeRead]; exact Reads.refl s
  | fuel + 1, tags, s, .mk _ ty, addr => by
    simp only [Mem.Concrete.exposeRead]
    split
    · split
      · exact Reads.exposeReadBytes s addr _
      · exact Reads.refl s
    · exact Reads.exposeReadBytes s addr 1
    · split
      · exact Reads.refl s
      · exact Reads.foldl _ (fun s i => Reads.exposeRead fuel tags s _ _) _ s
    · split
      · exact Reads.refl s
      · exact Reads.foldl _ (fun s x => Reads.exposeRead fuel tags s _ _) _ s
    · exact Reads.exposeRead fuel tags s _ addr
    · exact Reads.refl s

/-- A successful typed load leaves `Reads`. -/
theorem Reads.loadTyped {tags : Tags} {s s' : Mem.Concrete.State} {ty : Ctype} {p : Pointer}
    {v : MemoryValue} (h : loadTyped tags s ty p = .ok (v, s')) : Reads s s' := by
  unfold Mem.Concrete.loadTyped at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain ⟨id, addr, size⟩ := r
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact (Reads.exposeRead 64 tags s ty addr).lastUsed _

/-! ## Facts that survive reads -/

theorem _root_.Silmaril.Cerberus.Core.StartupArgs.Live.reads {m m' : Mem.Concrete.State} {id b size : Int} (h : Live m id b size)
    (g : Reads m m') : Live m' id b size := by
  obtain ⟨⟨r, hr, hb, hs, ha⟩, hd⟩ := h
  obtain ⟨r', h', b', s', a', -⟩ := g.allocs id r hr
  exact ⟨⟨r', h', b'.trans hb, s'.trans hs, a'.trans ha⟩, by rw [g.dead]; exact hd⟩

theorem _root_.Silmaril.Cerberus.Core.StartupArgs.StrAt.reads {m m' : Mem.Concrete.State} {id b : Int} {s : String} (h : StrAt m id b s)
    (g : Reads m m') : StrAt m' id b s where
  live := h.live.reads g
  chars j c hc := by rw [g.bytes]; exact h.chars j c hc
  nul := by rw [g.bytes]; exact h.nul

theorem _root_.Silmaril.Cerberus.Core.StartupArgs.ArrAt.reads {m m' : Mem.Concrete.State} {id B : Int} {qs : List Pointer} (h : ArrAt m id B qs)
    (g : Reads m m') : ArrAt m' id B qs where
  live := h.live.reads g
  slot i id' b hq := by rw [g.bytes, g.ptrs]; exact h.slot i id' b hq
  null := by rw [g.bytes]; exact h.null

theorem _root_.Silmaril.Cerberus.Core.StartupArgs.PtrAt.reads {m m' : Mem.Concrete.State} {id V id' b : Int} (h : PtrAt m id V id' b)
    (g : Reads m m') : PtrAt m' id V id' b :=
  ⟨h.live.reads g, by rw [g.bytes]; exact h.bytes, by rw [g.ptrs]; exact h.prov⟩

/-- The argument objects: the `argv` parameter object holds the array, whose slots hold the
strings of `args` (identifiers `0 …`), then the null pointer. -/
structure Objs (m : Mem.Concrete.State) (args : List String) (idV V idA B : Int)
    (qs : List Pointer) : Prop where
  ptr : PtrAt m idV V idA B
  arr : ArrAt m idA B qs
  strs : StrPtrs m 0 args qs
  pos : 0 < B
  top : B + 8 * (args.length + 1) ≤ 281474976710655

theorem Objs.reads {m m' : Mem.Concrete.State} {args : List String} {idV V idA B : Int}
    {qs : List Pointer} (h : Objs m args idV V idA B qs) (g : Reads m m') :
    Objs m' args idV V idA B qs where
  ptr := h.ptr.reads g
  arr := h.arr.reads g
  strs := by
    refine ⟨h.strs.1, fun i s hs => ?_⟩
    obtain ⟨b, hq, hstr, hlb, htop, hpos⟩ := h.strs.2 i s hs
    exact ⟨b, hq, hstr.reads g, by rwa [g.last], htop, hpos⟩
  pos := h.pos
  top := h.top

/-! ## Loads at any annotations -/

theorem typeLayout_char_ann (tags : Tags) (ann : List Annot) :
    typeLayout 64 tags (.mk ann (.basic (.integer .char))) = .ok ⟨1, 1, []⟩ := by
  simp [Mem.Concrete.typeLayout, layout_char, pure, Except.pure]

theorem typeLayout_pointer_ann (tags : Tags) (ann : List Annot) (q : Qualifiers) (ty : Ctype) :
    typeLayout 64 tags (.mk ann (.pointer q ty)) = .ok ⟨8, 8, []⟩ := by
  simp [Mem.Concrete.typeLayout, pure, Except.pure]

/-- `abstractPointer` of provenance bytes, for a referenced type that is not a function type. -/
theorem abstractPointer_prov (m : Mem.Concrete.State) {refTy : Ctype}
    (hr : ∀ ann r ps va, refTy ≠ .mk ann (.function r ps va)) {a id v : Int} (hv : v ≠ 0)
    (hp : ∀ k : Nat, k < 8 → m.pointerBytes.lookup (a + k) = some (some id, k)) :
    Mem.Concrete.abstractPointer m refTy a v = .ok (.allocated id v) := by
  have hall : (List.range 8).all (fun i : Nat => m.pointerBytes.lookup (a + i) == some (some id, i)) = true := by
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    simp [hp i hi]
  obtain ⟨ann, node⟩ := refTy
  cases node
  case function r ps va => exact absurd rfl (hr ann r ps va)
  all_goals
    have h0 := hp 0 (by norm_num)
    simp only [Nat.cast_zero, Int.add_zero] at h0
    simp [Mem.Concrete.abstractPointer, hv, h0, hall, pure, Except.pure]

theorem load_pointer_ann (tags : Tags) (m : Mem.Concrete.State) {id b size a v : Int}
    (h : Live m id b size) (ann : List Annot) (q : Qualifiers) (refTy : Ctype) (ha : b ≤ a)
    (ha' : a + 8 ≤ b + size) (hf : fetchBytes 8 a m.bytes = encodeInteger 8 v) (h0 : 0 ≤ v)
    (h1 : v < 18446744073709551616) {p : Pointer}
    (hp : Mem.Concrete.abstractPointer m refTy a v = .ok p) :
    ∃ m', loadTyped tags m (.mk ann (.pointer q refTy)) (.allocated id a) =
      .ok (.pointer refTy p, m') := by
  have hacc : accessTyped tags m (.mk ann (.pointer q refTy)) (.allocated id a) = .ok (id, a, 8) :=
    accessTyped_live tags m h _ (typeLayout_pointer_ann tags ann q refTy) ha ha'
  have hd := decodeInteger_encodeInteger 8 v h0 (by norm_num; omega)
  refine ⟨{Mem.Concrete.exposeRead 64 tags m (.mk ann (.pointer q refTy)) a with lastUsed := some id}, ?_⟩
  simp [Mem.Concrete.loadTyped, hacc, Mem.Concrete.abstractValue, typeLayout_pointer_ann, hf, hd, hp, bind,
    Except.bind, pure, Except.pure]

theorem load_char_ann (tags : Tags) (m : Mem.Concrete.State) {id b size a c : Int} (h : Live m id b size)
    (ann : List Annot) (ha : b ≤ a) (ha' : a + 1 ≤ b + size) (hc : m.bytes.lookup a = some (some c))
    (h0 : 0 ≤ c) (h1 : c < 128) :
    ∃ m', loadTyped tags m (.mk ann (.basic (.integer .char))) (.allocated id a) =
      .ok (.integer .char c, m') := by
  have hf : fetchBytes 1 a m.bytes = [some c] := fetchBytes_of 1 a m.bytes [c] rfl fun j hj => by
    obtain rfl : j = 0 := by omega
    simpa using hc
  have hacc : accessTyped tags m (.mk ann (.basic (.integer .char))) (.allocated id a) = .ok (id, a, 1) :=
    accessTyped_live tags m h _ (typeLayout_char_ann tags ann) ha ha'
  refine ⟨{Mem.Concrete.exposeRead 64 tags m (.mk ann (.basic (.integer .char))) a with lastUsed := some id}, ?_⟩
  simp [Mem.Concrete.loadTyped, hacc, Mem.Concrete.abstractValue, typeLayout_char_ann, layout_char, hf,
    Mem.Concrete.decodeInteger, bind, Except.bind, pure, Except.pure, show ¬ (128 ≤ c) by omega]

/-! ## The start of `main(argc, argv)` -/

/-- **`main(argc, argv)` starts with the argument objects.** From the initial state of a file
without global definitions whose `main` takes `argc` and `argv` (normal calling convention), for
every `ArgsOk` argument vector, the dynamics reaches `main`'s body with `argc` and `argv` bound to
pointers to the `argc` object and to the `argv` parameter object `idV` at `V`, which holds the array
`idA` at `B` of the strings `qs`, with empty output. -/
theorem initial_reaches_body_mem (file : Program) (enums : Map Sym IntegerType) (args : List String)
    (h : Spec.ArgsOk args) {sym : Sym} {loc : Loc} {marker : Option Nat} {ty : BaseType} {argc argv : Sym}
    {tc tv : BaseType} {body : EE}
    (nodefs : ∀ x ∈ file.globs, ∀ bt e, x.2 ≠ .definition bt e)
    (main : file.main = some sym)
    (decl : file.funs.lookup sym = some (.procedure loc marker ty [(argc, tc), (argv, tv)] body))
    (normal : file.callingConvention = .normal) :
    ∃ s labels xs qs pc V m, initial file enums args = .ok (s, labels) ∧
      StartupReach.Reaches file labels s ⟨.effectExpr body
        (extendEnv [(argc, .object (.pointer pc)),
          (argv, .object (.pointer (.allocated (args.length + 2) V)))] ∅),
        [.annotations xs], m⟩ ∧
      m.stdout = "" ∧ ∃ B, Objs m args (args.length + 2) V args.length B qs := by
  have hc := ArgvReloc.chars_of_argsOk h
  have hroom := ArgvReloc.room_of_argsOk h
  have hr0 : 0 ≤ strRoom args := Int.natCast_nonneg _
  let m0 : Mem.Concrete.State := {enumTypes := enums}
  obtain ⟨qs, B, C, V, m1, hs, g, hn, hd, hpos, hptrs, harr, hint, hptr, hB0, hBtop, hlV, hVC, hCB⟩ :=
    startObjects_args file.tagDefs args hc (by omega) loc sym argc argv m0 rfl (by simp [m0]) (by
      simp [m0]; omega)
  have hn0 : m0.nextId = 0 := rfl
  simp only [hn0, Int.zero_add] at hs hn harr hint hptr hptrs
  obtain ⟨hb1, -⟩ := nextBase_ge m1 4 4 (by norm_num)
  have hlast : (281474976710655 : Int) - 4096 - 32 ≤ m1.lastAddress := by
    change (281474976710655 : Int) - _ - _ - _ ≤ _ at hpos; omega
  obtain ⟨pe, m2, herrno, g2⟩ := createErrno_spec ⟨file.tagDefs, m1.enumTypes⟩ m1 hd (by omega)
  obtain ⟨s, labels, xs, hinit, hreach⟩ := initial_reaches_body_args file enums args nodefs main decl normal
    (objects_ok' args hc loc sym argc argv) hs herrno
  have hpv := Argc.paramValues_tail qs (.allocated args.length B) (.allocated (args.length + 1) C)
    (.allocated (args.length + 2) V)
  rw [hpv] at hreach
  refine ⟨s, labels, xs, qs, _, V, _, hinit, hreach, by simpa [m0] using g2.stdout.trans g.stdout, B,
    ?_⟩
  have hlen : qs.length = args.length := hptrs.1
  have hnext : m1.nextId = args.length + 3 := by rw [hn]
  refine Objs.reads (m := m2) ⟨?_, ?_, ?_, hB0, hBtop⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl⟩⟩
  · exact hptr.grows g2 (by omega) (by omega)
  · exact harr.grows g2 (by omega) (by omega)
  · refine ⟨hlen, fun i str hstr => ?_⟩
    obtain ⟨b, hq, hat, hlb, htop, hbpos⟩ := hptrs.2 i str hstr
    have hi : i < args.length := (List.getElem?_eq_some_iff.mp hstr).1
    exact ⟨b, hq, hat.grows g2 (by omega) hlb, g2.last.trans hlb, htop, hbpos⟩

end Silmaril.Compile.Core.Verified.ArgvMem
