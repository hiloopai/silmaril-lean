module

public import Silmaril.Compiler.Core.Verified.ArgvStore.Defs
public import Silmaril.Compiler.Core.Verified.PrintMem.Defs
public import Silmaril.Compiler.Core.Verified.RmwSound.Defs
/-! # The argument objects through the statements of the argv control-flow graph

The machine of `CfgArgv` runs `int` statements over slots: the `argc` parameter object (between
the `argv` parameter object and the pointer array) and the locals `main` creates (below every
argument object). `Mem` is its memory invariant: the exit budget, the argument objects
(`ArgvMem.Objs`) and, for each slot, four bytes apart from them (`Sep`). It survives reads
(`Mem.reads`) and every memory change of the statements (`closed`, `stmtClosed`): a store writes
four bytes of a slot and keeps every other byte (`objs_frame`).
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgArgvMem

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.StartupArgs
open Mem.Concrete (Pointer fetchBytes readByte)
open StateMem (Local)
open ArgvMem (Reads Objs)

/-- Four bytes at `a`: below the pointer array, and below or above the `argv` parameter object. -/
def Sep (V B a : Int) : Prop := a + 4 ≤ B ∧ (a + 4 ≤ V ∨ V + 8 ≤ a)

/-- The strings lie above the pointer array. -/
def StrAbove (args : List String) (B : Int) (qs : List Pointer) : Prop :=
  ∀ (i : Nat) (b : Int), qs[i]? = some (Pointer.allocated (0 + i) b) → B + 8 * (args.length + 1) ≤ b

/-- The memory of the machine over the slots `ls`. -/
def Mem (args : List String) (idV V idA B : Int) (qs : List Pointer) (ls : List Local)
    (m : Mem.Concrete.State) : Prop :=
  ExitCall.Budget m ∧ Objs m args idV V idA B qs ∧ ∀ l ∈ ls, Sep V B l.addr

theorem budget_frame {m m' : Mem.Concrete.State} (b : ExitCall.Budget m)
    (last : m'.lastAddress = m.lastAddress) (next : m'.nextId = m.nextId) (dead : m'.dead = m.dead) :
    ExitCall.Budget m' :=
  ⟨by simpa [Mem.Concrete.nextIntAddress, last] using b.room, by rw [next, dead]; exact b.fresh⟩

/-- Writing four bytes apart from the argument objects keeps them. -/
theorem objs_frame {m m' : Mem.Concrete.State} {args : List String} {idV V idA B : Int}
    {qs : List Pointer} (h : Objs m args idV V idA B qs) (hstr : StrAbove args B qs) {a : Int}
    (hsep : Sep V B a) (alloc : m'.allocations = m.allocations) (dead : m'.dead = m.dead)
    (last : m'.lastAddress = m.lastAddress)
    (bytes : ∀ x, (x < a ∨ a + 4 ≤ x) →
      m'.bytes.lookup x = m.bytes.lookup x ∧ m'.pointerBytes.lookup x = m.pointerBytes.lookup x) :
    Objs m' args idV V idA B qs := by
  have live {oid b sz : Int} (l : Live m oid b sz) : Live m' oid b sz :=
    ⟨by rw [alloc]; exact l.lookup, by rw [dead]; exact l.alive⟩
  have fetch (k : Nat) (x : Int) (hx : ∀ j : Nat, j < k → x + j < a ∨ a + 4 ≤ x + j) :
      fetchBytes k x m'.bytes = fetchBytes k x m.bytes := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      simp only [fetchBytes, readByte, (bytes x (by simpa using hx 0 (by omega))).1]
      rw [ih (x + 1) (fun j hj => by
        have := hx (j + 1) (by omega); push_cast at this ⊢; omega)]
  obtain ⟨hB, hV⟩ := hsep
  refine ⟨?_, ?_, ?_, h.pos, h.top⟩
  · refine ⟨live h.ptr.live, (fetch 8 V (fun j hj => by omega)).trans h.ptr.bytes,
      fun k hk => (bytes (V + k) (by omega)).2.trans (h.ptr.prov k hk)⟩
  · refine ⟨live h.arr.live, ?_, ?_⟩
    · intro i oid b hq
      obtain ⟨hb, hp⟩ := h.arr.slot i oid b hq
      exact ⟨(fetch 8 (B + 8 * i) (fun j hj => by omega)).trans hb,
        fun k hk => (bytes (B + 8 * i + k) (by omega)).2.trans (hp k hk)⟩
    · exact (fetch 8 (B + 8 * qs.length) (fun j hj => by omega)).trans h.arr.null
  · refine ⟨h.strs.1, ?_⟩
    intro i s hsi
    obtain ⟨b, hq, str, hl, ht, hp⟩ := h.strs.2 i s hsi
    have hb := hstr i b hq
    refine ⟨b, hq, ?_, by rwa [last], ht, hp⟩
    exact ⟨live str.live,
      fun j c hc => (bytes (b + j) (by omega)).1.trans (str.chars j c hc),
      (bytes (b + s.length) (by omega)).1.trans str.nul⟩

/-- A write of four bytes at `a`. -/
theorem objs_write {m : Mem.Concrete.State} {args : List String} {idV V idA B : Int}
    {qs : List Pointer} (h : Objs m args idV V idA B qs) (hstr : StrAbove args B qs) {a : Int}
    (hsep : Sep V B a) (bs : Mem.Concrete.Representation) (hlen : bs.length = 4) (u : Option Int) :
    Objs {Mem.Concrete.writeRepresentation a bs m with lastUsed := u} args idV V idA B qs := by
  obtain ⟨fa, -, fl, fd, -, -⟩ := writeRepresentation_fields a bs m
  exact objs_frame h hstr hsep fa fd fl fun x hx =>
    writeRepresentation_out a bs m x (by rw [hlen]; exact hx)

theorem Mem.reads {args : List String} {idV V idA B : Int} {qs : List Pointer} {ls : List Local}
    {m m' : Mem.Concrete.State} (h : Mem args idV V idA B qs ls m) (g : Reads m m') :
    Mem args idV V idA B qs ls m' :=
  ⟨budget_frame h.1 g.last g.next g.dead, h.2.1.reads g, h.2.2⟩

theorem Mem.touched {args : List String} {idV V idA B : Int} {qs : List Pointer} {ls : List Local}
    {m m' : Mem.Concrete.State} (h : Mem args idV V idA B qs ls m) (t : LoadTask.Touched m m') :
    Mem args idV V idA B qs ls m' :=
  h.reads (Reads.of_touched t)

theorem Mem.focus {args : List String} {idV V idA B : Int} {qs : List Pointer} {ls : List Local}
    {m : Mem.Concrete.State} (h : Mem args idV V idA B qs ls m) (ann : List Annot) :
    Mem args idV V idA B qs ls (ReturnConst.focusMemory ann m) :=
  h.touched (LoadTask.focusMemory_touched ann m)

theorem Mem.excluded {args : List String} {idV V idA B : Int} {qs : List Pointer} {ls : List Local}
    {m : Mem.Concrete.State} (h : Mem args idV V idA B qs ls m) (n : Nat) :
    Mem args idV V idA B qs ls {m with nextExcluded := n} :=
  h.reads ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ r h => ⟨r, h, rfl, rfl, rfl, rfl⟩⟩

theorem Mem.write {args : List String} {idV V idA B : Int} {qs : List Pointer} {ls : List Local}
    {m : Mem.Concrete.State} (h : Mem args idV V idA B qs ls m) (hstr : StrAbove args B qs)
    {l : Local} (hl : l ∈ ls) (bs : Mem.Concrete.Representation) (hlen : bs.length = 4)
    (u : Option Int) :
    Mem args idV V idA B qs ls {Mem.Concrete.writeRepresentation l.addr bs m with lastUsed := u} := by
  obtain ⟨-, hn, hl', hd, -, -⟩ := writeRepresentation_fields l.addr bs m
  exact ⟨budget_frame h.1 hl' hn hd, objs_write h.2.1 hstr (h.2.2 l hl) bs hlen u, h.2.2⟩

/-- The statements keep `Mem`. -/
theorem closed {args : List String} {idV V idA B : Int} {qs : List Pointer} (ls : List Local)
    (hstr : StrAbove args B qs) : PrintMem.Closed (Mem args idV V idA B qs ls) ls where
  touched h t := h.touched t
  excluded n h := h.excluded n
  stored v hl h := h.write hstr hl _ (by simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]) _
  unstored hl h := h.write hstr hl _ (by simp [Mem.Concrete.plainBytes]) _

/-- The read-modify-writes keep `Mem`. -/
theorem stmtClosed {args : List String} {idV V idA B : Int} {qs : List Pointer} (ls : List Local)
    (hstr : StrAbove args B qs) : Rmw.StmtClosed (Mem args idV V idA B qs ls) ls :=
  ⟨fun _ _ h t => h.touched t, fun _ n h => h.excluded n,
    fun _ v l hl h => h.write hstr hl _ (by simp [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length]) _⟩

end Silmaril.Compile.Core.Verified.CfgArgvMem
