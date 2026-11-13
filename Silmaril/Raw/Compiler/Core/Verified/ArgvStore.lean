module

public import Silmaril.Compiler.Core.Verified.ArgvMem.Defs
/-! # Keeping argument objects through local integer stores

`ArgvMem.Reads` preserves every byte and therefore cannot describe a loop that
updates a counter. Here a store below the argument objects preserves `Objs`
directly. The separation hypotheses are explicit: the CFG startup proof must
establish them for its allocated locals before using this result.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.ArgvStore

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.StartupArgs
open Mem.Concrete (Pointer fetchBytes readByte)

/-- Allocations below the argument objects preserve their invariant. Together
with `Objs.reads` and `objs_stored`, this separates the effects of creating a
loop counter, reading an argument, and updating the counter. -/
theorem objs_grows {m m' : Mem.Concrete.State} {args : List String}
    {idV V idA B : Int} {qs : List Pointer}
    (h : ArgvMem.Objs m args idV V idA B qs) (g : Grows m m')
    (iv : idV < m.nextId) (ia : idA < m.nextId)
    (count : (args.length : Int) ≤ m.nextId)
    (hv : m.lastAddress ≤ V) (ha : m.lastAddress ≤ B) :
    ArgvMem.Objs m' args idV V idA B qs := by
  refine ⟨h.ptr.grows g iv hv, h.arr.grows g ia ha, ?_, h.pos, h.top⟩
  refine ⟨h.strs.1, ?_⟩
  intro i s hi
  obtain ⟨b, hq, str, hl, ht, hp⟩ := h.strs.2 i s hi
  have ilt : i < args.length := (List.getElem?_eq_some_iff.mp hi).1
  exact ⟨b, hq, str.grows g (by omega) hl, g.last.trans hl, ht, hp⟩

/-- An integer store preserves argument objects that lie above its four bytes.
The store may change a local's bytes and pointer metadata; neither global byte
equality nor read-only execution is assumed. -/
theorem objs_stored {m : Mem.Concrete.State} {args : List String}
    {idV V idA B : Int} {qs : List Pointer}
    (h : ArgvMem.Objs m args idV V idA B qs) (id addr n : Int)
    (hv : addr + 4 ≤ V) (ha : addr + 4 ≤ B)
    (hs : ∀ (i : Nat) (s : String), args[i]? = some s → ∀ b : Int,
      qs[i]? = some (Pointer.allocated (0 + i) b) → addr + 4 ≤ b) :
    ArgvMem.Objs (Locals.stored m id addr n) args idV V idA B qs := by
  let m' := Locals.stored m id addr n
  have fields := writeRepresentation_fields addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  have allocs : m'.allocations = m.allocations := fields.1
  have dead : m'.dead = m.dead := fields.2.2.2.1
  have last : m'.lastAddress = m.lastAddress := fields.2.2.1
  have live {oid b sz : Int} (l : Live m oid b sz) : Live m' oid b sz := by
    exact ⟨by rw [allocs]; exact l.lookup, by rw [dead]; exact l.alive⟩
  have bytes (x : Int) (hx : addr + 4 ≤ x) :
      m'.bytes.lookup x = m.bytes.lookup x ∧
        m'.pointerBytes.lookup x = m.pointerBytes.lookup x := by
    apply writeRepresentation_out addr
      (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m x
    right
    simpa [Mem.Concrete.plainBytes, Mem.Concrete.encodeInteger_length] using hx
  have fetch (k : Nat) (x : Int) (hx : addr + 4 ≤ x) :
      fetchBytes k x m'.bytes = fetchBytes k x m.bytes := by
    induction k generalizing x with
    | zero => rfl
    | succ k ih =>
      simp only [fetchBytes, readByte, (bytes x hx).1, ih (x + 1) (by omega)]
  refine ⟨?_, ?_, ?_, h.pos, h.top⟩
  · exact ⟨live h.ptr.live, (fetch 8 V hv).trans h.ptr.bytes,
      fun k hk => (bytes (V + k) (by omega)).2.trans (h.ptr.prov k hk)⟩
  · refine ⟨live h.arr.live, ?_, ?_⟩
    · intro i oid b hq
      obtain ⟨hb, hp⟩ := h.arr.slot i oid b hq
      exact ⟨(fetch 8 (B + 8 * i) (by omega)).trans hb,
        fun k hk => (bytes (B + 8 * i + k) (by omega)).2.trans (hp k hk)⟩
    · exact (fetch 8 (B + 8 * qs.length) (by omega)).trans h.arr.null
  · refine ⟨h.strs.1, ?_⟩
    intro i s hsi
    obtain ⟨b, hq, str, hl, ht, hp⟩ := h.strs.2 i s hsi
    have hb := hs i s hsi b hq
    refine ⟨b, hq, ?_, by rwa [last], ht, hp⟩
    exact ⟨live str.live,
      fun j c hc => (bytes (b + j) (by omega)).1.trans (str.chars j c hc),
      (bytes (b + s.length) (by omega)).1.trans str.nul⟩

end Silmaril.Compile.Core.Verified.ArgvStore
