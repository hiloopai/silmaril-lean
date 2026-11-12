module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.FwdGrow

/-!
# The memory-alignment invariant holds along V1 runs

Pass 3 restates `memory.size` at page-aligned memories of fewer than `2^32` pages
(`MemsAligned10`). This module shows that the invariant is kept by every V1 step from a store
with no host function (`memsAligned10_step`), and so along every run (`memsAligned10_steps`):

* stores write within bounds, so the memory keeps its size (`Memory.writeBytes_size`);
* `memory.grow` succeeds only at a page-aligned memory and adds whole pages up to `65536`
  (`Memory.grow?`); a failing grow writes the memory back unchanged;
* every other step keeps the store, except a host call, which a store with no host function does
  not make. Typed states have no host function (`not_typed_host10`), and no V1 step adds one
  (`noHost10_step`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Whole

open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step frameMemory setMemory
  setGlobal storeInt storeFloat)
open Silmaril.Wasm.Execution.Runtime (Frame MemInst MemAddr FuncInst)

variable {H : Type} {hn : H → String}

/-- The store has no host function. -/
def NoHost10 (s : Store H) : Prop :=
  ∀ (i : Nat) (ft : V1.FuncType) (h : H), s.funcs[i]? ≠ some (.host ft h)

/-- A typed state has no host function. -/
theorem noHost10_of_typed {B : Builtins} {s : Store H} {f : Frame}
    (hz : Silmaril.Wasm.SpecTec.Sim.TypedV (simEnv10 B) Silmaril.Wasm.SpecTec.Sim.stateT
      (stateV hn s f)) : NoHost10 s :=
  fun i _ _ hs => not_typed_host10 (a := ⟨i⟩) hz hs

/-! ## Memories -/

/-- A memory with the same number of bytes is aligned when the old one was. -/
theorem memAligned10_of_size {m : MemInst} {d : Execution.Memory.Bytes} (hal : MemAligned10 m)
    (hs : d.size = m.data.size) : MemAligned10 {m with data := d} := by
  simp only [MemAligned10, Execution.Memory.size] at hal ⊢
  rw [hs]
  exact hal

/-- A grown memory is aligned. -/
theorem memAligned10_grow {m : MemInst} {n : Nat} {d : Execution.Memory.Bytes}
    (hg : Execution.Memory.grow? m.data m.max n = some d) : MemAligned10 {m with data := d} := by
  have hsz := Execution.Memory.grow_size _ _ _ _ hg
  unfold Execution.Memory.grow? at hg
  split at hg
  · rename_i hc
    simp only [MemAligned10, Execution.Memory.size, Execution.Memory.pageSize,
      Execution.Memory.maxPages] at hc hsz ⊢
    rw [hsz]
    omega
  · cases hg

/-- Replacing a memory of an aligned store by an aligned one keeps it aligned. -/
theorem memsAligned10_set {s : Store H} (hal : MemsAligned10 s) (a : MemAddr) {m : MemInst}
    (hm : MemAligned10 m) : MemsAligned10 (setMemory s a m) := fun m' h' =>
  (List.mem_or_eq_of_mem_set h').elim (hal m') fun e => e ▸ hm

/-- `storeInt` keeps the size. -/
theorem storeInt_size10 {t : IntType} {p : Option V1.PackSize} {mem b : Execution.Memory.Bytes}
    {start : Nat} {x : BitVec t.width} (h : storeInt t p mem start x = some b) :
    b.size = mem.size :=
  Execution.Memory.writeBytes_size _ _ _ _ h

/-- `storeFloat` keeps the size. -/
theorem storeFloat_size10 {t : FloatType} {mem b : Execution.Memory.Bytes} {start : Nat}
    {x : BitVec t.width} (h : storeFloat t mem start x = some b) : b.size = mem.size :=
  Execution.Memory.writeBytes_size _ _ _ _ h

/-! ## Every step -/

/-- Writing a memory of the frame keeps the store aligned, given the new memory's size. -/
theorem memsAligned10_write {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {d : Execution.Memory.Bytes} (hal : MemsAligned10 s) (hm : frameMemory s f = some (a, m))
    (hs : d.size = m.data.size) : MemsAligned10 (setMemory s a {m with data := d}) :=
  memsAligned10_set hal a (memAligned10_of_size (hal.frame hm) hs)

/-- `memory.grow` keeps the store aligned. -/
theorem memsAligned10_memoryGrow {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    {c r : BitVec 32} {b : Execution.Memory.Bytes} (hal : MemsAligned10 s)
    (hm : frameMemory s f = some (a, m)) (hg : Execution.Memory.Grow m.data m.max c.toNat b r) :
    MemsAligned10 (setMemory s a {m with data := b}) := by
  cases hg with
  | success _ h => exact memsAligned10_set hal a (memAligned10_grow h)
  | failure => exact memsAligned10_write hal hm rfl

/-- **Every V1 step from an aligned store with no host function keeps the store aligned.** -/
theorem memsAligned10_step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hnh : NoHost10 c.store) (hal : MemsAligned10 c.store) : MemsAligned10 c'.store := by
  induction h with
  | context _ vs tail ih => exact ih hnh hal
  | label _ n cont ih => exact ih hnh hal
  | frame _ n outer ih => exact ih hnh hal
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact absurd h₁ (hnh _ _ _)
  | intStore s f t p arg c x a m b h₁ h₂ => exact memsAligned10_write hal h₁ (storeInt_size10 h₂)
  | floatStore s f t arg c x a m b h₁ h₂ => exact memsAligned10_write hal h₁ (storeFloat_size10 h₂)
  | memoryGrow s f a m c r b h₁ h₂ => exact memsAligned10_memoryGrow hal h₁ h₂
  | globalSet s f i a g v _ _ _ => exact hal
  | _ => exact hal

/-- **No V1 step from a store with no host function adds one.** -/
theorem noHost10_step {host : HostSemantics H} {c c' : Config H} (h : Step host c c')
    (hnh : NoHost10 c.store) : NoHost10 c'.store := by
  induction h with
  | context _ vs tail ih => exact ih hnh
  | label _ n cont ih => exact ih hnh
  | frame _ n outer ih => exact ih hnh
  | invokeHost s s' f a ft fn args r h₁ _ _ => exact absurd h₁ (hnh _ _ _)
  | _ => exact hnh

/-- **The alignment invariant along every V1 run** from an aligned store with no host function. -/
theorem memsAligned10_steps {host : HostSemantics H} {c c' : Config H}
    (h : V1.Execution.Steps host c c') (hnh : NoHost10 c.store)
    (hal : MemsAligned10 c.store) : NoHost10 c'.store ∧ MemsAligned10 c'.store := by
  induction h with
  | refl => exact ⟨hnh, hal⟩
  | tail _ hs ih => exact ⟨noHost10_step hs ih.1, memsAligned10_step hs ih.1 ih.2⟩

end Silmaril.Wasm.SpecTec.Sim10.Whole
