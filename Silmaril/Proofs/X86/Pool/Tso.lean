module

public import Silmaril.X86.Pool.Defs

/-!
# Proofs: the TSO pool against the byte-granular store-buffer machine and the step decomposition

* `install_getElem?`: installing a span is the store-buffer machine's `writeMem` on the byte map.
* `overlay_getElem?`: a thread's view is the store-buffer machine's `viewMem` (its own buffer,
  newest entry first, over memory), so `TsoStep` reads what its `XStep.load` would read.
* `tsoFlush_toX`: a pool flush projects to the store-buffer machine's `XFlush`.
* `openEv_step`, `open9Ev_step`, `atomic9Ev_step`: the `EvMachine` steps are `Open.step`,
  `Open9.step` and `Atomic9.step` (`*_step_eq`).
* `ofPool_drained`, `forget_ofPool`: an SC pool is a drained TSO pool.
* `tsoStep_sync_sc`: a synchronising TSO step (empty buffer) is an SC step.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Pool

open Silmaril.X86 (State MState Byte)
open Silmaril.Process (Memory)
open Silmaril.X86.Pool
open Silmaril.X86.MemoryModel.Tso (entryByte writeMem readBufByte viewMem XFlush)

variable {Tid : Type}

/-! ## Installing spans and overlays -/

theorem install_getElem? (b : Silmaril.Process.ByteMemory) (a : Nat) (bs : List Byte) (x : Nat) :
    (Memory.install b a bs)[x]? = (entryByte a bs x).or b[x]? := by
  induction bs generalizing a with
  | nil => simp [Memory.install, entryByte]
  | cons y ys ih =>
    simp only [Memory.install, Std.ExtHashMap.getElem?_insert, ih]
    by_cases h : a = x
    · subst h; simp [entryByte]
    · have hb : (a == x) = false := by simpa using h
      rw [hb]
      simp only [Bool.false_eq_true, ite_false, entryByte]
      by_cases hx : a + 1 ≤ x
      · have : a ≤ x := by omega
        simp only [hx, this, ite_true]
        rw [show x - a = (x - (a + 1)) + 1 by omega]
        simp
      · have : ¬ a ≤ x := by omega
        simp [hx, this]

theorem foldl_install_getElem? (buf : List Entry) (b : Silmaril.Process.ByteMemory) (x : Nat) :
    (buf.foldl (fun b e => Memory.install b e.1 e.2) b)[x]? = (readBufByte x buf).or b[x]? := by
  induction buf generalizing b with
  | nil => simp [readBufByte]
  | cons e rest ih =>
    simp only [List.foldl_cons, ih, install_getElem?, readBufByte, Option.or_assoc]

/-- **A thread's view is the store-buffer machine's `viewMem`**: its own buffer, newest entry first,
over memory. -/
theorem overlay_getElem? (p : TPool Tid) (t : Tid) (x : Nat) :
    (overlay p.memory (p.buffer t)).bytes[x]? = viewMem p.toX t x := by
  simp [overlay, foldl_install_getElem?, viewMem, TPool.toX]

theorem overlay_nil (mem : Memory) : overlay mem [] = mem := rfl

theorem overlay_regions (mem : Memory) (buf : List Entry) :
    (overlay mem buf).regions = mem.regions := rfl

/-- **A pool flush is a store-buffer flush** of the projected state. -/
theorem tsoFlush_toX [DecidableEq Tid] {p p' : TPool Tid} (h : TsoFlush p p') :
    XFlush p.toX p'.toX := by
  cases h with
  | head hb =>
    rename_i t a bs rest
    have := XFlush.head p.toX t a bs rest hb
    convert this using 2
    · funext x
      simp [TPool.toX, install_getElem?, writeMem]
    · rfl

/-! ## Machines -/

theorem openEv_step : openEv.step = Silmaril.X86.Open.step := by
  funext m
  rw [Silmaril.X86.MemEvent.open_step_eq]
  rfl

theorem open9Ev_step : open9Ev.step = Silmaril.X86.Open9.step := by
  funext m
  rw [Silmaril.X86.MemEvent.open9_step_eq]
  rfl

theorem atomic9Ev_step : atomic9Ev.step = Silmaril.X86.Atomic9.step := by
  funext m
  rw [Silmaril.X86.MemEvent.atomic9_step_eq]
  rfl

/-! ## SC pools inside TSO pools -/

theorem ofPool_drained (p : Pool Tid) : Drained (TPool.ofPool p) := fun _ => rfl

theorem forget_ofPool (p : Pool Tid) : forget (TPool.ofPool p) = p := rfl

/-- **A synchronising TSO step is an SC step** of the forgotten pool. -/
theorem tsoStep_sync_sc [DecidableEq Tid] {M : EvMachine} {Fin : Tid → State → Prop}
    {p : TPool Tid} {t : Tid} {c c' : State} {i : M.Instr} {n : Nat} {mem' : Memory}
    (ht : p.threads t = some c) (hnf : ¬ Fin t c)
    (hf : M.fetch (overlay p.memory (p.buffer t)) c.rip.toNat = some (i, n))
    (he : p.buffer t = []) (hx : M.exec i c p.memory n = .ok c' mem') :
    SCStepF M.step Fin (forget p) t
      (forget { p with threads := Function.update p.threads t (some c'), memory := mem' }) := by
  refine ⟨⟨c, ht, hnf⟩, ?_⟩
  have hs : M.step ⟨c, p.memory⟩ = some ⟨c', mem'⟩ := by
    rw [he, overlay_nil] at hf
    simp [EvMachine.step, hf, hx, Silmaril.X86.Open.ofResult]
  exact SCStep.go (p := forget p) ht hs

end Silmaril.Proofs.X86.Pool
