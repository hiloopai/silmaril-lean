module

public import Silmaril.X86.Concurrency.Bridge.PoolRun.Thms
public import Silmaril.X86.MemEvent.Thms
public import Silmaril.X86.Pool.Thms

/-!
# Gap 1: the memory invariant of a TSO pool run over a test memory

Along a run of the TSO pool (`TsoReach atomic9Ev`) from a test memory, the memory
keeps the test's regions, stays backed, keeps the bytes of the code pages, and every buffered
byte is write-permitted (`MemInv`, `memInv_step`, `memInv_flush`). So every thread's view
`overlay memory buffer` has the test's regions, is backed and holds the code (`MemInv.view`):
the memory hypotheses of `xstep_of_step` and of `tvRunDefined_holds`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun

open Silmaril.X86 (State Byte Word)
open Silmaril.X86.Ext (Loaded)
open Silmaril.Process (Memory Region)
open Silmaril.X86 hiding Instr decode Reg Word Mem step Byte
open Silmaril.X86.Pool (TPool TsoStep TsoFlush overlay syncs storeEntries atomic9Ev readSpan
  Entry)
open Silmaril.X86.Concurrency.Bridge

/-! ## Bytes -/

theorem readBacking_congr {b b' : Silmaril.Process.ByteMemory} :
    ∀ (k a : Nat), (∀ j < k, b'[a + j]? = b[a + j]?) →
      Memory.readBacking b' a k = Memory.readBacking b a k
  | 0, _, _ => rfl
  | k + 1, a, h => by
    have h0 := h 0 (by omega)
    have ih := readBacking_congr (b := b) (b' := b') k (a + 1) fun j hj => by
      have := h (j + 1) (by omega)
      rw [show a + (j + 1) = a + 1 + j by omega] at this
      exact this
    simp only [Nat.add_zero] at h0
    simp only [Memory.readBacking, Std.ExtHashMap.get?_eq_getElem?, h0, ih]

/-- `Loaded` depends only on the regions and the executable bytes. -/
theorem loaded_congr {m m' : Memory} {base : Word} {code : List Byte} (hl : Loaded m base code)
    (hR : m'.regions = m.regions)
    (hx : ∀ a, m.permits .execute a = true → m'.bytes[a]? = m.bytes[a]?) :
    Loaded m' base code := by
  unfold Loaded Memory.fetchBytes Memory.readWith at *
  cases hc : m.checkSpan .execute base.toNat code.length
  · simp [hc] at hl
  have hc' : m'.checkSpan .execute base.toNat code.length = true := by
    simpa [Memory.checkSpan, Memory.permits, hR] using hc
  rw [hc] at hl
  rw [hc']
  simp only [ite_true] at hl ⊢
  rw [readBacking_congr]
  · exact hl
  · intro j hj
    apply hx
    rw [Memory.checkSpan_iff] at hc
    exact hc.2.2 j hj

/-- In a test's mapping list no byte is both writable and executable. -/
theorem wx {m : Memory} {N : Nat} (hR : m.regions = Silmaril.X86.Litmus.testRegions N)
    {a : Nat} (hw : m.permits .write a = true) : m.permits .execute a = false := by
  cases hx : m.permits .execute a
  · rfl
  exfalso
  simp only [Memory.permits, hR, Silmaril.X86.Litmus.testRegions, List.any_cons,
    List.any_nil, Bool.or_eq_true, Bool.and_eq_true,
    Silmaril.Process.Permissions.allows, Region.Contains, Silmaril.X86.Litmus.dataBase,
    Silmaril.X86.Litmus.dataSize, Bool.or_false] at hw hx
  rcases hw with ⟨h1, -⟩ | ⟨-, h2⟩
  · rcases hx with ⟨-, h3⟩ | ⟨h4, -⟩
    · cases h3
    · have := of_decide_eq_true h1
      have := of_decide_eq_true h4
      omega
  · cases h2

theorem install_outside' (b : Silmaril.Process.ByteMemory) (a : Nat) (bs : List Byte) (x : Nat)
    (h : x < a ∨ a + bs.length ≤ x) : (Memory.install b a bs)[x]? = b[x]? := by
  have := Memory.install_outside b a bs x h
  simpa [Std.ExtHashMap.get?_eq_getElem?] using this

theorem install_isSome (b : Silmaril.Process.ByteMemory) (a : Nat) (bs : List Byte) (x : Nat)
    (h : (b[x]?).isSome = true) : ((Memory.install b a bs)[x]?).isSome = true := by
  by_cases hx : x < a ∨ a + bs.length ≤ x
  · rw [install_outside' b a bs x hx]; exact h
  · have := Memory.install_get b a bs (x - a) (by omega)
    rw [show a + (x - a) = x by omega] at this
    simp [Std.ExtHashMap.get?_eq_getElem?] at this
    simp [this]

/-- Every byte of the buffer is write-permitted. -/
def BufOk (m : Memory) (buf : List Entry) : Prop :=
  ∀ e ∈ buf, ∀ j < e.2.length, m.permits .write (e.1 + j) = true

theorem foldl_install_outside (P : Nat → Prop) :
    ∀ (buf : List Entry) (b : Silmaril.Process.ByteMemory) (x : Nat),
      (∀ e ∈ buf, ∀ j < e.2.length, P (e.1 + j)) → ¬ P x →
      (buf.foldl (fun b e => Memory.install b e.1 e.2) b)[x]? = b[x]?
  | [], _, _, _, _ => rfl
  | e :: buf, b, x, h, hx => by
    simp only [List.foldl_cons]
    rw [foldl_install_outside P buf _ x (fun e' he' => h e' (by simp [he'])) hx]
    apply install_outside'
    by_contra hc
    exact hx (by
      have := h e (by simp) (x - e.1) (by omega)
      rwa [show e.1 + (x - e.1) = x by omega] at this)

theorem foldl_install_isSome :
    ∀ (buf : List Entry) (b : Silmaril.Process.ByteMemory) (x : Nat), (b[x]?).isSome = true →
      ((buf.foldl (fun b e => Memory.install b e.1 e.2) b)[x]?).isSome = true
  | [], _, _, h => h
  | e :: buf, b, x, h => by
    simp only [List.foldl_cons]
    exact foldl_install_isSome buf _ x (install_isSome _ _ _ _ h)

theorem overlay_nil (m : Memory) : overlay m [] = m := rfl

theorem backed_overlay {m : Memory} (hb : Backed m) (buf : List Entry) : Backed (overlay m buf) := by
  intro a ha
  have := hb a ha
  simp only [Std.ExtHashMap.get?_eq_getElem?] at this ⊢
  exact foldl_install_isSome buf _ a this

/-! ## The invariant -/

/-- **The memory invariant** of a pool run from the test memory `m₀` of a test with `N`
threads. -/
structure MemInv (N : Nat) (m₀ : Memory) (p : TPool Nat) : Prop where
  regions : p.memory.regions = Silmaril.X86.Litmus.testRegions N
  backed : Backed p.memory
  code : ∀ a, p.memory.permits .execute a = true → p.memory.bytes[a]? = m₀.bytes[a]?
  buf : ∀ t, BufOk p.memory (p.buffer t)

/-- **The views**: a thread's view has the test's regions, is backed, and holds the initial
memory's executable bytes. -/
theorem MemInv.view {N : Nat} {m₀ : Memory} {p : TPool Nat} (h : MemInv N m₀ p) (t : Nat) :
    (overlay p.memory (p.buffer t)).regions = Silmaril.X86.Litmus.testRegions N ∧
      Backed (overlay p.memory (p.buffer t)) ∧
      ∀ a, (overlay p.memory (p.buffer t)).permits .execute a = true →
        (overlay p.memory (p.buffer t)).bytes[a]? = m₀.bytes[a]? := by
  refine ⟨h.regions, backed_overlay h.backed _, fun a ha => ?_⟩
  have ha' : p.memory.permits .execute a = true := ha
  rw [← h.code a ha']
  apply foldl_install_outside (fun y => p.memory.permits .write y = true) _ _ a (h.buf t)
  intro hw
  rw [wx h.regions hw] at ha'
  cases ha'

/-- The initial pool of a test memory satisfies the invariant. -/
theorem memInv_init {t : Silmaril.X86.MemoryModel.Litmus.Test} {m₀ : Memory} (h : TestMem t m₀) :
    MemInv t.threads.length m₀ (testPool t m₀) :=
  ⟨h.1, h.2.2.2, fun _ _ => rfl, fun _ e he => by simp [testPool] at he⟩

/-- A local executor that succeeded keeps the regions, writes only write-permitted bytes, and
leaves them backed. -/
theorem exec_patched {i : Atomic9.Instr} {c c' : State} {n : Nat} {m m' : Memory}
    (hx : Atomic9.exec i c m n = .ok c' m') :
    MemEvent.Patched (MemEvent.writeSet (MemEvent.atomic9Accesses i c n)) m m' m m' :=
  MemEvent.Local.frame (MemEvent.atomic9_local i c n) (a := c') (by simp [MemEvent.extView, hx])

/-- **The invariant is kept by an instruction step.** -/
theorem memInv_step {N : Nat} {m₀ : Memory} {Fin : Nat → State → Prop} {p p' : TPool Nat}
    {t : Nat} (h : MemInv N m₀ p) (hs : TsoStep atomic9Ev Fin p t p') : MemInv N m₀ p' := by
  cases hs with
  | @sync c c' i n mem' ht hnf hf hsy he hx =>
    have hP := exec_patched hx
    refine ⟨hP.regions.trans h.regions, fun a ha => ?_, fun a ha => ?_, fun t' => ?_⟩
    · have ha' : p.memory.permits .read a = true := by
        simpa [Memory.permits, hP.regions] using ha
      by_cases hW : MemEvent.writeSet (MemEvent.atomic9Accesses i c n) a
      · simpa [Std.ExtHashMap.get?_eq_getElem?] using (hP.wrote a hW).2
      · have := h.backed a ha'
        simp only [Std.ExtHashMap.get?_eq_getElem?] at this ⊢
        rw [hP.outside a hW]; exact this
    · have ha' : p.memory.permits .execute a = true := by
        simpa [Memory.permits, hP.regions] using ha
      have hW : ¬ MemEvent.writeSet (MemEvent.atomic9Accesses i c n) a := fun hW => by
        rw [wx h.regions (hP.wrote a hW).1] at ha'; cases ha'
      dsimp only
      rw [hP.outside a hW]; exact h.code a ha'
    · intro e he j hj
      have := h.buf t' e he j hj
      simpa [Memory.permits, hP.regions] using this
  | @buffered c c' i n view' ht hnf hf hsy hx =>
    have hP := exec_patched hx
    refine ⟨h.regions, h.backed, h.code, fun t' => ?_⟩
    dsimp only
    by_cases htt : t' = t
    · subst htt
      simp only [Function.update_self]
      intro e he j hj
      rcases List.mem_append.mp he with he | he
      · exact h.buf _ e he j hj
      · simp only [storeEntries, List.mem_map, List.mem_filter] at he
        obtain ⟨ev, ⟨hev, hw⟩, rfl⟩ := he
        simp only [readSpan, List.length_map, List.length_range] at hj
        have := (hP.wrote (ev.addr + j) ⟨ev, hev, hw, by
          constructor <;> omega⟩).1
        exact this
    · simp only [Function.update_of_ne htt]
      exact h.buf t'

/-- **The invariant is kept by a flush.** -/
theorem memInv_flush {N : Nat} {m₀ : Memory} {p p' : TPool Nat} (h : MemInv N m₀ p)
    (hf : TsoFlush p p') : MemInv N m₀ p' := by
  cases hf with
  | @head t a bs rest hb =>
    have hok := h.buf t
    rw [hb] at hok
    have hw : ∀ j < bs.length, p.memory.permits .write (a + j) = true :=
      hok (a, bs) (by simp)
    refine ⟨h.regions, fun x hx => ?_, fun x hx => ?_, fun t' => ?_⟩
    · have := h.backed x hx
      simp only [Std.ExtHashMap.get?_eq_getElem?] at this ⊢
      exact install_isSome _ _ _ _ this
    · dsimp only
      have hx' : p.memory.permits .execute x = true := hx
      rw [install_outside']
      · exact h.code x hx'
      · by_contra hc
        have := hw (x - a) (by omega)
        rw [show a + (x - a) = x by omega, ] at this
        rw [wx h.regions this] at hx'; cases hx'
    · intro e he j hj
      have hp : ({ p.memory with bytes := Memory.install p.memory.bytes a bs } : Memory).permits
          .write (e.1 + j) = p.memory.permits .write (e.1 + j) := rfl
      rw [hp]
      by_cases htt : t' = t
      · subst htt
        simp only [Function.update_self] at he
        exact hok e (by simp [he]) j hj
      · simp only [Function.update_of_ne htt] at he
        exact h.buf t' e he j hj

end Silmaril.Proofs.X86.Concurrency.Bridge.TsoRun
