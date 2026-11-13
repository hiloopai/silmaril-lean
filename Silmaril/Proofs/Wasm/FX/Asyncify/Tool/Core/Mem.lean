module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core.Pure

/-!
# `i32.load` and `i32.store` of the frame machine as Core 3.0 steps

The machine keeps a word memory; Core keeps bytes. `MemAre s f mem cap` says that every aligned
word of the `cap`-byte memory 0 is the machine's word there. At an aligned, in-bounds address:

* `run_load`: Core loads the machine's word;
* `run_store`: Core stores the word, and the new memory holds `upd mem a v` (a store of four
  bytes at an aligned address leaves every other aligned word as it was,
  `load_write_disjoint`);
* `run_load_oob`, `run_store_oob`: an access past `cap` traps in Core, as in the bounded machine
  (`Silmaril.Wasm.FX.Asyncify.Tool.stepB`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Memory
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.FX.Asyncify.Tool

variable {H : Type} {Pf : Profile} {host : HostSemantics H}

/-- A write leaves the bytes outside its range as they were. -/
theorem extract_write_disjoint {memory bytes after : Bytes} {a b n : Nat}
    (h : writeBytes memory a bytes = some after)
    (hd : b + n ≤ a ∨ a + bytes.size ≤ b) : after.extract b (b + n) = memory.extract b (b + n) := by
  obtain ⟨bound, rfl⟩ := (writeBytes_eq_some_iff memory bytes after a).mp h
  ext1
  simp only [ByteArray.data_extract, ByteArray.data_append]
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp [Array.getElem_append, Array.getElem_extract] at h1 h2 ⊢
    repeat' split
    all_goals first | rfl | omega | (congr 1; omega)

/-- A store leaves the loads outside its range as they were. -/
theorem load_write_disjoint {memory after : Bytes} {a b : Nat} (w : BitVec (8 * 4))
    (h : store memory a w = some after) (hd : b + 4 ≤ a ∨ a + 4 ≤ b) :
    load after b 4 = load memory b 4 := by
  have hsz : after.size = memory.size := writeBytes_size _ _ _ _ h
  have he := extract_write_disjoint (n := 4) h (by simpa using hd)
  unfold load readBytes
  rw [hsz, he]

theorem mem?_setMem (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) {ma : Nat}
    {mi : MemInst} (hm : s.mem? f ⟨0⟩ = some (ma, mi)) (mi' : MemInst) :
    (s.setMem ma mi').mem? f ⟨0⟩ = some (ma, mi') := by
  unfold Store.mem? at hm ⊢
  cases hx : f.module.mems[(⟨0⟩ : MemIdx).toNat]? with
  | none => rw [hx] at hm; cases hm
  | some b =>
    rw [hx] at hm
    have hb : s.mems[b]? = some mi ∧ b = ma := by
      cases hs : s.mems[b]? with
      | none => simp [hs] at hm
      | some m => simp [hs] at hm; exact ⟨by rw [hm.2], hm.1⟩
    obtain ⟨hs, rfl⟩ := hb
    have hlt : b < s.mems.length := (List.getElem?_eq_some_iff.1 hs).1
    simp [Store.setMem, List.getElem?_set, hlt]

/-- The memory after an aligned store. -/
theorem memAre_store {s : Store H} {f : Silmaril.Wasm.Execution.Core.Frame} {mem : Nat → W}
    {cap ma : Nat} {mi : MemInst} (hM : MemAre s f mem cap) (hm : s.mem? f ⟨0⟩ = some (ma, mi))
    {a : Nat} (ha : a % 4 = 0) (v : W) {b : ByteArray} (hs : store mi.bytes a (count := 4) v = some b) :
    MemAre (s.setMem ma { mi with bytes := b }) f (upd mem a v) cap := by
  obtain ⟨ma', mi', hm', hsz, hw⟩ := hM
  rw [hm] at hm'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
  refine ⟨ma, { mi with bytes := b }, mem?_setMem s f hm _, ?_, fun c hc hcap => ?_⟩
  · show b.size = cap
    rw [writeBytes_size _ _ _ _ hs, hsz]
  · show load b c 4 = some (upd mem a v c)
    by_cases hca : c = a
    · subst hca
      simp only [upd, ↓reduceIte]
      exact load_store _ _ _ 4 v hs
    · have hd : c + 4 ≤ a ∨ a + 4 ≤ c := by omega
      rw [load_write_disjoint v hs hd, hw c hc hcap]
      simp [upd, hca]

theorem setWidth_self32 (c : BitVec 32) : c.setWidth 32 = c := BitVec.setWidth_eq c

/-- **`i32.load` at an aligned, in-bounds address loads the machine's word.** -/
theorem run_load (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops : List W} {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (x : W)
    (arg : MemArg) (ha : (x.toNat + arg.offset.val) % 4 = 0)
    (hcap : x.toNat + arg.offset.val + 4 ≤ cap) :
    Execution.Core.Steps Pf host
      ⟨s, localsF f ls, stackA (x :: ops) ++ .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA (mem (x.toNat + arg.offset.val) :: ops) ++ rest⟩ := by
  obtain ⟨ma, mi, hm, -, hw⟩ := hM
  have hl : load mi.bytes (effAddr x.toNat arg) 4 = some (mem (x.toNat + arg.offset.val)) :=
    hw _ ha hcap
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.memory (.loadIntVal (s := s) (f := localsF f ls) (t := .i32) (a := .i32) (i := x)
      (arg := arg) hm hl))
  rw [stackA_cons, stackA_cons]
  exact Relation.ReflTransGen.single (by simpa [stackA, aconst, i32_toAdmin, IntType.width, AddrType.intType] using hs)

/-- **`i32.store` at an aligned, in-bounds address stores the machine's word.** -/
theorem run_store (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops : List W} {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (v x : W)
    (arg : MemArg) (ha : (x.toNat + arg.offset.val) % 4 = 0)
    (hcap : x.toNat + arg.offset.val + 4 ≤ cap) :
    ∃ s', MemAre s' f (upd mem (x.toNat + arg.offset.val) v) cap ∧
      (∀ g, s'.global? f g = s.global? f g) ∧ s'.funcs = s.funcs ∧
      Execution.Core.Steps Pf host
        ⟨s, localsF f ls, stackA (v :: x :: ops) ++ .plain (.intStore .i32 none ⟨0⟩ arg) :: rest⟩
        ⟨s', localsF f ls, stackA ops ++ rest⟩ := by
  obtain ⟨ma, mi, hm, hsz, hw⟩ := hM
  have hbound : x.toNat + arg.offset.val + (encodeLE 4 v.toNat).size ≤ mi.bytes.size := by
    rw [encodeLE_size, hsz]; exact hcap
  have e1 : store mi.bytes (x.toNat + arg.offset.val) (count := IntType.i32.width / 8)
      (v.setWidth (8 * (IntType.i32.width / 8))) =
      writeBytes mi.bytes (x.toNat + arg.offset.val) (encodeLE 4 v.toNat) := by
    show writeBytes mi.bytes _ (encodeLE 4 (v.setWidth 32).toNat) = _
    rw [BitVec.setWidth_eq]
  have e3 : writeBytes mi.bytes (x.toNat + arg.offset.val) (encodeLE 4 v.toNat) =
      some ((encodeLE 4 v.toNat).copySlice 0 mi.bytes (x.toNat + arg.offset.val)
        (encodeLE 4 v.toNat).size) := by
    simp only [writeBytes, hbound, ↓reduceIte]
  obtain ⟨b, hb⟩ : ∃ b, store mi.bytes (x.toNat + arg.offset.val) (count := IntType.i32.width / 8)
      (v.setWidth (8 * (IntType.i32.width / 8))) = some b := ⟨_, e1.trans e3⟩
  have hb4 : store mi.bytes (x.toNat + arg.offset.val) (count := 4) v = some b :=
    (show store mi.bytes (x.toNat + arg.offset.val) (count := 4) v = _ from rfl).trans
      (e1.symm.trans hb)
  refine ⟨s.setMem ma { mi with bytes := b }, memAre_store ⟨ma, mi, hm, hsz, hw⟩ hm ha v hb4,
    fun _ => rfl, rfl, ?_⟩
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.memory (.storeIntVal (s := s) (f := localsF f ls) (t := .i32) (a := .i32) (i := x)
      (c := v) (arg := arg) hm hb))
  rw [stackA_cons2]
  exact Relation.ReflTransGen.single
    (by simpa [stackA, aconst, i32_toAdmin, IntType.width, AddrType.intType] using hs)

/-- **`i32.load` past `cap` bytes traps in Core.** -/
theorem run_load_oob (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops : List W} {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (x : W)
    (arg : MemArg) (hcap : cap < x.toNat + arg.offset.val + 4) :
    Step Pf host
      ⟨s, localsF f ls, stackA (x :: ops) ++ .plain (.intLoad .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ := by
  obtain ⟨ma, mi, hm, hsz, -⟩ := hM
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.memory (.loadIntOob (s := s) (f := localsF f ls) (t := .i32) (a := .i32) (i := x)
      (arg := arg) hm (by rw [hsz]; exact hcap)))
  rw [stackA_cons]
  simpa [stackA, aconst, i32_toAdmin, IntType.width, AddrType.intType] using hs

/-- **`i32.store` past `cap` bytes traps in Core.** -/
theorem run_store_oob (s : Store H) (f : Silmaril.Wasm.Execution.Core.Frame) (rest : List Admin)
    {ls ops : List W} {mem : Nat → W} {cap : Nat} (hM : MemAre s f mem cap) (v x : W)
    (arg : MemArg) (hcap : cap < x.toNat + arg.offset.val + 4) :
    Step Pf host
      ⟨s, localsF f ls, stackA (v :: x :: ops) ++ .plain (.intStore .i32 none ⟨0⟩ arg) :: rest⟩
      ⟨s, localsF f ls, stackA ops ++ .trap :: rest⟩ := by
  obtain ⟨ma, mi, hm, hsz, -⟩ := hM
  have hs := step_ctx (Pf := Pf) (host := host) (ops.reverse.map Val.i32) rest
    (.memory (.storeIntOob (s := s) (f := localsF f ls) (t := .i32) (a := .i32) (i := x)
      (c := v) (arg := arg) hm (by rw [hsz]; exact hcap)))
  rw [stackA_cons2]
  simpa [stackA, aconst, i32_toAdmin, IntType.width, AddrType.intType] using hs

end Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Core
