module

public import Silmaril.Wasm.JcoTool.KCore.Defs
public import Silmaril.Wasm.JcoTool.StreamSem.Thms
public import Silmaril.Wasm.Component.Streams.Kernel.Thms
public import Silmaril.Proofs.Wasm.JcoTool.KCore.Main
public import Silmaril.Proofs.Wasm.JcoTool.KCore.Complete

/-!
# The generated stream modules implement `Proc.tStep`

Proofs in `Silmaril.Proofs.Wasm.JcoTool.KCore.{Kernel,Feed,Sim,Ret,Main,Complete}` (moved out of
`Silmaril/Raw` and restyled to the Isar conventions).

For a byte kernel `k` and a read size `N ≤ 256`, the core module `gen k N` of
`Silmaril.Wasm.JcoTool.KCore`, run by the callback runtime `rstep` over the canonical built-ins of
`Silmaril.Wasm.Component.Async`, is an implementation of the `Proc` transformer `tStep (trV k) N`
in the sense of `StreamSem.Impl` — **the hypothesis of `StreamSem.newWith_stream_semantics`
holds for these modules**:

* `kimpl k N hN : Impl KSt (trV k) N`, with the simulation relation `Rel`: every step of the
  runtime (one callback invocation, with at most one built-in; or a wait for an event followed
  by the callback) is one step of `tStep` with the same effect on the shared store
  (`step_sound`), the machine starts related to `.rd (trV k).init` after the lift's prologue,
  and it exits only where `tStep` finishes.
* `kcore_correct`, `kcore_safe`: in a pipeline `producer → gen k N → consumer` in any
  interleaving, chunking and read sizes, the consumer receives a prefix of, and at the end
  exactly, the kernel's run on the input bytes (`StreamSem.impl_correct`, `impl_safe`).
* `kcore_stream_semantics`: `newWith_stream_semantics` with the implementation discharged.
* **`kimpl_complete`**: conversely, whenever `tStep` steps from a state related to the machine
  and the conditions `Cond` hold (the kernel's bounds for what it is fed or flushes in that step;
  the event a wait takes is well formed and is the completion the module waits for), the
  runtime steps to the same store and a related state: the module does everything `tStep`
  does, with no premature trap.
* For the kernels of the tests: `kcore_inc` (add one), `kcore_noDigit`, `kcore_take`,
  `kcore_lines` (the lines, the final partial one included, each followed by the newline),
  `kcore_rechunk` (uniform chunks after their length bytes).

**What is modelled, not proved**: the fragment's semantics `exec` stands for WebAssembly's
(the printed text `Prog.wat` is checked by `wasm-tools validate` and run under wasmtime in
`tools/wasm-jco/tests/kcore.sh`); the canonical built-ins and the callback runtime follow
`definitions.py` as modelled in `Silmaril.Wasm.Component.Async` (one handle table, items as values,
the runtime delivers only well-formed events, `wellFormed`); the link between the bytes given
to `wasm-jco new` and `gen k N` is that they are `wasm-tools parse` of `Prog.wat`.
-/

@[expose] public section

namespace Silmaril.Wasm.JcoTool.KCore

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Async (Store)
open Silmaril.Wasm.Component.Streams (Tr)
open Silmaril.Wasm.Component.Streams.Proc
open Silmaril.Wasm.Component.Streams.Kernel
open Silmaril.Wasm.JcoTool.StreamSem
open Silmaril.Proofs.Wasm.JcoTool.KCore

/-- The machine after the lift is related to the transformer's initial state. -/
theorem init_rel (k : KM) : Rel (initMS k) (.rd (trV k).init) := by
  refine ⟨⟨rfl, rfl, rfl, by simp [initMS, initG, upd_apply, BLEN, GST, INSR, OUTSW, WS, CAP],
    by simp [initMS, initG, upd_apply, OLEN, GST, INSR, OUTSW, WS, CAP],
    by simp [initMS, initG, upd_apply, OLEN, OOFF, GST, INSR, OUTSW, WS]⟩, rfl,
    by simp [initMS, initG, upd_apply, PC, GST, INSR, OUTSW, WS, pRD], ?_,
    by simp [initMS, initG, upd_apply, OLEN, GST, INSR, OUTSW, WS],
    by simp [initMS, initG, upd_apply, OOFF, GST, INSR, OUTSW, WS]⟩
  have hb : (initMS k).g BLEN = 0 := by simp [initMS, initG, upd_apply, BLEN, GST, INSR, OUTSW, WS]
  simp only [MS.kst, hb, slice_zero]
  simp [initMS, initG, upd_apply, GST, INSR, OUTSW, WS, trV, KM.tr, M32,
    Silmaril.Wasm.Component.Streams.Kernel.M32]

/-- Only the final state of the transformer is related to an exited machine. -/
theorem rel_exited {ms : MS} {t : TPc KSt} (hR : Rel ms t) (h : ms.mode = .exited) : t = .fin := by
  cases t with
  | fin => rfl
  | rd _ => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | wtR _ => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | eoi _ => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | wr _ _ => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | wtW _ _ => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | cl => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h
  | fault => obtain ⟨-, hm, -⟩ := hR; rw [hm] at h; cases h

/-- **The generated module is an implementation of `tStep (trV k) N`.** -/
def kimpl (k : KM) (N : Nat) (hN : N ≤ 256) : Impl KSt (trV k) N where
  M := MS
  step := rstep (gen k N)
  init := initMS k
  done ms := ms.mode == .exited
  R := Rel
  init_R := init_rel k
  step_R := fun hR h => .inl (step_sound hN hR h)
  done_R := fun hR hd => rel_exited hR (by simpa using hd)

/-- The whole output of the value transformer is the kernel's on the bytes. -/
theorem run_trV (k : KM) (xs : List Val) : (trV k).run xs = (k.tr.run (xs.map byteOf)).map u8v := by
  have hi : (trV k).init = k.tr.init := rfl
  simp only [Tr.run, hi, feed_trV, List.map_append]
  rfl

theorem runP_trV (k : KM) (xs : List Val) : (trV k).runP xs = (k.tr.runP (xs.map byteOf)).map u8v := by
  have hi : (trV k).init = k.tr.init := rfl
  simp only [Tr.runP, hi, feed_trV]

/-- **Correctness of the generated module in every pipeline**: when the producer, the module
and the consumer have finished, the consumer holds the kernel's output on the input bytes. -/
theorem kcore_correct (k : KM) (N : Nat) (hN : N ≤ 256) (cs : List (List Val))
    (s : SysM (kimpl k N hN).M) (h : ReachM (kimpl k N hN) cs s) (hp : s.p = .fin)
    (hm : s.m.mode = .exited) (acc : List Val) (hc : s.c = .fin acc) :
    acc = (k.tr.run (cs.flatten.map byteOf)).map u8v := by
  rw [← run_trV]
  exact impl_correct (kimpl k N hN) cs s h hp (by simpa [kimpl] using hm) acc hc

/-- **Safety**: at every point, the consumer holds a prefix of the kernel's output. -/
theorem kcore_safe (k : KM) (N : Nat) (hN : N ≤ 256) (cs : List (List Val))
    (s : SysM (kimpl k N hN).M) (h : ReachM (kimpl k N hN) cs s) (acc : List Val)
    (hc : s.c = .recv acc ∨ s.c = .wait acc ∨ s.c = .close acc ∨ s.c = .fin acc) :
    acc <+: (k.tr.run (cs.flatten.map byteOf)).map u8v := by
  rw [← run_trV]
  exact impl_safe (kimpl k N hN) cs s h acc hc

/-- **The meaning of a `wasm-jco new` output whose module is generated by `gen`**:
`newWith_stream_semantics` with its implementation hypothesis discharged by `kimpl`. -/
theorem kcore_stream_semantics {core : ByteArray} {w : Silmaril.Wasm.Wit.Binary.World} {o : Tool.Out}
    (h : Tool.newWith core w = .ok o) (name : String)
    (hs : ∀ p, New.plan core w = .ok p → xfShape p name = true) (k : KM) (N : Nat) (hN : N ≤ 256) :
    (∃ p c, New.plan core w = .ok p ∧ New.emit p = .ok c ∧ xparse o.bytes = .ok c.norm ∧
      xfShape p name = true) ∧
    ∀ (cs : List (List Val)) (s : SysM (kimpl k N hN).M), ReachM (kimpl k N hN) cs s → s.p = .fin →
      s.m.mode = .exited → ∀ acc, s.c = .fin acc → acc = (k.tr.run (cs.flatten.map byteOf)).map u8v := by
  obtain ⟨⟨p, c, hp, hc, hx, hsh, -⟩, -⟩ := newWith_stream_semantics h name hs
  exact ⟨⟨p, c, hp, hc, hx, hsh⟩, fun cs s hr hpf hm acc hacc => kcore_correct k N hN cs s hr hpf hm acc hacc⟩

/-- **Completeness**: when `tStep` steps from a state related to the machine and the
conditions hold, the generated module, run by the runtime, steps to the same store and a related
state. -/
theorem kimpl_complete (k : KM) (N : Nat) (hN : N ≤ 256) {st st' : Store} {ms : MS}
    {t t' : TPc KSt} (hR : Rel ms t) (hcd : Cond k N st t) (ht : tStep (trV k) N st t = some (st', t')) :
    ∃ ms', (kimpl k N hN).step st ms = some (st', ms') ∧ Rel ms' t' :=
  Silmaril.Proofs.Wasm.JcoTool.KCore.step_complete hN hR hcd ht

/-! ## The kernels of the tests -/

theorem byteOf_lt (v : Val) : byteOf v < 256 := by
  unfold byteOf
  split
  · exact BitVec.isLt _
  · decide

theorem bytes_byteOf (xs : List Val) : Bytes (xs.map byteOf) := by
  intro b hb
  obtain ⟨v, -, rfl⟩ := List.mem_map.mp hb
  exact byteOf_lt v

/-- `map`: every byte plus one. -/
theorem kcore_inc (N : Nat) (hN : N ≤ 256) (cs : List (List Val)) (s : SysM (kimpl kInc N hN).M)
    (h : ReachM (kimpl kInc N hN) cs s) (hp : s.p = .fin) (hm : s.m.mode = .exited)
    (acc : List Val) (hc : s.c = .fin acc) :
    acc = (cs.flatten.map byteOf |>.map fun b => (b + 1) % 256).map u8v := by
  rw [kcore_correct kInc N hN cs s h hp hm acc hc, kInc_run _ (bytes_byteOf _)]

/-- `filter`: the ASCII digits dropped. -/
theorem kcore_noDigit (N : Nat) (hN : N ≤ 256) (cs : List (List Val)) (s : SysM (kimpl kNoDigit N hN).M)
    (h : ReachM (kimpl kNoDigit N hN) cs s) (hp : s.p = .fin) (hm : s.m.mode = .exited)
    (acc : List Val) (hc : s.c = .fin acc) :
    acc = (cs.flatten.map byteOf |>.filter fun b => !(48 ≤ b && b < 58)).map u8v := by
  rw [kcore_correct kNoDigit N hN cs s h hp hm acc hc, kNoDigit_run _ (bytes_byteOf _)]

/-- `take n`: the first `n` bytes. -/
theorem kcore_take (n : Nat) (hn : n < Silmaril.Wasm.Component.Streams.Kernel.M32) (N : Nat) (hN : N ≤ 256)
    (cs : List (List Val)) (s : SysM (kimpl (kTake n) N hN).M) (h : ReachM (kimpl (kTake n) N hN) cs s)
    (hp : s.p = .fin) (hm : s.m.mode = .exited) (acc : List Val) (hc : s.c = .fin acc) :
    acc = ((cs.flatten.map byteOf).take n).map u8v := by
  rw [kcore_correct (kTake n) N hN cs s h hp hm acc hc, kTake_run n hn _ (bytes_byteOf _)]

/-- `lines`: the lines (the final partial one included), each followed by the newline. -/
theorem kcore_lines (nl : Nat) (hnl : nl < 256) (N : Nat) (hN : N ≤ 256) (cs : List (List Val))
    (s : SysM (kimpl (kLines nl) N hN).M) (h : ReachM (kimpl (kLines nl) N hN) cs s)
    (hp : s.p = .fin) (hm : s.m.mode = .exited) (acc : List Val) (hc : s.c = .fin acc) :
    acc = ((Silmaril.Wasm.Component.Streams.lines (· == nl) (cs.flatten.map byteOf)).flatMap
      (· ++ [nl])).map u8v := by
  rw [kcore_correct (kLines nl) N hN cs s h hp hm acc hc, kLines_run nl hnl _ (bytes_byteOf _)]

/-- `rechunk n`: uniform chunks of `n` bytes, each after its length byte. -/
theorem kcore_rechunk (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) (N : Nat) (hN : N ≤ 256)
    (cs : List (List Val)) (s : SysM (kimpl (kRechunk n) N hN).M)
    (h : ReachM (kimpl (kRechunk n) N hN) cs s) (hp : s.p = .fin) (hm : s.m.mode = .exited)
    (acc : List Val) (hc : s.c = .fin acc) :
    acc = ((Silmaril.Wasm.Component.Streams.chunksOf n (cs.flatten.map byteOf)).flatMap
      (fun c => c.length :: c)).map u8v := by
  rw [kcore_correct (kRechunk n) N hN cs s h hp hm acc hc, kRechunk_run n h1 h2 _ (bytes_byteOf _)]

end Silmaril.Wasm.JcoTool.KCore
