module

public import Silmaril.Wasm.Component.Streams.Callback.Defs
public import Silmaril.Wasm.Component.Streams.Kernel.Thms
public import Silmaril.Proofs.Wasm.Component.Streams.Callback.Main

/-!
# The generated driver loop refines the node program

Proofs in `Silmaril.Proofs.Wasm.Component.Streams.Callback.{Inv,Abs,Sim,Main}`.

`CB` (`Callback.Defs`) transcribes the callback-ABI driver loop that `Kernel.KM.coreWat` emits.
**`creach_abs`**: in a pipe `source → module → sink`, every reachable system stands, through the
refinement map `CSys.abs` (built from `CB.abs`), for a reachable system of `Pipes.pipe xs T`, the
pipe whose transformer is the generic node program of `Net`: every step of the module is a step of
that node (`cb_sim`: a `stream.read`, `stream.write`, drop or event delivery), or a pass of
`$pump` that changes neither the store nor the abstract state. The local invariant `CB.Inv` holds
throughout. So the theorems of `Pipes` hold for the module:

* **`cb_pipe_correct`**: once the sink has dropped its input it holds `T.run xs`; `cb_pipe_safe`:
  at every point, a prefix of it. Every interleaving, `batch > 0`, every `wmax`.
* For kernels (`KM.trV`, bytes as `u8` values): **`cb_kernel_correct`** (the sink holds the kernel's
  `KM.tr` run on the input bytes) and the instances `cb_lines_correct`, `cb_rechunk_correct`,
  `cb_take_correct`.

What is not covered: the WebAssembly text itself (the transcription is by reading the generated
code, and is tested by the wasmtime suites), the compilation of the kernel's statements
(`KStmt.wat`, here `T` is abstract), the tee template (`teeWat`), and liveness of the module (the
refinement transfers safety and correctness at the end).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Streams.Callback

open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Component.Streams
open Silmaril.Wasm.Component.Streams.Net
open Silmaril.Wasm.Component.Streams.Kernel
open Silmaril.Proofs.Wasm.Component.Streams.Callback

variable {σ : Type}

/-- **The refinement**: reachable systems with the module stand for reachable systems of the
pipe, and the module's invariant holds. -/
theorem creach_abs {xs : List Val} {T : Tr σ Val Val} {batch wmax : Nat} (hb : 0 < batch)
    {c : CSys σ} (h : CReach xs T batch wmax c) :
    Reach (Pipes.pipe xs T) (CSys.abs xs T c) ∧ c.cb.Inv T :=
  Silmaril.Proofs.Wasm.Component.Streams.Callback.creach_abs hb h

/-- **Correctness of the generated driver loop**: once the sink has dropped its input, it holds
`T.run xs`. -/
theorem cb_pipe_correct {xs : List Val} {T : Tr σ Val Val} {batch wmax : Nat} (hb : 0 < batch)
    {c : CSys σ} (h : CReach xs T batch wmax c) {b : Bool} (hC : c.snk.rd = .gone b) :
    c.snk.got = T.run xs :=
  Pipes.pipe_correct xs T (creach_abs hb h).1 hC

/-- **Safety**: at every point the sink holds a prefix of `T.run xs`. -/
theorem cb_pipe_safe {xs : List Val} {T : Tr σ Val Val} {batch wmax : Nat} (hb : 0 < batch)
    {c : CSys σ} (h : CReach xs T batch wmax c) : c.snk.got <+: T.run xs :=
  Pipes.pipe_safe xs T (creach_abs hb h).1

/-! ## Kernels on bytes -/

/-- A byte as a component value. -/
def u8v (n : Nat) : Val := .u8 (BitVec.ofNat 8 n)

/-- The byte of a component value (`0` for a value that is not a `u8`). -/
def byteOf : Val → Nat
  | .u8 x => x.toNat
  | _ => 0

/-- **A kernel on component values**: bytes travel as `u8` values. -/
def _root_.Silmaril.Wasm.Component.Streams.Kernel.KM.trV (k : KM) : Tr KSt Val Val where
  init := k.tr.init
  step s v := ((k.tr.step s (byteOf v)).1, (k.tr.step s (byteOf v)).2.map u8v)
  flush s := (k.tr.flush s).map u8v
  done := k.tr.done

theorem byteOf_u8v (n : Nat) : byteOf (u8v n) = n % 256 := by
  simp [byteOf, u8v, BitVec.toNat_ofNat]

theorem trV_step (k : KM) (s : KSt) (v : Val) :
    k.trV.step s v = ((k.tr.step s (byteOf v)).1, (k.tr.step s (byteOf v)).2.map u8v) := rfl

theorem trV_feed (k : KM) (s : KSt) (bs : List Nat) :
    k.trV.feed s (bs.map u8v) =
      ((k.tr.feed s (bs.map (· % 256))).1, (k.tr.feed s (bs.map (· % 256))).2.map u8v) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, Tr.feed]
    show (if k.tr.done s then _ else _) = _
    split
    · rfl
    · simp only [trV_step, byteOf_u8v, ih, List.map_append]

theorem trV_run (k : KM) (bs : List Nat) :
    k.trV.run (bs.map u8v) = (k.tr.run (bs.map (· % 256))).map u8v := by
  simp only [Tr.run, trV_feed, List.map_append]
  rfl

theorem bytes_mod {bs : List Nat} (hb : Bytes bs) : bs.map (· % 256) = bs := by
  conv => rhs; rw [← List.map_id bs]
  exact List.map_congr_left fun b h => Nat.mod_eq_of_lt (hb b h)

/-- **The generated module running a kernel**: once the sink has dropped its input it holds the
kernel's output on the input bytes. -/
theorem cb_kernel_correct (k : KM) {bs : List Nat} (hbs : Bytes bs) {batch wmax : Nat}
    (hb : 0 < batch) {c : CSys KSt} (h : CReach (bs.map u8v) k.trV batch wmax c) {b : Bool}
    (hC : c.snk.rd = .gone b) : c.snk.got = (k.tr.run bs).map u8v := by
  rw [cb_pipe_correct hb h hC, trV_run, bytes_mod hbs]

/-- The lines component: the lines of the input, each followed by `nl`. -/
theorem cb_lines_correct (nl : Nat) (hnl : nl < 256) {bs : List Nat} (hbs : Bytes bs)
    {batch wmax : Nat} (hb : 0 < batch) {c : CSys KSt}
    (h : CReach (bs.map u8v) (kLines nl).trV batch wmax c) {b : Bool} (hC : c.snk.rd = .gone b) :
    c.snk.got = ((lines (· == nl) bs).flatMap (· ++ [nl])).map u8v := by
  rw [cb_kernel_correct _ hbs hb h hC, kLines_run nl hnl bs hbs]

/-- The uniform rechunker: chunks of `n` bytes, each after its length. -/
theorem cb_rechunk_correct (n : Nat) (h1 : 0 < n) (h2 : n ≤ 255) {bs : List Nat} (hbs : Bytes bs)
    {batch wmax : Nat} (hb : 0 < batch) {c : CSys KSt}
    (h : CReach (bs.map u8v) (kRechunk n).trV batch wmax c) {b : Bool} (hC : c.snk.rd = .gone b) :
    c.snk.got = ((chunksOf n bs).flatMap (fun c => c.length :: c)).map u8v := by
  rw [cb_kernel_correct _ hbs hb h hC, kRechunk_run n h1 h2 bs hbs]

/-- `take n`: the first `n` bytes; the module stops reading after them. -/
theorem cb_take_correct (n : Nat) (hn : n < M32) {bs : List Nat} (hbs : Bytes bs)
    {batch wmax : Nat} (hb : 0 < batch) {c : CSys KSt}
    (h : CReach (bs.map u8v) (kTake n).trV batch wmax c) {b : Bool} (hC : c.snk.rd = .gone b) :
    c.snk.got = (bs.take n).map u8v := by
  rw [cb_kernel_correct _ hbs hb h hC, kTake_run n hn bs hbs]

end Silmaril.Wasm.Component.Streams.Callback
