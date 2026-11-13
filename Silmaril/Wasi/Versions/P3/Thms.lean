module

public import Silmaril.Wasi.Versions.P3.Defs
public import Silmaril.Wasi.Versions.P3.Wit.Thms
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Wasi.Os.Thms
public import Silmaril.Wasi.Runtime.Thms
public import Silmaril.Wasm.Component.Async.Thms

@[expose] public section

/-!
# WASI 0.3: theorems

PROVED (standard axioms), for the slice of `Silmaril.Wasi.Versions.P3`:

* **The concrete host is a typed model** (`host3_ok`, `host3_typed`): every answer of
  `host3 F` has its WIT type, so `host3 F` satisfies `typed3` (`hostSat`), for every `F`. The
  loose hosts `loose typed3`, `loose clockTh3`, `loose stdoutTh3`, `loose (fsReadTh3 F)` are
  models of their theories by `Silmaril.Wasi.loose_sat`.
* **`hello3`** (`hello3Run_mem`, `hello3Run_follows`, `hello3Run_typed`, `hello3Run_stdout`):
  `hello3Run` is a play of `hello3`; its answers follow `host3 F` and are accepted by `typed3`
  and by the loose `stdoutTh3`.
* **The OS image** (`hello3Run_os`): the OS image of `hello3Run` is the write of `hi`, the same
  as that of WASI 0.2's `helloRun` (`hello3_os_eq_p2`). Hence the 42-byte x86 runtime of
  `Silmaril.Wasi.Runtime` is LPS process-safe for the OS image of `hello3`'s run as well
  (`hello3Img_psafe8`), through `Silmaril.Machine.Process.IoSpec`.
* **Refutations of the theory's laxness** (`stdout_early_ok_rejected`,
  `stdout_overcount_rejected`): the stdout theory rejects a future `ok` before the writable end is
  dropped, and a write reporting more bytes than offered.
* **REFUTED: `hello3` is not correct over every loose host** (`hello3_not_loose_correct`): a
  model of `typed3` and `stdoutTh3` may complete the write of `hi` with one byte; `hello3`
  ignores the count and `run` returns `ok` with only `h` on stdout. Its correctness holds for the
  concrete host only (`hello3Run_os`).
* **The concrete host is the async machine's behaviour** (`stdout3_write_machine`,
  `stdout3_future_machine`): if the host keeps a read of at least `|xs|` items pending on the
  readable end (as a stdout reader does), the component's `stream.write w xs` completes with
  `packCopy .completed |xs|` in `Silmaril.Wasm.Component.Async`, which is `stdout3Impl`'s answer;
  and a host writing its future while the component waits delivers it to the component's
  `future-read` event.
* **Clocks** (`clockRun_ok`, `clockRun_bad`): a run `now = 1`, `wait-for 5`, `now = 7` is
  accepted by `clockTh3` and follows `host3`; `now = 10`, `wait-for 5`, `now = 12` is rejected.
* **`read-via-stream`** (`readRun_follows`, `readRun_ok`): on a file containing `hello`,
  `read-via-stream(0, 1)`, `stream.read(r, 2)`, `stream.read(r, 10)`, `stream.read(r, 10)`
  delivers `el`, `lo`, then `DROPPED 0`; the run follows `host3` and is accepted by
  `fsReadTh3`.

A Silmaril addition.
-/

namespace Silmaril.Wasi.Versions.P3

open Silmaril.Games
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasi.Os (hiOut osTrace helloRun follows_snoc follows_nil bytesOf_bytesV)
open Silmaril.Wasi.Examples (hiBytes)
open Silmaril.Wasm.Component.Async (packCopy CopyResult)

/-! ## The concrete host is typed -/

/-- The functions `host3` answers. -/
def served3 : List FnName :=
  [readVia3, cStreamRead, now3, waitFor3, cStreamDropR, cFutureDropR, cJoin, cWsNew, cWait,
   stdinRead3, getDirs3, openAt3, cStreamNew, stdoutWrite3, cStreamWrite, cStreamDropW, cFutureRead]

/-- **Every answer of `host3 F` is well typed.** -/
theorem host3_ok (F : BitVec 32 → List (BitVec 8)) (p : List WEv) (f : FnName) (a : List Val) :
    ok3 (.imp f a (host3 F p f a)) = true := by
  rw [ok3_eq_hand]
  by_cases hk : f ∈ served3
  · simp only [served3, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> rfl
  · simp only [served3, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hk
    simp only [ok3H, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10, h11, h12, h13, h14, h15, h16, h17, or_self, ↓reduceIte]

/-- **`host3 F` is a model of the typing theory.** -/
theorem host3_typed {Y : Sig.{0}} {I : Set FnName} (F : BitVec 32 → List (BitVec 8)) :
    (hostSat typed3.Accepts).holds (concrete (Y := Y) (I := I) (host3 F)) :=
  concrete_sat _ fun _ ht => follows_pointwise (host3_ok F) (fun e he => by
    cases e <;> first | rfl | exact absurd he (by simp [WEv.isImp])) ht

/-! ## `hello3` -/

/-- **`hello3Run` is a play of `hello3`.** -/
theorem hello3Run_mem : hello3Run ∈ ofBody hello3 := by
  have h1 := (Reach.nil (h := hello3)).snoc (CStep.ask run3Q)
  have h2 := h1.snoc (CStep.call run3Q newOp h3K1)
  have h3 := h2.snoc (CStep.reply run3Q newOp h3K1 (some [natV 1, natV 2]))
  have h4 := h3.snoc (CStep.call (h := hello3) run3Q (wvsOp (natV 1)) (h3K2 (natV 2)))
  have h5 := h4.snoc (CStep.reply run3Q (wvsOp (natV 1)) (h3K2 (natV 2)) (some [natV 3]))
  have h6 := h5.snoc (CStep.call (h := hello3) run3Q (swOp (natV 2)) (h3K3 (natV 2) (natV 3)))
  have h7 := h6.snoc (CStep.reply run3Q (swOp (natV 2)) (h3K3 (natV 2) (natV 3))
    (some [natV (packCopy .completed 2)]))
  have h8 := h7.snoc (CStep.call (h := hello3) run3Q (dwOp (natV 2)) (h3K4 (natV 3)))
  have h9 := h8.snoc (CStep.reply run3Q (dwOp (natV 2)) (h3K4 (natV 3)) (some []))
  have h10 := h9.snoc (CStep.call (h := hello3) run3Q (frOp (natV 3)) h3K5)
  have h11 := h10.snoc (CStep.reply run3Q (frOp (natV 3)) h3K5 (some [natV 0, okV none]))
  exact ⟨_, h11.snoc (CStep.ret (h := hello3) run3Q (some [okV none]))⟩

/-- **The answers of `hello3Run` follow the concrete host `host3 F`.** -/
theorem hello3Run_follows (F : BitVec 32 → List (BitVec 8)) :
    Follows (host3 F) (hostView (wtrace hello3Run)) := by
  have h1 := follows_snoc (follows_nil (host3 F)) (f := cStreamNew) (a := [])
    (r := some [natV 1, natV 2]) rfl
  have h2 := follows_snoc h1 (f := stdoutWrite3) (a := [natV 1]) (r := some [natV 3]) rfl
  have h3 := follows_snoc h2 (f := cStreamWrite) (a := [natV 2, bytesV hiBytes])
    (r := some [natV (packCopy .completed 2)]) rfl
  have h4 := follows_snoc h3 (f := cStreamDropW) (a := [natV 2]) (r := some []) rfl
  exact follows_snoc h4 (f := cFutureRead) (a := [natV 3]) (r := some [natV 0, okV none]) rfl

/-- The host view of `hello3Run`. -/
theorem hello3Run_hostView : hostView (wtrace hello3Run) =
    [.imp cStreamNew [] (some [natV 1, natV 2]), .imp stdoutWrite3 [natV 1] (some [natV 3]),
     .imp cStreamWrite [natV 2, bytesV hiBytes] (some [natV (packCopy .completed 2)]),
     .imp cStreamDropW [natV 2] (some []), .imp cFutureRead [natV 3] (some [natV 0, okV none])] :=
  rfl

/-- **`hello3Run`'s answers are well typed.** -/
theorem hello3Run_typed : typed3.Accepts (hostView (wtrace hello3Run)) :=
  follows_pointwise (host3_ok (fun _ => [])) (fun e he => by
    cases e <;> first | rfl | exact absurd he (by simp [WEv.isImp])) (hello3Run_follows _)

/-- **`hello3Run`'s answers are accepted by the loose stdout theory** (the future reports `ok`
after the writable end was dropped). -/
theorem hello3Run_stdout : stdoutTh3.Accepts (hostView (wtrace hello3Run)) := by
  rw [hello3Run_hostView]
  rfl

/-- **The stdout theory rejects an early `ok`**: a future reporting `ok` before the writable
end of its stream is dropped (data may still be pending) is not accepted. -/
theorem stdout_early_ok_rejected : ¬ stdoutTh3.Accepts
    [.imp cStreamNew [] (some [natV 1, natV 2]), .imp stdoutWrite3 [natV 1] (some [natV 3]),
     .imp cFutureRead [natV 3] (some [natV 0, okV none])] := by
  unfold Protocol.Accepts
  exact Bool.false_ne_true

/-- **The stdout theory rejects an over-reported write**: `COMPLETED 3` for two bytes. -/
theorem stdout_overcount_rejected : ¬ stdoutTh3.Accepts
    [.imp cStreamWrite [natV 2, bytesV hiBytes] (some [natV (packCopy .completed 3)])] := by
  unfold Protocol.Accepts
  exact Bool.false_ne_true

/-! ## The OS image -/

/-- **The OS image of `hello3Run` is the write of `hi`.** -/
theorem hello3Run_os (ch : Silmaril.Process.LPS.Word) :
    osTrace3 ch (wtrace hello3Run) = hiOut ch := by
  rfl

/-- **WASI 0.3's `hello3` and WASI 0.2's `hello` have the same OS image** on their runs against
the concrete hosts. -/
theorem hello3_os_eq_p2 (ch : Silmaril.Process.LPS.Word) :
    osTrace3 ch (wtrace hello3Run) = osTrace ch (wtrace helloRun) := by
  rw [hello3Run_os, Silmaril.Wasi.Os.helloRun_os]

open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Machine.Process.LpsBridge
  Silmaril.Machine.Process.IoSpec in
/-- **The x86 runtime of `hello` also runs `hello3`**: on the bridge's release machine, an LPS
configuration aligned with `helloStart` is process-safe for "a prefix of the OS image of
`hello3`'s WASI 0.3 run against `host3`, then `exit 0`". -/
theorem hello3Img_psafe8 {oracle : Oracle} {refused : RefusalFilter} {segs : List Segment}
    {ch : Word} {cfg : Config (machine oracle)} (al : Aligned cfg Silmaril.Wasi.Runtime.helloStart)
    (hfd : fdLookup cfg.model.fds 1 = some (.channel ch)) (hch : wIs0 ch = false) :
    PSafe segs refused
      (fun tr => tr <+: osTrace3 ch (wtrace hello3Run) ++ [.exitEv 0 cfg.model.fs]) cfg := by
  rw [hello3_os_eq_p2]
  exact Silmaril.Wasi.Runtime.helloImg_psafe8 al hfd hch

/-! ## A partial write: `hello3` is not correct for every loose host -/

/-- The run of `hello3` where the host accepts only one byte of `hi`. -/
def hello3Partial : List (Move (nsig p3World.imports) (nsig p3World.exports)) :=
  [.inr (.ask run3Q),
   .inl (.ask newOp), .inl (.ans newOp (some [natV 1, natV 2])),
   .inl (.ask (wvsOp (natV 1))), .inl (.ans (wvsOp (natV 1)) (some [natV 3])),
   .inl (.ask (swOp (natV 2))), .inl (.ans (swOp (natV 2)) (some [natV (packCopy .completed 1)])),
   .inl (.ask (dwOp (natV 2))), .inl (.ans (dwOp (natV 2)) (some [])),
   .inl (.ask (frOp (natV 3))), .inl (.ans (frOp (natV 3)) (some [natV 0, okV none])),
   .inr (.ans run3Q (some [okV none]))]

theorem hello3Partial_mem : hello3Partial ∈ ofBody hello3 := by
  have h1 := (Reach.nil (h := hello3)).snoc (CStep.ask run3Q)
  have h2 := h1.snoc (CStep.call run3Q newOp h3K1)
  have h3 := h2.snoc (CStep.reply run3Q newOp h3K1 (some [natV 1, natV 2]))
  have h4 := h3.snoc (CStep.call (h := hello3) run3Q (wvsOp (natV 1)) (h3K2 (natV 2)))
  have h5 := h4.snoc (CStep.reply run3Q (wvsOp (natV 1)) (h3K2 (natV 2)) (some [natV 3]))
  have h6 := h5.snoc (CStep.call (h := hello3) run3Q (swOp (natV 2)) (h3K3 (natV 2) (natV 3)))
  have h7 := h6.snoc (CStep.reply run3Q (swOp (natV 2)) (h3K3 (natV 2) (natV 3))
    (some [natV (packCopy .completed 1)]))
  have h8 := h7.snoc (CStep.call (h := hello3) run3Q (dwOp (natV 2)) (h3K4 (natV 3)))
  have h9 := h8.snoc (CStep.reply run3Q (dwOp (natV 2)) (h3K4 (natV 3)) (some []))
  have h10 := h9.snoc (CStep.call (h := hello3) run3Q (frOp (natV 3)) h3K5)
  have h11 := h10.snoc (CStep.reply run3Q (frOp (natV 3)) h3K5 (some [natV 0, okV none]))
  exact ⟨_, h11.snoc (CStep.ret (h := hello3) run3Q (some [okV none]))⟩

/-- **Refutation: `hello3` does not write `hi` over every loose stdout host.** A host model of
`typed3` and `stdoutTh3` may complete the write of `hi` with one byte (WASI 0.3 streams copy
partially); `hello3` ignores the count, drops the stream, and `run` returns `ok` with only `h`
on stdout. A correct component must re-write the rest (open: a looping `hello3`). -/
theorem hello3_not_loose_correct (ch : Silmaril.Process.LPS.Word) :
    ∃ s ∈ ofBody hello3, typed3.Accepts (hostView (wtrace s)) ∧
      stdoutTh3.Accepts (hostView (wtrace s)) ∧
      (wtrace s).getLast? = some (.ret run3 [] (some [okV none])) ∧
      osTrace3 ch (wtrace s) ≠ hiOut ch := by
  refine ⟨hello3Partial, hello3Partial_mem, rfl, rfl, rfl, fun h => ?_⟩
  have h1 : (osTrace3 ch (wtrace hello3Partial)).length = 1 := rfl
  have h2 : (hiOut ch).length = 2 := rfl
  rw [h, h2] at h1
  exact absurd h1 (by decide)

/-! ## The concrete host is the async machine's behaviour -/

open Silmaril.Wasm.Component.Async in
/-- **A stdout reader with a large enough pending read makes every write complete in full**:
`stdout3Impl`'s answer `packCopy .completed |xs|` is the async machine's. -/
theorem stdout3_write_machine {st : Store} {r w s n : Nat} {xs : List Val}
    (hw : st.tbl w = some (.streamW s)) (hr : st.tbl r = some (.streamR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).wDropped = false) (hn : xs.length ≤ n) :
    ∃ st₁ st₂, step st (.streamRead r n) = some (st₁, .nat blocked) ∧
      step st₁ (.streamWrite w xs) = some (st₂, .nat (packCopy .completed xs.length)) ∧
      (st₂.chans s).sent = (st.chans s).sent ++ xs := by
  obtain ⟨st₁, st₂, h1, h2, h3, -⟩ := read_write (n := n) (xs := xs) hw hr hp hd
  rw [Nat.min_eq_right hn] at h2
  rw [List.take_of_length_le hn] at h3
  exact ⟨st₁, st₂, h1, h2, h3⟩

open Silmaril.Wasm.Component.Async in
/-- **The future of `write-via-stream`**: a component waiting on the future receives the host's
value through its `future-read` event. -/
theorem stdout3_future_machine {st : Store} {r w s : Nat} {v : Val}
    (hw : st.tbl w = some (.futureW s)) (hr : st.tbl r = some (.futureR s))
    (hp : (st.chans s).pend = .idle) (hd : (st.chans s).done = false) :
    ∃ st₁ st₂, step st (.futureRead r) = some (st₁, .nat blocked) ∧
      step st₁ (.futureWrite w v) = some (st₂, .nat CopyResult.completed.toNat) ∧
      st₂.ev r = some ⟨.futureRead, r, CopyResult.completed.toNat, [v]⟩ := by
  obtain ⟨st₁, st₂, h1, h2, -, h4⟩ := future_read_write (v := v) hw hr hp hd
  exact ⟨st₁, st₂, h1, h2, h4⟩

/-! ## Clocks -/

/-- `now = 0`, `wait-for 5`, `now = 6`. -/
def clockRun : List WEv :=
  [.imp now3 [] (some [.u64 0]), .imp waitFor3 [.u64 5] (some []), .imp now3 [] (some [.u64 6])]

/-- **The run is accepted by the clock theory** and follows `host3`. -/
theorem clockRun_ok (F : BitVec 32 → List (BitVec 8)) :
    clockTh3.Accepts clockRun ∧ Follows (host3 F) clockRun := by
  refine ⟨rfl, ?_⟩
  have h1 := follows_snoc (follows_nil (host3 F)) (f := now3) (a := []) (r := some [.u64 0]) rfl
  have h2 := follows_snoc h1 (f := waitFor3) (a := [.u64 5]) (r := some []) rfl
  exact follows_snoc h2 (f := now3) (a := []) (r := some [.u64 6]) rfl

/-- **A clock going back after a wait is rejected**: `now = 10`, `wait-for 5`, `now = 12`. -/
theorem clockRun_bad : ¬ clockTh3.Accepts
    [.imp now3 [] (some [.u64 10]), .imp waitFor3 [.u64 5] (some []), .imp now3 [] (some [.u64 12])] := by
  unfold Protocol.Accepts
  exact Bool.false_ne_true

/-! ## `read-via-stream` -/

/-- A file containing `hello` behind every descriptor. -/
def helloFile : BitVec 32 → List (BitVec 8) := fun _ => [0x68, 0x65, 0x6c, 0x6c, 0x6f]

/-- `read-via-stream(0, 1)`, then reads of `2`, `10` and `10` bytes. -/
def readRun : List WEv :=
  [.imp readVia3 [.u32 0, .u64 1] (some [.record [natV 1, natV 2]]),
   .imp cStreamRead [natV 1, natV 2] (some [natV (packCopy .completed 2), bytesV [0x65, 0x6c]]),
   .imp cStreamRead [natV 1, natV 10] (some [natV (packCopy .completed 2), bytesV [0x6c, 0x6f]]),
   .imp cStreamRead [natV 1, natV 10] (some [natV (packCopy .dropped 0), bytesV []])]

/-- **The read run is accepted by the read theory over `helloFile`.** -/
theorem readRun_ok : (fsReadTh3 helloFile).Accepts readRun := by
  rfl

/-- **The read run follows the concrete host over `helloFile`.** -/
theorem readRun_follows : Follows (host3 helloFile) readRun := by
  have h1 := follows_snoc (follows_nil (host3 helloFile)) (f := readVia3) (a := [.u32 0, .u64 1])
    (r := some [.record [natV 1, natV 2]]) rfl
  have h2 := follows_snoc h1 (f := cStreamRead) (a := [natV 1, natV 2])
    (r := some [natV (packCopy .completed 2), bytesV [0x65, 0x6c]]) rfl
  have h3 := follows_snoc h2 (f := cStreamRead) (a := [natV 1, natV 10])
    (r := some [natV (packCopy .completed 2), bytesV [0x6c, 0x6f]]) rfl
  exact follows_snoc h3 (f := cStreamRead) (a := [natV 1, natV 10])
    (r := some [natV (packCopy .dropped 0), bytesV []]) rfl

end Silmaril.Wasi.Versions.P3
