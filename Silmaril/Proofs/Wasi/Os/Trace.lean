module

public import Silmaril.Proofs.Wasi.Os.Write
public import Silmaril.Wasi.Comp.Thms
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Wasi.Host.Thms

/-!
# Proofs: the OS image of the WASI runs of `hello` and `writeFile`

* `bytesOf_bytesV`, `osTrace_hostView` (only the host's answers have an OS image),
  `osTrace_replicate` (if every answered write carries `bs`, the OS trace is copies of `bs`).
* **`hello_writesHi`**: with no assumption on the host, every write of `hello` carries `hi`
  (`agP topP (pointwise (writesOnly hiBytes))`, by the invariant method).
* **`hello_os`**: the OS image of every play of `hello` is `k` copies of `hiOut ch`.
  **`hello_link_os`**: the same for the answers of every host linked below `hello`.
* `follows_snoc`, **`helloRun_mem`**, **`helloRun_follows`**, **`helloRun_os`**: `helloRun` is a
  play of `hello` whose answers follow the concrete host `stdoutImpl`, and its OS image is
  exactly `hiOut ch`.
* **`hello_e2e`**: an x86 runtime of `hello` is `IoSafeN` with `lpsEnv` for the traces "a
  prefix of the OS image of `helloRun`, then `exit 0`".
* The filesystem slice: `lookup_set_self`, **`wfRun_mem`**, **`wfRun_follows`** (the run of
  `writeFile` against `fsImpl`) and **`wfRun_fs`**: replayed on any LPS file system without
  `out.txt`, it leaves `out.txt` containing `hi`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Os

open Silmaril.Games Silmaril.Wasi Silmaril.Wasi.Examples
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Process.LPS (Event Word Byte)
open Silmaril.Process.LPS
open Silmaril.Machine.Process.IoSpec (IoSafeN lpsEnv)

/-! ## The OS image of events -/

/-- The bytes of an encoded byte list. -/
theorem bytesOf_bytesV (bs : List (BitVec 8)) : bytesOf (bytesV bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [bytesOf, bytesV, List.map_cons, List.filterMap_cons] at ih ⊢
    rw [ih]

/-- Only the host's answers have an OS image. -/
theorem osTrace_hostView (ch : Word) (t : List WEv) : osTrace ch (hostView t) = osTrace ch t := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | imp f a r =>
      simp only [hostView, osTrace, List.filter_cons, WEv.isImp, ite_true, List.flatMap_cons]
        at ih ⊢
      rw [ih]
    | req f a => exact ih
    | call f a => exact ih
    | ret f a r => exact ih

/-- An event allowed by `writesOnly bs` writes nothing or `bs`. -/
theorem osEv_cases {ch : Word} {bs : List Byte} {e : WEv} (h : writesOnly bs e = true) :
    osEv ch e = [] ∨ osEv ch e = bs.map (.writeEv ch) := by
  unfold osEv
  split
  · rename_i f x buf xs
    by_cases hf : f = streamWrite
    · right
      have hb : bytesOf buf = bs := by simpa [writesOnly, hf] using h
      simp only [hf, ↓reduceIte, hb]
    · left
      simp [hf]
  · left
    rfl

/-- **If every answered write carries `bs`, the OS image is copies of `bs`.** -/
theorem osTrace_replicate (ch : Word) (bs : List Byte) :
    ∀ t : List WEv, (∀ e ∈ t, writesOnly bs e = true) →
      ∃ k, osTrace ch t = (List.replicate k (bs.map (.writeEv ch))).flatten
  | [], _ => ⟨0, rfl⟩
  | e :: t, h => by
    obtain ⟨k, hk⟩ := osTrace_replicate ch bs t fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have ht : osTrace ch (e :: t) = osEv ch e ++ osTrace ch t := List.flatMap_cons
    rcases osEv_cases (ch := ch) (h e List.mem_cons_self) with he | he
    · exact ⟨k, by rw [ht, he, hk, List.nil_append]⟩
    · exact ⟨k + 1, by rw [ht, he, hk, List.replicate_succ, List.flatten_cons]⟩

/-! ## `hello` writes only `hi` -/

/-- The reachable control states of `hello`. -/
def HelloSt (c : CSt stdoutWorld.imports stdoutWorld.exports) (_ _ : Unit) : Prop :=
  c = .idle ∨ (∃ q, c = .run q helloProg) ∨ (∃ q, c = .wait q getOp helloK1) ∨
    (∃ q r, c = .run q (.pure r)) ∨ (∃ q hd, c = .run q (.call (writeOp hd) (helloK2 hd))) ∨
    (∃ q hd, c = .wait q (writeOp hd) (helloK2 hd)) ∨
    (∃ q hd, c = .run q (.call (dropOp hd) helloK3)) ∨ (∃ q hd, c = .wait q (dropOp hd) helloK3)

/-- After `get-stdout`, `hello` writes or returns. -/
theorem helloK1_cases' (n : Option (List Val)) :
    (∃ hd, helloK1 n = .call (writeOp hd) (helloK2 hd)) ∨ ∃ r, helloK1 n = .pure r := by
  unfold helloK1
  split
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩

/-- A pointwise guarantee accepts an allowed event. -/
theorem pointwise_step {ok : WEv → Bool} {e : WEv} (h : ok e = true) :
    (pointwise ok).step () e = some () := by
  simp [pointwise, h]

/-- The conclusion of one step of `hello`. -/
abbrev HStep (o : Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports))
    (c' : CSt stdoutWorld.imports stdoutWorld.exports) : Prop :=
  ∃ qG', (pointwise (writesOnly hiBytes)).step () (wev o) = some qG' ∧ HelloSt c' () qG'

theorem hello_got {q o c'} (hc : CStep hello (.wait q getOp helloK1) o c') : HStep o c' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  refine ⟨(), pointwise_step rfl, ?_⟩
  rcases helloK1_cases' n with ⟨hd, hk⟩ | ⟨r, hk⟩
  · exact .inr (.inr (.inr (.inr (.inl ⟨q, hd, hk ▸ rfl⟩))))
  · exact .inr (.inr (.inr (.inl ⟨q, r, hk ▸ rfl⟩)))

theorem hello_written {q hd o c'} (hc : CStep hello (.wait q (writeOp hd) (helloK2 hd)) o c') :
    HStep o c' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  have hw : writesOnly hiBytes (wev (I := stdoutWorld.imports) (X := stdoutWorld.exports)
      (.inl (.ans (writeOp hd) n))) = true := by
    simp [wev, writeOp, writesOnly, bytesOf_bytesV]
  exact ⟨(), pointwise_step hw, .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨q, hd, rfl⟩))))))⟩

/-- **The invariant of `hello` against `writesOnly hiBytes`.** -/
theorem hello_writes_inv : Inv hello topP (pointwise (writesOnly hiBytes)) HelloSt where
  init := .inl rfl
  step := fun hc hJ _ => by
    rcases hJ with rfl | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, r, rfl⟩ | ⟨q, hd, rfl⟩ | ⟨q, hd, rfl⟩ |
      ⟨q, hd, rfl⟩ | ⟨q, hd, rfl⟩
    · obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
      exact ⟨(), pointwise_step rfl, .inr (.inl ⟨q, rfl⟩)⟩
    · obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := getOp) (k := helloK1) hc
      exact ⟨(), pointwise_step rfl, .inr (.inr (.inl ⟨q, rfl⟩))⟩
    · exact hello_got hc
    · obtain ⟨rfl, rfl⟩ := hc.pure_inv
      exact ⟨(), pointwise_step rfl, .inl rfl⟩
    · obtain ⟨rfl, rfl⟩ := hc.call_inv
      exact ⟨(), pointwise_step rfl, .inr (.inr (.inr (.inr (.inr (.inl ⟨q, hd, rfl⟩)))))⟩
    · exact hello_written hc
    · obtain ⟨rfl, rfl⟩ := hc.call_inv
      exact ⟨(), pointwise_step rfl, .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨q, hd, rfl⟩))))))⟩
    · obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
      exact ⟨(), pointwise_step rfl, .inr (.inr (.inr (.inl ⟨q, _, rfl⟩)))⟩

/-- **`hello` writes only `hi`**, for every host. -/
theorem hello_writesHi : (agP topP (pointwise (writesOnly hiBytes))).holds (ofBody hello) :=
  ag_of_inv hello_writes_inv

/-- Every list is accepted by `topP`. -/
theorem topP_accepts (t : List WEv) : topP.Accepts t :=
  (pointwise_accepts_iff _ t).2 fun _ _ => rfl

/-- **The OS image of every play of `hello` is copies of `hi`.** -/
theorem hello_os (ch : Word) :
    ∀ s ∈ ofBody hello, ∃ k, osTrace ch (wtrace s) = (List.replicate k (hiOut ch)).flatten :=
  fun s hs => osTrace_replicate ch hiBytes _
    ((pointwise_accepts_iff _ _).1 (hello_writesHi s hs (topP_accepts _)))

/-- **For every host below `hello`, the OS image of its answers is copies of `hi`.** -/
theorem hello_link_os {Y : Sig.{0}} (η : Host Y stdoutWorld.imports) (ch : Word) :
    ∀ p ∈ link η (ofBody hello), ∃ s ∈ η, ∃ t ∈ ofBody hello, Zip s t p ∧
      ∃ k, osTrace ch (htrace s) = (List.replicate k (hiOut ch)).flatten := by
  rintro p ⟨s, hs, t, ht, hz⟩
  refine ⟨s, hs, t, ht, hz, ?_⟩
  rw [htrace_zip hz, osTrace_hostView]
  exact hello_os ch t ht

/-! ## The canonical run of `hello` -/

/-- Following an implementation, one answer more. -/
theorem follows_snoc {impl : Impl} {t : List WEv} {f : FnName} {a : List Val}
    {r : Option (List Val)} (ht : Follows impl t) (hr : r = impl t f a) :
    Follows impl (t ++ [.imp f a r]) := by
  intro p f' a' r' hp
  rcases List.prefix_concat_iff.1 hp with h | h
  · obtain ⟨rfl, h2⟩ := List.append_inj' h rfl
    injection h2 with h3
    injection h3 with h4 h5 h6
    subst h4 h5 h6
    exact hr
  · exact ht p f' a' r' h

/-- The empty answer list follows every implementation. -/
theorem follows_nil (impl : Impl) : Follows impl [] := (prefixClosed_follows impl).1

/-- **`helloRun` is a play of `hello`.** -/
theorem helloRun_mem : helloRun ∈ ofBody hello := by
  have h1 := (Reach.nil (h := hello)).snoc (CStep.ask runQ)
  have h2 := h1.snoc (CStep.call runQ getOp helloK1)
  have h3 := h2.snoc (CStep.reply runQ getOp helloK1 (some [.u32 0]))
  have h4 := h3.snoc (CStep.call (h := hello) runQ (writeOp 0) (helloK2 0))
  have h5 := h4.snoc (CStep.reply runQ (writeOp 0) (helloK2 0) (some [okV none]))
  have h6 := h5.snoc (CStep.call (h := hello) runQ (dropOp 0) helloK3)
  have h7 := h6.snoc (CStep.reply runQ (dropOp 0) helloK3 (some []))
  exact ⟨_, h7.snoc (CStep.ret (h := hello) runQ (some [okV none]))⟩

/-- **The answers of `helloRun` follow the concrete host `stdoutImpl`.** -/
theorem helloRun_follows : Follows stdoutImpl (hostView (wtrace helloRun)) := by
  have h1 := follows_snoc (follows_nil stdoutImpl) (f := getStdout) (a := [])
    (r := some [.u32 0]) rfl
  have h2 := follows_snoc h1 (f := streamWrite) (a := [.u32 0, bytesV hiBytes])
    (r := some [okV none]) rfl
  exact follows_snoc h2 (f := streamDrop) (a := [.u32 0]) (r := some []) rfl

/-- **The OS image of `helloRun` is the write of `hi`.** -/
theorem helloRun_os (ch : Word) : osTrace ch (wtrace helloRun) = hiOut ch := by
  simp [osTrace, wtrace, helloRun, wev, osEv, writeOp, getOp, dropOp, runQ, bytesOf_bytesV, hiOut,
    okV, getStdout, streamWrite, streamDrop]

/-- **End to end**: an x86 runtime of `hello` is `IoSafeN` with `lpsEnv` for the traces "a prefix
of the OS image of `hello`'s run against `stdoutImpl`, then `exit 0`". -/
theorem hello_e2e {c : Silmaril.X86.MState → Option Silmaril.X86.MState}
    {segs : List Silmaril.Process.LPS.Segment} {ch : Word} {e : Silmaril.Process.LPS.Model}
    (R : HelloRt c segs ch e) :
    ∀ n, IoSafeN c (lpsEnv segs) (fun _ _ _ => False) n R.start e
      (fun tr => tr <+: osTrace ch (wtrace helloRun) ++ [.exitEv 0 e.fs]) := by
  rw [helloRun_os]
  exact helloRt_ioSafe R

/-! ## The filesystem slice: the run of `writeFile` -/

/-- Looking up a path just set. -/
theorem lookup_set_self (fs : Fs.FileSystem) (p : Fs.Path) (d : List Byte) :
    Fs.lookup (Fs.set fs p d) p = some d := by
  have hp : Fs.pathEqb p p = true := beq_self_eq_true p
  induction fs with
  | nil => simp [Fs.set, Fs.lookup, hp]
  | cons qd r ih =>
    obtain ⟨q, d0⟩ := qd
    unfold Fs.set
    by_cases h1 : Fs.pathLtb p q = true
    · simp [h1, Fs.lookup, hp]
    · by_cases h2 : Fs.pathEqb p q = true
      · simp [h1, h2, Fs.lookup, hp]
      · simp [h1, h2, Fs.lookup, ih]

/-- The export call `run` of the filesystem world. -/
def runF : (nsig fsWorld.exports).Op := (⟨cliRun, rfl⟩, [])

/-- The preopen answer of `fsImpl`. -/
def preopens : Option (List Val) := some [.record [.record [.u32 0, strV "/"]]]

/-- **One run of `writeFile`** against `fsImpl`: the preopened directory is `0`, `open-at`
answers descriptor `2`, the write reports `2` bytes, the drop succeeds, `run` returns `ok`. -/
def wfRun : List (Move (nsig fsWorld.imports) (nsig fsWorld.exports)) :=
  [.inr (.ask runF), .inl (.ask dirsOp), .inl (.ans dirsOp preopens),
   .inl (.ask (openOp 0)), .inl (.ans (openOp 0) (some [okV (some (.u32 2))])),
   .inl (.ask (fwriteOp 2)), .inl (.ans (fwriteOp 2) (some [okV (some (.u64 2))])),
   .inl (.ask (fdropOp 2)), .inl (.ans (fdropOp 2) (some [])), .inr (.ans runF (some [okV none]))]

/-- **`wfRun` is a play of `writeFile`.** -/
theorem wfRun_mem : wfRun ∈ ofBody writeFile := by
  have h1 := (Reach.nil (h := writeFile)).snoc (CStep.ask runF)
  have h2 := h1.snoc (CStep.call runF dirsOp wfK1)
  have h3 := h2.snoc (CStep.reply runF dirsOp wfK1 preopens)
  have h4 := h3.snoc (CStep.call (h := writeFile) runF (openOp 0) wfK2)
  have h5 := h4.snoc (CStep.reply runF (openOp 0) wfK2 (some [okV (some (.u32 2))]))
  have h6 := h5.snoc (CStep.call (h := writeFile) runF (fwriteOp 2) (wfK3 2))
  have h7 := h6.snoc (CStep.reply runF (fwriteOp 2) (wfK3 2) (some [okV (some (.u64 2))]))
  have h8 := h7.snoc (CStep.call (h := writeFile) runF (fdropOp 2) wfK4)
  have h9 := h8.snoc (CStep.reply runF (fdropOp 2) wfK4 (some []))
  exact ⟨_, h9.snoc (CStep.ret (h := writeFile) runF (some [okV none]))⟩

/-- **The answers of `wfRun` follow the concrete host `fsImpl`.** -/
theorem wfRun_follows : Follows fsImpl (hostView (wtrace wfRun)) := by
  have h1 := follows_snoc (follows_nil fsImpl) (f := getDirs) (a := []) (r := preopens) rfl
  have h2 := follows_snoc h1 (f := openAt) (a := [.u32 0, strV "out.txt"])
    (r := some [okV (some (.u32 2))]) rfl
  have h3 := follows_snoc h2 (f := fdWrite) (a := [.u32 2, bytesV hiBytes, .u64 0])
    (r := some [okV (some (.u64 2))]) rfl
  exact follows_snoc h3 (f := fdDrop) (a := [.u32 2]) (r := some []) rfl

/-- **The OS image of `wfRun`**: on an LPS file system without `out.txt`, the host's answers
leave `out.txt` containing `hi`. -/
theorem wfRun_fs (fs : Fs.FileSystem) (h : Fs.lookup fs outPath = none) :
    Fs.lookup (fsOs fs (hostView (wtrace wfRun))) outPath = some hiBytes := by
  have hv : hostView (wtrace wfRun) =
      [.imp getDirs [] preopens, .imp openAt [.u32 0, strV "out.txt"] (some [okV (some (.u32 2))]),
       .imp fdWrite [.u32 2, bytesV hiBytes, .u64 0] (some [okV (some (.u64 2))]),
       .imp fdDrop [.u32 2] (some [])] := rfl
  have h2 : fsStep ⟨[], fs⟩ (.imp openAt [.u32 0, strV "out.txt"] (some [okV (some (.u32 2))])) =
      ⟨[(2, outPath)], Fs.set fs outPath []⟩ := by
    have h' : (Fs.lookup fs (pathOf (strV "out.txt"))).isSome = false := by
      rw [show pathOf (strV "out.txt") = outPath from rfl, h]
      rfl
    simp only [fsStep, okV, ↓reduceIte, h', Bool.false_eq_true]
    rfl
  have h3 : fsStep ⟨[(2, outPath)], Fs.set fs outPath []⟩
      (.imp fdWrite [.u32 2, bytesV hiBytes, .u64 0] (some [okV (some (.u64 2))])) =
      ⟨[(2, outPath)], Fs.set (Fs.set fs outPath []) outPath
        (writeAt ((Fs.lookup (Fs.set fs outPath []) outPath).getD []) 0 (bytesOf (bytesV hiBytes)))⟩ :=
    rfl
  have hf : fsOs fs (hostView (wtrace wfRun)) = Fs.set (Fs.set fs outPath []) outPath
      (writeAt ((Fs.lookup (Fs.set fs outPath []) outPath).getD []) 0 (bytesOf (bytesV hiBytes))) := by
    rw [hv]
    simp only [fsOs, List.foldl]
    rw [show fsStep ⟨[], fs⟩ (.imp getDirs [] preopens) = ⟨[], fs⟩ from rfl, h2, h3]
    rfl
  rw [hf, lookup_set_self, lookup_set_self, bytesOf_bytesV]
  rfl

end Silmaril.Wasi.Os
