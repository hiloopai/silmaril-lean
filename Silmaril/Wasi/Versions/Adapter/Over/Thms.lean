module

public import Silmaril.Wasi.Versions.Adapter.Over.Defs
public import Silmaril.Wasi.Versions.Adapter.Thms
public import Silmaril.Wasi.Versions.P2.Host.Thms
public import Silmaril.Wasi.Versions.Net.Thms

@[expose] public section

/-!
# The adapter over the 0.2.9 theory and over a concrete 0.2 host

PROVED:

* **`p2Th_of_p2`**: `P2.p2Th r` (WIT 0.2.9, either reading) together with `extraTh` implies
  the adapter's 0.2.12 theory `Adapter.p2Th`. Per import: `ok_of_p2`.
* **`adapter_model_p2`**: for every host satisfying `P2.p2Th r` and `extraTh`, the adapter over
  it is a model of the preview1 theory `P1.th`.
* `p2ImplA_accepts`, **`p2ImplA_sat_p2`**: the completed concrete host `p2ImplA` is a model of
  the strict 0.2 theory `P2.p2Th .strict`; `p2ImplA_extra`: of `extraTh` on well-typed calls;
  **`p2ImplA_sat`**: `concreteWT p2ImplA` is a model of `Adapter.p2Th`.
* **`adapter_concrete`**: `link (concreteWT p2ImplA) adapter` is a model of `P1.th`: the
  adapter instantiated over a concrete 0.2 host is a concrete preview1 host.
* `p2Sys_tcp`, `p2Sys_http`: the 0.2 host of a system is a model of the TCP and HTTP theories of
  its network and web; `p1Sys_eq`: the preview1 host of a system (the adapter over its 0.2 host)
  does not depend on the network or the web; **`no_tcp_adapter_sys`**,
  **`no_http_adapter_sys`**: a component over these preview1 hosts that is correct for every
  system decides no connect (no request).
-/

namespace Silmaril.Wasi.Versions.Adapter

open Silmaril.Games Silmaril.Wasi
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)

/-! ## Facts about accepted traces -/

/-- Every event of an accepted trace steps from some state. -/
theorem step_of_mem {S : Type} {P : Protocol S WEv} {t : List WEv} (h : P.Accepts t) {e : WEv}
    (he : e ∈ t) : ∃ q q', P.step q e = some q' := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem he
  have hp : P.Accepts (u ++ [e]) := h.of_prefix ⟨v, by simp⟩
  obtain ⟨q, -, q', hq'⟩ := (Protocol.accepts_concat_iff _ _ _).1 hp
  exact ⟨q, q', hq'⟩

/-- An answer of `now` accepted by the clock theory is a `u64`. -/
theorem now_u64 {t : List WEv} (h : clockTh.Accepts t) {a : List Val} {r : Option (List Val)}
    (he : WEv.imp clockNow a r ∈ t) : ∃ x, r = some [.u64 x] := by
  obtain ⟨q, q', hq⟩ := step_of_mem h he
  have hn : nowStep q r = some q' := by simpa [clockTh, clockStep] using hq
  unfold nowStep at hn
  split at hn
  · exact ⟨_, rfl⟩
  · exact absurd hn (by simp)

/-- The import named `f`, if any, is named `f`. -/
theorem Imp.name_of_ofName {f : FnName} {i : Imp} (h : Imp.ofName f = some i) : i.name = f := by
  have h' := List.find?_some h
  simpa using h'

/-! ## Per import -/

/-- WIT strings are the same in both modules. -/
theorem strOk_eq : P2.strOk = P1.isStrV := by
  funext v
  cases v <;> rfl

/-- An environment entry is the same in both modules. -/
theorem envEntryOk_eq : P2.envEntryOk = isEnvPair := by
  funext v
  unfold P2.envEntryOk
  rw [strOk_eq]
  rfl

variable {a : List Val} {r : Option (List Val)}

/-- Stream errors are the same in both modules. -/
theorem isStreamErr_eq : isStreamErr = P2.streamErrOk := by
  rw [P2.streamErrOk_eq_hand]
  funext v
  rfl

/-- `list<u8>` is the same in both modules. -/
theorem allU8_eq : allU8 = fun vs => vs.all P2.isU8 := by
  funext vs
  rfl

/-- The adapter's typing of `blocking-write-and-flush` is `wasi:io`'s `unitAns`. -/
theorem write_ok_eq : Imp.write.ok a r = P2.unitAns r := by
  rw [P2.unitAns_eq_hand]
  unfold Imp.ok P2.unitAnsH
  split <;> split <;> simp_all [isStreamErr_eq]

/-- `blocking-write-and-flush`: a non-trap answer admissible for `wasi:io`. -/
theorem ok_write {rd : P2.Reading} (hio : ∃ s, P2.ansOk rd s (P2.ioOp Imp.write.name) a r = true)
    (hx : r.isSome = true) : Imp.write.ok a r = true := by
  obtain ⟨s, hs⟩ := hio
  have hb : P2.ioOp Imp.write.name = .bwf := by decide
  have hs' : P2.ansOk rd s .bwf a r = true := hb ▸ hs
  rw [write_ok_eq]
  cases r with
  | none => exact absurd hx (by simp)
  | some l =>
    have h2 : P2.stickyOk s (P2.selfOf a) (some l) = true ∧ P2.unitAns (some l) = true := by
      simpa [P2.ansOk] using hs'
    exact h2.2

/-- Outside the shape `[self, u64 len]`, `extraOk` is the adapter's typing of `blocking-read`. -/
theorem read_extra_of_not (h : ¬ ∃ x len, a = [x, .u64 len]) :
    Imp.read.extraOk a r = Imp.read.ok a r := by
  match a with
  | [x, .u64 len] => exact absurd ⟨x, len, rfl⟩ h
  | [] | [_] => rfl
  | _ :: y :: _ :: _ => cases y <;> rfl
  | [_, .bool _] | [_, .s8 _] | [_, .u8 _] | [_, .s16 _] | [_, .u16 _] | [_, .s32 _] => rfl
  | [_, .u32 _] | [_, .s64 _] | [_, .f32 _] | [_, .f64 _] | [_, .char _] => rfl
  | [_, .record _] | [_, .variant _ _] => rfl

/-- `blocking-read(self, len)`: admissible for `wasi:io`. -/
theorem ok_read {rd : P2.Reading} (hio : ∃ s, P2.ansOk rd s (P2.ioOp Imp.read.name) a r = true)
    (hx : Imp.read.extraOk a r = true) : Imp.read.ok a r = true := by
  obtain ⟨s, hs⟩ := hio
  have hb : P2.ioOp Imp.read.name = .bread := by decide
  have hs' : P2.ansOk rd s .bread a r = true := hb ▸ hs
  by_cases hsh : ∃ x len, a = [x, .u64 len]
  · obtain ⟨x, len, ha⟩ := hsh
    have hy2 : P2.stickyOk s (P2.selfOf [x, .u64 len]) r = true ∧
        P2.bytesAns len.toNat (rd == .strict && decide (0 < len.toNat)) r = true := by
      simpa [ha, P2.ansOk, P2.lenOf] using hs'
    have hy : P2.bytesAns len.toNat (rd == .strict && decide (0 < len.toNat)) r = true := hy2.2
    rw [ha]
    unfold P2.bytesAns at hy
    split at hy <;> simp_all [Imp.ok, allU8_eq, isStreamErr_eq]
  · exact (read_extra_of_not hsh) ▸ hx

/-- A `datetime` of the 0.2 theory has the adapter's shape. -/
theorem datetime_ok {v : Val} (h : P2.datetimeOk v = true) :
    ∃ s ns, v = .record [.u64 s, .u32 ns] := by
  unfold P2.datetimeOk at h
  split at h
  · exact ⟨_, _, rfl⟩
  · exact absurd h (by simp)

/-- The typing of the `wasi:cli` and `wasi:clocks` imports from `cliOk`. -/
theorem ok_cli {i : Imp} (hp : P2.p2Ok (.imp i.name a r) = true)
    (hi : i = .getStdin ∨ i = .getStdout ∨ i = .getStderr ∨ i = .outDrop ∨ i = .monoRes ∨
      i = .wallNow ∨ i = .wallRes ∨ i = .getArgs ∨ i = .getEnv) : i.ok a r = true := by
  have ho : P2.ioOp i.name = .other := by
    rcases hi with h | h | h | h | h | h | h | h | h <;> (rw [h]; decide)
  have hc : P2.cliOk i.name r = true := (P2.p2Ok_of_other ho) ▸ hp
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (revert hc; rw [P2.cliOk_eq_hand]; unfold P2.cliOkH; simp [Imp.name, P2.cliExit, P2.getEnv, P2.getArgs, P2.initialCwd,
      P2.getStdin, getStdout, P2.getStderr, P2.monoSubInstant, P2.monoSubDuration,
      P2.getTermStdin, P2.getTermStdout, P2.getTermStderr, P2.monoRes, P2.wallNow, P2.wallRes,
      P2.fdReadStream, P2.fdWriteStream, P2.fdAppendStream, P2.fdGetType, streamDrop,
      Adapter.getStdin, Adapter.getStderr, Adapter.monoRes, Adapter.wallNow, Adapter.wallRes,
      Adapter.getArgs, Adapter.getEnv]
     ; split <;> intros <;>
      first
      | (obtain ⟨_, _, rfl⟩ := datetime_ok (by assumption); rfl)
      | simp_all [Imp.ok, strOk_eq, envEntryOk_eq])

/-- `[resource-drop]descriptor`: the base WASI theory's filesystem typing. -/
theorem ok_fdDrop (hf : fsOk (.imp Imp.fdDrop.name a r) = true) : Imp.fdDrop.ok a r = true := by
  revert hf
  unfold fsOk
  simp [Imp.name, Silmaril.Wasi.getDirs, Silmaril.Wasi.openAt, Silmaril.Wasi.fdWrite, Silmaril.Wasi.fdRead,
    Silmaril.Wasi.fdDrop]
  split <;> simp_all [Imp.ok]

/-- **The adapter's typing of an import**, from the 0.2.9 theory and `extraOk`. -/
theorem ok_of_p2 {rd : P2.Reading} (i : Imp) (hp : P2.p2Ok (.imp i.name a r) = true)
    (hf : fsOk (.imp i.name a r) = true) (hio : ∃ s, P2.ansOk rd s (P2.ioOp i.name) a r = true)
    (hcl : i = .now → ∃ x, r = some [.u64 x]) (hx : i.extraOk a r = true) : i.ok a r = true := by
  cases i
  case write => exact ok_write hio hx
  case read => exact ok_read hio hx
  case fdDrop => exact ok_fdDrop hf
  case now =>
    obtain ⟨x, hr⟩ := hcl rfl
    exact hr ▸ rfl
  case exit => rfl
  case getStdin | getStdout | getStderr | outDrop | monoRes | wallNow | wallRes | getArgs
    | getEnv => exact ok_cli hp (by simp)
  all_goals exact hx

/-- An answer of an import in a trace accepted by the 0.2.9 theory and `extraTh` is typed for
the adapter. -/
theorem ok_of_mem {rd : P2.Reading} {t : List WEv} (h : (P2.p2Th rd).Accepts t)
    (hx : extraTh.Accepts t) (i : Imp) {a : List Val} {r : Option (List Val)}
    (he : WEv.imp i.name a r ∈ t) : i.ok a r = true := by
  have hio : (P2.ioTh rd).Accepts t := ((Protocol.accepts_prod_iff _ _ _).1 h).1
  have hcl : clockTh.Accepts t := P2.p2_clockTh h
  have hfs : fsTyped.Accepts t := P2.p2_fsTyped h
  have hxe : i.extraOk a r = true := by
    simpa [extraOk, Imp.ofName_name] using (pointwise_accepts_iff _ _).1 hx _ he
  exact ok_of_p2 i (P2.p2_p2Ok h _ he) ((pointwise_accepts_iff _ _).1 hfs _ he)
    (P2.io_ansOk_of_mem hio he) (fun hnow => now_u64 hcl (hnow ▸ he)) hxe

/-- Every event of a trace accepted by the 0.2.9 theory and `extraTh` is typed for the
adapter. -/
theorem p2Ok_of_p2 {rd : P2.Reading} {t : List WEv} (h : (P2.p2Th rd).Accepts t)
    (hx : extraTh.Accepts t) : ∀ e ∈ t, p2Ok e = true := by
  intro e he
  cases e with
  | imp f a r =>
    cases hi : Imp.ofName f with
    | none => simp [p2Ok, hi]
    | some i =>
      have hn : i.name = f := Imp.name_of_ofName hi
      have hok : i.ok a r = true := ok_of_mem h hx i (hn ▸ he)
      simpa [p2Ok, hi] using hok
  | req f a => rfl
  | call f a => rfl
  | ret f a r => rfl

/-- **The 0.2.9 theory and `extraTh` imply the adapter's 0.2.12 theory.** -/
theorem p2Th_of_p2 {rd : P2.Reading} {t : List WEv} (h : (P2.p2Th rd).Accepts t)
    (hx : extraTh.Accepts t) : p2Th.Accepts t :=
  (Protocol.accepts_prod_iff _ _ _).2
    ⟨(pointwise_accepts_iff _ _).2 (p2Ok_of_p2 h hx), P2.p2_clockTh h⟩

/-- **The adapter over a host of the 0.2.9 theory** (and of `extraTh`) is a preview1 host. -/
theorem adapter_model_p2 {Y : Sig.{0}} {rd : P2.Reading} {η : Host Y imports}
    (hη : (hostSat (P2.p2Th rd).Accepts).holds η) (hx : (hostSat extraTh.Accepts).holds η) :
    (hostSat P1.th.Accepts).holds (link η adapter) :=
  adapter_model fun s hs => p2Th_of_p2 (hη s hs) (hx s hs)

/-! ## The concrete host `p2ImplA` -/

/-- The four functions on which `p2ImplA` completes `P2.p2Impl`. -/
def Completed (f : FnName) : Prop := f = inDrop ∨ f = errDrop ∨ f = fsErrCode ∨ f = randBytes

/-- Elsewhere `p2ImplA` is `P2.p2Impl`. -/
theorem p2ImplA_of_not {f : FnName} (hf : ¬ Completed f) (p : List WEv) (a : List Val) :
    p2ImplA p f a = P2.p2Impl p f a := by
  simp only [Completed, not_or] at hf
  simp [p2ImplA, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2]

/-- The completed functions are not `wasi:io` operations of the theory. -/
theorem ioOp_completed {f : FnName} (hf : Completed f) : P2.ioOp f = .other := by
  rcases hf with rfl | rfl | rfl | rfl <;> decide

/-- `p2ImplA`'s `wasi:io` answers are admissible in the state of its answers so far. -/
theorem p2ImplA_io (p : List WEv) (f : FnName) (a : List Val) :
    P2.ansOk .strict (P2.ioState p) (P2.ioOp f) a (p2ImplA p f a) = true := by
  by_cases hf : Completed f
  · rw [ioOp_completed hf]
    rfl
  · rw [p2ImplA_of_not hf]
    exact P2.p2Impl_io p f a

/-- One more answer of `p2ImplA` (as `P2.io_step_follows`). -/
theorem ioA_step {p : List WEv} {e : WEv} (he : ∀ f a r, e = .imp f a r → r = p2ImplA p f a) :
    P2.ioStep .strict (P2.ioState p) e = some (P2.ioState (p ++ [e])) := by
  have hst : P2.ioState (p ++ [e]) = P2.ioNext (P2.ioState p) e := by
    simp [P2.ioState, List.foldl_append]
  rw [hst]
  cases e
  case imp f a r =>
    have hr : r = p2ImplA p f a := he f a r rfl
    rw [hr]
    simp [P2.ioStep, P2.ioNext, p2ImplA_io]
  all_goals rfl

/-- `p2ImplA`'s answers are accepted by the strict `wasi:io` theory. -/
theorem ioA_follows {t : List WEv} (ht : Follows p2ImplA t) :
    P2.ioStrict.run P2.ioStrict.init t = some (P2.ioState t) := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t e ih =>
    have ht' : Follows p2ImplA t := (prefixClosed_follows p2ImplA).2 (List.prefix_append t [e]) ht
    have he : ∀ f a r, e = .imp f a r → r = p2ImplA t f a :=
      fun f a r h => ht t f a r (h ▸ List.prefix_refl _)
    rw [Protocol.run_concat, ih ht']
    exact ioA_step he

/-- `clockNow` is not completed. -/
theorem not_completed_now : ¬ Completed clockNow := by
  unfold Completed
  decide

/-- On `now`, `p2ImplA` is the tick clock. -/
theorem p2ImplA_now (p : List WEv) (a : List Val) :
    p2ImplA p clockNow a = clockImpl p clockNow a :=
  (p2ImplA_of_not not_completed_now p a).trans (P2.p2Impl_now p a)

/-- The completed functions are unconstrained by `cliOk`. -/
theorem cliOk_completed {f : FnName} (hf : Completed f) (r : Option (List Val)) :
    P2.cliOk f r = true := by
  rcases hf with rfl | rfl | rfl | rfl <;> rfl

/-- The completed functions are unconstrained by the base WASI theory's filesystem typing. -/
theorem fsOk_completed {f : FnName} (hf : Completed f) (a : List Val) (r : Option (List Val)) :
    fsOk (.imp f a r) = true := by
  rcases hf with rfl | rfl | rfl | rfl <;> rfl

/-- `p2ImplA`'s answers satisfy `p2Ok`. -/
theorem p2ImplA_p2Ok (p : List WEv) (f : FnName) (a : List Val) :
    P2.p2Ok (.imp f a (p2ImplA p f a)) = true := by
  by_cases hf : Completed f
  · rw [P2.p2Ok_of_other (ioOp_completed hf)]
    exact cliOk_completed hf _
  · rw [p2ImplA_of_not hf]
    exact P2.p2Impl_p2Ok p f a

/-- `p2ImplA`'s answers satisfy the base WASI theory's filesystem typing. -/
theorem p2ImplA_fsOk (p : List WEv) (f : FnName) (a : List Val) :
    fsOk (.imp f a (p2ImplA p f a)) = true := by
  by_cases hf : Completed f
  · exact fsOk_completed hf _ _
  · rw [p2ImplA_of_not hf]
    exact P2.p2Impl_fsOk p f a

/-- `p2ImplA`'s answer sequences are accepted by the strict 0.2 theory. -/
theorem p2ImplA_accepts {t : List WEv} (ht : Follows p2ImplA t) : (P2.p2Th .strict).Accepts t := by
  have hio : P2.ioStrict.Accepts t := (Protocol.accepts_iff_exists _ _).2 ⟨_, ioA_follows ht⟩
  have hcl : clockTh.Accepts t :=
    let ⟨q, hq, _⟩ := P2.clock_follows_of p2ImplA_now ht
    (Protocol.accepts_iff_exists _ _).2 ⟨q, hq⟩
  have hok : (pointwise P2.p2Ok).Accepts t := follows_pointwise p2ImplA_p2Ok (fun e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  have hfs : fsTyped.Accepts t := follows_pointwise p2ImplA_fsOk (fun e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  exact (Protocol.accepts_prod_iff _ _ _).2 ⟨hio, (Protocol.accepts_prod_iff _ _ _).2
    ⟨hcl, (Protocol.accepts_prod_iff _ _ _).2 ⟨hok, hfs⟩⟩⟩

/-- **`p2ImplA` is a model of the strict 0.2 theory.** -/
theorem p2ImplA_sat_p2 {Y : Sig.{0}} {I : Set FnName} :
    (hostSat (P2.p2Th .strict).Accepts).holds (concrete (Y := Y) (I := I) p2ImplA) :=
  concrete_sat _ fun _ ht => p2ImplA_accepts ht

/-- `p2ImplA` answers `blocking-write-and-flush`. -/
theorem p2ImplA_write_some (p : List WEv) (a : List Val) :
    (p2ImplA p Imp.write.name a).isSome = true := by
  have hn : ¬ Completed Imp.write.name := by
    unfold Completed
    decide
  rw [p2ImplA_of_not hn]
  show (P2.orClosed _ _ _).isSome = true
  unfold P2.orClosed
  split <;> rfl

/-- `error(closed)` is a well-typed answer of `blocking-read`. -/
theorem read_ok_closed : ∀ a : List Val, Imp.read.ok a (some [P2.errClosed]) = true
  | [] | [_] => rfl
  | [_, y] => by cases y <;> rfl
  | _ :: y :: _ :: _ => by cases y <;> rfl

/-- `p2ImplA`'s answer of `blocking-read` passes `extraOk`. -/
theorem p2ImplA_read_extra (p : List WEv) (a : List Val) :
    Imp.read.extraOk a (p2ImplA p Imp.read.name a) = true := by
  have hn : ¬ Completed Imp.read.name := by
    unfold Completed
    decide
  have hr : p2ImplA p Imp.read.name a = some [P2.errClosed] := by
    rw [p2ImplA_of_not hn]
    rfl
  rw [hr]
  by_cases hsh : ∃ x len, a = [x, .u64 len]
  · obtain ⟨x, len, ha⟩ := hsh
    rw [ha]
    rfl
  · rw [read_extra_of_not hsh]
    exact read_ok_closed a

/-- `p2ImplA`'s answer of a well-typed `get-random-bytes` passes `extraOk`. -/
theorem p2ImplA_rand_extra (p : List WEv) {a : List Val}
    (hw : wellCalled (.imp Imp.rand.name a none) = true) :
    Imp.rand.extraOk a (p2ImplA p Imp.rand.name a) = true := by
  have hs : ∃ len, a = [.u64 len] := by
    revert hw
    simp only [wellCalled, Imp.name, ite_true]
    split <;> simp_all
  obtain ⟨len, rfl⟩ := hs
  simp [Imp.extraOk, Imp.ok, p2ImplA, Imp.name, allU8, inDrop, errDrop, fsErrCode, randBytes]

/-- **`p2ImplA`'s answers to well-typed calls pass `extraOk`.** -/
theorem p2ImplA_extraOk (p : List WEv) (f : FnName) (a : List Val)
    (hw : wellCalled (.imp f a none) = true) : extraOk (.imp f a (p2ImplA p f a)) = true := by
  cases hi : Imp.ofName f with
  | none => simp [extraOk, hi]
  | some i =>
    have hn : i.name = f := Imp.name_of_ofName hi
    have hx : i.extraOk a (p2ImplA p i.name a) = true := by
      cases i
      case write => exact p2ImplA_write_some p a
      case read => exact p2ImplA_read_extra p a
      case rand => exact p2ImplA_rand_extra p (hn ▸ hw)
      all_goals rfl
    simpa [extraOk, hi, hn] using hx

/-- Well-typedness does not depend on the answer. -/
theorem wellCalled_imp (f : FnName) (a : List Val) (r : Option (List Val)) :
    wellCalled (.imp f a r) = wellCalled (.imp f a none) := rfl

/-- `p2ImplA`'s answer sequences to well-typed calls are accepted by `extraTh`. -/
theorem p2ImplA_extra {t : List WEv} (ht : Follows p2ImplA t)
    (hw : ∀ e ∈ t, wellCalled e = true) : extraTh.Accepts t := by
  refine (pointwise_accepts_iff _ _).2 fun e he => ?_
  obtain ⟨u, v, rfl⟩ := List.append_of_mem he
  cases e with
  | imp f a r =>
    have hr : r = p2ImplA u f a := ht u f a r ⟨v, by simp⟩
    have hwe : wellCalled (.imp f a none) = true := (wellCalled_imp f a r) ▸ hw _ he
    exact hr ▸ p2ImplA_extraOk u f a hwe
  | req f a => rfl
  | call f a => rfl
  | ret f a r => rfl

/-- **`p2ImplA` on well-typed calls is a model of the adapter's 0.2.12 theory.** -/
theorem p2ImplA_sat {Y : Sig.{0}} :
    (hostSat p2Th.Accepts).holds (concreteWT (Y := Y) (I := imports) p2ImplA) :=
  fun _ hs => p2Th_of_p2 (p2ImplA_accepts hs.2.1) (p2ImplA_extra hs.2.1 hs.2.2)

/-- **The adapter over a concrete 0.2 host is a concrete preview1 host.** -/
theorem adapter_concrete {Y : Sig.{0}} :
    (hostSat P1.th.Accepts).holds (link (concreteWT (Y := Y) (I := imports) p2ImplA) adapter) :=
  adapter_model p2ImplA_sat

/-! ## Systems -/

/-- The functions of a host's answers are its imports. -/
theorem htrace_mem_fn {Y : Sig.{0}} {I : Set FnName} {s : List (Move Y (nsig I))} {f : FnName}
    {a : List Val} {r : Option (List Val)} (he : WEv.imp f a r ∈ htrace s) : f ∈ I := by
  obtain ⟨o, -, ho⟩ := List.mem_filterMap.1 he
  rcases o with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩)
  · simp [hev] at ho
  · simp [hev] at ho
  · simp [hev] at ho
  · have hq : q.1.1 = f := by
      simp only [hev, Option.some.injEq, WEv.imp.injEq] at ho
      exact ho.1
    exact hq ▸ q.1.2

/-- Following two implementations that agree on the answered calls is the same. -/
theorem follows_congr {impl₁ impl₂ : Impl} {t : List WEv}
    (h : ∀ p f a r, p ++ [WEv.imp f a r] <+: t → impl₁ p f a = impl₂ p f a) :
    Follows impl₁ t ↔ Follows impl₂ t :=
  ⟨fun h₁ p f a r hp => (h₁ p f a r hp).trans (h p f a r hp),
    fun h₂ p f a r hp => (h₂ p f a r hp).trans (h p f a r hp).symm⟩

/-- **Hosts of implementations that agree on the imports are equal.** -/
theorem concreteWT_congr {Y : Sig.{0}} {I : Set FnName} {impl₁ impl₂ : Impl}
    (h : ∀ p, ∀ f ∈ I, ∀ a, impl₁ p f a = impl₂ p f a) :
    concreteWT (Y := Y) (I := I) impl₁ = concreteWT impl₂ := by
  ext s
  have hf : Follows impl₁ (htrace s) ↔ Follows impl₂ (htrace s) :=
    follows_congr fun p f a r hp =>
      h p f (htrace_mem_fn (hp.subset (List.mem_append_right p (List.mem_singleton_self _)))) a
  change (Legal s ∧ (Follows impl₁ (htrace s) ∧ ∀ e ∈ htrace s, wellCalled e = true)) ↔
    (Legal s ∧ (Follows impl₂ (htrace s) ∧ ∀ e ∈ htrace s, wellCalled e = true))
  exact and_congr_right fun _ => and_congr_left fun _ => hf

/-- No import of the adapter is a network function. -/
theorem imports_not_net : ∀ f ∈ importList, f.iface ∉ netIfaces := by decide

/-- On the adapter's imports, the 0.2 host of a system is `p2ImplA`. -/
theorem p2Sys_imports {O : Type} (x : Net.Sys O) (p : List WEv) (f : FnName) (hf : f ∈ imports)
    (a : List Val) : p2Sys x p f a = p2ImplA p f a := by
  have hn : f.iface ∉ netIfaces := imports_not_net f hf
  simp [p2Sys, hn]

/-- **The preview1 host of a system does not depend on its network or web.** -/
theorem p1Sys_eq {Y : Sig.{0}} {O : Type} (x : Net.Sys O) :
    p1Sys (Y := Y) x = link (concreteWT p2ImplA) adapter := by
  unfold p1Sys
  rw [concreteWT_congr (p2Sys_imports x)]

/-- The preview1 host of a system is a model of the preview1 theory. -/
theorem p1Sys_model {Y : Sig.{0}} {O : Type} (x : Net.Sys O) :
    (hostSat P1.th.Accepts).holds (p1Sys (Y := Y) x) :=
  (p1Sys_eq x) ▸ adapter_concrete

/-- `tcpOk` constrains only `finish-connect`. -/
theorem tcpOk_of_ne {N : Net.Network} {q : Net.TcpSt} {f : FnName} {a : List Val}
    {r : Option (List Val)} (hf : f ≠ Net.finishConnect) : Net.tcpOk N q (.imp f a r) = true := by
  unfold Net.tcpOk
  split <;> simp_all

/-- `httpOk` constrains only `get` and `status`. -/
theorem httpOk_of_ne {W : Net.Web} {q : Net.HttpSt} {f : FnName} {a : List Val}
    {r : Option (List Val)} (hg : f ≠ Net.futGet) (hs : f ≠ Net.respStatus) :
    Net.httpOk W q (.imp f a r) = true := by
  unfold Net.httpOk
  split <;> simp_all

/-- The 0.2 host of a system answers `finish-connect` by its network. -/
theorem p2Sys_finish {O : Type} (x : Net.Sys O) (p : List WEv) (a : List Val) :
    p2Sys x p Net.finishConnect a = Net.tcpImpl x.net p Net.finishConnect a := by
  simp [p2Sys, netIfaces, Net.finishConnect]

/-- The 0.2 host of a system answers `get` by its web. -/
theorem p2Sys_get {O : Type} (x : Net.Sys O) (p : List WEv) (a : List Val) :
    p2Sys x p Net.futGet a = Net.httpImpl x.web p Net.futGet a := by
  simp [p2Sys, netIfaces, Net.futGet]

/-- The 0.2 host of a system answers `status` by its web. -/
theorem p2Sys_status {O : Type} (x : Net.Sys O) (p : List WEv) (a : List Val) :
    p2Sys x p Net.respStatus a = Net.httpImpl x.web p Net.respStatus a := by
  simp [p2Sys, netIfaces, Net.respStatus]

/-- **The 0.2 host of a system is a model of the TCP theory of its network.** -/
theorem p2Sys_tcp {Y : Sig.{0}} {I : Set FnName} {O : Type} (x : Net.Sys O) :
    (hostSat (Net.tcpTh x.net).Accepts).holds (concrete (Y := Y) (I := I) (p2Sys x)) := by
  refine concrete_sat _ fun _ ht => Net.gated_follows (fun p f a => ?_) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  by_cases hf : f = Net.finishConnect
  · rw [hf, p2Sys_finish]
    exact Net.tcpImpl_ok x.net p _ a
  · exact tcpOk_of_ne hf

/-- **The 0.2 host of a system is a model of the HTTP theory of its web.** -/
theorem p2Sys_http {Y : Sig.{0}} {I : Set FnName} {O : Type} (x : Net.Sys O) :
    (hostSat (Net.httpTh x.web).Accepts).holds (concrete (Y := Y) (I := I) (p2Sys x)) := by
  refine concrete_sat _ fun _ ht => Net.gated_follows (fun p f a => ?_) (fun q e he => by
    cases e <;> first | rfl | simp [WEv.isImp] at he) ht
  by_cases hg : f = Net.futGet
  · rw [hg, p2Sys_get]
    exact Net.httpImpl_ok x.web p _ a
  · by_cases hs : f = Net.respStatus
    · rw [hs, p2Sys_status]
      exact Net.httpImpl_ok x.web p _ a
    · exact httpOk_of_ne hg hs

/-- **No TCP connect over the adapter's preview1 hosts**: a component correct over the
preview1 host of every system (the adapter over the system's 0.2 host, itself a model of the
system's TCP theory) decides no connect. -/
theorem no_tcp_adapter_sys {Y : Sig.{0}} {O : Type} {X : Set FnName}
    {σ : Strategy (nsig P1.imports) (nsig X)}
    (hσ : ∀ x : Net.Sys O, (hostSat (Net.tcpTh x.net).Accepts).holds (link (p1Sys (Y := Y) x) σ))
    (x : Net.Sys O) : ¬ ∃ p ∈ link (p1Sys (Y := Y) x) σ, Net.TcpDecides (htrace p) := by
  rw [p1Sys_eq x]
  exact Net.no_tcp_sys (fun _ : O => link (concreteWT p2ImplA) adapter)
    (fun x' => (p1Sys_eq x') ▸ hσ x') x.obs

/-- **No outgoing HTTP over the adapter's preview1 hosts.** -/
theorem no_http_adapter_sys {Y : Sig.{0}} {O : Type} {X : Set FnName}
    {σ : Strategy (nsig P1.imports) (nsig X)}
    (hσ : ∀ x : Net.Sys O, (hostSat (Net.httpTh x.web).Accepts).holds (link (p1Sys (Y := Y) x) σ))
    (x : Net.Sys O) : ¬ ∃ p ∈ link (p1Sys (Y := Y) x) σ, Net.HttpDecides (htrace p) := by
  rw [p1Sys_eq x]
  exact Net.no_http_sys (fun _ : O => link (concreteWT p2ImplA) adapter)
    (fun x' => (p1Sys_eq x') ▸ hσ x') x.obs

end Silmaril.Wasi.Versions.Adapter
