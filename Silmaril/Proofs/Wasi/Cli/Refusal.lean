module

public import Silmaril.Wasi.Cli.Refusal.Defs
public import Silmaril.Wasi.Comp.Thms
public import Silmaril.Wasi.Theory.Thms
public import Silmaril.Cli.Behaviour.Thms

/-!
# The WASI 0.2 `hello` component meets `orRefused hiSpec` for every typed host

Proofs for `Silmaril.Wasi.Cli.Refusal.Thms`. Every play of `hello` with at most one call of `run`,
against a host whose `get-stdout` answers a handle (`stdoutTyped`), is a prefix of

  `call run a; get-stdout → hd; write(hd, "hi") → r; drop(hd) → r'; return ok`

(`HelloAt`, by induction on the reachable plays). Its WASI 0.2 view is: nothing yet before the
write's answer; then `hi` on stdout if the write succeeded, or a refusal with nothing written
if it did not; exit `0` once `run` returned; no stdin, no file (`p2View_ok`, `p2View_fail`). Each is a partial view of a run that
`orRefused hiSpec` allows.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Refusal

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Examples
open Silmaril.Games (Move)
open Silmaril.Wasm.Component (Val)

/-! ## Distinct functions -/

theorem getStdout_ne_osWrite : getStdout ≠ Versions.P2.osWrite := by decide
theorem getStdout_ne_streamWrite : getStdout ≠ streamWrite := by decide
theorem streamDrop_ne_osWrite : streamDrop ≠ Versions.P2.osWrite := by decide
theorem streamDrop_ne_streamWrite : streamDrop ≠ streamWrite := by decide
theorem streamWrite_ne_getStderr : streamWrite ≠ Versions.P2.getStderr := by decide
theorem streamDrop_ne_getStderr : streamDrop ≠ Versions.P2.getStderr := by decide
theorem getStderr_ne_getStdout : Versions.P2.getStderr ≠ getStdout := by decide
theorem getStderr_ne_streamWrite : Versions.P2.getStderr ≠ streamWrite := by decide
theorem getStderr_ne_streamDrop : Versions.P2.getStderr ≠ streamDrop := by decide
theorem streamDrop_ne_cliExit : streamDrop ≠ Versions.P2.cliExit := by decide
theorem getStdout_ne_fdRead : getStdout ≠ fdRead := by decide
theorem getStdout_ne_fdWrite : getStdout ≠ fdWrite := by decide
theorem getStdout_ne_getDirs : getStdout ≠ getDirs := by decide
theorem getStdout_ne_openAt : getStdout ≠ openAt := by decide
theorem streamWrite_ne_fdRead : streamWrite ≠ fdRead := by decide
theorem streamWrite_ne_fdWrite : streamWrite ≠ fdWrite := by decide
theorem streamWrite_ne_getDirs : streamWrite ≠ getDirs := by decide
theorem streamWrite_ne_openAt : streamWrite ≠ openAt := by decide
theorem streamDrop_ne_fdRead : streamDrop ≠ fdRead := by decide
theorem streamDrop_ne_fdWrite : streamDrop ≠ fdWrite := by decide
theorem streamDrop_ne_getDirs : streamDrop ≠ getDirs := by decide
theorem streamDrop_ne_openAt : streamDrop ≠ openAt := by decide
theorem getStdin_ne_getStdout : Versions.P2.getStdin ≠ getStdout := by decide
theorem getStdin_ne_streamWrite : Versions.P2.getStdin ≠ streamWrite := by decide
theorem getStdin_ne_streamDrop : Versions.P2.getStdin ≠ streamDrop := by decide

/-! ## The events of a run of `hello` -/

/-- The successful answer of a write. -/
def okAns : Option (List Val) := some [.variant 0 none]

/-- **The events of one run of `hello`**: `run` called with `a`, `get-stdout` answering `hd`,
the write of `hi` answered `r`, the drop answered `r'`, `run` returning `ok`. -/
def full (a : List Val) (hd : BitVec 32) (r r' : Option (List Val)) : List WEv :=
  [.call cliRun a, .req getStdout [], .imp getStdout [] (some [.u32 hd]),
   .req streamWrite [.u32 hd, bytesV hiBytes], .imp streamWrite [.u32 hd, bytesV hiBytes] r,
   .req streamDrop [.u32 hd], .imp streamDrop [.u32 hd] r', .ret cliRun a (some [okV none])]

/-- The control state of `hello` after `k` events of `full`. -/
def stAt (q : (nsig stdoutWorld.exports).Op) (hd : BitVec 32) (r r' : Option (List Val)) :
    Nat → CSt stdoutWorld.imports stdoutWorld.exports
  | 0 => .idle
  | 1 => .run q helloProg
  | 2 => .wait q getOp helloK1
  | 3 => .run q (helloK1 (some [.u32 hd]))
  | 4 => .wait q (writeOp hd) (helloK2 hd)
  | 5 => .run q (helloK2 hd r)
  | 6 => .wait q (dropOp hd) helloK3
  | 7 => .run q (helloK3 r')
  | _ => .idle

/-- **Where a play of `hello` is**: two runs started, or `k ≤ 8` events into one run. -/
def HelloAt (t : List WEv) (c : CSt stdoutWorld.imports stdoutWorld.exports) : Prop :=
  2 ≤ calls cliRun t ∨
    ∃ q hd r r' k, q.1.1 = cliRun ∧ k ≤ 8 ∧ t = (full q.2 hd r r').take k ∧ c = stAt q hd r r' k

/-! ## The view of each prefix -/

/-- No handle comes from `f` when no event answers it. -/
theorem handles_eq_nil {f : FnName} {t : List WEv} (h : ∀ e ∈ t, ∀ a n, e ≠ .imp f a n) :
    handles f t = [] := by
  rw [handles, List.filterMap_eq_nil_iff]
  intro e he
  split
  · next g a x =>
    exact ite_eq_right_iff.2 fun hf => absurd (by rw [hf]) (h _ he a _)
  · rfl

theorem errHandles_full (a : List Val) (hd : BitVec 32) (r r' : Option (List Val)) (k : Nat) :
    handles Versions.P2.getStderr ((full a hd r r').take k) = [] := by
  refine handles_eq_nil fun e he b n hen => ?_
  have hmem : e ∈ full a hd r r' := List.mem_of_mem_take he
  rw [hen] at hmem
  simp [full, getStderr_ne_getStdout, getStderr_ne_streamWrite, getStderr_ne_streamDrop] at hmem

theorem inHandles_full (a : List Val) (hd : BitVec 32) (r r' : Option (List Val)) (k : Nat) :
    handles Versions.P2.getStdin ((full a hd r r').take k) = [] := by
  refine handles_eq_nil fun e he b n hen => ?_
  have hmem : e ∈ full a hd r r' := List.mem_of_mem_take he
  rw [hen] at hmem
  simp [full, getStdin_ne_getStdout, getStdin_ne_streamWrite, getStdin_ne_streamDrop] at hmem

/-! ## No file effects -/

/-- An event that neither touches a file nor opens a descriptor. -/
def NoFile (e : WEv) : Prop := (∀ ds, fileEff ds e = none) ∧ ∀ ds, fdStep ds e = ds

theorem noFile_imp {f : FnName} (a : List Val) (r : Option (List Val)) (h1 : f ≠ fdRead)
    (h2 : f ≠ fdWrite) (h3 : f ≠ getDirs) (h4 : f ≠ openAt) : NoFile (.imp f a r) := by
  refine ⟨fun ds => ?_, fun ds => ?_⟩
  · unfold fileEff
    split
    · next g _ _ _ heq =>
      obtain ⟨rfl, -⟩ := WEv.imp.inj heq
      simp [h1, h2]
    · rfl
  · unfold fdStep
    split
    · next g _ _ heq =>
      obtain ⟨rfl, -⟩ := WEv.imp.inj heq
      simp [h3, h4]
    · rfl

/-- **No file effects** along events that touch no file. -/
theorem fileEffs_eq_nil {t : List WEv} (h : ∀ e ∈ t, NoFile e) (ds : Fds) :
    fileEffs ds t = [] := by
  induction t generalizing ds with
  | nil => rfl
  | cons e t ih =>
    obtain ⟨h1, h2⟩ := h e List.mem_cons_self
    rw [fileEffs, h1, h2, ih fun e he => h e (List.mem_cons_of_mem _ he)]
    rfl

theorem noFile_full (a : List Val) (hd : BitVec 32) (r r' : Option (List Val)) :
    ∀ e ∈ full a hd r r', NoFile e := by
  intro e he
  simp only [full, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact noFile_imp _ _ getStdout_ne_fdRead getStdout_ne_fdWrite getStdout_ne_getDirs
      getStdout_ne_openAt
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact noFile_imp _ _ streamWrite_ne_fdRead streamWrite_ne_fdWrite streamWrite_ne_getDirs
      streamWrite_ne_openAt
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact noFile_imp _ _ streamDrop_ne_fdRead streamDrop_ne_fdWrite streamDrop_ne_getDirs
      streamDrop_ne_openAt
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem fileEffs_full (a : List Val) (hd : BitVec 32) (r r' : Option (List Val)) (k : Nat) :
    fileEffs [] ((full a hd r r').take k) = [] :=
  fileEffs_eq_nil (fun e he => noFile_full a hd r r' e (List.mem_of_mem_take he)) []

/-! ## The view of each event -/

/-- The write of `hi` answered `r`. -/
abbrev eWrote (hd : BitVec 32) (r : Option (List Val)) : WEv :=
  .imp streamWrite [.u32 hd, bytesV hiBytes] r

theorem write2_ok (hd : BitVec 32) : write2 (eWrote hd okAns) = some (hd, hiBytes) := by
  simp only [write2, okAns, or_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, true_and]
  decide

theorem write2_fail {hd : BitVec 32} {r : Option (List Val)} (hr : r ≠ okAns) :
    write2 (eWrote hd r) = none := by
  unfold write2
  split
  · next heq => exact absurd (WEv.imp.inj heq).2.2 hr
  · rfl

theorem failedWrite2_ok (hd : BitVec 32) : failedWrite2 (eWrote hd okAns) = false := by
  simp [failedWrite2, okAns]

theorem failedWrite2_fail {hd : BitVec 32} {r : Option (List Val)} (hr : r ≠ okAns) :
    failedWrite2 (eWrote hd r) = true := by
  simp only [failedWrite2, or_true, ↓reduceIte]
  split <;> simp_all [okAns]

theorem write2_dropped (hd : BitVec 32) (r' : Option (List Val)) :
    write2 (.imp streamDrop [.u32 hd] r') = none := by
  unfold write2
  split
  · next heq => exact absurd (WEv.imp.inj heq).2.1 (by simp)
  · rfl

theorem failedWrite2_dropped (hd : BitVec 32) (r' : Option (List Val)) :
    failedWrite2 (.imp streamDrop [.u32 hd] r') = false := by
  simp [failedWrite2, streamDrop_ne_osWrite, streamDrop_ne_streamWrite]

theorem failedWrite2_got (hd : BitVec 32) :
    failedWrite2 (.imp getStdout [] (some [.u32 hd])) = false := by
  simp [failedWrite2, getStdout_ne_osWrite, getStdout_ne_streamWrite]

@[simp] theorem write2_call (f : FnName) (a : List Val) : write2 (.call f a) = none := rfl
@[simp] theorem write2_req (f : FnName) (a : List Val) : write2 (.req f a) = none := rfl
@[simp] theorem write2_ret (f : FnName) (a : List Val) (r : Option (List Val)) :
    write2 (.ret f a r) = none := rfl
@[simp] theorem write2_got (hd : BitVec 32) :
    write2 (.imp getStdout [] (some [.u32 hd])) = none := rfl
@[simp] theorem failedWrite2_call (f : FnName) (a : List Val) : failedWrite2 (.call f a) = false :=
  rfl
@[simp] theorem failedWrite2_req (f : FnName) (a : List Val) : failedWrite2 (.req f a) = false :=
  rfl
@[simp] theorem failedWrite2_ret (f : FnName) (a : List Val) (r : Option (List Val)) :
    failedWrite2 (.ret f a r) = false := rfl
@[simp] theorem endCode_call (f : FnName) (a : List Val) :
    endCode cliRun (some Versions.P2.cliExit) (.call f a) = none := rfl
@[simp] theorem endCode_imp (f : FnName) (a : List Val) (r : Option (List Val)) :
    endCode cliRun (some Versions.P2.cliExit) (.imp f a r) = none := rfl
@[simp] theorem endCode_get :
    endCode cliRun (some Versions.P2.cliExit) (.req getStdout []) = none := rfl
@[simp] theorem endCode_write (hd : BitVec 32) :
    endCode cliRun (some Versions.P2.cliExit) (.req streamWrite [.u32 hd, bytesV hiBytes]) =
      none := rfl

theorem endCode_drop (hd : BitVec 32) :
    endCode cliRun (some Versions.P2.cliExit) (.req streamDrop [.u32 hd]) = none := by
  simp [endCode, streamDrop_ne_cliExit]

theorem endCode_ret (a : List Val) :
    endCode cliRun (some Versions.P2.cliExit) (.ret cliRun a (some [okV none])) = some 0 := by
  simp only [endCode, ↓reduceIte, Option.some.injEq]
  decide

/-! ## The view of each prefix -/

/-- The bytes of `hi` in the model. -/
def hiOut : Bytes := [0x68, 0x69]

theorem toBytes_hiBytes : toBytes hiBytes = hiOut := by decide

/-- What the view shows `k` events into a run whose write succeeded (`ok`) or not, on `i`. -/
def seenAt (i : Input) (ok : Bool) (k : Nat) : Silmaril.Cli.Seen where
  stdout := if ok ∧ 5 ≤ k then hiOut else []
  exit := if k = 8 then some 0 else none
  fs := some i.fs
  refused := !ok && decide (5 ≤ k)

/-- The view of a prefix, from the events it contains. -/
theorem p2View_take_eq (i : Input) (a : List Val) (hd : BitVec 32) (r r' : Option (List Val))
    (k : Nat) :
    p2View.seen i ((full a hd r r').take k) =
      { stdout := toBytes ((((full a hd r r').take k).filterMap write2).flatMap Prod.snd)
        exit := ((full a hd r r').take k).findSome? (endCode cliRun (some Versions.P2.cliExit))
        fs := some i.fs
        refused := ((full a hd r r').take k).any failedWrite2 } := by
  have hn := errHandles_full a hd r r' k
  have hin := inHandles_full a hd r r' k
  have hf := fileEffs_full a hd r r' k
  simp [View.seen, p2View, written2, stdin2, hn, hin, hf, exitOf, toBytes, applyWrites]

/-- **The view of a run whose write succeeded.** -/
theorem p2View_ok (i : Input) (a : List Val) (hd : BitVec 32) (r' : Option (List Val)) {k : Nat}
    (hk : k ≤ 8) : p2View.seen i ((full a hd okAns r').take k) = seenAt i true k := by
  rw [p2View_take_eq]
  have hw := write2_ok hd
  have hf := failedWrite2_ok hd
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals
    simp [full, seenAt, hw, hf, write2_dropped, failedWrite2_dropped, failedWrite2_got,
      endCode_drop, endCode_ret, toBytes, List.filterMap_cons, List.findSome?_cons]
  all_goals exact toBytes_hiBytes

/-- **The view of a run whose write was refused.** -/
theorem p2View_fail (i : Input) (a : List Val) (hd : BitVec 32) {r : Option (List Val)}
    (r' : Option (List Val)) (hr : r ≠ okAns) {k : Nat} (hk : k ≤ 8) :
    p2View.seen i ((full a hd r r').take k) = seenAt i false k := by
  rw [p2View_take_eq]
  have hw := write2_fail (hd := hd) hr
  have hf := failedWrite2_fail (hd := hd) hr
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals
    simp [full, seenAt, hw, hf, write2_dropped, failedWrite2_dropped, failedWrite2_got,
      endCode_drop, endCode_ret, toBytes, List.filterMap_cons, List.findSome?_cons]

/-! ## Each view is allowed -/

/-- The run `hiSpec` allows. -/
def hiRun (i : Input) : Obs := { stdout := hiOut, fs := i.fs }

/-- A run whose write was refused: nothing printed, exit `0`. -/
def refusedRun (i : Input) : Obs := { fs := i.fs, refused := true }

theorem hiSpec_hiRun (i : Input) : Silmaril.Wasi.Cli.hiSpec i (hiRun i) :=
  ⟨rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, rfl⟩

/-- **Ignoring a refused write is allowed by `orRefused`.** -/
theorem orRefused_refusedRun (i : Input) :
    Spec.orRefused Silmaril.Wasi.Cli.hiSpec i (refusedRun i) :=
  .inr ⟨rfl, hiRun i, hiSpec_hiRun i, List.nil_prefix, .inl rfl⟩

/-- **Every view of a run of `hello` is a partial view of an allowed run.** -/
theorem partial_seenAt (i : Input) (ok : Bool) (k : Nat) :
    (Spec.orRefused Silmaril.Wasi.Cli.hiSpec).Partial i (seenAt i ok k) := by
  cases ok
  · refine ⟨refusedRun i, orRefused_refusedRun i, ?_, List.nil_prefix, Nat.zero_le _,
      fun _ h => absurd h List.not_mem_nil, fun _ => rfl, fun c hc => ?_⟩
    · simp [seenAt]
    · by_cases h8 : k = 8 <;> simp_all [seenAt, refusedRun]
  · refine ⟨hiRun i, Spec.le_orRefused _ _ _ (hiSpec_hiRun i), ?_, List.nil_prefix,
      Nat.zero_le _, fun _ h => absurd h List.not_mem_nil, fun h => absurd h (by simp [seenAt]),
      fun c hc => ?_⟩
    · by_cases h5 : 5 ≤ k <;> simp [seenAt, hiRun, h5]
    · by_cases h8 : k = 8 <;> simp_all [seenAt, hiRun]

/-! ## Where a play of `hello` is -/

/-- The `run` call of `stdoutWorld`. -/
def runOp : (nsig stdoutWorld.exports).Op := (⟨cliRun, rfl⟩, [])

theorem helloAt_nil : HelloAt [] .idle :=
  .inr ⟨runOp, 0, none, none, 0, rfl, by omega, rfl, rfl⟩

/-- A second call of `run` keeps the play out of the one-run case. -/
theorem calls_append_le (t : List WEv) (e : WEv) : calls cliRun t ≤ calls cliRun (t ++ [e]) := by
  unfold calls
  rw [List.countP_append]
  omega

/-- An answer the typing theory accepts on its own. -/
theorem stdoutOk_of_accepts {e : WEv} (h : stdoutTyped.Accepts (hostView [e])) :
    stdoutOk e = true := by
  have h' : ∀ e' ∈ hostView [e], stdoutOk e' = true := (pointwise_accepts_iff stdoutOk _).1 h
  cases e with
  | imp f a n => exact h' _ (by simp [hostView, WEv.isImp])
  | req => rfl
  | call => rfl
  | ret => rfl

/-- The typing theory: `get-stdout` answers a handle. -/
theorem got_handle {n : Option (List Val)} (h : stdoutOk (.imp getStdout [] n) = true) :
    ∃ hd, n = some [.u32 hd] := by
  simp only [stdoutOk, ↓reduceIte] at h
  split at h
  · exact ⟨_, rfl⟩
  · exact absurd h (by simp)

/-- The membership of an export call. -/
theorem op_cliRun (q : (nsig stdoutWorld.exports).Op) : q.1.1 = cliRun := q.1.2

/-- The steps from the idle states. -/
theorem helloAt_idle {t : List WEv} {o : Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports)}
    {c' : CSt stdoutWorld.imports stdoutWorld.exports} (hc : CStep hello .idle o c')
    (ht : t = [] ∨ 1 ≤ calls cliRun t) : HelloAt (t ++ [wev o]) c' := by
  obtain ⟨q, rfl, rfl⟩ := hc.idle_inv
  have hcall : wev (I := stdoutWorld.imports) (.inr (.ask q)) = .call cliRun q.2 := by
    simp only [wev, op_cliRun]
  rcases ht with rfl | h1
  · exact .inr ⟨q, 0, none, none, 1, op_cliRun q, by omega, by rw [hcall]; rfl, rfl⟩
  · refine .inl ?_
    have h2 : calls cliRun [wev (I := stdoutWorld.imports) (.inr (.ask q))] = 1 := by
      rw [hcall]; simp [calls]
    unfold calls at h1 h2 ⊢
    rw [List.countP_append]
    omega

section Steps

variable {q : (nsig stdoutWorld.exports).Op} {hd : BitVec 32} {r r' : Option (List Val)}
  {o : Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports)}
  {c' : CSt stdoutWorld.imports stdoutWorld.exports}

theorem helloAt_1 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 1) o c') :
    HelloAt ((full q.2 hd r r').take 1 ++ [wev o]) c' := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := getOp) (k := helloK1) hc
  exact .inr ⟨q, hd, r, r', 2, hq, by omega, rfl, rfl⟩

theorem helloAt_2 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 2) o c')
    (hok : stdoutOk (wev o) = true) : HelloAt ((full q.2 hd r r').take 2 ++ [wev o]) c' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  obtain ⟨hd', rfl⟩ := got_handle hok
  exact .inr ⟨q, hd', r, r', 3, hq, by omega, rfl, rfl⟩

theorem helloAt_3 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 3) o c') :
    HelloAt ((full q.2 hd r r').take 3 ++ [wev o]) c' := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := writeOp hd) (k := helloK2 hd) hc
  exact .inr ⟨q, hd, r, r', 4, hq, by omega, rfl, rfl⟩

theorem helloAt_4 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 4) o c') :
    HelloAt ((full q.2 hd r r').take 4 ++ [wev o]) c' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  exact .inr ⟨q, hd, n, r', 5, hq, by omega, rfl, rfl⟩

theorem helloAt_5 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 5) o c') :
    HelloAt ((full q.2 hd r r').take 5 ++ [wev o]) c' := by
  obtain ⟨rfl, rfl⟩ := CStep.call_inv (m := dropOp hd) (k := helloK3) hc
  exact .inr ⟨q, hd, r, r', 6, hq, by omega, rfl, rfl⟩

theorem helloAt_6 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 6) o c') :
    HelloAt ((full q.2 hd r r').take 6 ++ [wev o]) c' := by
  obtain ⟨n, rfl, rfl⟩ := hc.wait_inv
  exact .inr ⟨q, hd, r, n, 7, hq, by omega, rfl, rfl⟩

theorem helloAt_7 (hq : q.1.1 = cliRun) (hc : CStep hello (stAt q hd r r' 7) o c') :
    HelloAt ((full q.2 hd r r').take 7 ++ [wev o]) c' := by
  obtain ⟨rfl, rfl⟩ := CStep.pure_inv (r := some [okV none]) hc
  refine .inr ⟨q, hd, r, r', 8, hq, by omega, ?_, rfl⟩
  simp only [full, wev, hq]; rfl

/-- One step from `k` events into a run. -/
theorem helloAt_run (hq : q.1.1 = cliRun) {k : Nat} (hk : k ≤ 8)
    (hc : CStep hello (stAt q hd r r' k) o c') (hok : stdoutOk (wev o) = true) :
    HelloAt ((full q.2 hd r r').take k ++ [wev o]) c' :=
  match k, hk with
  | 0, _ => helloAt_idle hc (.inl rfl)
  | 1, _ => helloAt_1 hq hc
  | 2, _ => helloAt_2 hq hc hok
  | 3, _ => helloAt_3 hq hc
  | 4, _ => helloAt_4 hq hc
  | 5, _ => helloAt_5 hq hc
  | 6, _ => helloAt_6 hq hc
  | 7, _ => helloAt_7 hq hc
  | 8, _ => helloAt_idle hc (.inr (by simp [full, calls]))

end Steps

/-- **One step of `hello`** keeps it in one of the places of `HelloAt`. -/
theorem helloAt_step {t : List WEv} {c c' : CSt stdoutWorld.imports stdoutWorld.exports}
    {o : Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports)} (h : HelloAt t c)
    (hc : CStep hello c o c') (hok : stdoutOk (wev o) = true) : HelloAt (t ++ [wev o]) c' := by
  rcases h with h2 | ⟨q, hd, r, r', k, hq, hk, rfl, rfl⟩
  · exact .inl (h2.trans (calls_append_le _ _))
  · exact helloAt_run hq hk hc hok

/-- **Every reachable play of `hello` against a typed host is in `HelloAt`.** -/
theorem helloAt_reach {s : List (Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports))}
    {c : CSt stdoutWorld.imports stdoutWorld.exports} (hs : Reach hello s c)
    (hA : stdoutTyped.Accepts (hostView (wtrace s))) : HelloAt (wtrace s) c := by
  induction hs with
  | nil => exact helloAt_nil
  | @snoc s c c' o _ hc ih =>
    have hall : ∀ e ∈ hostView (wtrace s) ++ hostView [wev o], stdoutOk e = true := by
      rw [← hostView_append, ← wtrace_concat]; exact (pointwise_accepts_iff stdoutOk _).1 hA
    have hA' : stdoutTyped.Accepts (hostView (wtrace s)) :=
      (pointwise_accepts_iff stdoutOk _).2 fun e he => hall e (List.mem_append_left _ he)
    have hok : stdoutOk (wev o) = true :=
      stdoutOk_of_accepts ((pointwise_accepts_iff stdoutOk _).2 fun e he =>
        hall e (List.mem_append_right _ he))
    rw [wtrace_concat]
    exact helloAt_step (ih hA') hc hok

/-- **The view of every play of `hello` with one run is allowed by `orRefused hiSpec`.** -/
theorem hello_partial (i : Input)
    {s : List (Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports))}
    {c : CSt stdoutWorld.imports stdoutWorld.exports} (hs : Reach hello s c)
    (hA : stdoutTyped.Accepts (hostView (wtrace s))) (h1 : calls cliRun (wtrace s) ≤ 1) :
    (Spec.orRefused Silmaril.Wasi.Cli.hiSpec).Partial i (p2View.seen i (wtrace s)) := by
  rcases helloAt_reach hs hA with h2 | ⟨q, hd, r, r', k, -, hk, ht, -⟩
  · omega
  · rw [ht]
    by_cases hr : r = okAns
    · rw [hr, p2View_ok i _ _ _ hk]; exact partial_seenAt i true k
    · rw [p2View_fail i _ _ _ hr hk]; exact partial_seenAt i false k

/-! ## A refused write: `orRefused` is needed -/

/-- A typed error answer of the write. -/
def failAns : Option (List Val) := some [errV (some (.variant 0 none))]

/-- The moves of a run of `hello` whose write is refused. -/
def failMoves : List (Move (nsig stdoutWorld.imports) (nsig stdoutWorld.exports)) :=
  [] ++ [.inr (.ask runOp)] ++ [.inl (.ask getOp)] ++ [.inl (.ans getOp (some [.u32 0]))] ++
    [.inl (.ask (writeOp 0))] ++ [.inl (.ans (writeOp 0) failAns)] ++ [.inl (.ask (dropOp 0))] ++
    [.inl (.ans (dropOp 0) (some []))] ++ [.inr (.ans runOp (some [okV none]))]

/-- It is a play of `hello`. -/
theorem failMoves_reach : Reach hello failMoves .idle :=
  ((((((((Reach.nil.snoc (.ask runOp)).snoc (.call _ _ _)).snoc (.reply _ _ _ _)).snoc
    (.call _ _ _)).snoc (.reply _ _ _ _)).snoc (.call _ _ _)).snoc (.reply _ _ _ _)).snoc
    (.ret _ _))

/-- Its events are a full run with a refused write. -/
theorem failMoves_wtrace : wtrace failMoves = (full [] 0 failAns (some [])).take 8 := rfl

/-- A typed host can answer it. -/
theorem failMoves_typed : stdoutTyped.Accepts (hostView (wtrace failMoves)) :=
  (pointwise_accepts_iff stdoutOk _).2 (by rw [failMoves_wtrace]; decide)

/-- **`hello` does not meet `orFail hiSpec`**: after a refused write it prints nothing and
exits `0`. -/
theorem hello_not_orFail_partial (i : Input) :
    ¬ (Spec.orFail Silmaril.Wasi.Cli.hiSpec).Partial i (p2View.seen i (wtrace failMoves)) := by
  intro h
  have hv : p2View.seen i (wtrace failMoves) = seenAt i false 8 := by
    rw [failMoves_wtrace]; exact p2View_fail i _ _ _ (by simp [failAns, okAns, errV]) (by omega)
  rw [hv] at h
  obtain ⟨o, ho, hs, -, hx, -⟩ := h.ended (c := 0) rfl
  have hhi : Silmaril.Wasi.Cli.hiSpec i o := Spec.orFail_inf_succeeds _ i o ⟨ho, hx⟩
  have hout : o.stdout = hiOut := hhi.1
  rw [hs] at hout
  exact absurd hout (by simp [seenAt, hiOut])

end Silmaril.Wasi.Cli.Refusal
