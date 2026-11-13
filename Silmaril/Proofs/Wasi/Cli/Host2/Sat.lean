module

public import Silmaril.Proofs.Wasi.Cli.Host2.Put

/-!
# The WASI 0.2 host: printing a line is read as printing it

Proofs for `Silmaril.Wasi.Cli.Host2.Thms`: **`emit2_ok`** (`Api.EmitOk` for `api2`, `cliTh2`,
`p2View` and `spec2`). A play of the component that prints a line is the export call, quiet
events (`get-arguments`, `get-environment`), a run of `api2.put` (`PutFacts`) and possibly the
return; `allows_put` reads it through `p2View` (`obs2_plain`): the bytes written so far are a
prefix of the line's, on its channel only; a finished run either wrote it all and exits with
`0`/`1` as `k` says, or exits with `1`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host2

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)

/-! ## Bytes -/

theorem flatten_chunk4096 {α : Type} : ∀ l : List α, (chunk4096 l).flatten = l
  | [] => by rw [chunk4096]; rfl
  | a :: l => by
    rw [chunk4096, List.flatten_cons, flatten_chunk4096 ((a :: l).drop 4096)]
    exact List.take_append_drop _ _
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

theorem toBytes_toWasm (b : Bytes) : toBytes (toWasm b) = b := by
  simp [toBytes, toWasm, Function.comp_def]

/-- The bytes of the first `j` chunks are a prefix of `b`. -/
theorem written_prefix (b : Bytes) (j : Nat) :
    toBytes ((chunk4096 (toWasm b)).take j).flatten <+: b := by
  have h : ((chunk4096 (toWasm b)).take j).flatten <+: toWasm b := by
    conv => rhs; rw [← flatten_chunk4096 (toWasm b), ← List.take_append_drop j (chunk4096 _)]
    rw [List.flatten_append]; exact List.prefix_append _ _
  simpa [toBytes_toWasm] using toBytes_prefix h

/-! ## The specification -/

/-- The observation of printing the line `s` on `ch` and exiting with `k`. -/
abbrev lineObs (i : Input) (ch : Channel) (s : String) (k : ExitCode) : Obs :=
  { Beh.lineObs i (some (ch, s)) with exit := k }

theorem lineObs_stdout (i : Input) (ch : Channel) (s : String) (k : ExitCode) :
    (lineObs i ch s k).stdout = if decide (ch = .stderr) = false then utf8 (s ++ "\n") else [] := by
  cases ch <;> rfl

theorem lineObs_stderr (i : Input) (ch : Channel) (s : String) (k : ExitCode) :
    (lineObs i ch s k).stderr = if decide (ch = .stderr) = true then utf8 (s ++ "\n") else [] := by
  cases ch <;> rfl

/-- **What `spec2 (lineSpec ch s k)` allows**: a stdout that is a prefix of the line's and,
once finished, the line with the exit code read as `0`/`1`, or a failure. -/
theorem allows_spec2 {i : Input} {ch : Channel} {s : String} {k : ExitCode} {T : List WEv}
    (hout : p2View.stdout T <+: (lineObs i ch s k).stdout)
    (hd : (p2View.code T).isSome = true →
      p2View.obs i T = { lineObs i ch s k with exit := if k = 0 then 0 else 1 } ∨
        (p2View.obs i T).exit ≠ 0) :
    (spec2 (lineSpec ch s k)).Partial i (p2View.seen i T) := by
  have hS : exit01 (lineSpec ch s k) i { lineObs i ch s k with exit := if k = 0 then 0 else 1 } :=
    ⟨lineObs i ch s k, rfl, rfl⟩
  refine View.partial_orFail hS hout fun hdn => ?_
  rcases hd hdn with heq | hx
  · exact .inl (heq ▸ hS)
  · exact .inr hx

/-! ## Reading the trace -/

/-- The code of the return of `run` with the `finish` of `api2`. -/
def fin2 (k : UInt32) : Val := if k.toUInt8 = 0 then okV none else errV none

theorem retCode_fin2 (k : UInt32) :
    retCode (some [fin2 k]) = if k.toUInt8 = 0 then 0 else 1 := by
  unfold fin2
  split <;> rfl

theorem quiet_list {l : List WEv} (hq : ∀ e ∈ l, Quiet e) :
    l.filterMap write2 = [] ∧ handles Versions.P2.getStderr l = [] ∧
      l.findSome? (endCode cliRun (some Versions.P2.cliExit)) = none ∧
      l.any failedWrite2 = false := by
  refine ⟨List.filterMap_eq_nil_iff.2 fun e he => (hq e he).2.1,
    List.filterMap_eq_nil_iff.2 fun e he => ?_, List.findSome?_eq_none_iff.2 fun e he =>
      (hq e he).2.2.2.1, List.any_eq_false.2 fun e he => by simp [(hq e he).2.2.2.2]⟩
  exact List.filterMap_eq_nil_iff.1 (hq e he).2.2.1 e (by simp)

/-- The tail after the writes: nothing, or the return of `run`. -/
def TailOk (q : (nsig ({cliRun} : Set FnName)).Op) (k : UInt32) (ro : Option Bool)
    (tail : List WEv) : Prop :=
  tail = [] ∨ ∃ ok, ro = some ok ∧ tail = [.ret q.1.1 q.2 (some [fin2 (if ok then k else 1)])]

theorem tail_facts {q : (nsig ({cliRun} : Set FnName)).Op} {k : UInt32} {ro : Option Bool}
    {tail : List WEv} (ht : TailOk q k ro tail) :
    (∀ e ∈ tail, PlainEv e) ∧ tail.filterMap write2 = [] ∧
      handles Versions.P2.getStderr tail = [] ∧ tail.any failedWrite2 = false := by
  rcases ht with rfl | ⟨ok, -, rfl⟩
  · exact ⟨fun e he => absurd he List.not_mem_nil, rfl, rfl, rfl⟩
  · exact ⟨fun e he => List.mem_singleton.1 he ▸ plainEv_ret _ _ _, rfl, rfl, rfl⟩

/-- The written bytes on one channel. -/
theorem written2_eq {t : List WEv} {cs : List (List (BitVec 8))} {ch : Channel} {h : BitVec 32}
    {j : Nat} (hW : t.filterMap write2 = (cs.take j).map (h, ·))
    (hH : j = 0 ∨ handles Versions.P2.getStderr t = if ch = .stderr then [h] else [])
    (err : Bool) :
    written2 err t = if decide (ch = .stderr) = err then (cs.take j).flatten else [] := by
  unfold written2
  rw [hW]
  rcases hH with rfl | hH
  · simp
  · rw [hH, List.flatMap_map]
    cases ch <;> cases err <;> simp [List.flatMap_id']


/-- The whole trace, event classes. -/
theorem trace_facts {ch : Channel} {cs : List (List (BitVec 8))} {k : UInt32}
    {q : (nsig ({cliRun} : Set FnName)).Op} {pre v tail : List WEv} {ro : Option Bool}
    (hq : ∀ e ∈ pre, Quiet e) (hP : PutFacts ch cs v ro) (htail : TailOk q k ro tail) :
    let T := .call q.1.1 q.2 :: (pre ++ v ++ tail)
    (∀ e ∈ T, PlainEv e) ∧
      (∃ h j, T.filterMap write2 = (cs.take j).map (h, ·) ∧
        (j = 0 ∨ handles Versions.P2.getStderr T = if ch = .stderr then [h] else []) ∧
        (ro = some true → j = cs.length ∧ v.any failedWrite2 = false)) ∧
      exitOf cliRun (some Versions.P2.cliExit) T =
        tail.findSome? (endCode cliRun (some Versions.P2.cliExit)) ∧
      T.any failedWrite2 = v.any failedWrite2 := by
  intro T
  have hq' : ∀ e ∈ WEv.call q.1.1 q.2 :: pre, Quiet e := fun e he =>
    (List.mem_cons.1 he).elim (fun h => h ▸ quiet_call _ _) (hq e)
  obtain ⟨hWp, hHp, hCp, hFp⟩ := quiet_list hq'
  obtain ⟨hpt, hWt, hHt, hFt⟩ := tail_facts htail
  obtain ⟨h, j, hj, hH, hdone⟩ := hP.written
  have hT : T = (WEv.call q.1.1 q.2 :: pre) ++ v ++ tail := rfl
  refine ⟨fun e he => ?_, ⟨h, j, ?_, ?_, hdone⟩, ?_, ?_⟩
  · rw [hT, List.mem_append, List.mem_append] at he
    rcases he with (he | he) | he
    exacts [(hq' e he).1, hP.plain e he, hpt e he]
  · rw [hT, List.filterMap_append, List.filterMap_append, hWp, hWt, hj]; simp
  · rcases hH with rfl | hH
    · exact .inl rfl
    · right; rw [hT, handles_append, handles_append, hHp, hHt, hH]; simp
  · have hCv : v.findSome? (endCode cliRun (some Versions.P2.cliExit)) = none :=
      List.findSome?_eq_none_iff.2 hP.code
    rw [exitOf, hT, List.findSome?_append, List.findSome?_append, hCp, hCv]; simp
  · rw [hT, List.any_append, List.any_append, hFp, hFt]; simp


/-- The observation `p2View` makes of a plain trace (`obs2_plain`). -/
abbrev obs2 (i : Input) (T : List WEv) : Obs :=
  { stdout := toBytes (written2 false T), stderr := toBytes (written2 true T),
    exit := (exitOf cliRun (some Versions.P2.cliExit) T).getD 0, fs := i.fs,
    refused := T.any failedWrite2 }

/-- **A finished run**: the whole line with the code read as `0`/`1`, or a failure. -/
theorem done_case {i : Input} {ch : Channel} {s : String} {k : UInt32}
    {q : (nsig ({cliRun} : Set FnName)).Op} {T v tail : List WEv} {ro : Option Bool}
    {h : BitVec 32} {j : Nat}
    (hW : T.filterMap write2 = ((chunk4096 (toWasm (utf8 (s ++ "\n")))).take j).map (h, ·))
    (hH : j = 0 ∨ handles Versions.P2.getStderr T = if ch = .stderr then [h] else [])
    (hdone : ro = some true →
      j = (chunk4096 (toWasm (utf8 (s ++ "\n")))).length ∧ v.any failedWrite2 = false)
    (hC : exitOf cliRun (some Versions.P2.cliExit) T =
      tail.findSome? (endCode cliRun (some Versions.P2.cliExit)))
    (hF : T.any failedWrite2 = v.any failedWrite2)
    (hd : (exitOf cliRun (some Versions.P2.cliExit) T).isSome = true)
    (htail : TailOk q k ro tail) :
    obs2 i T = { lineObs i ch s k.toUInt8 with exit := if k.toUInt8 = 0 then 0 else 1 } ∨
      (obs2 i T).exit ≠ 0 := by
  rcases htail with rfl | ⟨ok, rfl, rfl⟩
  · exact absurd (hC ▸ hd) (by simp)
  have hq1 : q.1.1 = cliRun := q.1.2
  have hC' : exitOf cliRun (some Versions.P2.cliExit) T =
      some (if (if ok then k else 1).toUInt8 = 0 then 0 else 1) := by
    rw [hC]; simp [hq1, endCode_ret, retCode_fin2]
  cases ok
  · exact .inr (by simp [hC'])
  · obtain ⟨hl, hfa⟩ := hdone rfl
    have hw := written2_eq hW hH
    left
    cases ch <;> simp [obs2, hw, hl, flatten_chunk4096, hC', hF, hfa, Beh.lineObs, toBytes, toWasm,
      Function.comp_def]

/-- **A play of the printing component, read through `p2View`.** -/
theorem allows_put {i : Input} {ch : Channel} {s : String} {k : UInt32}
    {q : (nsig ({cliRun} : Set FnName)).Op} {pre v tail : List WEv} {ro : Option Bool}
    (hq : ∀ e ∈ pre, Quiet e) (hP : PutFacts ch (chunk4096 (toWasm (utf8 (s ++ "\n")))) v ro)
    (htail : TailOk q k ro tail) :
    (spec2 (lineSpec ch s k.toUInt8)).Partial i
      (p2View.seen i (.call q.1.1 q.2 :: (pre ++ v ++ tail))) := by
  obtain ⟨hplain, ⟨h, j, hW, hH, hdone⟩, hC, hF⟩ := trace_facts hq hP htail
  have hw := written2_eq hW hH
  refine allows_spec2 ?_ fun hd => ?_
  · show toBytes (written2 false _) <+: _
    rw [hw, lineObs_stdout]; split
    · exact written_prefix _ _
    · exact List.nil_prefix
  · rw [obs2_plain i hplain]
    exact done_case hW hH hdone hC hF hd htail


/-- Nothing seen yet. -/
theorem allows_nil2 (i : Input) (ch : Channel) (s : String) (k : ExitCode) :
    (spec2 (lineSpec ch s k)).Partial i (p2View.seen i []) :=
  allows_spec2 List.nil_prefix (fun h => absurd h (by simp [p2View, exitOf]))

/-- The decided program of a printing component, as a sequence. -/
theorem after_putLine (vs : List String) (ch : Channel) (s : String) (k : UInt32) :
    api2.after vs (api2.putLine ch s >>= fun _ => pure k) =
      api2.args.bind fun _ => api2.env.bind fun _ =>
        (api2.put ch (utf8 (s ++ "\n"))).bind fun ok => .pure (some [fin2 (if ok then k else 1)]) := by
  rw [Api.after_eq, Api.close_putLine]; rfl

/-- The trace of a run of the printing component, regrouped. -/
theorem runTrace_eq (q : (nsig ({cliRun} : Set FnName)).Op) (pre v : List WEv)
    (r : Option (Option (List Val))) :
    runTrace q (pre ++ (v ++ [])) r = .call q.1.1 q.2 :: (pre ++ v ++ retEv q r) := by
  simp [runTrace]

/-- **Printing a line is read as printing it** (WASI 0.2): `Api.EmitOk` for `api2`. -/
theorem emit2_ok : api2.EmitOk cliTh2 p2View spec2 {cliRun} := by
  intro i vs ch s k sp hs hA h1
  rcases plays_run (f := cliRun) (fun q => q.1.2) hs h1 with h0 | ⟨q, u, r, hr, ht⟩
  · rw [h0]; exact allows_nil2 i ch s _
  have hr' := hr
  rw [Api.bodyAfter, after_putLine] at hr'
  rw [ht]
  rcases prefix_quiet hr' with ⟨hq, rfl⟩ | ⟨pre, u', rfl, hq, hQ⟩
  · have hP : PutFacts ch (chunk4096 (toWasm (utf8 (s ++ "\n")))) [] none :=
      putFacts_get none List.nil_prefix (by simp)
    simpa [runTrace, retEv] using allows_put (k := k) (q := q) (tail := []) hq hP (.inl rfl)
  rcases PRun.bind_inv hQ with ⟨hp, rfl⟩ | ⟨v, v', ok, rfl, hp, hf⟩
  · simpa [runTrace, retEv] using allows_put (k := k) (q := q) (tail := []) hq (put_facts hp)
      (.inl rfl)
  have hf' : PRun (I := I2) (.pure (some [fin2 (if ok then k else 1)])) v' r := hf
  obtain ⟨rfl, hr0⟩ := PRun.pure_inv hf'
  rw [runTrace_eq]
  rcases hr0 with rfl | rfl
  · exact allows_put (k := k) hq (put_facts hp) (.inl rfl)
  · exact allows_put (k := k) hq (put_facts hp) (.inr ⟨ok, rfl, rfl⟩)

end Silmaril.Wasi.Cli.Host2

end
