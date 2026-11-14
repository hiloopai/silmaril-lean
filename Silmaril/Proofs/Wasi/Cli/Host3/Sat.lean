module

public import Silmaril.Proofs.Wasi.Cli.Host3.Put
public import Silmaril.Wasi.Cli.Host2.Thms

/-!
# The WASI 0.3 host: the theory pins the front end, and printing is read as printing

Proofs for `Silmaril.Wasi.Cli.Host3.Thms`: `args3_ok`, `env3_ok` (`cliTh3` pins
`get-arguments` and `get-environment`) and **`emit3_ok`** (`Api.EmitOk` for `api3`, `cliTh3`,
`p3CliView` and `orFail`): a play of the component that prints a line is the export call,
quiet events, a run of `put3` (`put3_facts`) and of `finish3` (`FinOk`), and `allows_put3`
reads it through `p3CliView`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasi.Cli.Host3

open Silmaril.Cli Silmaril.Wasi Silmaril.Wasi.Cli Silmaril.Games
open Silmaril.Wasm.Component (Val)
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions.P3 (natOf run3)
open Silmaril.Wasi.Cli.Host2 (u32Of toWasm lineObs lineObs_stdout lineObs_stderr toBytes_toWasm)

/-! ## Before the decision -/

theorem quiet_env_fn {f : FnName} (hk : k3 f = .other) (h1 : f ≠ Versions.P3.stdoutWrite3)
    (h2 : f ≠ W3.stderrWrite) (h3 : f ≠ W3.writeVia) (h4 : f ≠ exit3) (h5 : f ≠ W3.exitCode)
    {β : Type} {hf : f ∈ I3} {g : Option (List Val) → β} {t : List WEv} {r : Option β}
    (h : PRun ((callI f hf []).bind fun n => .pure (g n)) t r) : ∀ e ∈ t, Quiet3 e := by
  have h0 : PRun (.call (⟨f, hf⟩, []) fun n => .pure (g n)) t r := h
  rcases call_cases h0 with ⟨hv, -⟩ | ⟨n, v', rfl, h'⟩
  · exact fun e he => (List.mem_singleton.1 (hv.mem he)) ▸ quiet3_req [] h4 h5
  · have hv' : v' = [] := (PRun.pure_inv h').1
    subst hv'
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil, or_false]
    rintro e (rfl | rfl)
    exacts [quiet3_req [] h4 h5, quiet3_imp' [] n hk h1 h2 h3]

theorem args3_quiet {t : List WEv} {r : Option (Option (List String))} (h : PRun api3.args t r) :
    ∀ e ∈ t, Quiet3 e :=
  quiet_env_fn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h

theorem env3_quiet {t : List WEv} {r : Option (List (String × String))} (h : PRun api3.env t r) :
    ∀ e ∈ t, Quiet3 e :=
  quiet_env_fn (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h

/-- Before the front end's decision, nothing is seen. -/
theorem prefix_quiet3 {Q : BProg I3} {u : List WEv} {r : Option (Option (List Val))}
    (h : PRun (api3.args.bind fun _ => api3.env.bind fun _ => Q) u r) :
    ((∀ e ∈ u, Quiet3 e) ∧ r = none) ∨
      ∃ pre u', u = pre ++ u' ∧ (∀ e ∈ pre, Quiet3 e) ∧ PRun Q u' r := by
  rcases PRun.bind_inv h with ⟨h1, rfl⟩ | ⟨t₁, t₂, a, rfl, h1, h2⟩
  · exact .inl ⟨args3_quiet h1, rfl⟩
  have hq₁ : ∀ e ∈ t₁, Quiet3 e := args3_quiet h1
  rcases PRun.bind_inv h2 with ⟨h3, rfl⟩ | ⟨t₃, t₄, e, rfl, h3, h4⟩
  · refine .inl ⟨fun e he => ?_, rfl⟩
    rcases List.mem_append.1 he with he | he
    exacts [hq₁ e he, env3_quiet h3 e he]
  · refine .inr ⟨t₁ ++ t₃, t₄, (List.append_assoc _ _ _).symm, fun e he => ?_, h4⟩
    rcases List.mem_append.1 he with he | he
    exacts [hq₁ e he, env3_quiet h3 e he]

/-! ## The theory -/

theorem run_call_done3 {β : Type} {f : FnName} {hf : f ∈ I3} {g : Option (List Val) → β}
    {t : List WEv} {b : β} (h : PRun ((callI f hf []).bind fun n => .pure (g n)) t (some b)) :
    ∃ n, t = [.req f [], .imp f [] n] ∧ b = g n := by
  have h0 : PRun (.call (⟨f, hf⟩, []) fun n => .pure (g n)) t (some b) := h
  rcases PRun.call_inv h0 with ⟨-, h'⟩ | ⟨-, h'⟩ | ⟨n, t', rfl, h'⟩
  · exact absurd h' (by simp)
  · exact absurd h' (by simp)
  · obtain ⟨rfl, hb⟩ := PRun.pure_inv h'
    exact ⟨n, rfl, by simpa using hb⟩

theorem cliTh3_point {i : Input} {t : List WEv} (h : (cliTh3 i).Accepts t) {e : WEv}
    (he : e ∈ t) :
    (argsOk W3.getArgs i e && envOk W3.getEnv i e && preopensOk Versions.P3.getDirs3 i e) =
      true :=
  (pointwise_accepts_iff _ _).1 h e he

/-- **`cliTh3` pins `get-arguments`.** -/
theorem args3_ok : api3.ArgsOk cliTh3 := by
  intro i t a h hA
  obtain ⟨n, rfl, rfl⟩ := run_call_done3 h
  have hp := cliTh3_point hA (e := .imp W3.getArgs [] n) (by simp [hostView, WEv.isImp])
  have hargs : argsOk W3.getArgs i (.imp W3.getArgs [] n) = true := by
    simp only [Bool.and_eq_true] at hp; exact hp.1.1
  simpa [argsOk, Input.argv] using hargs

/-- **`cliTh3` pins `get-environment`.** -/
theorem env3_ok : api3.EnvOk cliTh3 := by
  intro i pre t e h hA
  obtain ⟨n, rfl, rfl⟩ := run_call_done3 h
  have hp := cliTh3_point hA (e := .imp W3.getEnv [] n) (by simp [hostView, WEv.isImp])
  have henv : envOk W3.getEnv i (.imp W3.getEnv [] n) = true := by
    simp only [Bool.and_eq_true] at hp; exact hp.1.2
  have hn : envOf n = some i.env := by simpa [envOk] using henv
  simp [hn]

/-! ## The specification -/

/-- **What `orFail (lineSpec ch s k)` allows.** -/
theorem allows_spec3 {i : Input} {ch : Channel} {s : String} {k : ExitCode} {T : List WEv}
    (hout : p3CliView.stdout T <+: (lineObs i ch s k).stdout)
    (hd : (p3CliView.code T).isSome = true →
      p3CliView.obs i T = lineObs i ch s k ∨ (p3CliView.obs i T).exit ≠ 0) :
    (Spec.orFail (lineSpec ch s k)).Partial i (p3CliView.seen i T) :=
  View.partial_orFail (rfl : lineSpec ch s k i (lineObs i ch s k)) hout hd

/-! ## Reading the trace -/

/-- The run of `finish3` and the return: no output, and the exit code, if any, is the code
`finish3` was given. -/
def FinOk (k : UInt32) (ro : Option Bool) (fin : List WEv) : Prop :=
  (∀ e ∈ fin, ∀ q : Sc3, q.step e = (q, [])) ∧
    (fin.findSome? endCode3 = none ∨
      ∃ ok, ro = some ok ∧ fin.findSome? endCode3 = some (if ok then k else 1).toUInt8)

/-- What a plain-sink output list shows. -/
theorem outOk_view {k : Sink} {bs : List (BitVec 8)} {O : List Out3} (h : OutOk k bs O) :
    ∃ x, x <+: bs ∧ (∀ k', sinkBytes k' O = if k' = k then x else []) ∧
      O.flatMap (fun | .inp b => b | _ => []) = [] ∧
      O.filterMap (fun | .read p => some p | _ => none) = [] := by
  rcases h with rfl | ⟨j, rfl | rfl⟩
  · exact ⟨[], List.nil_prefix, fun k' => by simp [sinkBytes], rfl, rfl⟩
  · exact ⟨bs.take j, List.take_prefix _ _, fun k' => by simp [sinkBytes, eq_comm], rfl, rfl⟩
  · exact ⟨bs.take j, List.take_prefix _ _, fun k' => by simp [sinkBytes, eq_comm], rfl, rfl⟩

/-- Events that change and show nothing. -/
theorem scan3_still {t : List WEv} (ht : ∀ e ∈ t, ∀ q : Sc3, q.step e = (q, [])) (q : Sc3) :
    scan3 q t = [] := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    rw [scan3_cons, ht e List.mem_cons_self q, ih fun e' he' => ht e' (List.mem_cons_of_mem _ he')]
    rfl

/-- The scan of the whole trace is that of the write. -/
theorem scan_trace {q : (nsig ({run3} : Set FnName)).Op} {pre v fin : List WEv}
    (hq : ∀ e ∈ pre, Quiet3 e) (hfin : ∀ e ∈ fin, ∀ q : Sc3, q.step e = (q, [])) :
    scan3 {} (.call q.1.1 q.2 :: (pre ++ v ++ fin)) = scan3 {} v := by
  have hq' : ∀ e ∈ WEv.call q.1.1 q.2 :: pre, Quiet3 e := fun e he =>
    (List.mem_cons.1 he).elim (fun h => h ▸ quiet3_call _ _) (hq e)
  have hT : WEv.call q.1.1 q.2 :: (pre ++ v ++ fin) = (WEv.call q.1.1 q.2 :: pre) ++ v ++ fin :=
    rfl
  rw [hT, scan3_append, scan3_append, (scan3_quiet hq' _).1, (scan3_quiet hq' _).2,
    scan3_still hfin]
  simp


/-- The code of the whole trace is that of `finish3` and the return. -/
theorem code_trace {q : (nsig ({run3} : Set FnName)).Op} {pre v fin : List WEv}
    {k : Sink} {bs : List (BitVec 8)} {ro : Option Bool}
    (hq : ∀ e ∈ pre, Quiet3 e) (hP : Facts {} k bs v ro) :
    (WEv.call q.1.1 q.2 :: (pre ++ v ++ fin)).findSome? endCode3 = fin.findSome? endCode3 := by
  have hpre : pre.findSome? endCode3 = none := List.findSome?_eq_none_iff.2 fun e he => (hq e he).2
  have hv : v.findSome? endCode3 = none := List.findSome?_eq_none_iff.2 hP.code
  simp [List.findSome?_cons, endCode3, hpre, hv]

/-- The last steps cannot be `run`'s return to another export. -/
theorem endCode3_ret (q : (nsig ({run3} : Set FnName)).Op) (a : Option (List Val)) :
    endCode3 (.ret q.1.1 q.2 a) = some (retCode a) := by
  have hq : q.1.1 = run3 := q.1.2
  simp [endCode3, hq]

theorem toUInt8_one : (1 : UInt32).toUInt8 = 1 := rfl

/-- What `finish3`'s runs with the return show: nothing, and the code, if any, is `c`. -/
def FinShows (c : ExitCode) (fin : List WEv) : Prop :=
  (∀ e ∈ fin, ∀ q' : Sc3, q'.step e = (q', [])) ∧
    (fin.findSome? endCode3 = none ∨ fin.findSome? endCode3 = some c)

/-- `finish3` with a zero code: return `ok`. -/
theorem finish3_zero {k' : UInt32} (h0 : k'.toUInt8 = 0) {v : List WEv}
    {r : Option (Option (List Val))} (h : PRun (I := I3) (.pure (some [okV none])) v r)
    (q : (nsig ({run3} : Set FnName)).Op) : FinShows k'.toUInt8 (v ++ retEv q r) := by
  obtain ⟨rfl, hr⟩ := PRun.pure_inv h
  rcases hr with rfl | rfl
  · exact ⟨fun e he => absurd he List.not_mem_nil, .inl rfl⟩
  · refine ⟨fun e he q' => (List.mem_singleton.1 he) ▸ rfl, .inr ?_⟩
    show List.findSome? endCode3 [WEv.ret q.1.1 q.2 (some [okV none])] = _
    rw [List.findSome?_cons, endCode3_ret, h0]; rfl

/-- The events of `exit-with-code`: no output. -/
theorem exitCode_still (c : UInt8) (n : Option (List Val)) (q' : Sc3) :
    q'.step (.req W3.exitCode [.u8 c.toBitVec]) = (q', []) ∧
      q'.step (.imp W3.exitCode [.u8 c.toBitVec] n) = (q', []) :=
  ⟨rfl, (quiet3_imp' (f := W3.exitCode) _ n (by decide) (by decide) (by decide) (by decide)).1 q'⟩

theorem endCode3_exitCode (c : UInt8) : endCode3 (.req W3.exitCode [.u8 c.toBitVec]) = some c := by
  have hne : W3.exitCode ≠ exit3 := by decide
  unfold endCode3; simp only [hne, ↓reduceIte]

/-- `finish3` with a nonzero code: `exit-with-code`, whose request ends the run. -/
theorem finish3_exit {c : UInt8} {v : List WEv} {r : Option (Option (List Val))}
    (h : PRun (.call (⟨W3.exitCode, exitCode_mem⟩, [.u8 c.toBitVec])
      fun _ => .pure (some [errV none])) v r) (q : (nsig ({run3} : Set FnName)).Op) :
    FinShows c (v ++ retEv q r) := by
  rcases call_cases h with ⟨hv, rfl⟩ | ⟨n, v', rfl, h'⟩
  · rcases List.prefix_cons_iff.1 hv with rfl | ⟨_, rfl, hv'⟩
    · exact ⟨fun e he => absurd he List.not_mem_nil, .inl rfl⟩
    · rw [List.prefix_nil.1 hv']
      refine ⟨fun e he q' => (List.mem_singleton.1 he) ▸ (exitCode_still c none q').1, .inr ?_⟩
      show List.findSome? endCode3 [WEv.req W3.exitCode [.u8 c.toBitVec]] = _
      rw [List.findSome?_cons, endCode3_exitCode]
  · have hv' : v' = [] := (PRun.pure_inv h').1
    subst hv'
    refine ⟨fun e he q' => ?_, .inr ?_⟩
    · show q'.step e = (q', [])
      rcases List.mem_append.1 he with he | he
      · rcases List.mem_pair.1 he with rfl | rfl
        exacts [(exitCode_still c n q').1, (exitCode_still c n q').2]
      · cases r with
        | none => exact absurd he List.not_mem_nil
        | some a => rw [List.mem_singleton.1 he]; rfl
    · show List.findSome? endCode3 (WEv.req W3.exitCode [.u8 c.toBitVec] :: _) = _
      rw [List.findSome?_cons, endCode3_exitCode]

/-- **The runs of `finish3`**, with the return: nothing shown, and the code, if any, is the
one `finish3` was given. -/
theorem finish3_fin {k' : UInt32} {v : List WEv} {r : Option (Option (List Val))}
    (h : PRun (finish3 k') v r) (q : (nsig ({run3} : Set FnName)).Op) :
    FinShows k'.toUInt8 (v ++ retEv q r) := by
  unfold finish3 at h
  split at h
  · next h0 => exact finish3_zero h0 h q
  · exact finish3_exit h q

/-- `finish3` after a write that returned `ok`, as `FinOk`. -/
theorem finOk_of {k : UInt32} {ok : Bool} {v : List WEv} {r : Option (Option (List Val))}
    (h : PRun (finish3 (if ok then k else 1)) v r) (q : (nsig ({run3} : Set FnName)).Op) :
    FinOk k (some ok) (v ++ retEv q r) :=
  have h' := finish3_fin h q
  ⟨h'.1, h'.2.imp_right fun h => ⟨ok, rfl, h⟩⟩

/-- Neither stdin nor files are read. -/
theorem view3_quiet {k : Sink} {bs : List (BitVec 8)} {T : List WEv}
    (h : OutOk k bs (scan3 {} T)) : p3CliView.stdin T = [] ∧ p3CliView.reads T = [] := by
  unfold p3CliView
  rcases h with h | ⟨j, h | h⟩ <;> simp [h] <;> rfl

/-- **A finished run**: the line with its exit code, or a failure. -/
theorem done3 {i : Input} {ch : Channel} {s : String} {k : UInt32} {T v fin : List WEv}
    {ro : Option Bool} (hS : scan3 {} T = scan3 {} v)
    (hC : T.findSome? endCode3 = fin.findSome? endCode3)
    (hP : Facts {} (Sink.ofChannel ch) (toWasm (utf8 (s ++ "\n"))) v ro) (hfin : FinOk k ro fin)
    (hd : (p3CliView.code T).isSome = true) :
    p3CliView.obs i T = lineObs i ch s k.toUInt8 ∨ (p3CliView.obs i T).exit ≠ 0 := by
  have hd' : (T.findSome? endCode3).isSome = true := hd
  rcases hfin.2 with hn | ⟨ok, rfl, hc⟩
  · rw [hC, hn] at hd'; exact absurd hd' (by simp)
  have hcode : T.findSome? endCode3 = some (if ok then k else 1).toUInt8 := hC.trans hc
  cases ok
  · exact .inr (by simp [View.obs, p3CliView, hcode])
  · have hv := hP.done rfl
    left
    have h0 : toBytes [] = [] := rfl
    cases ch <;> simp [View.obs, p3CliView, hS, hv, hcode, sinkBytes, Sink.ofChannel,
      toBytes_toWasm, applyWrites, Beh.lineObs, lineObs, h0]

/-- The outputs on stdout and stderr are prefixes of the line's. -/
theorem sink_prefixes {i : Input} {ch : Channel} {s : String} {k : ExitCode} {O : List Out3}
    {x : List (BitVec 8)}
    (hsink : ∀ k', sinkBytes k' O = if k' = Sink.ofChannel ch then x else [])
    (hxb : toBytes x <+: utf8 (s ++ "\n")) :
    toBytes (sinkBytes .stdout O) <+: (lineObs i ch s k).stdout ∧
      toBytes (sinkBytes .stderr O) <+: (lineObs i ch s k).stderr := by
  rw [hsink, hsink, lineObs_stdout, lineObs_stderr]
  cases ch
  · exact ⟨hxb, List.nil_prefix⟩
  · exact ⟨List.nil_prefix, hxb⟩

/-- **A play of the printing component, read through `p3CliView`.** -/
theorem allows_put3 {i : Input} {ch : Channel} {s : String} {k : UInt32}
    {q : (nsig ({run3} : Set FnName)).Op} {pre v fin : List WEv} {ro : Option Bool}
    (hq : ∀ e ∈ pre, Quiet3 e)
    (hP : Facts {} (Sink.ofChannel ch) (toWasm (utf8 (s ++ "\n"))) v ro)
    (hfin : FinOk k ro fin) :
    (Spec.orFail (lineSpec ch s k.toUInt8)).Partial i
      (p3CliView.seen i (.call q.1.1 q.2 :: (pre ++ v ++ fin))) := by
  obtain ⟨x, hx, hsink, -, -⟩ := outOk_view hP.outs
  have hS : scan3 {} (.call q.1.1 q.2 :: (pre ++ v ++ fin)) = scan3 {} v :=
    scan_trace hq hfin.1
  have hxb : toBytes x <+: utf8 (s ++ "\n") := by
    simpa [toBytes_toWasm] using toBytes_prefix hx
  have hpre := sink_prefixes (i := i) (k := k.toUInt8) (hS ▸ hsink) hxb
  exact allows_spec3 hpre.1 fun hd => done3 hS (code_trace hq hP) hP hfin hd

/-- Nothing seen yet. -/
theorem allows_nil3 (i : Input) (ch : Channel) (s : String) (k : ExitCode) :
    (Spec.orFail (lineSpec ch s k)).Partial i (p3CliView.seen i []) :=
  allows_spec3 List.nil_prefix (fun h => absurd h (by simp [p3CliView]))

/-- The decided program of a printing component, as a sequence. -/
theorem after_putLine3 (vs : List String) (ch : Channel) (s : String) (k : UInt32) :
    api3.after vs (api3.putLine ch s >>= fun _ => pure k) =
      api3.args.bind fun _ => api3.env.bind fun _ =>
        (put3 ch (utf8 (s ++ "\n"))).bind fun ok => finish3 (if ok then k else 1) := by
  rw [Api.after_eq, Api.close_putLine]; rfl

/-- The trace of a run of the printing component, regrouped. -/
theorem runTrace_eq3 (q : (nsig ({run3} : Set FnName)).Op) (pre v v' : List WEv)
    (r : Option (Option (List Val))) :
    runTrace q (pre ++ (v ++ v')) r = .call q.1.1 q.2 :: (pre ++ v ++ (v' ++ retEv q r)) := by
  simp [runTrace]

/-- **Printing a line is read as printing it** (WASI 0.3): `Api.EmitOk` for `api3`. -/
theorem emit3_ok : api3.EmitOk cliTh3 p3CliView Spec.orFail {run3} := by
  intro i vs ch s k sp hs hA h1
  rcases plays_run (f := run3) (fun q => q.1.2) hs h1 with h0 | ⟨q, u, r, hr, ht⟩
  · rw [h0]; exact allows_nil3 i ch s _
  have hr' := hr
  rw [Api.bodyAfter, after_putLine3] at hr'
  rw [ht]
  have hfin0 : FinOk k none [] := ⟨fun e he => absurd he List.not_mem_nil, .inl rfl⟩
  rcases prefix_quiet3 hr' with ⟨hq, rfl⟩ | ⟨pre, u', rfl, hq, hQ⟩
  · have hP : Facts {} (Sink.ofChannel ch) (toWasm (utf8 (s ++ "\n"))) [] none :=
      facts_quiet (fun e he => absurd he List.not_mem_nil) (by simp)
    simpa [runTrace, retEv] using allows_put3 (k := k) (q := q) hq hP hfin0
  rcases PRun.bind_inv hQ with ⟨hp, rfl⟩ | ⟨v, v', ok, rfl, hp, hf⟩
  · simpa [runTrace, retEv] using allows_put3 (k := k) (q := q) hq (put3_facts hp) hfin0
  · rw [runTrace_eq3]
    exact allows_put3 hq (put3_facts hp) (finOk_of hf q)

end Silmaril.Wasi.Cli.Host3

end
