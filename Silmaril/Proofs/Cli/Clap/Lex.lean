module

public import Silmaril.Cli.Clap.Defs
public import Silmaril.Cli.Args.Thms

/-!
# Proofs: the clap pre-pass and the args front end

* `pre_render`: the clap pre-pass passes the args normal form `render c fs` of a valid
  invocation of a well-formed grammar when the invocation is `Plain`; `read_render`: so the
  clap reading of the normal form is the args parser's (`scan_render`) followed by `readInv`;
* `readOpt_step`, `readCluster_cluster`, **`scans_quiet`**: token by token, where the pre-pass
  goes on, the args parser reads the same tokens (clusters, attached values, optional values,
  exact tokens included) and consumes the same next token, and what it reads comes from
  options that are neither the help nor the version flag;
* **`read_agrees`**: when the pre-pass passes, the clap reading agrees with the args front
  end `interpret` (`Outcome.Agrees`), for grammars whose help and version options are flags;
* `read_run_valid`, `read_run_render`: what the clap reading runs is a valid invocation, and
  its normal form reads back the same.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Clap

open Silmaril.Cli

/-! ## Unfolding the pre-pass -/

theorem pre_next {t : Tool} {c : Command} {path : List String} {tok : String}
    {rest : List String} (h : step t c path tok rest = .next) :
    pre t c path (tok :: rest) = pre t c path rest := by
  simp only [pre, h]

theorem pre_value {t : Tool} {c : Command} {path : List String} {tok x : String}
    {rest : List String} {o : Opt} (h : step t c path tok (x :: rest) = .value o)
    (hx : optionLike x = false) :
    pre t c path (tok :: x :: rest) = pre t c path rest := by
  simp only [pre, h, hx, Bool.false_eq_true, ↓reduceIte]

theorem pre_enter {t : Tool} {c s : Command} {path : List String} {tok : String}
    {rest : List String} (h : step t c path tok rest = .enter s) :
    pre t c path (tok :: rest) = pre t s (path ++ [s.name]) rest := by
  simp only [pre, h]

theorem pre_stop {t : Tool} {c : Command} {path : List String} {tok : String}
    {rest : List String} (h : step t c path tok rest = .stop) :
    pre t c path (tok :: rest) = none := by
  simp only [pre, h]

theorem pre_early {t : Tool} {c : Command} {path : List String} {tok : String}
    {rest : List String} {e : Early} (h : step t c path tok rest = .early e) :
    pre t c path (tok :: rest) = some e := by
  simp only [pre, h]

/-- Where the pre-pass passes, no token stops it early. -/
theorem step_ne_early {t : Tool} {c : Command} {path : List String} {tok : String}
    {rest : List String} (h : pre t c path (tok :: rest) = none) :
    ∀ e, step t c path tok rest ≠ .early e := by
  intro e he
  rw [pre_early he] at h
  exact absurd h (by simp)

/-! ## The normal form passes -/

/-- The conditions of `PlainOcc` on one option. -/
structure PlainOpt (o : Opt) (g : Given) : Prop where
  help : isHelpOpt o = false
  version : isVersionOpt o = false
  notOff : g ≠ .off
  value : ∀ x, g = .val x → optionLike x = false

/-- A bare occurrence (a flag, or an optional value) goes on. -/
theorem optStep_on {path : List String} {o : Opt} {g : Given} (hp : PlainOpt o g)
    (hacc : o.accepts .on = true) : optStep path o none = .next := by
  cases ha : o.arg with
  | none => simp [optStep, hp.help, hp.version, ha]
  | some a =>
    have hvo : o.valueOptional = true := by
      simpa [Opt.accepts, Opt.takesValue, ha] using hacc
    simp [optStep, hp.help, hp.version, ha, hvo]

/-- An attached value of a value-taking option goes on. -/
theorem optStep_attached {path : List String} {o : Opt} (hh : isHelpOpt o = false)
    (hv : isVersionOpt o = false) (ha : o.arg.isSome = true) (x : String) :
    optStep path o (some x) = .next := by
  obtain ⟨a, ha'⟩ := Option.isSome_iff_exists.mp ha
  simp [optStep, hh, hv, ha']

/-- A value-taking option without an attached value, whose value is not optional, takes the
next token. -/
theorem optStep_value {path : List String} {o : Opt} (hh : isHelpOpt o = false)
    (hv : isVersionOpt o = false) (ha : o.arg.isSome = true) (hvo : o.valueOptional = false) :
    optStep path o none = .value o := by
  obtain ⟨a, ha'⟩ := Option.isSome_iff_exists.mp ha
  simp [optStep, hh, hv, ha', hvo]

/-- The spelling of a declared option reaches the option (well-formed levels). -/
theorem step_spelling {t : Tool} {c : Command} (h : c.LocalWF) {path : List String} {o : Opt}
    (ho : o ∈ c.opts) (rest : List String) :
    step t c path o.spelling rest = optStep path o none := by
  rcases spelling_cases h ho with ⟨n, -, hsp, hn, hf⟩ | ⟨-, n, hsp, hn, hf⟩
  · rw [hsp]; simp only [step, classify_long hn, hf]
  · rw [hsp]; simp only [step, classify_short hn, hf]

/-- A value occurrence in normal form passes. -/
theorem pre_given_val {t : Tool} {c : Command} (h : c.LocalWF) {path : List String} {o : Opt}
    (ho : o ∈ c.opts) {x : String} (hacc : o.accepts (.val x) = true)
    (hp : PlainOpt o (.val x)) (tail : List String) :
    pre t c path (renderGiven o (.val x) ++ tail) = pre t c path tail := by
  have ha : o.arg.isSome = true := by simpa [Opt.accepts, Opt.takesValue] using hacc
  cases hvo : o.valueOptional with
  | true =>
    have hw := (h.opt ho).2.2.2.1 hvo
    rcases spelling_cases h ho with ⟨n, hhd, -, hn, hf⟩ | ⟨hl, -⟩
    · have hr : renderGiven o (.val x) = ["--" ++ n ++ "=" ++ x] := by
        simp [renderGiven, hvo, hhd]
      rw [hr]
      have hs : step t c path ("--" ++ n ++ "=" ++ x) tail = .next := by
        simp only [step, classify_longEq hn, hf]
        exact optStep_attached hp.help hp.version ha x
      exact pre_next hs
    · exact absurd hl hw.2
  | false =>
    have hr : renderGiven o (.val x) = [o.spelling, x] := by simp [renderGiven, hvo]
    rw [hr]
    exact pre_value ((step_spelling h ho (x :: tail)).trans
      (optStep_value hp.help hp.version ha hvo)) (hp.value x rfl)

/-- One option occurrence in normal form passes. -/
theorem pre_given {t : Tool} {c : Command} (h : c.LocalWF) {path : List String} {o : Opt}
    (ho : o ∈ c.opts) {g : Given} (hacc : o.accepts g = true) (hp : PlainOpt o g)
    (tail : List String) :
    pre t c path (renderGiven o g ++ tail) = pre t c path tail := by
  cases g with
  | on => exact pre_next ((step_spelling h ho tail).trans (optStep_on hp hacc))
  | off => exact absurd rfl hp.notOff
  | val x => exact pre_given_val h ho hacc hp tail

/-- The options of a frame in normal form pass. -/
theorem pre_renderOpts {t : Tool} {c : Command} (h : c.LocalWF) {path : List String}
    {ps : List (String × Given)}
    (hps : ∀ p ∈ ps, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true)
    (hpl : ∀ p ∈ ps, PlainOcc c p) (tail : List String) :
    pre t c path (ps.flatMap (renderOpt c.opts) ++ tail) = pre t c path tail := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨o, hfo, hacc⟩ := hps p List.mem_cons_self
    have ho : o ∈ c.opts := lookup_mem hfo
    have hq := hpl p List.mem_cons_self o hfo
    have hpo : PlainOpt o p.2 := ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2⟩
    have hr : renderOpt c.opts p = renderGiven o p.2 := by simp [renderOpt, hfo]
    calc pre t c path ((p :: ps).flatMap (renderOpt c.opts) ++ tail)
        = pre t c path (renderGiven o p.2 ++ (ps.flatMap (renderOpt c.opts) ++ tail)) := by
          simp [hr]
      _ = pre t c path (ps.flatMap (renderOpt c.opts) ++ tail) := pre_given h ho hacc hpo _
      _ = _ := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
            (fun q hq => hpl q (List.mem_cons_of_mem _ hq))

/-- Words at a command without subcommands pass. -/
theorem pre_words (t : Tool) (c : Command) (path : List String) (hsub : c.subs.isEmpty = true) :
    ∀ ws : List String, (∀ w ∈ ws, classify w = .word w) → pre t c path ws = none
  | [], _ => rfl
  | w :: ws, hw => by
    have hc : classify w = .word w := hw w List.mem_cons_self
    have hst : step t c path w ws = .next := by simp [step, hc, hsub]
    rw [pre_next hst]
    exact pre_words t c path hsub ws fun x hx => hw x (List.mem_cons_of_mem _ hx)

/-- Positional words in normal form pass. -/
theorem pre_renderArgs (t : Tool) (c : Command) (path args : List String) :
    pre t c path (renderArgs c args) = none := by
  by_cases he : args.isEmpty
  · have hnil : args = [] := List.isEmpty_iff.mp he
    simp [renderArgs, hnil, pre]
  · by_cases hg : !c.subs.isEmpty || !args.all isWord
    · have hr : renderArgs c args = "--" :: args := by simp only [renderArgs, he, hg]; rfl
      have hstop : step t c path "--" args = .stop := by
        simp [step, show classify "--" = .dashdash by decide]
      rw [hr, pre_stop hstop]
    · have hsub : c.subs.isEmpty = true := by simp_all
      have hw : ∀ w ∈ args, classify w = .word w := by
        intro w hw
        have hiw : isWord w = true := by simp_all
        simpa [isWord] using hiw
      have hargs : renderArgs c args = args := by simp_all [renderArgs]
      rw [hargs]
      exact pre_words t c path hsub args hw

/-- The step of `pre_render` through a subcommand. -/
theorem pre_render_cons {t : Tool} {c s : Command} {path : List String} {f g : Frame}
    {gs : Invocation} (hwf : c.Good)
    (hopts : ∀ p ∈ f.opts, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true)
    (hpl : ∀ p ∈ f.opts, PlainOcc c p) (hhelp : t.helpSub = true → g.cmd ≠ "help")
    (hfind : findSub c.subs g.cmd = some s) (hgname : g.cmd = s.name)
    (hsub : pre t (c.child s) (path ++ [(c.child s).name]) (render (c.child s) (g :: gs)) =
      none) :
    pre t c path (render c (f :: g :: gs)) = none := by
  have hs : s ∈ c.subs := lookup_mem hfind
  have hword : classify g.cmd = .word g.cmd := hgname ▸ hwf.local.2.2.2.2.2 s hs
  have hnh : (t.helpSub && g.cmd == "help") = false := by
    cases hh : t.helpSub
    · rfl
    · simpa using hhelp hh
  have hst : step t c path g.cmd (render (c.child s) (g :: gs)) = .enter (c.child s) := by
    simp only [step, hword, subs_isEmpty_of_mem hs, hnh, hfind]
    rfl
  have hr : render c (f :: g :: gs) =
      f.opts.flatMap (renderOpt c.opts) ++ g.cmd :: render (c.child s) (g :: gs) := by
    simp [render, hfind]
  rw [hr, pre_renderOpts hwf.local hopts hpl, pre_enter hst, hsub]

/-- **The clap pre-pass passes the args normal form** of a valid, plain invocation of a
well-formed grammar. -/
theorem pre_render (t : Tool) (rest : Invocation) :
    ∀ (c : Command) (f : Frame) (path : List String), c.Good → Valid c (f :: rest) →
      Plain t c (f :: rest) → pre t c path (render c (f :: rest)) = none := by
  induction rest with
  | nil =>
    intro c f path hwf hv hp
    show pre t c path (f.opts.flatMap (renderOpt c.opts) ++ renderArgs c f.args) = none
    rw [pre_renderOpts hwf.local hv.1.2 hp.1, pre_renderArgs]
  | cons g gs ih =>
    intro c f path hwf hv hp
    obtain ⟨⟨_, hopts⟩, _, s, hfind, hvs⟩ := hv
    obtain ⟨hpl, hhelp, hps⟩ := hp
    have hs : s ∈ c.subs := lookup_mem hfind
    exact pre_render_cons hwf hopts hpl hhelp hfind hvs.1.1
      (ih (c.child s) g _ (hwf.sub hs) hvs (hps s hfind))

/-- **The clap reading of the args normal form** is the args parser's reading: the pre-pass
passes it, `scan` gives the invocation back (`scan_render`), then `readInv`. -/
theorem read_render (t : Tool) (env : String → Option String) {fs : Invocation}
    (hwf : t.grammar.WF) (hv : Valid t.grammar fs) (hp : Plain t t.grammar fs) :
    t.read env (render t.grammar fs) = t.readInv env fs := by
  match fs, hv, hp with
  | f :: rest, hv, hp =>
    have hpre := pre_render t rest t.grammar f [t.grammar.name] hwf.good hv hp
    simp only [Tool.read, hpre, scan_render hwf hv]

/-! ## Token by token: the pre-pass and the args parser -/

/-- An occurrence read from an option of `os` that is neither the help nor the version flag. -/
def Quiet (os : List Opt) (p : String × Given) : Prop :=
  ∃ o ∈ os, p.1 = o.id ∧ isHelpOpt o = false ∧ isVersionOpt o = false

/-- The pre-pass's step and the args reading of one token agree on consuming the next token
(`b`): the pre-pass goes on and nothing is consumed, or it takes a value and the args reading
consumes it. -/
def Agree (st : Step) (b : Bool) : Prop :=
  (st = .next ∧ b = false) ∨ ∃ o, st = .value o ∧ b = true

theorem optStep_flags {path : List String} {o : Opt} {v : Option String}
    (h : ∀ e, optStep path o v ≠ .early e) : isHelpOpt o = false ∧ isVersionOpt o = false := by
  by_cases hh : isHelpOpt o
  · exact absurd (show optStep path o v = .early (.help path) by simp [optStep, hh]) (h _)
  · by_cases hv : isVersionOpt o
    · exact absurd (show optStep path o v = .early .version by simp [optStep, hh, hv]) (h _)
    · simp_all

/-- The occurrences `valueFromNext` reads are of its option. -/
theorem valueFromNext_ids {o : Opt} {t : String} {x : Option String} {r : Read}
    (h : valueFromNext o t x = .ok r) : ∀ p ∈ r.1, p.1 = o.id := by
  unfold valueFromNext at h
  split at h
  · rw [← Except.ok.inj h]; simp
  · split at h
    · rw [← Except.ok.inj h]; simp
    · exact absurd h (by simp)

/-- A flag: the pre-pass goes on, nothing is consumed. -/
theorem agree_flag {path : List String} {o : Opt} (hh : isHelpOpt o = false)
    (hv : isVersionOpt o = false) (ha : o.takesValue = false) :
    Agree (optStep path o none) false := by
  have ha' : o.arg = none := by simpa [Opt.takesValue] using ha
  exact .inl ⟨by simp [optStep, hh, hv, ha'], rfl⟩

/-- A value-taking option without an attached value: `valueFromNext` and the pre-pass agree. -/
theorem agree_valueFromNext {path : List String} {o : Opt} {t : String} {x : Option String}
    {r : Read} (hh : isHelpOpt o = false) (hv : isVersionOpt o = false)
    (ha : o.takesValue = true) (h : valueFromNext o t x = .ok r) :
    Agree (optStep path o none) r.2 := by
  have ha' : o.arg.isSome = true := by simpa [Opt.takesValue] using ha
  obtain ⟨a, ha''⟩ := Option.isSome_iff_exists.mp ha'
  cases hvo : o.valueOptional with
  | true =>
    have hr : r = ([(o.id, .on)], false) := by simpa [valueFromNext, hvo] using h.symm
    exact .inl ⟨by simp [optStep, hh, hv, ha'', hvo], by simp [hr]⟩
  | false =>
    cases x with
    | none => simp [valueFromNext, hvo] at h
    | some y =>
      have hr : r = ([(o.id, .val y)], true) := by simpa [valueFromNext, hvo] using h.symm
      exact .inr ⟨o, optStep_value hh hv ha' hvo, by simp [hr]⟩

/-- **A cluster, letter by letter**: where clap's `cluster` succeeds, the args reading of the
same letters reads occurrences of quiet options, and consumes the next token exactly when
clap takes it as a value. -/
theorem readCluster_cluster {c : Command} {path : List String} {t : String}
    {x : Option String} :
    ∀ {cs : List Char} {r : Read} {q : Option Opt}, readCluster c.opts t x cs = .ok r →
      cluster c path cs = .ok q →
      (∀ p ∈ r.1, Quiet c.opts p) ∧ ((q = none ∧ r.2 = false) ∨ (q.isSome ∧ r.2 = true))
  | [], r, q, h, hc => by
    have hr : r = ([], false) := (Except.ok.inj h).symm
    have hq : q = none := (Except.ok.inj hc).symm
    simp [hr, hq]
  | ch :: cs, r, q, h, hc => by
    cases hf : findShort (clusterOpts c.opts) (String.singleton ch) with
    | none => simp [readCluster, hf] at h
    | some o =>
      have hm : o ∈ c.opts := (List.mem_filter.mp (lookup_mem hf)).1
      have hh : isHelpOpt o = false := by
        cases hh : isHelpOpt o
        · rfl
        · simp [cluster, hf, hh] at hc
      have hv : isVersionOpt o = false := by
        cases hv : isVersionOpt o
        · rfl
        · simp [cluster, hf, hh, hv] at hc
      cases ha : o.arg with
      | none =>
        have htv : o.takesValue = false := by simp [Opt.takesValue, ha]
        have hmap : (readCluster c.opts t x cs).map (fun p => ((o.id, .on) :: p.1, p.2)) =
            .ok r := by simpa [readCluster, hf, htv] using h
        have hc' : cluster c path cs = .ok q := by simpa [cluster, hf, hh, hv, ha] using hc
        cases hrc : readCluster c.opts t x cs with
        | error e => rw [hrc] at hmap; exact absurd hmap (by simp [Except.map])
        | ok r' =>
          rw [hrc] at hmap
          have hr : r = ((o.id, .on) :: r'.1, r'.2) := (Except.ok.inj hmap).symm
          obtain ⟨hq1, hq2⟩ := readCluster_cluster hrc hc'
          refine ⟨fun p hp => ?_, by simpa [hr] using hq2⟩
          rw [hr] at hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact ⟨o, hm, rfl, hh, hv⟩
          · exact hq1 p hp
      | some a =>
        have htv : o.takesValue = true := by simp [Opt.takesValue, ha]
        cases hcs : cs.isEmpty
        · have hr : attachedValue o cs = r := by simpa [readCluster, hf, htv, hcs] using h
          have hq : q = none := by simpa [cluster, hf, hh, hv, ha, hcs] using hc.symm
          refine ⟨fun p hp => ?_, .inl ⟨hq, ?_⟩⟩
          · rw [← hr] at hp
            unfold attachedValue at hp
            split at hp <;>
              exact ⟨o, hm, (List.mem_singleton.mp hp) ▸ rfl, hh, hv⟩
          · rw [← hr]; unfold attachedValue; split <;> rfl
        · have hvf : valueFromNext o t x = .ok r := by
            simpa [readCluster, hf, htv, hcs] using h
          refine ⟨fun p hp => ⟨o, hm, valueFromNext_ids hvf p hp, hh, hv⟩, ?_⟩
          cases hvo : o.valueOptional with
          | true =>
            have hq : q = none := by simpa [cluster, hf, hh, hv, ha, hcs, hvo] using hc.symm
            have hr : r = ([(o.id, .on)], false) := by
              simpa [valueFromNext, hvo] using hvf.symm
            exact .inl ⟨hq, by simp [hr]⟩
          | false =>
            have hq : q = some o := by simpa [cluster, hf, hh, hv, ha, hcs, hvo] using hc.symm
            cases x with
            | none => simp [valueFromNext, hvo] at hvf
            | some y =>
              have hr : r = ([(o.id, .val y)], true) := by
                simpa [valueFromNext, hvo] using hvf.symm
              exact .inr ⟨by simp [hq], by simp [hr]⟩

/-- A long option token, as `readOpt_step` needs it. -/
theorem readLong_step {path : List String} {o : Opt} {tok n : String} {v x : Option String}
    {os : List Opt} {r : Read} (hf : findLong os n = some o) (h : readLong os tok n v x = .ok r)
    (hne : ∀ e, optStep path o v ≠ .early e) :
    (∀ p ∈ r.1, p.1 = o.id) ∧ Agree (optStep path o v) r.2 := by
  obtain ⟨hh, hv⟩ := optStep_flags hne
  simp only [readLong, hf] at h
  cases htv : o.takesValue with
  | false =>
    cases v with
    | none =>
      have hr : r = ([(o.id, .on)], false) := by simpa [htv] using h.symm
      exact ⟨by simp [hr], hr ▸ agree_flag hh hv htv⟩
    | some y => simp [htv] at h
  | true =>
    cases v with
    | none =>
      have hvf : valueFromNext o tok x = .ok r := by simpa [htv] using h
      exact ⟨valueFromNext_ids hvf, agree_valueFromNext hh hv htv hvf⟩
    | some y =>
      have hr : r = ([(o.id, .val y)], false) := by simpa [htv] using h.symm
      have ha : o.arg.isSome = true := by simpa [Opt.takesValue] using htv
      exact ⟨by simp [hr], .inl ⟨optStep_attached hh hv ha y, by simp [hr]⟩⟩

/-- An exact single-dash token, as `readOpt_step` needs it. -/
theorem readShortExact_step {path : List String} {o : Opt} {tok : String} {x : Option String}
    {r : Read}
    (h : (if o.takesValue then valueFromNext o tok x else .ok ([(o.id, .on)], false) :
      Except ArgError Read) = .ok r)
    (hne : ∀ e, optStep path o none ≠ .early e) :
    (∀ p ∈ r.1, p.1 = o.id) ∧ Agree (optStep path o none) r.2 := by
  obtain ⟨hh, hv⟩ := optStep_flags hne
  cases htv : o.takesValue with
  | false =>
    have hr : r = ([(o.id, .on)], false) := by simpa [htv] using h.symm
    exact ⟨by simp [hr], hr ▸ agree_flag hh hv htv⟩
  | true =>
    have hvf : valueFromNext o tok x = .ok r := by simpa [htv] using h
    exact ⟨valueFromNext_ids hvf, agree_valueFromNext hh hv htv hvf⟩

/-- A long option token, as `readOpt_step` needs it. -/
theorem readOpt_step_long {t : Tool} {c : Command} {path : List String} {tok n : String}
    {v : Option String} {rest : List String} {x : Option String} {r : Read}
    (hcl : classify tok = .long n v) (h : readLong c.opts tok n v x = .ok r)
    (hne : ∀ e, step t c path tok rest ≠ .early e) :
    (∀ p ∈ r.1, Quiet c.opts p) ∧ Agree (step t c path tok rest) r.2 := by
  cases hf : findLong c.opts n with
  | none =>
    exact absurd (show step t c path tok rest =
      .early (.error ("unexpected argument '--" ++ n ++ "' found")) by
        simp only [step, hcl, hf]) (hne _)
  | some o =>
    have hst : step t c path tok rest = optStep path o v := by simp only [step, hcl, hf]
    have hne' : ∀ e, optStep path o v ≠ .early e := hst ▸ hne
    have hfl : isHelpOpt o = false ∧ isVersionOpt o = false := optStep_flags hne'
    have hlr : (∀ p ∈ r.1, p.1 = o.id) ∧ Agree (optStep path o v) r.2 := readLong_step hf h hne'
    exact ⟨fun p hp => ⟨o, lookup_mem hf, hlr.1 p hp, hfl.1, hfl.2⟩, by rw [hst]; exact hlr.2⟩

/-- A cluster token, as `readOpt_step` needs it. -/
theorem readOpt_step_cluster {t : Tool} {c : Command} {path : List String} {tok n : String}
    {rest : List String} {x : Option String} {r : Read} (hcl : classify tok = .short n)
    (hf : findShort c.opts n = none) (h : readCluster c.opts tok x n.toList = .ok r)
    (hne : ∀ e, step t c path tok rest ≠ .early e) :
    (∀ p ∈ r.1, Quiet c.opts p) ∧ Agree (step t c path tok rest) r.2 := by
  cases hc : cluster c path n.toList with
  | error e => exact absurd (show step t c path tok rest = .early e by
      simp only [step, hcl, hf, hc]) (hne e)
  | ok q =>
    have hq : (∀ p ∈ r.1, Quiet c.opts p) ∧
        ((q = none ∧ r.2 = false) ∨ (q.isSome ∧ r.2 = true)) := readCluster_cluster h hc
    refine ⟨hq.1, ?_⟩
    cases q with
    | none =>
      have hst : step t c path tok rest = .next := by simp only [step, hcl, hf, hc]
      have hb : r.2 = false := by simpa using hq.2
      exact .inl ⟨hst, hb⟩
    | some o =>
      have hst : step t c path tok rest = .value o := by simp only [step, hcl, hf, hc]
      have hb : r.2 = true := by simpa using hq.2
      exact .inr ⟨o, hst, hb⟩

/-- A single-dash token, as `readOpt_step` needs it. -/
theorem readOpt_step_short {t : Tool} {c : Command} {path : List String} {tok n : String}
    {rest : List String} {x : Option String} {r : Read} (hcl : classify tok = .short n)
    (h : readShort c.opts tok n x = .ok r) (hne : ∀ e, step t c path tok rest ≠ .early e) :
    (∀ p ∈ r.1, Quiet c.opts p) ∧ Agree (step t c path tok rest) r.2 := by
  cases hf : findShort c.opts n with
  | some o =>
    have hst : step t c path tok rest = optStep path o none := by simp only [step, hcl, hf]
    have hne' : ∀ e, optStep path o none ≠ .early e := hst ▸ hne
    have hfl : isHelpOpt o = false ∧ isVersionOpt o = false := optStep_flags hne'
    have h' : (if o.takesValue then valueFromNext o tok x else .ok ([(o.id, .on)], false) :
        Except ArgError Read) = .ok r := by simpa [readShort, hf] using h
    have hlr : (∀ p ∈ r.1, p.1 = o.id) ∧ Agree (optStep path o none) r.2 :=
      readShortExact_step h' hne'
    exact ⟨fun p hp => ⟨o, lookup_mem hf, hlr.1 p hp, hfl.1, hfl.2⟩, by rw [hst]; exact hlr.2⟩
  | none =>
    have h' : readCluster c.opts tok x n.toList = .ok r := by simpa [readShort, hf] using h
    exact readOpt_step_cluster hcl hf h' hne

/-- **One option token**: where the pre-pass goes on or takes a value, the args reading of
the token reads occurrences of quiet options and consumes the next token exactly when the
pre-pass does. -/
theorem readOpt_step {t : Tool} {c : Command} {path : List String} {tok : String}
    {rest : List String} {x : Option String} {r : Read}
    (h : readOpt c.opts tok x = .ok r) (hne : ∀ e, step t c path tok rest ≠ .early e) :
    (∀ p ∈ r.1, Quiet c.opts p) ∧ Agree (step t c path tok rest) r.2 := by
  cases hcl : classify tok with
  | long n v => exact readOpt_step_long hcl (by simpa [readOpt, hcl] using h) hne
  | short n => exact readOpt_step_short hcl (by simpa [readOpt, hcl] using h) hne
  | dashdash => exact absurd h (by simp [readOpt, hcl])
  | word w => exact absurd h (by simp [readOpt, hcl])

/-! ## Whole command lines -/

theorem classify_word {s w : String} (h : classify s = .word w) : w = s := by
  unfold classify at h
  split at h <;> (try split at h) <;> simp_all

/-- What a command line the pre-pass passes reads, at the level it reads it: the root
frame's occurrences are of quiet options of the root, every other frame's of quiet options of
some level of the grammar. -/
def QuietRead (c : Command) (r : Frame × Invocation) : Prop :=
  (∀ p ∈ r.1.opts, Quiet c.opts p) ∧
    ∀ fr ∈ r.2, ∀ p ∈ fr.opts, ∃ ws d, c.walk ws = some d ∧ Quiet d.opts p

theorem QuietRead.consOpts {c : Command} {f : Frame} {fs : Invocation}
    {ps : List (String × Given)} (h : QuietRead c (f, fs)) (hps : ∀ p ∈ ps, Quiet c.opts p) :
    QuietRead c ({ f with opts := ps ++ f.opts }, fs) := by
  refine ⟨fun p hp => ?_, h.2⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hps p hp
  · exact h.1 p hp

theorem QuietRead.sub {c s : Command} {w : String} {g : Frame} {gs : Invocation}
    (hf : findSub c.subs w = some s) (h : QuietRead (c.child s) (g, gs)) :
    QuietRead c ({ cmd := c.name }, g :: gs) := by
  refine ⟨fun p hp => absurd hp (by simp), fun fr hfr p hp => ?_⟩
  rcases List.mem_cons.mp hfr with rfl | hfr
  · exact ⟨[w], c.child s, by simp [Command.walk, hf], h.1 p hp⟩
  · obtain ⟨ws, d, hw, hq⟩ := h.2 fr hfr p hp
    exact ⟨w :: ws, d, by rw [walk_cons, hf]; exact hw, hq⟩

theorem agree_next {st : Step} {b : Bool} (h : Agree st b) (hb : b = false) : st = .next := by
  rcases h with ⟨h, _⟩ | ⟨_, _, hb'⟩
  · exact h
  · rw [hb] at hb'; exact absurd hb' (by simp)

theorem agree_value {st : Step} {b : Bool} (h : Agree st b) (hb : b = true) :
    ∃ o, st = .value o := by
  rcases h with ⟨_, hb'⟩ | ⟨o, h, _⟩
  · rw [hb] at hb'; exact absurd hb' (by simp)
  · exact ⟨o, h⟩

/-- The pre-pass on a value-taking option: the value is not option-like, and the rest passes. -/
theorem pre_value_none {t : Tool} {c : Command} {path : List String} {tok x : String}
    {rest : List String} {o : Opt} (hst : step t c path tok (x :: rest) = .value o)
    (hpre : pre t c path (tok :: x :: rest) = none) : pre t c path rest = none := by
  cases hx : optionLike x
  · rw [← pre_value hst hx]; exact hpre
  · exact absurd hpre (by simp [pre, hst, hx])

/-- The pre-pass on a subcommand word: not clap's `help`, and the rest passes below. -/
theorem pre_sub_none {t : Tool} {c s : Command} {path : List String} {tok w : String}
    {rest : List String} (hcl : classify tok = .word w) (hsub : c.subs.isEmpty = false)
    (hf : findSub c.subs w = some s) (hpre : pre t c path (tok :: rest) = none) :
    pre t (c.child s) (path ++ [(c.child s).name]) rest = none := by
  have hw : w = tok := classify_word hcl
  have hf' : findSub c.subs tok = some s := hw ▸ hf
  have hnh : (t.helpSub && tok == "help") = false := by
    cases hh : (t.helpSub && tok == "help")
    · rfl
    · exact absurd hpre (by simp [pre, step, hcl, hsub, hh])
  have hst : step t c path tok rest = .enter (c.child s) := by
    simp only [step, hcl, hsub, hnh, hf']
    rfl
  rw [← pre_enter hst]; exact hpre

/-- **Where the pre-pass passes, the args parser reads quiet options only.** -/
theorem scans_quiet {t : Tool} {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : Scans c argv r) : ∀ path, pre t c path argv = none → QuietRead c r := by
  induction h with
  | nil c => intro _ _; exact ⟨fun p hp => absurd hp (by simp), fun fr hfr => absurd hfr (by simp)⟩
  | dashdash _ =>
    intro _ _; exact ⟨fun p hp => absurd hp (by simp), fun fr hfr => absurd hfr (by simp)⟩
  | @opt c tok rest ps f fs hr _ ih =>
    intro path hpre
    have hq := readOpt_step (path := path) hr (step_ne_early hpre)
    have hrest : pre t c path rest = none := by rw [← pre_next (agree_next hq.2 rfl)]; exact hpre
    exact (ih path hrest).consOpts hq.1
  | @optNext c tok x rest ps f fs hr _ ih =>
    intro path hpre
    have hq := readOpt_step (path := path) (rest := x :: rest) hr (step_ne_early hpre)
    obtain ⟨o, hst⟩ := agree_value hq.2 rfl
    exact (ih path (pre_value_none hst hpre)).consOpts hq.1
  | @arg c tok w rest f fs hcl hsub _ ih =>
    intro path hpre
    have hst : step t c path tok rest = .next := by simp [step, hcl, hsub]
    have hrest : pre t c path rest = none := by rw [← pre_next hst]; exact hpre
    exact ⟨(ih path hrest).1, (ih path hrest).2⟩
  | @sub c tok w s rest g gs hcl hsub hf _ ih =>
    intro path hpre
    exact QuietRead.sub hf (ih _ (pre_sub_none hcl hsub hf hpre))

/-- Without occurrences of `help`, no frame asks for help. -/
theorem helpPath_none : ∀ (fs : Invocation) (acc : List String),
    (∀ fr ∈ fs, ∀ p ∈ fr.opts, p.1 ≠ "help") → helpPath fs acc = none
  | [], _, _ => rfl
  | f :: rest, acc, h => by
    have hf : f.opts.any (·.1 == "help") = false := by
      simpa using fun a b hab => h f List.mem_cons_self (a, b) hab
    simp only [helpPath, hf, Bool.false_eq_true, ↓reduceIte]
    exact helpPath_none rest _ fun fr hfr => h fr (List.mem_cons_of_mem _ hfr)

/-- A quiet occurrence at a level of a grammar whose help options are flags is not `help`. -/
theorem quiet_not_help {c d : Command} {ws : List String} (hhf : HelpFlags c)
    (hw : c.walk ws = some d) {p : String × Given} (hq : Quiet d.opts p) : p.1 ≠ "help" := by
  obtain ⟨o, ho, hid, hh, -⟩ := hq
  intro hp
  have hoid : o.id = "help" := hid ▸ hp
  have ha : o.arg = none := hhf.1 o (walk_allOpts ws c d hw o ho) hoid
  simp [isHelpOpt, hoid, ha] at hh

/-- **The clap reading agrees with the args front end** on every command line the clap
pre-pass passes (clusters, attached values, optional values and exact tokens included), when
the help and version options are flags: the same run, help or version, or usage errors on both
sides (where the clap reading leaves a value undecided, the args front end runs). -/
theorem read_agrees (t : Tool) (env : String → Option String) {argv : List String}
    (hhf : HelpFlags t.grammar) (hp : pre t t.grammar [t.grammar.name] argv = none) :
    (t.read env argv).Agrees (interpret t.grammar env argv) := by
  cases hs : scan t.grammar argv with
  | error l =>
    obtain ⟨p, e⟩ := l
    simp [Tool.read, hp, hs, interpret, Outcome.ofLocated, Outcome.Agrees]
  | ok fs =>
    show (t.read env argv).Agrees (interpret t.grammar env argv)
    obtain ⟨f, rest, rfl, hsc⟩ := scan_eq_ok_iff.mp hs
    obtain ⟨hroot, hbelow⟩ := scans_quiet hsc _ hp
    have hnh : ∀ fr ∈ f :: rest, ∀ p ∈ fr.opts, p.1 ≠ "help" := by
      intro fr hfr p hpm
      rcases List.mem_cons.mp hfr with rfl | hfr
      · exact quiet_not_help (ws := []) hhf rfl (hroot p hpm)
      · obtain ⟨ws, d, hw, hq⟩ := hbelow fr hfr p hpm
        exact quiet_not_help hhf hw hq
    have hver : ¬ AsksVersion t.grammar (f :: rest) := by
      rintro ⟨-, hany⟩
      obtain ⟨p, hpm, hpv⟩ := List.any_eq_true.mp hany
      obtain ⟨o, ho, hid, -, hv⟩ := hroot p hpm
      have hoid : o.id = "version" := hid ▸ (by simpa using hpv)
      have ha : o.arg = none := hhf.2 o ho hoid
      simp [isVersionOpt, hoid, ha] at hv
    have hread : t.read env argv = t.readInv env (f :: rest) := by
      simp [Tool.read, hp, hs]
    rw [hread, interpret_of_scan hs (helpPath_none _ _ hnh) hver]
    unfold Tool.readInv resolveOutcome
    cases judge t.grammar env (f :: rest) with
    | unresolved l =>
      obtain ⟨p, e⟩ := l
      cases e <;> simp [Outcome.Agrees, Outcome.ofLocated]
    | _ => simp [Outcome.Agrees]

/-! ## What the reading runs -/

theorem readInv_run {t : Tool} {env : String → Option String} {fs fs' : Invocation}
    {m : Matches} (h : t.readInv env fs' = .run fs m) : fs' = fs := by
  unfold Tool.readInv at h
  split at h <;> (cases h <;> rfl)

/-- What the clap reading runs is what the args parser read from the argument vector. -/
theorem read_run_scan {t : Tool} {env : String → Option String} {argv : List String}
    {fs : Invocation} {m : Matches} (h : t.read env argv = .run fs m) :
    pre t t.grammar [t.grammar.name] argv = none ∧ scan t.grammar argv = .ok fs := by
  unfold Tool.read at h
  split at h
  · cases h
  · cases h
  · cases h
  · next hpre =>
    split at h
    · cases h
    · next fs' hscan => exact ⟨hpre, (readInv_run h) ▸ hscan⟩

/-- What the clap reading runs is a valid invocation of the grammar. -/
theorem read_run_valid {t : Tool} {env : String → Option String} {argv : List String}
    {fs : Invocation} {m : Matches} (hwf : t.grammar.WF) (h : t.read env argv = .run fs m) :
    Valid t.grammar fs :=
  scan_valid hwf.good (read_run_scan h).2

/-- The normal form of what the clap reading runs reads back the same (plain invocations). -/
theorem read_run_render {t : Tool} {env : String → Option String} {argv : List String}
    {fs : Invocation} {m : Matches} (hwf : t.grammar.WF) (h : t.read env argv = .run fs m)
    (hp : Plain t t.grammar fs) : t.read env (render t.grammar fs) = .run fs m := by
  obtain ⟨hpre, hscan⟩ := read_run_scan h
  have hinv : t.readInv env fs = .run fs m := by
    unfold Tool.read at h
    rw [hpre] at h
    simpa only [hscan] using h
  rw [read_render t env hwf (scan_valid hwf.good hscan) hp, hinv]

end Silmaril.Cli.Clap
