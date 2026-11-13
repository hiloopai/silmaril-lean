module

public import Silmaril.Proofs.Cli.Info.Args
public import Silmaril.Cli.Clap.Main.Thms

@[expose] public section

/-!
# Proofs: a clap front end answers help and version requests

clap's pre-pass stops at the first help flag it meets, so after subcommand words a help
spelling wins over everything that follows (`pre_help`); the `help` subcommand word of a group
names the help of a command (`pre_word`).

* **`Clap.spec_help`**, **`Clap.spec_version`**: under `Clap.helpTriggers`
  (`versionTriggers`) and texts that fit, `Tool.spec t S` refines the variant's sentence;
* **`Clap.helpTriggers_everywhere`**: every well-formed grammar built with
  `Command.helpEverywhere` meets the conditions, for every variant without a usage-error claim
  at paths its words select.

A Silmaril addition.
-/

namespace Silmaril.Cli.Info.Clap

open Silmaril.Cli Silmaril.Cli.Clap Silmaril.Cli.Institution

theorem step_help {t : Tool} {d : Command} {path : List String} {tok : String}
    {rest : List String} (h : stepsAs d.opts isHelpOpt tok = true) :
    step t d path tok rest = .early (.help path) := by
  unfold stepsAs at h
  split at h
  · next n v hc =>
    cases hf : findLong d.opts n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some] at h
      simp [step, hc, hf, optStep, h]
  · next n hc =>
    cases hf : findShort d.opts n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some] at h
      simp [step, hc, hf, optStep, h]
  · simp at h

theorem step_version {t : Tool} {d : Command} {path : List String} {tok : String}
    {rest : List String} (h : stepsAs d.opts versionFlag tok = true) :
    step t d path tok rest = .early .version := by
  unfold stepsAs at h
  split at h
  · next n v hc =>
    cases hf : findLong d.opts n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some, versionFlag, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [step, hc, hf, optStep, h.1, h.2]
  · next n hc =>
    cases hf : findShort d.opts n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some, versionFlag, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [step, hc, hf, optStep, h.1, h.2]
  · simp at h

theorem pathLevel_cons {t : Tool} {c d : Command} {w : String} {ws : List String}
    (h : pathLevel t c (w :: ws) = some d) :
    isWord w = true ∧ c.subs.isEmpty = false ∧ (t.helpSub && w == "help") = false ∧
      ∃ s, findSub c.subs w = some s ∧ pathLevel t (c.child s) ws = some d := by
  unfold pathLevel at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    cases hf : findSub c.subs w with
    | none => rw [hf] at h; cases h
    | some s => rw [hf] at h; exact ⟨hc.1.1, hc.1.2, hc.2, s, rfl, h⟩
  · cases h

/-- **clap's pre-pass after subcommand words**: a help spelling stops it with the help of the
path, whatever follows. -/
theorem pre_help {t : Tool} {tok : String} {rest : List String} :
    ∀ {p : List String} {c d : Command} {path : List String}, pathLevel t c p = some d →
    stepsAs d.opts isHelpOpt tok = true →
    pre t c path (p ++ tok :: rest) = some (.help (path ++ c.subNames p))
  | [], c, d, path, hp, ht => by
    cases hp
    simp [pre, step_help ht, Command.subNames]
  | w :: ws, c, d, path, hp, ht => by
    obtain ⟨hw, hs, hh, s, hf, hp'⟩ := pathLevel_cons hp
    have ih := pre_help (rest := rest) (p := ws) (path := path ++ [(c.child s).name]) hp' ht
    have hstep : step t c path w (ws ++ tok :: rest) = .enter (c.child s) := by
      simp [step, classify_of_isWord hw, hs, hh, hf]
    simp only [List.cons_append, pre, hstep, ih, Command.subNames, hf]
    simp

/-- clap's walk of `help NAME…` names the commands `walk` finds, by their names. -/
theorem helpWalk_of_walk : ∀ {c : Command} {acc p : List String} {d : Command},
    c.walk p = some d → helpWalk c acc p = .ok (acc ++ c.subNames p)
  | c, acc, [], _, _ => by simp [helpWalk, Command.subNames]
  | c, acc, w :: ws, d, h => by
    simp only [Command.walk] at h
    cases hf : findSub c.subs w with
    | none => rw [hf] at h; cases h
    | some s =>
      rw [hf] at h
      have ih := helpWalk_of_walk (acc := acc ++ [s.name])
        (show (c.child s).walk ws = some d from h)
      have hn : (c.child s).name = s.name := rfl
      simp only [helpWalk, hf, Command.subNames, ih, hn, List.append_assoc,
        List.singleton_append]

/-- **The `help` subcommand word** of a group names the help of the command its words name. -/
theorem pre_word {t : Tool} (hs : t.helpSub = true) (hg : t.grammar.subs.isEmpty = false)
    {p : List String} (hw : (t.grammar.walk p).isSome = true) :
    pre t t.grammar [t.grammar.name] ("help" :: p) =
      some (.help (t.grammar.name :: t.grammar.subNames p)) := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hw
  have hc : classify "help" = .word "help" := by decide +kernel
  simp [pre, step, hc, hg, hs, helpOf, helpWalk_of_walk (acc := []) hd]

theorem spec_front {t : Tool} {S : Matches → Spec} {i : Input} {o : Obs} (hs : t.spec S i o)
    {out : Silmaril.Cli.Clap.Outcome} (h : t.outcome i = out) (hr : out.runs = false) :
    o = t.frontObs i out := by
  unfold Tool.spec at hs
  rw [h] at hs
  cases out with
  | run => cases hr
  | undecided => cases hr
  | help => exact hs
  | version => exact hs
  | needCommand => exact hs
  | error => exact hs

theorem frontObs_help (t : Tool) (i : Input) (q : List String) (hp : t.present = none) :
    t.frontObs i (.help q) = { stdout := helpBytes t q, exit := 0, fs := i.fs } := by
  simp only [Tool.frontObs, Tool.text, Tool.body, hp]
  rfl

theorem frontObs_version (t : Tool) (i : Input) (hp : t.present = none) :
    t.frontObs i .version = { stdout := versionBytes t, exit := 0, fs := i.fs } := by
  simp only [Tool.frontObs, Tool.text, Tool.body, hp]
  rfl

theorem quiet_help (t : Tool) (i : Input) (q : List String) : Quiet i (t.frontObs i (.help q)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem helpTriggers_key {t : Tool} {v : HelpVariant} (h : helpTriggers t v = true) :
    v.extra ≠ .error ∧ (v.word = true → t.helpSub = true ∧ t.grammar.subs.isEmpty = false) ∧
    ∀ p ∈ v.roots, (∃ d, pathLevel t t.grammar p = some d ∧
      ∀ tok ∈ v.tokens, stepsAs d.opts isHelpOpt tok = true) ∧
      (v.word = true → (t.grammar.walk p).isSome = true) := by
  simp only [helpTriggers, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hx, hw⟩, hr⟩ := h
  refine ⟨hx, fun hw' => ?_, fun p hp => ?_⟩
  · rcases hw with hw | hw
    · simp [hw] at hw'
    · simpa using hw
  · obtain ⟨h1, h2⟩ := hr p hp
    refine ⟨?_, fun hw' => ?_⟩
    · cases hd : pathLevel t t.grammar p with
      | none => rw [hd] at h1; cases h1
      | some d =>
        rw [hd] at h1
        exact ⟨d, rfl, by simpa [List.all_eq_true] using h1⟩
    · rcases h2 with h2 | h2
      · simp [hw'] at h2
      · exact h2

/-- **A clap front end meets a help variant** whose requests it answers
(`Clap.helpTriggers`) with texts that fit: `Tool.spec t S` refines the sentence, for every
`S`. -/
theorem spec_help {t : Tool} {v : HelpVariant} (hpres : t.present = none)
    (h : helpTriggers t v = true)
    (hfit : ∀ p ∈ v.roots, v.Fits p (helpBytes t (t.grammar.pathNames p)))
    (S : Matches → Spec) : t.spec S ≤ v.sen := by
  obtain ⟨hx, hw, key⟩ := helpTriggers_key h
  intro i o hs
  have hspell : ∀ p ∈ v.roots, ∀ tok ∈ v.tokens, ∀ rest, i.args = p ++ tok :: rest →
      o = t.frontObs i (.help (t.grammar.pathNames p)) := by
    intro p hp tok htok rest ha
    obtain ⟨⟨d, hd, hts⟩, _⟩ := key p hp
    have hpre := pre_help (rest := rest) (path := [t.grammar.name]) hd (hts tok htok)
    have hout : t.outcome i = .help (t.grammar.pathNames p) := by
      simp only [Tool.outcome, Tool.read, ha, hpre]
      rfl
    exact spec_front hs hout rfl
  have hword' : v.word = true → ∀ p ∈ v.roots, i.args = "help" :: p →
      o = t.frontObs i (.help (t.grammar.pathNames p)) := by
    intro hw' p hp ha
    obtain ⟨hsub, hg⟩ := hw hw'
    have hpre := pre_word hsub hg ((key p hp).2 hw')
    have hout : t.outcome i = .help (t.grammar.pathNames p) := by
      simp only [Tool.outcome, Tool.read, ha, hpre]
      rfl
    exact spec_front hs hout rfl
  refine ⟨fun p hp => ⟨fun tok htok ha => ?_, fun hw' ha => ?_, fun tok htok rest _ ha => ?_⟩,
    fun _ ha => ?_⟩
  · rw [hspell p hp tok htok [] ha, frontObs_help t i _ hpres]
    exact HelpVariant.shows_line (hfit p hp)
  · rw [hword' hw' p hp ha, frontObs_help t i _ hpres]
    exact HelpVariant.shows_line (hfit p hp)
  · rw [hspell p hp tok htok rest ha, frontObs_help t i _ hpres]
    have hsh := HelpVariant.shows_line (hfit p hp)
    cases hxe : v.extra with
    | ignore => trivial
    | wins => exact hsh
    | winsOperands => exact fun _ => hsh
    | error => exact absurd hxe hx
    | either => exact .inl hsh
  · obtain ⟨p, hp, ⟨tok, htok, ha | ⟨rest, _, ha, _⟩⟩ | ⟨hw', ha⟩⟩ := ha
    · rw [hspell p hp tok htok [] ha]; exact quiet_help _ _ _
    · rw [hspell p hp tok htok rest ha]; exact quiet_help _ _ _
    · rw [hword' hw' p hp ha]; exact quiet_help _ _ _

/-- **A clap front end meets a version variant** whose requests it answers. -/
theorem spec_version {t : Tool} {v : VersionVariant} (hpres : t.present = none)
    (h : versionTriggers t v = true)
    (hfit : v.Fits (versionBytes t)) (S : Matches → Spec) : t.spec S ≤ v.sen := by
  simp only [versionTriggers, List.all_eq_true] at h
  intro i o hs
  have key : ∀ tok ∈ v.tokens, i.args = [tok] → o = t.frontObs i .version := by
    intro tok htok ha
    have hout : t.outcome i = .version := by
      simp only [Tool.outcome, Tool.read, ha]
      simp [pre, step_version (h tok htok)]
    exact spec_front hs hout rfl
  refine ⟨fun tok htok ha => ?_, fun _ tok htok ha => ?_⟩
  · rw [key tok htok ha, frontObs_version t i hpres]; exact VersionVariant.shows_line hfit
  · rw [key tok htok ha]; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Grammars with help on every command -/

theorem helpEverywhere_opts (e : Command) :
    e.helpEverywhere.opts = e.opts ++ [helpFlag] := by
  cases e; simp [Command.helpEverywhere]

theorem helpEverywhere_subs (e : Command) :
    e.helpEverywhere.subs = Command.helpEverywhereAll e.subs := by
  cases e; simp [Command.helpEverywhere]

theorem mem_helpEverywhereAll : ∀ {l : List Command} {s : Command},
    s ∈ Command.helpEverywhereAll l → ∃ e : Command, s = Command.helpEverywhere e
  | [], _, h => by simp [Command.helpEverywhereAll] at h
  | e :: l, s, h => by
    simp only [Command.helpEverywhereAll, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨e, rfl⟩
    · exact mem_helpEverywhereAll h

/-- The levels of a grammar with help on every command have the help flag. -/
theorem pathLevel_everywhere {t : Tool} : ∀ {p : List String} {e : Command} {inh : List Opt}
    {d : Command}, (e.helpEverywhere.inherit inh).Good →
    pathLevel t (e.helpEverywhere.inherit inh) p = some d → d.Good ∧ helpFlag ∈ d.opts
  | [], e, inh, d, hg, hp => by
    cases hp
    refine ⟨hg, ?_⟩
    show helpFlag ∈ e.helpEverywhere.opts ++ inh
    simp [helpEverywhere_opts]
  | w :: ws, e, inh, d, hg, hp => by
    obtain ⟨_, _, _, s, hf, hp'⟩ := pathLevel_cons hp
    have hsm : s ∈ (e.helpEverywhere.inherit inh).subs := lookup_mem hf
    have hsm' : s ∈ Command.helpEverywhereAll e.subs := by
      rw [← helpEverywhere_subs]; exact hsm
    obtain ⟨e', rfl⟩ := mem_helpEverywhereAll hsm'
    exact pathLevel_everywhere (hg.sub hsm) hp'

theorem pathLevel_walk {t : Tool} : ∀ {p : List String} {c d : Command},
    pathLevel t c p = some d → c.walk p = some d
  | [], c, d, hp => by cases hp; rfl
  | w :: ws, c, d, hp => by
    obtain ⟨_, _, _, s, hf, hp'⟩ := pathLevel_cons hp
    simp [Command.walk, hf, pathLevel_walk hp']

theorem stepsAs_of_mem {d : Command} (hg : d.LocalWF) {o : Opt} (ho : o ∈ d.opts)
    {f : Opt → Bool} (hf : f o = true) {tok : String} :
    ((∃ n ∈ o.long, classify tok = .long n none) ∨ ∃ n ∈ o.short, classify tok = .short n) →
    stepsAs d.opts f tok = true := by
  rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc⟩)
  · have h : findLong d.opts n = some o := (findLong_eq_some_iff hg).mpr ⟨ho, hn⟩
    simp [stepsAs, hc, h, hf]
  · have h : findShort d.opts n = some o := (findShort_eq_some_iff hg).mpr ⟨ho, hn⟩
    simp [stepsAs, hc, h, hf]

/-- **Every well-formed grammar with help on every command** (`Command.helpEverywhere`, clap's
`-h, --help`) answers the help requests of every variant without a usage-error claim, at paths
its words select (with clap's `help` subcommand for a `help` word). -/
theorem helpTriggers_everywhere {t : Tool} {c : Command} (hc : t.grammar = c.helpEverywhere)
    (hwf : t.grammar.WF) {v : HelpVariant} (hx : v.extra ≠ .error)
    (hw : v.word = true → t.helpSub = true ∧ t.grammar.subs.isEmpty = false)
    (hp : ∀ p ∈ v.roots, (pathLevel t t.grammar p).isSome = true) :
    helpTriggers t v = true := by
  have hg : (c.helpEverywhere.inherit []).Good := by
    rw [Command.inherit_nil, ← hc]; exact hwf.good
  simp only [helpTriggers, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨hx, ?_⟩, fun p hpm => ⟨?_, ?_⟩⟩
  · by_cases hw' : v.word = true
    · obtain ⟨h1, h2⟩ := hw hw'
      exact .inr ⟨h1, h2⟩
    · exact .inl (by simpa using hw')
  · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hp p hpm)
    have hd' : pathLevel t (c.helpEverywhere.inherit []) p = some d := by
      rw [Command.inherit_nil, ← hc]; exact hd
    obtain ⟨hgd, hfl⟩ := pathLevel_everywhere hg hd'
    rw [hd]
    simp only [List.all_eq_true]
    intro tok htok
    have := stepsAs_of_mem hgd.local hfl (f := isHelpOpt) rfl (tok := tok)
    rcases HelpVariant.mem_tokens.mp htok with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact this (.inl ⟨"help", by simp [helpFlag], classify_help⟩)
    · exact this (.inr ⟨"h", by simp [helpFlag], classify_h⟩)
  · by_cases hw' : v.word = true
    · obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hp p hpm)
      exact .inr (by simp [pathLevel_walk hd])
    · exact .inl (by simpa using hw')

end Silmaril.Cli.Info.Clap
