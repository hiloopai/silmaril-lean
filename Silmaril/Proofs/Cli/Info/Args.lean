module

public import Silmaril.Proofs.Cli.Info.Basic
public import Silmaril.Cli.Args.Thms
public import Silmaril.Cli.Io.Command.Thms

@[expose] public section

/-!
# Proofs: a derived args front end answers help and version requests

* `readsAs_readOpt`, `scanAux_readsAs`: a token that reads as a flag occurrence;
* `scanAux_path_help`, `interpret_help_path`: after subcommand words `p`, a help spelling makes
  the front end print the help of `p` (`Command.pathNames`), whatever follows unless the rest
  does not parse (then a usage error); when the rest is empty, or operands at a level without
  subcommands, it is help;
* **`spec_help`**, **`spec_version`**: under `Command.helpTriggers` (`versionTriggers`) and
  a text that fits, `Command.spec c S` refines the variant's sentence, for every `S`;
* **`helpTriggers_of_wf`**, **`versionTriggers_of_wf`**: every well-formed grammar with the
  conventional help (version) flag meets the conditions.

A Silmaril addition.
-/

namespace Silmaril.Cli.Info

open Silmaril.Cli Silmaril.Cli.Institution

/-! ## Reading one flag -/

theorem readsAs_classify {os : List Opt} {id t : String} (h : readsAs os id t = true) :
    (∃ n, classify t = .long n none) ∨ ∃ n, classify t = .short n := by
  unfold readsAs at h
  split at h
  · next n hc => exact .inl ⟨n, hc⟩
  · next n hc => exact .inr ⟨n, hc⟩
  · simp at h

theorem readsAs_readOpt {os : List Opt} {id t : String} (h : readsAs os id t = true)
    (x : Option String) : readOpt os t x = .ok ([(id, .on)], false) := by
  unfold readsAs at h
  unfold readOpt
  split at h
  · next n hc =>
    rw [hc]
    cases hf : findLong os n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      simp [readLong, hf, h.1, h.2]
  · next n hc =>
    rw [hc]
    cases hf : findShort os n with
    | none => simp [hf] at h
    | some o =>
      simp only [hf, Option.any_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      simp [readShort, hf, h.1, h.2]
  · simp at h

theorem scanAux_readsAs {c : Command} {id t : String} (h : readsAs c.opts id t = true)
    (rest : List String) : scanAux c (t :: rest) = consOpts [(id, .on)] (scanAux c rest) := by
  rcases readsAs_classify h with ⟨n, hc⟩ | ⟨n, hc⟩ <;>
    simp only [scanAux, hc, readsAs_readOpt h]

theorem scans_cmd {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : Scans c argv r) : r.1.cmd = c.name := by
  induction h with
  | nil => rfl
  | dashdash => rfl
  | opt _ _ ih => exact ih
  | optNext _ _ ih => exact ih
  | arg _ _ _ ih => exact ih
  | sub => rfl

theorem scanAux_cmd {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : scanAux c argv = .ok r) : r.1.cmd = c.name :=
  scans_cmd (scanAux_eq_ok_iff.mp h)

/-! ## Operands -/

theorem classify_operand {w : String} (h : Operand w) : classify w = .word w := by
  unfold classify
  split <;> simp_all [Operand]

theorem scanAux_operands {d : Command} (hs : d.subs.isEmpty = true) :
    ∀ {rest : List String}, (∀ w ∈ rest, Operand w) → ∃ r, scanAux d rest = .ok r
  | [], _ => ⟨({ cmd := d.name }, []), by simp [scanAux]⟩
  | w :: ws, h => by
    obtain ⟨r, hr⟩ := scanAux_operands hs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [scanAux, classify_operand (h w List.mem_cons_self), hs, hr, consArg, Except.map]

/-! ## A help spelling after subcommand words -/

theorem classify_of_isWord {w : String} (h : isWord w = true) : classify w = .word w := by
  simpa [isWord] using h

theorem pathLevel_cons {c d : Command} {w : String} {ws : List String}
    (h : c.pathLevel (w :: ws) = some d) :
    isWord w = true ∧ c.subs.isEmpty = false ∧
      ∃ s, findSub c.subs w = some s ∧ (c.child s).pathLevel ws = some d := by
  unfold Command.pathLevel at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    cases hf : findSub c.subs w with
    | none => rw [hf] at h; cases h
    | some s => rw [hf] at h; exact ⟨hc.1, hc.2, s, rfl, h⟩
  · cases h

/-- **After subcommand words `p`, a help spelling**: the scan fails when the rest fails at the
level `p` selects, and otherwise reads an invocation whose help path is `c.pathNames p`. -/
theorem scanAux_path_help {t : String} {rest : List String} :
    ∀ {p : List String} {c d : Command}, c.pathLevel p = some d →
    readsAs d.opts "help" t = true →
    (∀ l, scanAux d rest = .error l → ∃ l', scanAux c (p ++ t :: rest) = .error l') ∧
    (∀ r', scanAux d rest = .ok r' → ∃ r, scanAux c (p ++ t :: rest) = .ok r ∧
      ∀ acc, helpPath (r.1 :: r.2) acc = some (acc ++ c.pathNames p))
  | [], c, d, hp, ht => by
    cases hp
    rw [List.nil_append, scanAux_readsAs ht]
    refine ⟨fun l hl => ⟨l, by simp [hl, consOpts, Except.map]⟩, fun r' hr => ?_⟩
    refine ⟨({ r'.1 with opts := ("help", .on) :: r'.1.opts }, r'.2),
      by simp [hr, consOpts, Except.map], fun acc => ?_⟩
    simp [helpPath, Command.pathNames, Command.subNames, scanAux_cmd hr]
  | w :: ws, c, d, hp, ht => by
    obtain ⟨hw, hs, s, hf, hp'⟩ := pathLevel_cons hp
    obtain ⟨ih1, ih2⟩ := scanAux_path_help (p := ws) hp' ht
    have hstep : scanAux c ((w :: ws) ++ t :: rest) =
        underSub c s.name (scanAux (c.child s) (ws ++ t :: rest)) := by
      simp [scanAux, classify_of_isWord hw, hs, hf]
    rw [hstep]
    refine ⟨fun l hl => ?_, fun r' hr => ?_⟩
    · obtain ⟨⟨q, e⟩, he⟩ := ih1 l hl
      exact ⟨(s.name :: q, e), by simp [he, underSub]⟩
    · obtain ⟨r, he, hh⟩ := ih2 r' hr
      refine ⟨({ cmd := c.name }, r.1 :: r.2), by simp [he, underSub], fun acc => ?_⟩
      have := hh (acc ++ [c.name])
      simp only [helpPath, List.any_nil, Bool.false_eq_true, ↓reduceIte] at this ⊢
      rw [this]
      simp [Command.pathNames, Command.subNames, hf, Command.child, Command.inherit]

/-- **The front end on a help request after subcommand words**: help or a usage error. -/
theorem interpret_help_or_error {c d : Command} {p : List String} (hp : c.pathLevel p = some d)
    {t : String} (ht : readsAs d.opts "help" t = true) (env : String → Option String)
    (rest : List String) :
    interpret c env (p ++ t :: rest) = .help (c.pathNames p) ∨
      ∃ q e, interpret c env (p ++ t :: rest) = .error q e := by
  obtain ⟨h1, h2⟩ := scanAux_path_help (rest := rest) hp ht
  cases hd : scanAux d rest with
  | error l =>
    obtain ⟨⟨q, e⟩, he⟩ := h1 l hd
    exact .inr ⟨c.name :: q, e, by simp [interpret, scan, he, Except.map, Outcome.ofLocated]⟩
  | ok r' =>
    obtain ⟨r, he, hh⟩ := h2 r' hd
    exact .inl (by simp [interpret, scan, he, Except.map, hh])

/-- **The front end on a help request whose rest parses** at the level the words select: help. -/
theorem interpret_help_path {c d : Command} {p : List String} (hp : c.pathLevel p = some d)
    {t : String} (ht : readsAs d.opts "help" t = true) (env : String → Option String)
    {rest : List String} (hr : ∃ r', scanAux d rest = .ok r') :
    interpret c env (p ++ t :: rest) = .help (c.pathNames p) := by
  obtain ⟨_, h2⟩ := scanAux_path_help (rest := rest) hp ht
  obtain ⟨r', hd⟩ := hr
  obtain ⟨r, he, hh⟩ := h2 r' hd
  simp [interpret, scan, he, Except.map, hh]

/-! ## The front end's observations -/

theorem spec_front {c : Command} {S : Matches → Spec} {i : Input} {o : Obs} (hs : c.spec S i o)
    {out : Outcome} (h : interpret c (c.envOf i) i.args = out) (hnr : ∀ m, out ≠ .run m) :
    o = c.frontObs out i := by
  rw [Command.spec_eq, h] at hs
  cases out with
  | run m => exact absurd rfl (hnr m)
  | help => exact hs
  | version => exact hs
  | error => exact hs

theorem quiet_frontObs (c : Command) (out : Outcome) (i : Input) : Quiet i (c.frontObs out i) := by
  unfold Command.frontObs
  generalize out.text c = x
  rcases x with _ | ⟨_ | _, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Help -/

theorem helpTriggers_key {c : Command} {v : HelpVariant} (h : c.helpTriggers v = true) :
    v.word = false ∧ argsExtra v.extra = true ∧
    ∀ p ∈ v.roots, ∃ d, c.pathLevel p = some d ∧
      (∀ t ∈ v.tokens, readsAs d.opts "help" t = true) ∧
      (v.extra = .winsOperands → d.subs.isEmpty = true) := by
  simp only [Command.helpTriggers, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨⟨hw, hx⟩, hr⟩ := h
  refine ⟨hw, hx, fun p hp => ?_⟩
  have := hr p hp
  cases hd : c.pathLevel p with
  | none => rw [hd] at this; cases this
  | some d =>
    rw [hd] at this
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨d, rfl, this.1, fun he => this.2.resolve_left (not_not.mpr he)⟩

/-- **A derived args front end meets a help variant** whose requests it answers
(`Command.helpTriggers`) with texts that fit: `Command.spec c S` refines the sentence, for
every `S`. -/
theorem spec_help {c : Command} {v : HelpVariant} (h : c.helpTriggers v = true)
    (hfit : ∀ p ∈ v.roots, v.Fits p (c.helpBytes p)) (S : Matches → Spec) :
    c.spec S ≤ v.sen := by
  obtain ⟨hw, hx, key⟩ := helpTriggers_key h
  intro i o hs
  -- every request is answered by help or a usage error, touching nothing
  have hany : ∀ p ∈ v.roots, ∀ t ∈ v.tokens, ∀ rest, i.args = p ++ t :: rest →
      Quiet i o ∧ (o = c.frontObs (.help (c.pathNames p)) i ∨
        UsageErr (Level.command.outProj o)) := by
    intro p hp t ht rest ha
    obtain ⟨d, hd, hts, _⟩ := key p hp
    rcases interpret_help_or_error hd (hts t ht) (c.envOf i) rest with h1 | ⟨q, e, h1⟩
    · rw [← ha] at h1
      have ho := spec_front hs h1 (fun m h => by cases h)
      subst ho
      exact ⟨quiet_frontObs _ _ _, .inl rfl⟩
    · rw [← ha] at h1
      have ho := spec_front hs h1 (fun m h => by cases h)
      subst ho
      exact ⟨quiet_frontObs _ _ _, .inr (usageErr_line _)⟩
  have hhelp : ∀ p ∈ v.roots, ∀ t ∈ v.tokens, ∀ rest,
      (rest = [] ∨ (v.extra = .winsOperands ∧ ∀ w ∈ rest, Operand w)) → i.args = p ++ t :: rest →
      v.Shows p (Level.command.outProj o) := by
    intro p hp t ht rest hr ha
    obtain ⟨d, hd, hts, hleaf⟩ := key p hp
    have hok : ∃ r', scanAux d rest = .ok r' := by
      rcases hr with rfl | ⟨he, hops⟩
      · exact ⟨({ cmd := d.name }, []), by simp [scanAux]⟩
      · exact scanAux_operands (hleaf he) hops
    have h1 := interpret_help_path hd (hts t ht) (c.envOf i) hok
    rw [← ha] at h1
    have ho := spec_front hs h1 (fun m h => by cases h)
    subst ho
    exact HelpVariant.shows_line (hfit p hp)
  refine ⟨fun p hp => ⟨fun t ht ha => hhelp p hp t ht [] (.inl rfl) ha,
    fun hw' => absurd hw' (by simp [hw]), fun t ht rest hr ha => ?_⟩, fun _ ha => ?_⟩
  · cases hxe : v.extra with
    | ignore => trivial
    | wins => simp [hxe, argsExtra] at hx
    | error => simp [hxe, argsExtra] at hx
    | winsOperands => exact fun hops => hhelp p hp t ht rest (.inr ⟨hxe, hops⟩) ha
    | either =>
      rcases (hany p hp t ht rest ha).2 with ho | hu
      · subst ho; exact .inl (HelpVariant.shows_line (hfit p hp))
      · exact .inr hu
  · obtain ⟨p, hp, ⟨t, ht, ha | ⟨rest, _, ha, _⟩⟩ | ⟨hw', _⟩⟩ := ha
    · exact (hany p hp t ht [] ha).1
    · exact (hany p hp t ht rest ha).1
    · simp [hw] at hw'

/-! ## Grammars with the conventional help flag -/

theorem classify_help : classify "--help" = .long "help" none := by decide +kernel
theorem classify_h : classify "-h" = .short "h" := by decide +kernel
theorem classify_version : classify "--version" = .long "version" none := by decide +kernel
theorem classify_V : classify "-V" = .short "V" := by decide +kernel

/-- The levels of a well-formed grammar with the conventional (global) help flag. -/
theorem pathLevel_helpOpt : ∀ {p : List String} {c d : Command}, c.Good → helpOpt ∈ c.opts →
    c.pathLevel p = some d → d.Good ∧ helpOpt ∈ d.opts
  | [], c, d, hg, hh, hp => by cases hp; exact ⟨hg, hh⟩
  | w :: ws, c, d, hg, hh, hp => by
    obtain ⟨_, _, s, hf, hp'⟩ := pathLevel_cons hp
    have hsm : s ∈ c.subs := lookup_mem hf
    refine pathLevel_helpOpt (hg.sub hsm) ?_ hp'
    show helpOpt ∈ s.opts ++ c.globals
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hh, rfl⟩)

theorem readsAs_of_mem {d : Command} (hg : d.LocalWF) {o : Opt} (ho : o ∈ d.opts)
    (htv : o.takesValue = false) {t : String} :
    ((∃ n ∈ o.long, classify t = .long n none) ∨ ∃ n ∈ o.short, classify t = .short n) →
    readsAs d.opts o.id t = true := by
  rintro (⟨n, hn, hc⟩ | ⟨n, hn, hc⟩)
  · have hf : findLong d.opts n = some o := (findLong_eq_some_iff hg).mpr ⟨ho, hn⟩
    simp [readsAs, hc, hf, htv]
  · have hf : findShort d.opts n = some o := (findShort_eq_some_iff hg).mpr ⟨ho, hn⟩
    simp [readsAs, hc, hf, htv]

/-- **Every well-formed grammar with the conventional help flag** (`helpOpt`, which
`Command.withHelp` adds) answers the help requests of every variant without a `help` word, with
an extra-argument claim the args dialect meets, at paths its words select (levels without
subcommands for `winsOperands`). -/
theorem helpTriggers_of_wf {c : Command} (hwf : c.WF) (hh : helpOpt ∈ c.opts) {v : HelpVariant}
    (hw : v.word = false) (hx : argsExtra v.extra = true)
    (hp : ∀ p ∈ v.roots, ∃ d, c.pathLevel p = some d ∧
      (v.extra = .winsOperands → d.subs.isEmpty = true)) :
    c.helpTriggers v = true := by
  simp only [Command.helpTriggers, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨hw, hx⟩, fun p hpm => ?_⟩
  obtain ⟨d, hd, hleaf⟩ := hp p hpm
  obtain ⟨hg, hhd⟩ := pathLevel_helpOpt hwf.good hh hd
  rw [hd]
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq]
  refine ⟨fun t ht => ?_, ?_⟩
  · have := readsAs_of_mem hg.local hhd rfl (t := t)
    rcases HelpVariant.mem_tokens.mp ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact this (.inl ⟨"help", by simp [helpOpt], classify_help⟩)
    · exact this (.inr ⟨"h", by simp [helpOpt], classify_h⟩)
  · by_cases he : v.extra = .winsOperands
    · exact .inr (hleaf he)
    · exact .inl he

/-- `Command.withHelp` gives a grammar with the conventional help flag. -/
theorem helpOpt_mem_withHelp (c : Command) : helpOpt ∈ c.withHelp.opts := by
  show helpOpt ∈ c.opts ++ [helpOpt]
  simp

/-- `Command.withVersion` keeps the help flag. -/
theorem helpOpt_mem_withVersion {c : Command} (h : helpOpt ∈ c.opts) (ver : String) :
    helpOpt ∈ (c.withVersion ver).opts := by
  show helpOpt ∈ c.opts ++ [versionOpt]
  simp [h]

/-! ## Version -/

/-- **A derived args front end meets a version variant** whose requests it answers. -/
theorem spec_version {c : Command} {v : VersionVariant} (h : c.versionTriggers v = true)
    (hfit : v.Fits c.versionBytes) (S : Matches → Spec) : c.spec S ≤ v.sen := by
  simp only [Command.versionTriggers, Bool.and_eq_true, Option.isSome_iff_exists,
    List.all_eq_true] at h
  obtain ⟨⟨ver, hver⟩, hts⟩ := h
  have key : ∀ t ∈ v.tokens, ∀ i : Input, ∀ o, c.spec S i o → i.args = [t] →
      o = c.frontObs (.version ver) i := by
    intro t ht i o hs ha
    have h1 : interpret c (c.envOf i) i.args = .version ver := by
      rw [ha]
      simp [interpret, scan, scanAux_readsAs (hts t ht), scanAux, consOpts, Except.map, helpPath,
        hver]
    exact spec_front hs h1 (fun m h => by cases h)
  intro i o hs
  refine ⟨fun t ht ha => ?_, fun _ t ht ha => ?_⟩
  · have ho := key t ht i o hs ha
    subst ho
    have hb : c.versionBytes = utf8 (c.name ++ " " ++ ver ++ "\n") := by
      simp [Command.versionBytes, hver]
    rw [hb] at hfit
    exact VersionVariant.shows_line hfit
  · have ho := key t ht i o hs ha
    subst ho
    exact quiet_frontObs _ _ _

/-- **Every well-formed grammar with the conventional version flag and a version** answers
the version requests of every variant. -/
theorem versionTriggers_of_wf {c : Command} (hwf : c.WF) (hv : versionOpt ∈ c.opts)
    (hver : c.version.isSome = true) (v : VersionVariant) : c.versionTriggers v = true := by
  simp only [Command.versionTriggers, hver, Bool.true_and, List.all_eq_true]
  intro t ht
  have := readsAs_of_mem hwf.local hv rfl (t := t)
  rcases VersionVariant.mem_tokens.mp ht with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact this (.inl ⟨"version", by simp [versionOpt], classify_version⟩)
  · exact this (.inr ⟨"V", by simp [versionOpt], classify_V⟩)

theorem versionBytes_withVersion (c : Command) (ver : String) :
    (c.withVersion ver).versionBytes = utf8 (c.name ++ " " ++ ver ++ "\n") := rfl

end Silmaril.Cli.Info
