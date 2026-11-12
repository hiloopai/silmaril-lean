module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Proofs.Cli.Args.Scan
public import Silmaril.Proofs.Cli.Args.Values
public import Silmaril.Proofs.Cli.Args.Resolve

@[expose] public section

/-!
# Proofs: from matches back to an argument vector

The direction opposite to parsing: every result of the front end is reached by a command line,
and typed values can be spelled so that they read back.

* **`interpret_render`**: for every valid invocation of a well-formed grammar that asks for
  neither help nor the version, the normal form `render c fs` is a command line whose outcome is
  the resolution of `fs` (`resolveOutcome`): every `Matches` (and every resolution error) that
  resolution gives is the outcome of an argument vector;
* `interpret_normalize`: an argument vector and its normal form have the same outcome;
* `Given.ofValue`, `givenValue_ofValue`, **`resolveOpt_ofValues`**: values of an option's type,
  given as occurrences, resolve to themselves;
* **`binds_show`**: positional words spelled canonically from the values they bound bind to the
  same values (so `"007"` may be written `"7"`).

A Silmaril addition.
-/

namespace Silmaril.Cli

/-- An invocation asks for the version when its root frame has the version flag and the
grammar has a version. -/
def AsksVersion (c : Command) : Invocation → Prop
  | f :: _ => c.version.isSome ∧ f.opts.any (·.1 == "version") = true
  | [] => False

theorem interpret_of_scan {c : Command} {env : String → Option String} {argv : List String}
    {fs : Invocation} (h : scan c argv = .ok fs) (hh : helpPath fs [] = none)
    (hver : ¬ AsksVersion c fs) : interpret c env argv = resolveOutcome c env fs := by
  unfold interpret
  rw [h]
  simp only [hh]
  cases hv : c.version with
  | none => cases fs <;> rfl
  | some v =>
    match fs, hver with
    | [], _ => rfl
    | f :: rest, hver =>
      have hf : f.opts.any (·.1 == "version") = false := by
        cases hany : f.opts.any (·.1 == "version")
        · rfl
        · exact absurd ⟨by simp [hv], hany⟩ hver
      simp [hf]

/-- **Every result of resolution is the outcome of a command line**: the normal form of a valid
invocation that asks for neither help nor the version. -/
theorem interpret_render {c : Command} (hwf : c.WF) {fs : Invocation} (hv : Valid c fs)
    (hh : helpPath fs [] = none) (hver : ¬ AsksVersion c fs) (env : String → Option String) :
    interpret c env (render c fs) = resolveOutcome c env fs :=
  interpret_of_scan (scan_render hwf hv) hh hver

/-- An argument vector and its normal form have the same outcome. -/
theorem interpret_normalize {c : Command} (hwf : c.WF) {argv nf : List String}
    (h : normalize c argv = .ok nf) (env : String → Option String) :
    interpret c env nf = interpret c env argv := by
  unfold normalize at h
  cases hs : scan c argv with
  | error l => simp [hs, Except.map] at h
  | ok fs =>
    have hnf : render c fs = nf := by simpa [hs, Except.map] using h
    have hs' : scan c nf = .ok fs := hnf ▸ scan_render_scan hwf hs
    simp [interpret, hs, hs']

/-! ## Typed values as occurrences -/

/-- The occurrence that gives a value. -/
def Given.ofValue : Value → Given
  | .flag => .on
  | .off => .off
  | v => .val v.show

theorem givenValue_ofValue {id : String} {t : ArgType} {d : Option String} {v : Value}
    (h : t.Has v) : givenValue id t d (Given.ofValue v) = .ok v := by
  match t, v, h with
  | .str, .str s, _ => rfl
  | .path, .str s, _ => rfl
  | .nat, .nat n, h => exact parseAs_eq_ok.mpr (parse_show h)
  | .int, .int i, h => exact parseAs_eq_ok.mpr (parse_show h)
  | .enum cs, .str s, h => exact parseAs_eq_ok.mpr (parse_show h)

theorem mapM_givenValue {id : String} {t : ArgType} {d : Option String} :
    ∀ {vs : List Value}, (∀ v ∈ vs, t.Has v) →
      (vs.map Given.ofValue).mapM (givenValue id t d) = .ok vs
  | [], _ => rfl
  | v :: vs, h => by
    have hv : givenValue id t d (Given.ofValue v) = .ok v := givenValue_ofValue (h v (by simp))
    have hvs : (vs.map Given.ofValue).mapM (givenValue id t d) = .ok vs :=
      mapM_givenValue fun w hw => h w (List.mem_cons_of_mem _ hw)
    simp only [List.map_cons, List.mapM_cons, hv, hvs]
    rfl

/-- **Values of an option's type, given as occurrences, resolve to themselves.** -/
theorem resolveOpt_ofValues {env : String → Option String} {o : Opt} {t : ArgType}
    (ht : o.arg = some t) {vs : List Value} (hvs : ∀ v ∈ vs, t.Has v) (hne : vs ≠ [])
    (hrep : vs.length ≤ 1 ∨ o.repeated = true) :
    resolveOpt env (vs.map Given.ofValue) o = .ok (o.id, vs) := by
  have hr : (!o.repeated && (vs.map Given.ofValue).length > 1) = false := by
    rcases hrep with h | h <;> simp [h] <;> omega
  have hne' : (vs.map Given.ofValue).isEmpty = false := by
    cases vs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  rw [resolveOpt_cmdline ht hne' hr, mapM_givenValue hvs]
  rfl

/-! ## Positional words from values -/

theorem binds_nil_values {ps : List Pos} {r : List (String × List Value)} (h : Binds ps [] r) :
    r.flatMap (·.2) = [] := by
  generalize hw : ([] : List String) = ws at h
  induction h with
  | nil => rfl
  | one _ _ _ _ => cases hw
  | optSome _ _ _ _ => cases hw
  | optNone _ _ ih => simpa using ih hw
  | @many p ps ws vs r _ hvs _ ih =>
    subst hw
    have hv : vs = [] := by simpa using hvs.symm
    simp [hv, ih rfl]
  | atLeastOne _ hne _ _ _ => exact absurd hw.symm hne

theorem parse_show_of_parse {t : ArgType} {w : String} {v : Value} (h : t.parse w = some v) :
    t.parse v.show = some v :=
  parse_show (parse_has h)

theorem mapM_option_mem {α β : Type} {f : α → Option β} :
    ∀ {ws : List α} {vs : List β}, ws.mapM f = some vs → ∀ v ∈ vs, ∃ w, f w = some v
  | [], vs, h => by simp at h; subst h; simp
  | w :: ws, vs, h => by
    cases hw : f w with
    | none => simp [List.mapM_cons, hw] at h
    | some b =>
      cases hr : ws.mapM f with
      | none => simp [List.mapM_cons, hw, hr] at h
      | some bs =>
        have hvs : vs = b :: bs := by simpa [List.mapM_cons, hw, hr] using h.symm
        intro v hv
        rw [hvs] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨w, hw⟩
        · exact mapM_option_mem hr v hv

theorem mapM_option_length {α β : Type} {f : α → Option β} :
    ∀ {ws : List α} {vs : List β}, ws.mapM f = some vs → vs.length = ws.length
  | [], vs, h => by simp at h; subst h; rfl
  | w :: ws, vs, h => by
    cases hw : f w with
    | none => simp [List.mapM_cons, hw] at h
    | some b =>
      cases hr : ws.mapM f with
      | none => simp [List.mapM_cons, hw, hr] at h
      | some bs =>
        have hvs : vs = b :: bs := by simpa [List.mapM_cons, hw, hr] using h.symm
        rw [hvs, List.length_cons, List.length_cons, mapM_option_length hr]

theorem mapM_show_of_mapM {t : ArgType} {ws : List String} {vs : List Value}
    (h : ws.mapM t.parse = some vs) : (vs.map Value.show).mapM t.parse = some vs := by
  have hall : ∀ v ∈ vs, t.Has v := by
    intro v hv
    obtain ⟨w, hw⟩ := mapM_option_mem h v hv
    exact parse_has hw
  exact mapM_parse_show hall

/-- The canonical words of bound values. -/
def wordsOf (r : List (String × List Value)) : List String := (r.flatMap (·.2)).map Value.show

theorem wordsOf_cons (k : String) (vs : List Value) (r : List (String × List Value)) :
    wordsOf ((k, vs) :: r) = vs.map Value.show ++ wordsOf r := by
  simp [wordsOf]

theorem wordsOf_nil_values {ps : List Pos} {r : List (String × List Value)} (h : Binds ps [] r) :
    wordsOf r = [] := by
  simp [wordsOf, binds_nil_values h]

/-- **Canonical words bind to the same values.** -/
theorem binds_show {ps : List Pos} {ws : List String} {r : List (String × List Value)}
    (h : Binds ps ws r) : Binds ps (wordsOf r) r := by
  induction h with
  | nil => exact .nil
  | @one p ps w ws v r ha hv _ ih =>
    rw [wordsOf_cons]; exact .one ha (parse_show_of_parse hv) ih
  | @optSome p ps w ws v r ha hv _ ih =>
    rw [wordsOf_cons]; exact .optSome ha (parse_show_of_parse hv) ih
  | @optNone p ps r ha hr _ =>
    rw [wordsOf_cons, wordsOf_nil_values hr]; exact .optNone ha hr
  | @many p ps ws vs r ha hvs hr _ =>
    rw [wordsOf_cons, wordsOf_nil_values hr, List.append_nil]
    exact .many ha (mapM_show_of_mapM hvs) hr
  | @atLeastOne p ps ws vs r ha hne hvs hr _ =>
    have hvne : vs ≠ [] := by
      intro he
      have hl := mapM_option_length hvs
      rw [he] at hl
      exact hne (List.eq_nil_of_length_eq_zero hl.symm)
    rw [wordsOf_cons, wordsOf_nil_values hr, List.append_nil]
    exact .atLeastOne ha (by simpa using hvne) (mapM_show_of_mapM hvs) hr

end Silmaril.Cli
