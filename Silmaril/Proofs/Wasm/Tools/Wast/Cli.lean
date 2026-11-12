module

public import Silmaril.Wasm.Tools.Wast.Cli.Defs

/-!
# The `wast`/`json-from-wast` argument grammar: proofs

Proofs for `Silmaril.Wasm.Tools.Wast.Cli.Thms`: the tokenizer `tokens`
computes exactly the declarative grammar `Spells` (`tokens_ok_iff`), the short-cluster reader
exactly `Cluster`, and the records `jsonRecord`/`wastRecord` read the tokens as stated.
-/

@[expose] public section

namespace Silmaril.Wasm.Tools.Wast.Cli

theorem map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {b : β} (h : x.map f = .ok b) :
    ∃ a, x = .ok a ∧ b = f a := by
  cases x with
  | error e => simp [Except.map] at h
  | ok a => simp only [Except.map, Except.ok.injEq] at h; exact ⟨a, rfl, h.symm⟩

theorem shortCluster_sound {specs : List OptSpec} {whole : String} {next : Option String} :
    ∀ {cs : List Char} {ts : List Tok} {used : Bool},
      shortCluster specs whole next cs = .ok (ts, used) → Cluster specs next cs ts used
  | [], ts, used, h => by
    simp only [shortCluster, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .nil
  | c :: cs, ts, used, h => by
    unfold shortCluster at h
    split at h
    · simp at h
    · rename_i sp hsp
      split at h
      · rename_i hv
        split at h
        · rename_i he
          cases cs with
          | cons _ _ => simp at he
          | nil =>
            split at h
            · rename_i v
              split at h
              · rename_i hval
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact .nextArg hsp hv rfl hval
              · simp at h
            · simp at h
        · rename_i he
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .attached hsp hv (by simpa using he)
      · rename_i hv
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i r hr
          simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .flag hsp (by simpa using hv) (shortCluster_sound hr)

theorem shortCluster_complete {specs : List OptSpec} {whole : String} {next : Option String}
    {cs : List Char} {ts : List Tok} {used : Bool} (h : Cluster specs next cs ts used) :
    shortCluster specs whole next cs = .ok (ts, used) := by
  induction h with
  | nil => rfl
  | flag hsp hv _ ih =>
    simp [shortCluster, hsp, hv, ih, bind, Except.bind, pure, Except.pure]
  | attached hsp hv hne =>
    rename_i c cs _
    cases cs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp [shortCluster, hsp, hv]
  | nextArg hsp hv hn hval =>
    simp [shortCluster, hsp, hv, hn, hval]

/-- The induction hypothesis of `tokens_sound`: soundness for every shorter command line. -/
abbrev SoundBelow (specs : List OptSpec) (rest : List String) : Prop :=
  ∀ r ts, r.length ≤ rest.length → tokens specs r = .ok ts → Spells specs r ts

theorem beq_dashDash {a : String} (hdd : a ≠ "--") : (a == "--") = false := by
  simpa using hdd

/-- `tokens` on `--name=value` or `--name value`. -/
theorem tokens_sound_longValue {specs : List OptSpec} {a name : String} {val : Option String}
    {rest : List String} {sp : OptSpec} {ts : List Tok} (hdd : a ≠ "--")
    (hl : a.startsWith "--" = true) (hsplit : splitEq (a.drop 2).toString = (name, val))
    (hsp : specs.find? (·.long == name) = some sp) (hv : sp.takesValue = true)
    (ih : SoundBelow specs rest) (h : tokens specs (a :: rest) = .ok ts) :
    Spells specs (a :: rest) ts := by
  rw [tokens] at h
  simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp, hv] at h
  cases val with
  | some v =>
    obtain ⟨ts', h', rfl⟩ := map_ok h
    exact .longEq hdd hl hsplit hsp hv (ih rest ts' (Nat.le_refl _) h')
  | none =>
    cases rest with
    | nil => simp at h
    | cons v rest' =>
      by_cases hval : isValue v = true
      · simp only [hval, ↓reduceIte] at h
        obtain ⟨ts', h', rfl⟩ := map_ok h
        exact .longNext hdd hl hsplit hsp hv hval (ih rest' ts' (by simp) h')
      · simp [hval] at h

/-- `tokens` on `--flag`. -/
theorem tokens_sound_longFlag {specs : List OptSpec} {a name : String} {val : Option String}
    {rest : List String} {sp : OptSpec} {ts : List Tok} (hdd : a ≠ "--")
    (hl : a.startsWith "--" = true) (hsplit : splitEq (a.drop 2).toString = (name, val))
    (hsp : specs.find? (·.long == name) = some sp) (hv : sp.takesValue = false)
    (ih : SoundBelow specs rest) (h : tokens specs (a :: rest) = .ok ts) :
    Spells specs (a :: rest) ts := by
  rw [tokens] at h
  simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp, hv] at h
  cases val with
  | some v => simp at h
  | none =>
    obtain ⟨ts', h', rfl⟩ := map_ok h
    exact .longFlag hdd hl hsplit hsp hv (ih rest ts' (Nat.le_refl _) h')

/-- `tokens` on a long option. -/
theorem tokens_sound_long {specs : List OptSpec} {a : String} {rest : List String}
    {ts : List Tok} (hdd : a ≠ "--") (hl : a.startsWith "--" = true)
    (ih : SoundBelow specs rest) (h : tokens specs (a :: rest) = .ok ts) :
    Spells specs (a :: rest) ts := by
  rcases hsplit : splitEq (a.drop 2).toString with ⟨name, val⟩
  cases hsp : specs.find? (·.long == name) with
  | none =>
    rw [tokens] at h
    simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp,
      reduceCtorEq] at h
  | some sp =>
    cases hv : sp.takesValue
    · exact tokens_sound_longFlag hdd hl hsplit hsp hv ih h
    · exact tokens_sound_longValue hdd hl hsplit hsp hv ih h

/-- `tokens` on a short cluster. -/
theorem tokens_sound_short {specs : List OptSpec} {a : String} {rest : List String}
    {ts : List Tok} (hdd : a ≠ "--") (hl : a.startsWith "--" = false)
    (hs : a.startsWith "-" = true ∧ a ≠ "-")
    (ih : SoundBelow specs rest) (h : tokens specs (a :: rest) = .ok ts) :
    Spells specs (a :: rest) ts := by
  have hs' : (a.startsWith "-" && a != "-") = true := by simp [hs.1, hs.2]
  rw [tokens] at h
  simp only [beq_dashDash hdd, hl, hs', Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · simp at h
  · rename_i tsc used hc
    have hcl : Cluster specs rest.head? (a.drop 1).toString.toList tsc used :=
      shortCluster_sound hc
    cases used with
    | true =>
      obtain ⟨ts', h', rfl⟩ := map_ok h
      exact .short hl hs.1 hs.2 hcl (ih rest.tail ts' (by simp) h')
    | false =>
      obtain ⟨ts', h', rfl⟩ := map_ok h
      exact .short hl hs.1 hs.2 hcl (ih rest ts' (Nat.le_refl _) h')

/-- `tokens` on a positional argument. -/
theorem tokens_sound_pos {specs : List OptSpec} {a : String} {rest : List String}
    {ts : List Tok} (hdd : a ≠ "--") (hl : a.startsWith "--" = false)
    (hs : ¬ (a.startsWith "-" = true ∧ a ≠ "-"))
    (ih : SoundBelow specs rest) (h : tokens specs (a :: rest) = .ok ts) :
    Spells specs (a :: rest) ts := by
  have hs' : (a.startsWith "-" && a != "-") = false := by
    cases hm : a.startsWith "-" <;> simp_all
  rw [tokens] at h
  simp only [beq_dashDash hdd, hl, hs', Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨ts', h', rfl⟩ := map_ok h
  have hp : a.startsWith "-" = false ∨ a = "-" := by
    cases hm : a.startsWith "-" <;> simp_all
  exact .pos hdd hl hp (ih rest ts' (Nat.le_refl _) h')

/-- `tokens` is sound for `Spells`. -/
theorem tokens_sound (specs : List OptSpec) :
    ∀ (args : List String) (ts : List Tok), tokens specs args = .ok ts → Spells specs args ts
  | [], ts, h => by
    rw [tokens] at h
    cases h
    exact .nil
  | a :: rest, ts, h => by
    have ih : SoundBelow specs rest := fun r ts' _ hr => tokens_sound specs r ts' hr
    by_cases hdd : a = "--"
    · subst hdd
      rw [tokens] at h
      cases h
      exact .dashDash
    by_cases hl : a.startsWith "--" = true
    · exact tokens_sound_long hdd hl ih h
    have hl' : a.startsWith "--" = false := by simpa using hl
    by_cases hs : a.startsWith "-" = true ∧ a ≠ "-"
    · exact tokens_sound_short hdd hl' hs ih h
    · exact tokens_sound_pos hdd hl' hs ih h
termination_by args => args.length

/-- `tokens` on a short cluster, backwards. -/
theorem tokens_complete_short {specs : List OptSpec} {a : String} {rest : List String}
    {tsc ts' : List Tok} {used : Bool} (hl : a.startsWith "--" = false)
    (hs : a.startsWith "-" = true) (hne : a ≠ "-")
    (hc : Cluster specs rest.head? (a.drop 1).toString.toList tsc used)
    (ih : tokens specs (if used then rest.tail else rest) = .ok ts') :
    tokens specs (a :: rest) = .ok (tsc ++ ts') := by
  have hdd : (a == "--") = false := by
    cases hx : (a == "--")
    · rfl
    · simp only [beq_iff_eq] at hx; subst hx; simp at hl
  have hs' : (a.startsWith "-" && a != "-") = true := by simp [hs, hne]
  have hc' := shortCluster_complete (whole := a) hc
  rw [tokens]
  cases used <;> simp_all [Except.map]

/-- `tokens` is complete for `Spells`. -/
theorem tokens_complete {specs : List OptSpec} {args : List String} {ts : List Tok}
    (h : Spells specs args ts) : tokens specs args = .ok ts := by
  induction h with
  | nil => rw [tokens]
  | dashDash => rw [tokens]; simp
  | longEq hdd hl hsplit hsp hv _ ih =>
    rw [tokens]
    simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp, hv, ih, Except.map]
  | longNext hdd hl hsplit hsp hv hval _ ih =>
    rw [tokens]
    simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp, hv, hval, ih,
      Except.map]
  | longFlag hdd hl hsplit hsp hv _ ih =>
    rw [tokens]
    simp only [beq_dashDash hdd, Bool.false_eq_true, ↓reduceIte, hl, hsplit, hsp, hv, ih, Except.map]
  | short hl hs hne hc _ ih => exact tokens_complete_short hl hs hne hc ih
  | @pos a rest ts hdd hl hp _ ih =>
    have hs : (a.startsWith "-" && a != "-") = false := by rcases hp with hp | hp <;> simp [hp]
    rw [tokens]
    simp only [beq_dashDash hdd, hl, hs, Bool.false_eq_true, ↓reduceIte, ih, Except.map]

/-- **`tokens` computes the declarative grammar.** -/
theorem tokens_ok_iff {specs : List OptSpec} {args : List String} {ts : List Tok} :
    tokens specs args = .ok ts ↔ Spells specs args ts :=
  ⟨tokens_sound specs args ts, tokens_complete⟩

/-! ## The records -/

theorem jsonRecord_ok {ts : List Tok} {o : JsonOpts} (h : jsonRecord ts = .ok o) :
    positionals ts = [o.wast] ∧ single ts "output" = .ok o.output ∧
      single ts "wasm-dir" = .ok o.wasmDir ∧ flag ts "pretty" = .ok o.pretty := by
  simp only [jsonRecord, bind, Except.bind] at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i out hout
  split at h; · simp at h
  rename_i wd hwd
  split at h; · simp at h
  rename_i pr hpr
  split at h; · simp at h
  split at h
  · rename_i hpos
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hpos, hout, hwd, hpr⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The asserts a successful `wastRecord` read are known names. -/
theorem asserts_ok {ts : List Tok}
    (hfind : ∀ b, (listValues ts "assert").find? (fun a => !assertValues.contains a) = some b →
      False) :
    ∀ a ∈ listValues ts "assert", a ∈ assertValues := by
  intro a ha
  have hn : (listValues ts "assert").find? (fun a => !assertValues.contains a) = none := by
    cases hx : (listValues ts "assert").find? (fun a => !assertValues.contains a) with
    | none => rfl
    | some b => exact absurd hx (hfind b)
  have hc : ¬ (!assertValues.contains a) = true := List.find?_eq_none.1 hn a ha
  simpa using hc

/-- The features a successful `wastRecord` read parse. -/
theorem features_ok {ts : List Tok}
    (hbad : ∀ v m, badFeature? ((values ts "features").filterMap id) = some (v, m) → False) :
    ∀ v ∈ (values ts "features").filterMap id, ∃ acts, Features.parseFeatures v = .ok acts := by
  intro v hv
  have hn : badFeature? ((values ts "features").filterMap id) = none := by
    cases hb : badFeature? ((values ts "features").filterMap id) with
    | none => rfl
    | some p => exact absurd hb (hbad p.1 p.2)
  unfold badFeature? at hn
  have := List.findSome?_eq_none_iff.1 hn v hv
  cases hp : Features.parseFeatures v with
  | ok acts => exact ⟨acts, rfl⟩
  | error m => simp [hp] at this

theorem wastRecord_ok {ts : List Tok} {o : WastOpts} (h : wastRecord ts = .ok o) :
    positionals ts = o.input.toList ∧
      flag ts "ignore-error-messages" = .ok o.ignoreErrorMessages ∧
      single ts "snapshot" = .ok o.snapshot ∧
      o.asserts = listValues ts "assert" ∧ (∀ a ∈ o.asserts, a ∈ assertValues) ∧
      o.features = (values ts "features").filterMap id ∧
      (∀ v ∈ o.features, ∃ acts, Features.parseFeatures v = .ok acts) := by
  simp only [wastRecord, bind, Except.bind] at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i iem hiem
  split at h; · simp at h
  split at h; · simp at h
  rename_i snap hsnap
  split at h; · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hfind
  simp only [pure, Except.pure] at h
  split at h; · simp [throw, throwThe, MonadExceptOf.throw] at h
  rename_i hbad
  have hA := asserts_ok hfind
  have hF := features_ok hbad
  split at h <;> try (simp only [Except.ok.injEq] at h; subst h; exact ⟨‹_›, hiem, hsnap, rfl, hA, rfl, hF⟩)
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The readers -/

theorem jsonOpts?_run {args : List String} {o : JsonOpts} (h : jsonOpts? args = .run o) :
    ∃ ts, Spells jsonSpecs args ts ∧ values ts "help" = [] ∧ jsonRecord ts = .ok o := by
  unfold jsonOpts? at h
  split at h
  · simp at h
  · rename_i ts hts
    split at h
    · simp at h
    · rename_i hhelp
      split at h
      · rename_i o' ho
        simp only [Parsed.run.injEq] at h
        subst h
        exact ⟨ts, tokens_sound _ _ _ hts, by simpa using hhelp, ho⟩
      · simp at h

theorem wastOpts?_run {args : List String} {o : WastOpts} (h : wastOpts? args = .run o) :
    ∃ ts, Spells wastSpecs args ts ∧ values ts "help" = [] ∧ wastRecord ts = .ok o := by
  unfold wastOpts? at h
  split at h
  · simp at h
  · rename_i ts hts
    split at h
    · simp at h
    · rename_i hhelp
      split at h
      · rename_i o' ho
        simp only [Parsed.run.injEq] at h
        subst h
        exact ⟨ts, tokens_sound _ _ _ hts, by simpa using hhelp, ho⟩
      · simp at h

end Silmaril.Wasm.Tools.Wast.Cli
