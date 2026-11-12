module

public import Silmaril.Cli.Getopt.Defs
public import Silmaril.Proofs.Cli.Getopt.Permute

/-!
# Proofs: the getopt reading and the args front end

* `find_longsOf`, `find_shortsOf`: the derived table finds the option the args lookups find;
* `readTok_readOpt`: where the pre-pass passes a token, getopt and the args dialect read it
  alike (the same occurrences and the same use of the next token, or an error on both sides);
* `parse_scanAux`: where the pre-pass passes a command line, getopt (in either ordering) and the
  args scanner read the same frame, or both fail;
* **`read_agrees`**: so the getopt reading and `interpret` agree (`Agrees`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Cli.Getopt

open Silmaril.Cli Silmaril.Cli.Getopt

/-! ## The derived table -/

/-- The longopts entry of the long name `n` of `o`. -/
def longEntry (n : String) (o : Opt) : Long := { name := n, arg := hasArgOf o, key := o.id }

/-- The optstring character `ch` of `o`. -/
def shortEntry (ch : Char) (o : Opt) : Short := { ch, arg := hasArgOf o, key := o.id }

theorem find_map_long (o : Opt) (n : String) :
    ∀ l : List String, (l.map fun m => longEntry m o).find? (·.name == n) =
      if l.contains n then some (longEntry n o) else none
  | [] => by simp
  | m :: l => by
    rw [List.map_cons, List.find?_cons]
    by_cases h : m = n
    · subst h; simp [longEntry]
    · have : ((longEntry m o).name == n) = false := by simp [longEntry, h]
      rw [this]
      simp only
      rw [find_map_long o n l]
      have : (m :: l).contains n = l.contains n := by
        simp only [List.contains_cons]
        have : (n == m) = false := by simpa using Ne.symm h
        simp [this]
      rw [this]

theorem find_longsOf (n : String) :
    ∀ os : List Opt, (os.flatMap longsOf).find? (·.name == n) = (findLong os n).map (longEntry n)
  | [] => rfl
  | o :: os => by
    rw [List.flatMap_cons, List.find?_append]
    have h1 : (longsOf o).find? (·.name == n) = if o.long.contains n then some (longEntry n o)
        else none := find_map_long o n o.long
    rw [h1, find_longsOf n os]
    simp only [findLong, lookupKey, List.find?_cons]
    cases o.long.contains n <;> simp

theorem singleton_of_toList {s : String} {c : Char} (h : s.toList = [c]) : s = String.singleton c :=
  String.toList_inj.1 (by simp [h])

theorem find_filterMap_short (o : Opt) (ch : Char) :
    ∀ l : List String, (l.filterMap (shortOf o)).find? (·.ch == ch) =
      if l.contains (String.singleton ch) then some (shortEntry ch o) else none
  | [] => by simp
  | s :: l => by
    rw [List.filterMap_cons, List.contains_cons]
    have ih := find_filterMap_short o ch l
    unfold shortOf
    cases hs : s.toList with
    | nil =>
      have : (String.singleton ch == s) = false := by
        simp only [beq_eq_false_iff_ne]; intro he; subst he; simp at hs
      simp only [this, Bool.false_or]; exact ih
    | cons c r =>
      cases r with
      | nil =>
        simp only [List.find?_cons]
        by_cases hch : c = ch
        · subst hch
          have := singleton_of_toList hs
          subst this
          simp [shortEntry]
        · have : (String.singleton ch == s) = false := by
            simp only [beq_eq_false_iff_ne]; intro he; subst he; simp at hs; exact hch hs.symm
          simp only [this, Bool.false_or]
          have : (c == ch) = false := by simpa using hch
          simp only [this]; exact ih
      | cons d r =>
        have : (String.singleton ch == s) = false := by
          simp only [beq_eq_false_iff_ne]; intro he; subst he; simp at hs
        simp only [this, Bool.false_or]; exact ih

theorem find_shortsOf (ch : Char) :
    ∀ os : List Opt, (os.flatMap shortsOf).find? (·.ch == ch) =
      (findShort (clusterOpts os) (String.singleton ch)).map (shortEntry ch)
  | [] => rfl
  | o :: os => by
    rw [List.flatMap_cons, List.find?_append, find_shortsOf ch os]
    unfold shortsOf
    cases hx : o.exact
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [find_filterMap_short o ch o.short]
      simp only [clusterOpts, List.filter_cons, hx, Bool.not_false, ↓reduceIte, findShort,
        lookupKey, List.find?_cons]
      cases o.short.contains (String.singleton ch) <;> simp
    · simp [clusterOpts, hx]

/-! ## One token -/

theorem toOption_map {ε α β : Type} (f : α → β) (e : Except ε α) :
    (e.map f).toOption = e.toOption.map f := by
  cases e <;> rfl

/-- Under `Fits`, no option is negatable, so `--no-x` that is no option's long name is unknown. -/
theorem readNo_error {os : List Opt} (hneg : ∀ o ∈ os, o.negatable = false) {t n : String}
    {v : Option String} : (readNo os t n v).toOption = none := by
  unfold readNo
  split
  · rename_i o ho
    have hm : o ∈ os := by
      simp only [Option.bind_eq_some_iff] at ho
      obtain ⟨_, _, h⟩ := ho
      exact List.mem_of_find?_eq_some h
    simp [hneg o hm, Except.toOption]
  · rfl

theorem readLong_agree {os : List Opt} (hneg : ∀ o ∈ os, o.negatable = false) {t : Table}
    (ht : t.longs = os.flatMap longsOf) {tok n : String} {v next : Option String}
    (hd : ∀ l, resolveLong (os.flatMap longsOf) n = .ok l → l.name = n) :
    (Getopt.readLong t tok n v next).toOption = (Cli.readLong os tok n v next).toOption := by
  unfold Getopt.readLong Cli.readLong
  rw [ht]
  cases hf : findLong os n with
  | some o =>
    have he : (os.flatMap longsOf).find? (·.name == n) = some (longEntry n o) := by
      rw [find_longsOf, hf]; rfl
    rw [resolveLong_exact he]
    simp only [longEntry, hasArgOf, Opt.takesValue, valueFromNext]
    cases ha : o.arg <;> cases hvo : o.valueOptional <;> cases v <;> cases next <;>
      simp [Except.toOption]
  | none =>
    rw [readNo_error hneg]
    cases hr : resolveLong (os.flatMap longsOf) n with
    | ok l =>
      exfalso
      have hn := hd l hr
      have hm := (resolveLong_ok hr).1
      have : (os.flatMap longsOf).find? (·.name == n) ≠ none := by
        intro hc
        have := List.find?_eq_none.1 hc l hm
        simp [hn] at this
      rw [find_longsOf, hf] at this
      exact this rfl
    | error cs => cases cs <;> rfl

theorem hasArgOf_cases (o : Opt) :
    (hasArgOf o = .none ∧ o.arg.isSome = false) ∨
      (hasArgOf o = .optional ∧ o.arg.isSome = true ∧ o.valueOptional = true) ∨
      (hasArgOf o = .required ∧ o.arg.isSome = true ∧ o.valueOptional = false) := by
  unfold hasArgOf
  cases o.arg with
  | none => simp
  | some _ => cases o.valueOptional <;> simp

theorem readCluster_agree {os : List Opt} {t : Table} (ht : t.shorts = os.flatMap shortsOf)
    {tok : String} {next : Option String} :
    ∀ cs : List Char, clusterDiverge t tok cs = none →
      (Getopt.readCluster t tok next cs).toOption = (Cli.readCluster os tok next cs).toOption
  | [], _ => rfl
  | ch :: r, hd => by
    unfold clusterDiverge at hd
    unfold Getopt.readCluster Cli.readCluster
    by_cases hw : (t.wLong && ch == 'W') = true
    · simp [hw] at hd
    · simp only [Bool.not_eq_true] at hw
      simp only [hw, Bool.false_eq_true, ↓reduceIte] at hd ⊢
      have hfc : findChar t ch =
          (findShort (clusterOpts os) (String.singleton ch)).map (shortEntry ch) := by
        unfold findChar; rw [ht, find_shortsOf]
      rw [hfc] at hd ⊢
      cases hf : findShort (clusterOpts os) (String.singleton ch) with
      | none => rfl
      | some o =>
        simp only [hf, Option.map_some] at hd ⊢
        simp only [shortEntry, Opt.takesValue, valueFromNext] at hd ⊢
        rcases hasArgOf_cases o with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · simp only [h1, h2] at hd ⊢
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [toOption_map, toOption_map, readCluster_agree ht r hd]
        all_goals
          simp only [h1, h2, h3] at hd ⊢
          cases r with
          | nil => cases next <;> simp [Except.toOption]
          | cons a b =>
            by_cases hq : a = '='
            · subst hq; simp at hd
            · simp [attachedValue, hq, Except.toOption]

theorem readShort_fits {os : List Opt} (hx : ∀ o ∈ os, o.exact = false)
    (hs : ∀ o ∈ os, ∀ s ∈ o.short, s.toList.length = 1) {tok n : String} {next : Option String} :
    Cli.readShort os tok n next = Cli.readCluster os tok next n.toList := by
  unfold Cli.readShort
  cases hf : findShort os n with
  | none => rfl
  | some o =>
    simp only
    have hm : o ∈ os := List.mem_of_find?_eq_some hf
    have hn : n ∈ o.short := by have := List.find?_some hf; simpa using this
    obtain ⟨ch, hch⟩ := List.length_eq_one_iff.1 (hs o hm n hn)
    have hn' : n = String.singleton ch := singleton_of_toList hch
    have hco : clusterOpts os = os := List.filter_eq_self.2 (by intro o ho; simp [hx o ho])
    rw [hch]
    unfold Cli.readCluster
    rw [hco, ← hn', hf]
    simp only
    cases o.takesValue <;> simp [Cli.readCluster, Except.map]

/-- **One token**: where the pre-pass passes an option token, getopt with the derived table and
the args dialect read it alike, or both fail. -/
theorem readTok_readOpt {c : Command} (hf : Fits c) {plus w : Bool} {tok : String}
    {next : Option String} (hd : tokDiverge (Table.ofCommand c plus w) tok = none) :
    (readTok (Table.ofCommand c plus w) tok next).toOption =
      (readOpt c.opts tok next).toOption := by
  obtain ⟨_, hopt⟩ := hf
  unfold readTok readOpt
  unfold tokDiverge at hd
  cases hc : classify tok with
  | dashdash => rfl
  | word s => rfl
  | long n v =>
    simp only [hc] at hd
    refine readLong_agree (fun o ho => (hopt o ho).2.1) rfl fun l hl => ?_
    simp only [Table.ofCommand] at hd
    rw [hl] at hd
    simpa using hd
  | short n =>
    simp only [hc] at hd
    simp only
    rw [readShort_fits (fun o ho => (hopt o ho).1) (fun o ho => (hopt o ho).2.2)]
    exact readCluster_agree rfl n.toList hd

/-! ## The command line -/

/-- The args frame of a getopt reading. -/
def frameOf (c : Command) (p : Parsed) : Frame × Invocation :=
  ({ cmd := c.name, opts := p.opts, args := p.operands }, [])

theorem isWord_classify {x : String} (h : isWord x = true) : classify x = .word x := by
  simpa [isWord] using h

theorem words_scanAux {c : Command} (hs : c.subs = []) :
    ∀ ws : List String, (∀ x ∈ ws, isWord x = true) →
      scanAux c ws = .ok ({ cmd := c.name, args := ws }, [])
  | [], _ => rfl
  | x :: ws, h => by
    have hw := isWord_classify (h x List.mem_cons_self)
    rw [scanAux, hw]
    simp only [hs, List.isEmpty_nil]
    rw [words_scanAux hs ws (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

/-- **The command line**: where the pre-pass passes, getopt (in either ordering) and the args
scanner read the same frame, or both fail. -/
theorem parse_scanAux {c : Command} (hf : Fits c) {plus w : Bool} {ord : Order} :
    ∀ argv : List String, pre (Table.ofCommand c plus w) ord argv = none →
      (parse (Table.ofCommand c plus w) ord argv).toOption.map (frameOf c) =
        (scanAux c argv).toOption
  | [], _ => rfl
  | tok :: rest, hp => by
    have hsub := hf.1
    unfold pre at hp
    unfold parse scanAux
    cases hc : classify tok with
    | dashdash => rfl
    | word s =>
      have hs := classify_word_eq hc
      subst hs
      simp only [hc] at hp
      simp only [hsub, List.isEmpty_nil]
      cases ord with
      | requireOrder =>
        simp only [Option.map_eq_none_iff, List.find?_eq_none, Bool.not_eq_true',
          Bool.not_eq_false] at hp
        have hall : ∀ x ∈ rest, isWord x = true := by
          intro x hx; have := hp x hx; simpa using this
        rw [words_scanAux hsub rest hall]
        rfl
      | permute =>
        have ih := parse_scanAux hf rest hp
        cases hr : parse (Table.ofCommand c plus w) .permute rest <;>
          cases hs : scanAux c rest <;>
            (simp_all [Except.map, Except.toOption, consArg, frameOf]) <;> (subst ih; simp)
    | long n v =>
      simp only [hc] at hp
      cases hd : tokDiverge (Table.ofCommand c plus w) tok with
      | some d => simp [hd] at hp
      | none =>
        simp only [hd] at hp
        have htok := readTok_readOpt (next := rest.head?) hf hd
        simp only
        cases hrt : readTok (Table.ofCommand c plus w) tok rest.head? with
        | error e =>
          cases hro : readOpt c.opts tok rest.head? with
          | error e' => rfl
          | ok r => simp [hrt, hro, Except.toOption] at htok
        | ok q =>
          obtain ⟨ps, b⟩ := q
          cases hro : readOpt c.opts tok rest.head? with
          | error e' => simp [hrt, hro, Except.toOption] at htok
          | ok r =>
            simp only [hrt, hro, Except.toOption, Option.some.injEq] at htok
            subst htok
            simp only [hrt] at hp
            cases b with
            | false =>
              have ih := parse_scanAux hf rest hp
              cases hr : parse (Table.ofCommand c plus w) ord rest <;>
                cases hs : scanAux c rest <;>
                  (simp_all [Except.map, Except.toOption, consOpts, frameOf]) <;> (subst ih; simp)
            | true =>
              cases rest with
              | nil => rfl
              | cons x rest' =>
                have ih := parse_scanAux hf rest' hp
                cases hr : parse (Table.ofCommand c plus w) ord rest' <;>
                  cases hs : scanAux c rest' <;>
                  (simp_all [Except.map, Except.toOption, consOpts, frameOf]) <;> (subst ih; simp)
    | short n =>
      simp only [hc] at hp
      cases hd : tokDiverge (Table.ofCommand c plus w) tok with
      | some d => simp [hd] at hp
      | none =>
        simp only [hd] at hp
        have htok := readTok_readOpt (next := rest.head?) hf hd
        simp only
        cases hrt : readTok (Table.ofCommand c plus w) tok rest.head? with
        | error e =>
          cases hro : readOpt c.opts tok rest.head? with
          | error e' => rfl
          | ok r => simp [hrt, hro, Except.toOption] at htok
        | ok q =>
          obtain ⟨ps, b⟩ := q
          cases hro : readOpt c.opts tok rest.head? with
          | error e' => simp [hrt, hro, Except.toOption] at htok
          | ok r =>
            simp only [hrt, hro, Except.toOption, Option.some.injEq] at htok
            subst htok
            simp only [hrt] at hp
            cases b with
            | false =>
              have ih := parse_scanAux hf rest hp
              cases hr : parse (Table.ofCommand c plus w) ord rest <;>
                cases hs : scanAux c rest <;>
                  (simp_all [Except.map, Except.toOption, consOpts, frameOf]) <;> (subst ih; simp)
            | true =>
              cases rest with
              | nil => rfl
              | cons x rest' =>
                have ih := parse_scanAux hf rest' hp
                cases hr : parse (Table.ofCommand c plus w) ord rest' <;>
                  cases hs : scanAux c rest' <;>
                  (simp_all [Except.map, Except.toOption, consOpts, frameOf]) <;> (subst ih; simp)

/-! ## The reading -/

theorem interpret_afterScan (c : Command) (env : String → Option String) (argv : List String) :
    interpret c env argv = match scan c argv with
      | .error l => Outcome.ofLocated c l
      | .ok fs => afterScan c env fs := rfl

theorem agrees_refl (o : Outcome) : Agrees o o := by
  cases o <;> simp [Agrees]

/-- **The getopt reading agrees with the args front end** where the pre-pass passes. -/
theorem read_agrees (t : Tool) (env : String → Option String) (argv : List String)
    (hf : Fits t.grammar) (hp : t.pre env argv = none) :
    Agrees (t.read env argv) (interpret t.grammar env argv) := by
  have h := parse_scanAux hf argv hp
  unfold Tool.read Tool.parse
  rw [interpret_afterScan]
  unfold scan
  unfold Tool.table at h
  cases hpa : Getopt.parse (Table.ofCommand t.grammar t.plus t.wLong) (t.order env) argv with
  | error e =>
    cases hs : scanAux t.grammar argv with
    | error l =>
      obtain ⟨p, e'⟩ := l
      simp [Tool.table, hpa, Except.map, Agrees, Outcome.ofLocated]
    | ok r => simp [hpa, hs, Except.toOption] at h
  | ok p =>
    cases hs : scanAux t.grammar argv with
    | error l => simp [hpa, hs, Except.toOption] at h
    | ok r =>
      simp only [hpa, hs, Except.toOption, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [Tool.table, hpa, Except.map]
      exact agrees_refl _

end Silmaril.Proofs.Cli.Getopt
