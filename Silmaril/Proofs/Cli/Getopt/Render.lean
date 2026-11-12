module

public import Silmaril.Cli.Args.Thms
public import Silmaril.Proofs.Cli.Getopt.Agree

/-!
# Proofs: the getopt pre-pass passes the args normal form

* `pre_opt_false`, `pre_opt_true`: the pre-pass reads past an option token it passes;
* `tokDiverge_long`, `tokDiverge_short`, `spelling_tok`: the spellings of the normal form
  (exact long names, one-letter single-dash names) are not where the readings differ;
* `pre_given`, `pre_renderOpts`, `pre_renderArgs`: occurrences and positionals in normal form
  pass;
* **`pre_render`**: for a well-formed grammar getopt can express, the pre-pass (without `W;`,
  in either ordering) passes the normal form of every valid invocation.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Proofs.Cli.Getopt

open Silmaril.Cli Silmaril.Cli.Getopt

/-! ## Reading past a token -/

theorem pre_opt_false {t : Table} {ord : Order} {tok : String} {rest : List String}
    {ps : List (String × Given)} (hdd : classify tok ≠ .dashdash)
    (hw : ∀ w, classify tok ≠ .word w) (hd : tokDiverge t tok = none)
    (hr : readTok t tok rest.head? = .ok (ps, false)) :
    pre t ord (tok :: rest) = pre t ord rest := by
  conv => lhs; rw [pre.eq_def]
  dsimp only
  split
  · rename_i hc; exact absurd hc hdd
  · rename_i w hc; exact absurd hc (hw w)
  · rw [hd, hr]

theorem pre_opt_true {t : Table} {ord : Order} {tok x : String} {rest : List String}
    {ps : List (String × Given)} (hdd : classify tok ≠ .dashdash)
    (hw : ∀ w, classify tok ≠ .word w) (hd : tokDiverge t tok = none)
    (hr : readTok t tok (some x) = .ok (ps, true)) :
    pre t ord (tok :: x :: rest) = pre t ord rest := by
  conv => lhs; rw [pre.eq_def]
  dsimp only
  split
  · rename_i hc; exact absurd hc hdd
  · rename_i w hc; exact absurd hc (hw w)
  · simp only [List.head?_cons]
    rw [hd, hr]

/-! ## The spellings of the normal form -/

theorem tokDiverge_long {c : Command} {plus w : Bool} {n : String} {o : Opt}
    (hfo : findLong c.opts n = some o) {tok : String} {v : Option String}
    (htok : classify tok = .long n v) : tokDiverge (Table.ofCommand c plus w) tok = none := by
  have he : (c.opts.flatMap longsOf).find? (·.name == n) = some (longEntry n o) := by
    rw [find_longsOf, hfo]; rfl
  unfold tokDiverge
  rw [htok]
  simp only [Table.ofCommand]
  rw [resolveLong_exact he]
  simp [longEntry]

theorem clusterOpts_fits {c : Command} (hf : Fits c) : clusterOpts c.opts = c.opts :=
  List.filter_eq_self.2 (by intro o ho; simp [(hf.2 o ho).1])

theorem tokDiverge_short {c : Command} (hf : Fits c) {plus : Bool} {ch : Char} {o : Opt}
    (hfo : findShort c.opts (String.singleton ch) = some o) {tok : String}
    (htok : classify tok = .short (String.singleton ch)) :
    tokDiverge (Table.ofCommand c plus false) tok = none := by
  have hfc : findChar (Table.ofCommand c plus false) ch = some (shortEntry ch o) := by
    unfold findChar
    simp only [Table.ofCommand]
    rw [find_shortsOf, clusterOpts_fits hf, hfo]; rfl
  have hl : (String.singleton ch).toList = [ch] := by simp
  unfold tokDiverge
  rw [htok]
  simp only [hl]
  unfold clusterDiverge
  have hwl : (Table.ofCommand c plus false).wLong = false := rfl
  simp only [hwl, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hfc]
  cases ha : hasArgOf o <;> simp [shortEntry, ha, clusterDiverge]

/-- The canonical spelling of an option is an option token the pre-pass passes. -/
theorem spelling_tok {c : Command} (hf : Fits c) (h : c.LocalWF) {plus : Bool} {o : Opt}
    (ho : o ∈ c.opts) :
    classify o.spelling ≠ .dashdash ∧ (∀ w, classify o.spelling ≠ .word w) ∧
      tokDiverge (Table.ofCommand c plus false) o.spelling = none := by
  rcases spelling_cases h ho with ⟨n, -, hsp, hn, hfl⟩ | ⟨-, n, hsp, hn, hfs⟩
  · rw [hsp, classify_long hn]
    exact ⟨by simp, fun _ => by simp, tokDiverge_long hfl (classify_long hn)⟩
  · have hmem := ((findShort_eq_some_iff h).1 hfs).2
    obtain ⟨ch, hch⟩ := List.length_eq_one_iff.1 ((hf.2 o ho).2.2 n hmem)
    have hn' := singleton_of_toList hch
    rw [hsp, classify_short hn]
    refine ⟨by simp, fun _ => by simp, ?_⟩
    exact tokDiverge_short hf (hn' ▸ hfs) (by rw [classify_short hn, hn'])

theorem readTok_of_readOpt {c : Command} (hf : Fits c) {plus w : Bool} {tok : String}
    {next : Option String} {r : Read} (hd : tokDiverge (Table.ofCommand c plus w) tok = none)
    (h : readOpt c.opts tok next = .ok r) :
    readTok (Table.ofCommand c plus w) tok next = .ok r := by
  have := readTok_readOpt (next := next) hf hd
  rw [h] at this
  cases hr : readTok (Table.ofCommand c plus w) tok next <;> simp_all [Except.toOption]

/-! ## The normal form passes -/

/-- One occurrence in normal form passes. -/
theorem pre_given {c : Command} (hf : Fits c) (h : c.LocalWF) {plus : Bool} {ord : Order}
    {o : Opt} (ho : o ∈ c.opts) {g : Given} (hacc : o.accepts g = true) (tail : List String) :
    pre (Table.ofCommand c plus false) ord (renderGiven o g ++ tail) =
      pre (Table.ofCommand c plus false) ord tail := by
  obtain ⟨h1, h2, h3⟩ := spelling_tok (plus := plus) hf h ho
  cases g with
  | on =>
    exact pre_opt_false h1 h2 h3 (readTok_of_readOpt hf h3 (readOpt_on h ho hacc _))
  | off => simp [Opt.accepts, (hf.2 o ho).2.1] at hacc
  | val x =>
    have htv : o.takesValue = true := by simpa [Opt.accepts] using hacc
    cases hvo : o.valueOptional with
    | false =>
      have hr : renderGiven o (.val x) = [o.spelling, x] := by simp [renderGiven, hvo]
      rw [hr]
      exact pre_opt_true h1 h2 h3 (readTok_of_readOpt hf h3 (readOpt_val h ho htv hvo x))
    | true =>
      have hro := readOpt_valEq h ho hvo x tail.head?
      have hw := (h.opt ho).2.2.2.1 hvo
      have hr : renderGiven o (.val x) = ["--" ++ o.long.headD o.id ++ "=" ++ x] := by
        simp [renderGiven, hvo]
      rw [hr]
      rcases spelling_cases h ho with ⟨n, hhd, -, hn, hfl⟩ | ⟨hl, -⟩
      · rw [(headD_of_head? (d := o.id) hhd).1] at hro ⊢
        have hc := classify_longEq hn x
        have hd := tokDiverge_long (plus := plus) (w := false) hfl hc
        exact pre_opt_false (by rw [hc]; simp) (fun _ => by rw [hc]; simp) hd
          (readTok_of_readOpt hf hd hro)
      · exact absurd hl hw.2

/-- The options of a frame in normal form pass. -/
theorem pre_renderOpts {c : Command} (hf : Fits c) (h : c.LocalWF) {plus : Bool} {ord : Order}
    {ps : List (String × Given)}
    (hps : ∀ p ∈ ps, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true)
    (tail : List String) :
    pre (Table.ofCommand c plus false) ord (ps.flatMap (renderOpt c.opts) ++ tail) =
      pre (Table.ofCommand c plus false) ord tail := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨o, hfo, hacc⟩ := hps p List.mem_cons_self
    have ho : o ∈ c.opts := lookup_mem hfo
    have hr : renderOpt c.opts p = renderGiven o p.2 := by simp [renderOpt, hfo]
    calc pre (Table.ofCommand c plus false) ord ((p :: ps).flatMap (renderOpt c.opts) ++ tail)
        = pre (Table.ofCommand c plus false) ord
            (renderGiven o p.2 ++ (ps.flatMap (renderOpt c.opts) ++ tail)) := by
          simp [hr]
      _ = pre (Table.ofCommand c plus false) ord (ps.flatMap (renderOpt c.opts) ++ tail) :=
          pre_given hf h ho hacc _
      _ = _ := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))

/-- Words pass, in either ordering. -/
theorem pre_words (t : Table) (ord : Order) :
    ∀ ws : List String, (∀ w ∈ ws, isWord w = true) → pre t ord ws = none
  | [], _ => by simp [pre]
  | w :: ws, h => by
    have hc := isWord_classify (h w List.mem_cons_self)
    rw [pre.eq_def]
    dsimp only
    rw [hc]
    cases ord with
    | requireOrder =>
      simp only [Option.map_eq_none_iff, List.find?_eq_none]
      intro x hx
      simp [h x (List.mem_cons_of_mem _ hx)]
    | permute => exact pre_words t .permute ws fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- Positional words in normal form pass. -/
theorem pre_renderArgs {c : Command} (hs : c.subs = []) (t : Table) (ord : Order)
    (args : List String) : pre t ord (renderArgs c args) = none := by
  by_cases he : args.isEmpty
  · have hnil : args = [] := List.isEmpty_iff.mp he
    simp [renderArgs, hnil, pre]
  · by_cases hg : args.all isWord
    · have hargs : renderArgs c args = args := by simp [renderArgs, he, hg, hs]
      rw [hargs]
      exact pre_words t ord args (by simpa using hg)
    · have hr : renderArgs c args = "--" :: args := by simp [renderArgs, he, hg]
      rw [hr, pre.eq_def]
      dsimp only
      rw [show classify "--" = .dashdash by decide]

/-- **The pre-pass passes the args normal form** of every valid invocation of a well-formed
grammar getopt can express (without `W;`, in either ordering). -/
theorem pre_render (c : Command) (plus : Bool) (ord : Order) (fs : Invocation) (hf : Fits c)
    (hwf : c.WF) (hv : Valid c fs) :
    pre (Table.ofCommand c plus false) ord (render c fs) = none := by
  match fs, hv with
  | [f], hv =>
    show pre _ _ (f.opts.flatMap (renderOpt c.opts) ++ renderArgs c f.args) = none
    rw [pre_renderOpts hf hwf.local hv.1.2, pre_renderArgs hf.1]
  | _ :: _ :: _, hv =>
    obtain ⟨_, _, s, hs, _⟩ := hv
    rw [hf.1] at hs
    simp [findSub, lookupKey] at hs

end Silmaril.Proofs.Cli.Getopt
