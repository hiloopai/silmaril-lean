module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Proofs.Cli.Args.Scan

@[expose] public section

/-!
# Proofs: grammar morphisms

* `Extends.refl`, `Extends.trans`: grammars and their morphisms form a preorder;
* `readOpt_append_fresh`, `readOpt_append`: appending options fresh in the table
  (`Opt.FreshIn`: exact multi-letter tokens such as `-O2` allowed when they start with no
  cluster letter), or `Plain` ones, keeps every reading of an option token (clusters,
  attached values and `--no-` included);
* `walk_allOpts`: every option a level of the parser sees is declared in the grammar;
* `extends_appendFresh`, `extends_addFresh` (fresh options, `Opt.FreshIn g.allOpts`, decidable),
  `extends_appendOpts`, `extends_addOpt`, `extends_withHelp`, `extends_withGlobal`: appending
  plain options (local or global) is a morphism; `extends_addSub` (to a command that already
  has subcommands) and `extends_withVersion` too;
* `scans_extends`, `scan_extends`: **compatibility**: along a morphism every command line keeps
  its parse.

A Silmaril addition.
-/

namespace Silmaril.Cli

theorem LocalExt.refl (d : Command) : LocalExt d d :=
  ⟨rfl, rfl, fun _ _ _ h => h⟩

theorem LocalExt.trans {d₁ d₂ d₃ : Command} (h₁ : LocalExt d₁ d₂) (h₂ : LocalExt d₂ d₃) :
    LocalExt d₁ d₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun t x r h => h₂.2.2 t x r (h₁.2.2 t x r h)⟩

theorem Extends.refl (c : Command) : c ⊑ c :=
  fun _ d h => ⟨d, h, LocalExt.refl d⟩

theorem Extends.trans {c₁ c₂ c₃ : Command} (h₁ : c₁ ⊑ c₂) (h₂ : c₂ ⊑ c₃) : c₁ ⊑ c₃ := by
  intro ws d hd
  obtain ⟨d₂, hd₂, hl₁⟩ := h₁ ws d hd
  obtain ⟨d₃, hd₃, hl₂⟩ := h₂ ws d₂ hd₂
  exact ⟨d₃, hd₃, hl₁.trans hl₂⟩

/-- A morphism is a local extension at the root. -/
theorem Extends.root {c c' : Command} (h : c ⊑ c') : LocalExt c c' := by
  obtain ⟨d', hd', hl⟩ := h [] c rfl
  have hc' : d' = c' := (Option.some.inj hd').symm
  exact hc' ▸ hl

theorem walk_cons {c : Command} {w : String} {ws : List String} :
    c.walk (w :: ws) = (findSub c.subs w).bind fun s => (c.child s).walk ws := rfl

/-- A morphism restricts to the subcommands. -/
theorem Extends.sub {c c' s : Command} {w : String} (h : c ⊑ c')
    (hs : findSub c.subs w = some s) :
    ∃ s', findSub c'.subs w = some s' ∧ c.child s ⊑ c'.child s' := by
  obtain ⟨d', hd', _⟩ := h [w] (c.child s) (by simp [hs, Command.walk])
  obtain ⟨s', hfd, hd's⟩ : ∃ s', findSub c'.subs w = some s' ∧ c'.child s' = d' := by
    cases hf : findSub c'.subs w with
    | none => simp [walk_cons, hf] at hd'
    | some t =>
      have ht : (c'.child t).walk [] = some d' := by simpa [walk_cons, hf] using hd'
      exact ⟨t, rfl, by simpa [Command.walk] using ht⟩
  refine ⟨s', hfd, fun ws e he => ?_⟩
  obtain ⟨e', he', hl⟩ := h (w :: ws) e (by simp [walk_cons, hs, he])
  have hwalk : (c'.child s').walk ws = some e' := by simpa [walk_cons, hfd] using he'
  exact ⟨e', hwalk, hl⟩

/-- **Compatibility**: along a morphism every derivation stays a derivation. -/
theorem scans_extends {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : Scans c argv r) : ∀ {c'}, c ⊑ c' → Scans c' argv r := by
  induction h with
  | nil c =>
    intro c' hc
    have hname : c'.name = c.name := hc.root.1
    exact hname ▸ Scans.nil c'
  | @dashdash c t rest ht =>
    intro c' hc
    have hname : c'.name = c.name := hc.root.1
    exact hname ▸ Scans.dashdash ht
  | opt hr _ ih => intro c' hc; exact .opt (hc.root.2.2 _ _ _ hr) (ih hc)
  | optNext hr _ ih => intro c' hc; exact .optNext (hc.root.2.2 _ _ _ hr) (ih hc)
  | arg ht hs _ ih =>
    intro c' hc; exact .arg ht (hc.root.2.1.trans hs) (ih hc)
  | @sub c t w s rest g gs ht hs hf _ ih =>
    intro c' hc
    obtain ⟨s', hf', hss⟩ := hc.sub hf
    have hname : c'.name = c.name := hc.root.1
    exact hname ▸ Scans.sub ht (hc.root.2.1.trans hs) hf' (ih hss)

/-- **Compatibility**: along a morphism every command line keeps its parse. -/
theorem scanAux_extends {c c' : Command} (hc : c ⊑ c') {argv : List String}
    {r : Frame × Invocation} (h : scanAux c argv = .ok r) : scanAux c' argv = .ok r :=
  scanAux_complete (scans_extends (scanAux_sound h) hc)

/-- **Compatibility** for `scan`. -/
theorem scan_extends {c c' : Command} (hc : c ⊑ c') {argv : List String} {fs : Invocation}
    (h : scan c argv = .ok fs) : scan c' argv = .ok fs := by
  obtain ⟨f, rest, rfl, hs⟩ := scan_eq_ok_iff.mp h
  exact scan_eq_ok_iff.mpr ⟨f, rest, rfl, scans_extends hs hc⟩

/-! ## Appending options keeps every reading -/

theorem find?_append_of_some {α : Type} {p : α → Bool} {l l' : List α} {a : α}
    (h : l.find? p = some a) : (l ++ l').find? p = some a := by
  simp [List.find?_append, h]

theorem lookup_append_of_some {α : Type} {keys : α → List String} {l l' : List α} {k : String}
    {a : α} (h : lookupKey keys l k = some a) : lookupKey keys (l ++ l') k = some a :=
  find?_append_of_some h

theorem lookup_append_of_none {α : Type} {keys : α → List String} {l l' : List α} {k : String}
    (h : lookupKey keys l k = none) : lookupKey keys (l ++ l') k = lookupKey keys l' k := by
  unfold lookupKey at h ⊢
  rw [List.find?_append, h, Option.none_or]

theorem clusterOpts_append (os e : List Opt) :
    clusterOpts (os ++ e) = clusterOpts os ++ clusterOpts e := List.filter_append ..

theorem readCluster_append {os e : List Opt} {t : String} {x : Option String} :
    ∀ {cs : List Char} {r : Read}, readCluster os t x cs = .ok r →
      readCluster (os ++ e) t x cs = .ok r
  | [], _, h => h
  | ch :: cs, r, h => by
    cases hf : findShort (clusterOpts os) (String.singleton ch) with
    | none => simp [readCluster, hf] at h
    | some o =>
      have hf' : findShort (clusterOpts (os ++ e)) (String.singleton ch) = some o := by
        rw [clusterOpts_append]; exact lookup_append_of_some hf
      cases htv : o.takesValue with
      | true => simpa [readCluster, hf, hf', htv] using h
      | false =>
        have hmap : (readCluster os t x cs).map (fun p => ((o.id, .on) :: p.1, p.2)) = .ok r := by
          simpa [readCluster, hf, htv] using h
        show readCluster (os ++ e) t x (ch :: cs) = .ok r
        simp only [readCluster, hf', htv, Bool.false_eq_true, ↓reduceIte]
        exact except_map_ok (P := fun r => (readCluster (os ++ e) t x cs).map
          (fun p => ((o.id, .on) :: p.1, p.2)) = .ok r) hmap fun a ha => by
            rw [readCluster_append ha]; rfl

theorem length_one {n : String} (h : n.length = 1) : ∃ ch, n.toList = [ch] := by
  have hl : n.toList.length = 1 := by simpa [String.length_toList] using h
  match hn : n.toList, hl with
  | [ch], _ => exact ⟨ch, rfl⟩

theorem singleton_eq {n : String} {ch : Char} (h : n.toList = [ch]) : String.singleton ch = n := by
  apply String.toList_inj.mp
  simp [h]

/-- A key of a member is found. -/
theorem lookup_isSome_of_mem {α : Type} {keys : α → List String} {l : List α} {k : String} {a : α}
    (ha : a ∈ l) (hk : k ∈ keys a) : (lookupKey keys l k).isSome := by
  unfold lookupKey
  exact List.find?_isSome.mpr ⟨a, ha, by simpa using hk⟩

/-- A key found in a list is found in a list containing it. -/
theorem lookup_isSome_of_subset {α : Type} {keys : α → List String} {l l' : List α} {k : String}
    {a : α} (hsub : ∀ x ∈ l, x ∈ l') (h : lookupKey keys l k = some a) :
    (lookupKey keys l' k).isSome :=
  lookup_isSome_of_mem (hsub a (lookup_mem h)) (lookup_key h)

/-- Plain options are fresh in every table. -/
theorem Opt.Plain.freshIn {o : Opt} (h : o.Plain) (os : List Opt) : o.FreshIn os :=
  ⟨h.1, fun n hn => .inl (h.2 n hn)⟩

/-- Freshness in a table gives freshness in a smaller one. -/
theorem Opt.FreshIn.mono {os os' : List Opt} {o : Opt} (hsub : ∀ x ∈ os, x ∈ os')
    (h : o.FreshIn os') : o.FreshIn os := by
  refine ⟨h.1, fun n hn => (h.2 n hn).imp (fun h1 => h1) fun hh => ?_⟩
  cases hc : n.toList.head? with
  | none => rw [hc] at hh; exact absurd hh (by simp)
  | some ch =>
    have h' := hh
    rw [hc] at h'
    simp only [Option.any_some, Option.isNone_iff_eq_none] at h' ⊢
    cases hf : findShort (clusterOpts os) (String.singleton ch) with
    | none => rfl
    | some o' =>
      have hsub' : ∀ x ∈ clusterOpts os, x ∈ clusterOpts os' := fun x hx =>
        List.mem_filter.mpr ⟨hsub x (List.mem_filter.mp hx).1, (List.mem_filter.mp hx).2⟩
      have hs : (findShort (clusterOpts os') (String.singleton ch)).isSome :=
        lookup_isSome_of_subset hsub' hf
      rw [h'] at hs
      exact absurd hs (by simp)

/-- A fresh option has no long name of the form `no-…`. -/
theorem findLong_append_fresh {os e : List Opt} (he : ∀ o ∈ e, o.FreshIn os) {n m : String}
    (hs : stripNo n = some m) (hf : findLong os n = none) : findLong (os ++ e) n = none := by
  rw [show findLong (os ++ e) n = findLong e n from lookup_append_of_none hf]
  cases hfe : findLong e n with
  | none => rfl
  | some o' =>
    have h : stripNo n = none := (he o' (lookup_mem hfe)).1 n (lookup_key hfe)
    rw [hs] at h; exact absurd h (by simp)

theorem readLong_append {os e : List Opt} (he : ∀ o ∈ e, o.FreshIn os) {t n : String}
    {v x : Option String} {r : Read} (h : readLong os t n v x = .ok r) :
    readLong (os ++ e) t n v x = .ok r := by
  cases hf : findLong os n with
  | some o =>
    have hf' : findLong (os ++ e) n = some o := lookup_append_of_some hf
    simpa [readLong, hf, hf'] using h
  | none =>
    have hno : readNo os t n v = .ok r := by simpa [readLong, hf] using h
    cases hs : stripNo n with
    | none => simp [readNo, hs] at hno
    | some m =>
      have hf' : findLong (os ++ e) n = none := findLong_append_fresh he hs hf
      cases hm : findLong os m with
      | none => simp [readNo, hs, hm] at hno
      | some o =>
        have hm' : findLong (os ++ e) m = some o := lookup_append_of_some hm
        simpa [readLong, readNo, hf', hs, hm', hm] using hno

/-- A cluster that reads starts with a cluster letter of the table. -/
theorem readCluster_head {os : List Opt} {t : String} {x : Option String} {ch : Char}
    {cs : List Char} {r : Read} (h : readCluster os t x (ch :: cs) = .ok r) :
    (findShort (clusterOpts os) (String.singleton ch)).isSome := by
  cases hf : findShort (clusterOpts os) (String.singleton ch) with
  | none => simp [readCluster, hf] at h
  | some _ => rfl

/-- A cluster cannot read a fresh option's name that the table does not declare: a
one-letter name would be the table's own letter, a longer one starts with no cluster letter. -/
theorem readCluster_fails {os : List Opt} {t n : String} {x : Option String} {r : Read}
    (hf : findShort os n = none)
    (hfr : n.length = 1 ∨ n.toList.head?.any
      (fun ch => (findShort (clusterOpts os) (String.singleton ch)).isNone) = true) :
    readCluster os t x n.toList ≠ .ok r := by
  intro hc
  cases hn : n.toList with
  | nil =>
    have hlen : n.length = 0 := by rw [← String.length_toList, hn]; rfl
    have hhd : n.toList.head? = none := by rw [hn]; rfl
    rcases hfr with h1 | hh
    · omega
    · exact absurd hh (by simp [hhd])
  | cons ch cs =>
    show False
    have hc' : readCluster os t x (ch :: cs) = .ok r := hn ▸ hc
    have hs : (findShort (clusterOpts os) (String.singleton ch)).isSome := readCluster_head hc'
    rcases hfr with h1 | hh
    · obtain ⟨c', hc1⟩ := length_one h1
      have hcs : ch :: cs = [c'] := hn ▸ hc1
      have hn1 : n.toList = [ch] := by rw [hn, (List.cons.inj hcs).2]
      have hs' : (findShort os n).isSome := singleton_eq hn1 ▸
        lookup_isSome_of_subset (fun y hy => (List.mem_filter.mp hy).1) (Option.get_mem hs)
      exact absurd hs' (by simp [hf])
    · have hno : (findShort (clusterOpts os) (String.singleton ch)).isNone = true := by
        simpa [hn] using hh
      exact absurd hs (by simpa [Option.isNone_iff_eq_none] using hno)

/-- A fresh option has no single-dash name that would shadow a cluster. -/
theorem findShort_append_fresh {os e : List Opt} (he : ∀ o ∈ e, o.FreshIn os) {t n : String}
    {x : Option String} {r : Read} (hf : findShort os n = none)
    (hc : readCluster os t x n.toList = .ok r) : findShort (os ++ e) n = none := by
  have he' : findShort (os ++ e) n = findShort e n := lookup_append_of_none hf
  rw [he']
  cases hfe : findShort e n with
  | none => rfl
  | some o' => exact absurd hc (readCluster_fails hf ((he o' (lookup_mem hfe)).2 n (lookup_key hfe)))

theorem readShort_append {os e : List Opt} (he : ∀ o ∈ e, o.FreshIn os) {t n : String}
    {x : Option String} {r : Read} (h : readShort os t n x = .ok r) :
    readShort (os ++ e) t n x = .ok r := by
  cases hf : findShort os n with
  | some o =>
    have hf' : findShort (os ++ e) n = some o := lookup_append_of_some hf
    simpa [readShort, hf, hf'] using h
  | none =>
    have hc : readCluster os t x n.toList = .ok r := by simpa [readShort, hf] using h
    have hf' : findShort (os ++ e) n = none := findShort_append_fresh he hf hc
    simpa [readShort, hf'] using readCluster_append hc

/-- **Appending fresh options keeps every reading of an option token.** -/
theorem readOpt_append_fresh {os e : List Opt} (he : ∀ o ∈ e, o.FreshIn os) {t : String}
    {x : Option String} {r : Read} (h : readOpt os t x = .ok r) : readOpt (os ++ e) t x = .ok r := by
  unfold readOpt at h ⊢
  split at h
  · exact readLong_append he h
  · exact readShort_append he h
  · exact absurd h (by simp)

/-- **Appending plain options keeps every reading of an option token.** -/
theorem readOpt_append {os e : List Opt} (he : ∀ o ∈ e, o.Plain) {t : String}
    {x : Option String} {r : Read} (h : readOpt os t x = .ok r) : readOpt (os ++ e) t x = .ok r :=
  readOpt_append_fresh (fun o ho => (he o ho).freshIn os) h

/-! ## Builders are morphisms -/

theorem child_inherit (c s : Command) (e : List Opt) :
    (c.inherit e).child s = (c.child s).inherit (e.filter (·.global)) := by
  simp [Command.child, Command.inherit, Command.globals, List.filter_append]

/-- Walking a command with appended options: the same commands, with some of them appended. -/
theorem walk_inherit (ws : List String) :
    ∀ (c : Command) (e : List Opt) (d : Command), c.walk ws = some d →
      ∃ e', (∀ o ∈ e', o ∈ e) ∧ (c.inherit e).walk ws = some (d.inherit e') := by
  induction ws with
  | nil =>
    intro c e d hd
    simp only [Command.walk, Option.some.injEq] at hd
    subst hd
    exact ⟨e, fun _ h => h, rfl⟩
  | cons w ws ih =>
    intro c e d hd
    cases hf : findSub c.subs w with
    | none => simp [walk_cons, hf] at hd
    | some s =>
      have hd' : (c.child s).walk ws = some d := by simpa [walk_cons, hf] using hd
      obtain ⟨e', he', hw⟩ := ih (c.child s) (e.filter (·.global)) d hd'
      refine ⟨e', fun o ho => (List.mem_filter.mp (he' o ho)).1, ?_⟩
      have hf' : findSub (c.inherit e).subs w = some s := hf
      rw [walk_cons, hf', Option.bind_some, child_inherit]
      exact hw

theorem localExt_inherit (d : Command) {e : List Opt} (he : ∀ o ∈ e, o.FreshIn d.opts) :
    LocalExt d (d.inherit e) :=
  ⟨rfl, rfl, fun _ _ _ h => readOpt_append_fresh he h⟩

theorem allOpts_eq (c : Command) : c.allOpts = c.opts ++ Command.allOptsAll c.subs := by
  cases c; rfl

theorem allOptsAll_mem {l : List Command} {s : Command} (hs : s ∈ l) {o : Opt}
    (ho : o ∈ s.allOpts) : o ∈ Command.allOptsAll l := by
  induction l with
  | nil => cases hs
  | cons a l ih =>
    show o ∈ a.allOpts ++ Command.allOptsAll l
    rcases List.mem_cons.mp hs with rfl | hs
    · exact List.mem_append_left _ ho
    · exact List.mem_append_right _ (ih hs)

/-- The options of a subcommand as the parser sees it are declared in the grammar. -/
theorem allOpts_child {c s : Command} {w : String} (hf : findSub c.subs w = some s) {o : Opt}
    (h : o ∈ (c.child s).allOpts) : o ∈ c.allOpts := by
  have hs : s ∈ c.subs := lookup_mem hf
  have hsplit : o ∈ s.opts ∨ o ∈ c.globals ∨ o ∈ Command.allOptsAll s.subs := by
    have h' : o ∈ (s.opts ++ c.globals) ++ Command.allOptsAll s.subs := by
      simpa only [allOpts_eq, Command.child, Command.inherit] using h
    simpa only [List.mem_append, or_assoc] using h'
  have hsub : ∀ x, x ∈ s.allOpts → x ∈ c.allOpts := fun x hx =>
    (allOpts_eq c) ▸ List.mem_append_right _ (allOptsAll_mem hs hx)
  rcases hsplit with h1 | h2 | h3
  · exact hsub o ((allOpts_eq s) ▸ List.mem_append_left _ h1)
  · exact (allOpts_eq c) ▸ List.mem_append_left _ (List.mem_filter.mp h2).1
  · exact hsub o ((allOpts_eq s) ▸ List.mem_append_right _ h3)

/-- **Every option a level of the parser sees is declared somewhere in the grammar.** -/
theorem walk_allOpts (ws : List String) :
    ∀ (c d : Command), c.walk ws = some d → ∀ o ∈ d.opts, o ∈ c.allOpts := by
  induction ws with
  | nil =>
    intro c d hd o ho
    have hcd : c = d := Option.some.inj hd
    have ho' : o ∈ c.opts := hcd ▸ ho
    exact (allOpts_eq c) ▸ List.mem_append_left _ ho'
  | cons w ws ih =>
    intro c d hd o ho
    cases hf : findSub c.subs w with
    | none => exact absurd hd (by simp [walk_cons, hf])
    | some s =>
      have hd' : (c.child s).walk ws = some d := by simpa [walk_cons, hf] using hd
      exact allOpts_child hf (ih (c.child s) d hd' o ho)

/-- **Appending fresh options is a morphism** (global ones reach every level below): options
whose exact multi-letter tokens (`-O2`, `-all`) start with no cluster letter of the grammar. -/
theorem extends_appendFresh (c : Command) {e : List Opt} (he : ∀ o ∈ e, o.FreshIn c.allOpts) :
    c ⊑ c.appendOpts e := by
  intro ws d hd
  obtain ⟨e', he', hw⟩ := walk_inherit ws c e d hd
  exact ⟨d.inherit e', hw, localExt_inherit d fun o ho =>
    (he o (he' o ho)).mono (walk_allOpts ws c d hd)⟩

/-- **Appending plain options is a morphism** (global ones reach every level below). -/
theorem extends_appendOpts (c : Command) {e : List Opt} (he : ∀ o ∈ e, o.Plain) :
    c ⊑ c.appendOpts e :=
  extends_appendFresh c fun o ho => (he o ho).freshIn _

/-- Adding a fresh option at the end is a morphism. -/
theorem extends_addFresh (c : Command) {o : Opt} (ho : o.FreshIn c.allOpts) : c ⊑ c.addOpt o :=
  extends_appendFresh c fun _ h => (List.mem_singleton.mp h) ▸ ho

/-- Adding a plain option at the end is a morphism. -/
theorem extends_addOpt (c : Command) {o : Opt} (ho : o.Plain) : c ⊑ c.addOpt o :=
  extends_appendOpts c fun _ h => (List.mem_singleton.mp h) ▸ ho

theorem helpOpt_plain : helpOpt.Plain := by decide

theorem versionOpt_plain : versionOpt.Plain := by decide

/-- Adding `-h, --help` everywhere is a morphism. -/
theorem extends_withHelp (c : Command) : c ⊑ c.withHelp := extends_addOpt c helpOpt_plain

/-- Adding plain global options is a morphism. -/
theorem extends_withGlobal (c : Command) {os : List Opt} (hos : ∀ o ∈ os, o.Plain) :
    c ⊑ c.withGlobal os :=
  extends_appendOpts c fun o ho => by
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
    exact hos o' ho'

/-- Changing the version string is a morphism (it changes no reading). -/
theorem extends_setVersion (c : Command) (v : Option String) : c ⊑ { c with version := v } := by
  intro ws d hd
  match ws, hd with
  | [], hd =>
    have hcd : c = d := Option.some.inj hd
    exact ⟨{ c with version := v }, rfl, hcd ▸ ⟨rfl, rfl, fun _ _ _ h => h⟩⟩
  | w :: ws, hd => exact ⟨d, hd, LocalExt.refl d⟩

/-- Adding the version flag is a morphism. -/
theorem extends_withVersion (c : Command) (v : String) : c ⊑ c.withVersion v :=
  (extends_addOpt c versionOpt_plain).trans (extends_setVersion _ _)

/-- Adding a subcommand at the end of a command that has subcommands is a morphism. (Adding the
first one is not: words that were positionals become subcommand names.) -/
theorem extends_addSub {c : Command} (hne : c.subs ≠ []) (s : Command) : c ⊑ c.addSub s := by
  intro ws d hd
  match ws, hd with
  | [], hd =>
    have hcd : c = d := Option.some.inj hd
    have hempty : (c.subs ++ [s]).isEmpty = c.subs.isEmpty := by
      cases hc : c.subs with
      | nil => exact absurd hc hne
      | cons _ _ => rfl
    exact ⟨c.addSub s, rfl, hcd ▸ ⟨rfl, hempty, fun _ _ _ h => h⟩⟩
  | w :: ws, hd =>
    cases hf : findSub c.subs w with
    | none => simp [walk_cons, hf] at hd
    | some t =>
      have hf' : findSub (c.addSub s).subs w = some t := find?_append_of_some hf
      have hwalk : (c.addSub s).walk (w :: ws) = c.walk (w :: ws) := by
        simp only [walk_cons, hf, hf', Option.bind_some]; rfl
      exact ⟨d, hwalk.trans hd, LocalExt.refl d⟩

end Silmaril.Cli
