module

public import Silmaril.Cli.Args.Defs

@[expose] public section

/-!
# Proofs: the derived parser is sound and complete, and renders back

* `scanAux_sound`, `scanAux_complete`: `scanAux c argv = .ok r ↔ Scans c argv r`, for every
  grammar (no well-formedness needed), by functional induction and rule induction;
* `lookup_of_nodup`, `findLong_eq_some_iff`, …: in a well-formed grammar a name finds exactly
  the option (or subcommand) that declares it;
* `readOpt_mem`, `scans_valid`: what a grammar reads is a `Valid` invocation;
  `scanAux_error_walk`: errors are located at a subcommand path of the grammar;
* `readOpt_on`, `readOpt_val`, `readOpt_valEq`, `readOpt_off`: the spellings of the normal form
  read back;
* `scanAux_render`: rendering a valid invocation and parsing it back gives it unchanged.

A Silmaril addition.
-/

namespace Silmaril.Cli

/-! ## Results -/

theorem consOpts_ok {P : Frame × Invocation → Prop} {ps : List (String × Given)}
    {e : Except Located (Frame × Invocation)} {r : Frame × Invocation}
    (h : consOpts ps e = .ok r)
    (hk : ∀ f fs, e = .ok (f, fs) → P ({ f with opts := ps ++ f.opts }, fs)) : P r := by
  match e, h with
  | .ok (f, fs), h =>
    have hr : ({ f with opts := ps ++ f.opts }, fs) = r := Except.ok.inj h
    exact hr ▸ hk f fs rfl

theorem consArg_ok {P : Frame × Invocation → Prop} {w : String}
    {e : Except Located (Frame × Invocation)} {r : Frame × Invocation}
    (h : consArg w e = .ok r)
    (hk : ∀ f fs, e = .ok (f, fs) → P ({ f with args := w :: f.args }, fs)) : P r := by
  match e, h with
  | .ok (f, fs), h =>
    have hr : ({ f with args := w :: f.args }, fs) = r := Except.ok.inj h
    exact hr ▸ hk f fs rfl

theorem underSub_ok {P : Frame × Invocation → Prop} {c : Command} {n : String}
    {e : Except Located (Frame × Invocation)} {r : Frame × Invocation}
    (h : underSub c n e = .ok r) (hk : ∀ g gs, e = .ok (g, gs) → P ({ cmd := c.name }, g :: gs)) :
    P r := by
  match e, h with
  | .ok (g, gs), h =>
    have hr : ({ cmd := c.name }, g :: gs) = r := Except.ok.inj h
    exact hr ▸ hk g gs rfl
  | .error (_, _), h => exact absurd h (by simp [underSub])

theorem except_map_ok {ε α β : Type} {P : β → Prop} {g : α → β} {e : Except ε α} {b : β}
    (h : e.map g = .ok b) (hk : ∀ a, e = .ok a → P (g a)) : P b := by
  match e, h with
  | .ok a, h =>
    have hb : g a = b := Except.ok.inj h
    exact hb ▸ hk a rfl

/-- What `readOpt` reads is an option token. -/
theorem readOpt_tok {os : List Opt} {t : String} {x : Option String} {r : Read}
    (h : readOpt os t x = .ok r) :
    (∃ n v, classify t = .long n v) ∨ ∃ n, classify t = .short n := by
  unfold readOpt at h
  split at h
  · exact .inl ⟨_, _, by assumption⟩
  · exact .inr ⟨_, by assumption⟩
  · exact absurd h (by simp)

/-- An option token read without the next token. -/
theorem scanAux_opt {c : Command} {t : String} {rest : List String} {ps : List (String × Given)}
    (hr : readOpt c.opts t rest.head? = .ok (ps, false)) :
    scanAux c (t :: rest) = consOpts ps (scanAux c rest) := by
  rcases readOpt_tok hr with ⟨n, v, hc⟩ | ⟨n, hc⟩ <;> simp [scanAux, hc, hr]

/-- An option token taking the next token as its value. -/
theorem scanAux_optNext {c : Command} {t x : String} {rest : List String}
    {ps : List (String × Given)} (hr : readOpt c.opts t (some x) = .ok (ps, true)) :
    scanAux c (t :: x :: rest) = consOpts ps (scanAux c rest) := by
  rcases readOpt_tok hr with ⟨n, v, hc⟩ | ⟨n, hc⟩ <;> simp [scanAux, hc, hr]

/-! ## Soundness and completeness -/

/-- **Soundness**: what the parser returns is derived by the grammar. -/
theorem scanAux_sound {c : Command} {argv : List String} {r : Frame × Invocation} :
    scanAux c argv = .ok r → Scans c argv r := by
  fun_induction scanAux c argv generalizing r with
  | case1 c => intro h; exact Except.ok.inj h ▸ .nil c
  | case2 c t rest hc => intro h; exact Except.ok.inj h ▸ .dashdash hc
  | case3 c t rest w hc hs ih =>
    intro h; exact consArg_ok h fun f fs he => .arg hc hs (ih he)
  | case4 => intro h; exact absurd h (by simp)
  | case5 c t rest w hc hs s hf ih =>
    intro h; exact underSub_ok h fun g gs he => .sub hc hs hf (ih he)
  | case6 => intro h; exact absurd h (by simp)
  | case7 =>
    intro h; rename_i ih
    exact consOpts_ok h fun f fs he => .opt (by assumption) (ih he)
  | case8 => intro h; exact absurd h (by simp)
  | case9 =>
    intro h; rename_i ih
    exact consOpts_ok h fun f fs he => .optNext (by assumption) (ih he)

/-- **Completeness**: every derivation of the grammar is found by the parser. -/
theorem scanAux_complete {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : Scans c argv r) : scanAux c argv = .ok r := by
  induction h with
  | nil c => simp [scanAux]
  | dashdash hc => simp [scanAux, hc]
  | opt hr _ ih => rw [scanAux_opt hr, ih]; rfl
  | optNext hr _ ih => rw [scanAux_optNext hr, ih]; rfl
  | arg hc hs _ ih => simp [scanAux, hc, hs, ih, consArg, Except.map]
  | sub hc hs hf _ ih => simp [scanAux, hc, hs, hf, ih, underSub]

/-- The parser is the grammar. -/
theorem scanAux_eq_ok_iff {c : Command} {argv : List String} {r : Frame × Invocation} :
    scanAux c argv = .ok r ↔ Scans c argv r :=
  ⟨scanAux_sound, scanAux_complete⟩

/-- The grammar is deterministic. -/
theorem Scans.deterministic {c : Command} {argv : List String} {r r' : Frame × Invocation}
    (h : Scans c argv r) (h' : Scans c argv r') : r = r' :=
  Except.ok.inj ((scanAux_complete h).symm.trans (scanAux_complete h'))

/-- `scan` in terms of the grammar. -/
theorem scan_eq_ok_iff {c : Command} {argv : List String} {fs : Invocation} :
    scan c argv = .ok fs ↔ ∃ f rest, fs = f :: rest ∧ Scans c argv (f, rest) := by
  constructor
  · intro h
    exact except_map_ok (P := fun fs => ∃ f rest, fs = f :: rest ∧ Scans c argv (f, rest)) h
      fun r he => ⟨r.1, r.2, rfl, scanAux_sound he⟩
  · rintro ⟨f, rest, rfl, hs⟩
    simp [scan, scanAux_complete hs, Except.map]

/-! ## Lookup in well-formed grammars -/

theorem lookup_mem {α : Type} {keys : α → List String} {l : List α} {k : String} {a : α}
    (h : lookupKey keys l k = some a) : a ∈ l :=
  List.mem_of_find?_eq_some h

theorem lookup_key {α : Type} {keys : α → List String} {l : List α} {k : String} {a : α}
    (h : lookupKey keys l k = some a) : k ∈ keys a := by
  have hp : (keys a).contains k = true := List.find?_some (p := fun a => (keys a).contains k) h
  simpa using hp

/-- With distinct keys, a key finds the element declaring it. -/
theorem lookup_of_nodup {α : Type} {keys : α → List String} {l : List α} {k : String} {a : α}
    (hnd : (l.flatMap keys).Nodup) (ha : a ∈ l) (hk : k ∈ keys a) :
    lookupKey keys l k = some a := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    have hsplit : (keys b ++ l.flatMap keys).Nodup := by simpa using hnd
    have hparts := List.nodup_append.mp hsplit
    by_cases hb : k ∈ keys b
    · have hab : a = b := by
        rcases List.mem_cons.mp ha with hab | ha'
        · exact hab
        · exact absurd rfl (hparts.2.2 k hb k (List.mem_flatMap.mpr ⟨a, ha', hk⟩))
      simp [lookupKey, hb, hab]
    · have ha' : a ∈ l := by
        rcases List.mem_cons.mp ha with hab | ha'
        · exact absurd (hab ▸ hk) hb
        · exact ha'
      have hrest : lookupKey keys l k = some a := ih hparts.2.1 ha'
      simpa [lookupKey, List.find?_cons, hb] using hrest

theorem wfInAll_iff {inh : List Opt} {l : List Command} :
    Command.wfInAll inh l = true ↔ ∀ s ∈ l, s.wfIn inh = true := by
  induction l with
  | nil => simp [Command.wfInAll]
  | cons s l ih => simp [Command.wfInAll, ih]

/-- Well-formedness level by level. -/
theorem Command.wfIn_iff {inh : List Opt} {c : Command} :
    c.wfIn inh = true ↔
      (c.inherit inh).LocalWF ∧ ∀ s ∈ c.subs, s.wfIn (c.inherit inh).globals = true := by
  cases c
  simp only [Command.wfIn, wfInAll_iff, Command.inherit, Command.globals, Bool.and_eq_true,
    List.filter_append]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨of_decide_eq_true h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨decide_eq_true h1, h2⟩

theorem Command.sizeOf_lt_of_mem {c s : Command} (h : s ∈ c.subs) : sizeOf s < sizeOf c := by
  cases c with
  | mk n al ab os ps subs r ex v ck rl =>
    have h' : s ∈ subs := h
    have := List.sizeOf_lt_of_mem h'
    simp only [Command.mk.sizeOf_spec]
    omega

theorem Command.inherit_nil (c : Command) : c.inherit [] = c := by
  cases c; simp [Command.inherit]

/-- The decidable check gives well-formedness of the tree the parser sees. -/
theorem Command.wfIn_good (c : Command) (inh : List Opt) (h : c.wfIn inh = true) :
    (c.inherit inh).Good := by
  obtain ⟨hl, hs⟩ := Command.wfIn_iff.mp h
  refine .mk hl fun s hs' => ?_
  have : sizeOf s < sizeOf c := Command.sizeOf_lt_of_mem hs'
  exact Command.wfIn_good s _ (hs s hs')
termination_by sizeOf c

theorem Command.WF.good {c : Command} (h : c.WF) : c.Good := by
  have := Command.wfIn_good c [] h
  rwa [Command.inherit_nil] at this

theorem Command.Good.local {c : Command} (h : c.Good) : c.LocalWF := by
  cases h with | mk hl _ => exact hl

theorem Command.Good.sub {c s : Command} (h : c.Good) (hs : s ∈ c.subs) : (c.child s).Good := by
  cases h with | mk _ hsub => exact hsub s hs

theorem Command.WF.local {c : Command} (h : c.WF) : c.LocalWF := h.good.local

theorem flatMap_singleton_eq_map {α β : Type} (g : α → β) (l : List α) :
    (l.flatMap fun a => [g a]) = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem findId_self {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) :
    findId c.opts o.id = some o := by
  have hnd : (c.opts.flatMap fun o => [o.id]).Nodup := by
    rw [flatMap_singleton_eq_map]; exact h.1
  exact lookup_of_nodup hnd ho (List.mem_singleton_self _)

/-- In a well-formed grammar a long name finds the option declaring it. -/
theorem findLong_eq_some_iff {c : Command} (h : c.LocalWF) {n : String} {o : Opt} :
    findLong c.opts n = some o ↔ o ∈ c.opts ∧ n ∈ o.long :=
  ⟨fun hf => ⟨lookup_mem hf, lookup_key hf⟩, fun ⟨ho, hn⟩ => lookup_of_nodup h.2.1 ho hn⟩

/-- In a well-formed grammar a single-dash name finds the option declaring it. -/
theorem findShort_eq_some_iff {c : Command} (h : c.LocalWF) {n : String} {o : Opt} :
    findShort c.opts n = some o ↔ o ∈ c.opts ∧ n ∈ o.short :=
  ⟨fun hf => ⟨lookup_mem hf, lookup_key hf⟩, fun ⟨ho, hn⟩ => lookup_of_nodup h.2.2.1 ho hn⟩

/-- In a well-formed grammar a word finds the subcommand with that name or alias. -/
theorem findSub_eq_some_iff {c : Command} (h : c.LocalWF) {w : String} {s : Command} :
    findSub c.subs w = some s ↔ s ∈ c.subs ∧ w ∈ s.names :=
  ⟨fun hf => ⟨lookup_mem hf, lookup_key hf⟩, fun ⟨hs, hw⟩ => lookup_of_nodup h.2.2.2.1 hs hw⟩

theorem findSub_name {c s : Command} (h : c.LocalWF) (hs : s ∈ c.subs) :
    findSub c.subs s.name = some s :=
  (findSub_eq_some_iff h).mpr ⟨hs, List.mem_cons_self⟩

/-! ## What the parser reads fits the grammar -/

/-- An occurrence of an option of `os`, fitting it. -/
def Fits (os : List Opt) (p : String × Given) : Prop :=
  ∃ o ∈ os, p.1 = o.id ∧ o.accepts p.2 = true

theorem fits_single {os : List Opt} {o : Opt} {g : Given} (hm : o ∈ os)
    (hacc : o.accepts g = true) : ∀ p ∈ [(o.id, g)], Fits os p := by
  intro p hp
  rw [List.mem_singleton.mp hp]
  exact ⟨o, hm, rfl, hacc⟩

theorem valueFromNext_mem {os : List Opt} {o : Opt} {t : String} {x : Option String} {r : Read}
    (hm : o ∈ os) (htv : o.takesValue = true) (h : valueFromNext o t x = .ok r) :
    ∀ p ∈ r.1, Fits os p := by
  unfold valueFromNext at h
  split at h
  · rename_i hvo
    rw [← Except.ok.inj h]
    exact fits_single hm (by simp [Opt.accepts, hvo])
  · split at h
    · rw [← Except.ok.inj h]; exact fits_single hm (by simp [Opt.accepts, htv])
    · exact absurd h (by simp)

theorem attachedValue_mem {os : List Opt} {o : Opt} (hm : o ∈ os) (htv : o.takesValue = true)
    (cs : List Char) : ∀ p ∈ (attachedValue o cs).1, Fits os p := by
  unfold attachedValue
  split <;> exact fits_single hm (by simp [Opt.accepts, htv])

theorem readCluster_mem {os : List Opt} {t : String} {x : Option String} :
    ∀ {cs : List Char} {r : Read}, readCluster os t x cs = .ok r → ∀ p ∈ r.1, Fits os p
  | [], r, h => by
    have hr : r = ([], false) := (Except.ok.inj h).symm
    simp [hr]
  | ch :: cs, r, h => by
    cases ho : findShort (clusterOpts os) (String.singleton ch) with
    | none => simp [readCluster, ho] at h
    | some o =>
      have hm : o ∈ os := (List.mem_filter.mp (lookup_mem ho)).1
      cases htv : o.takesValue with
      | true =>
        cases hcs : cs.isEmpty
        · have hr : attachedValue o cs = r := by simpa [readCluster, ho, htv, hcs] using h
          exact hr ▸ attachedValue_mem hm htv cs
        · exact valueFromNext_mem hm htv (by simpa [readCluster, ho, htv, hcs] using h)
      | false =>
        have hmap : (readCluster os t x cs).map (fun p => ((o.id, .on) :: p.1, p.2)) = .ok r := by
          simpa [readCluster, ho, htv] using h
        exact except_map_ok (P := fun r : Read => ∀ p ∈ r.1, Fits os p) hmap fun a ha p hp =>
          (List.mem_cons.mp hp).elim (fun he => he ▸ ⟨o, hm, rfl, by simp [Opt.accepts, htv]⟩)
            (readCluster_mem ha p)

theorem readNo_mem {os : List Opt} {t n : String} {v : Option String} {r : Read}
    (h : readNo os t n v = .ok r) : ∀ p ∈ r.1, Fits os p := by
  unfold readNo at h
  split at h
  · rename_i o ho
    have hm : o ∈ os := by
      cases hs : stripNo n with
      | none => simp [hs] at ho
      | some m => simp only [hs, Option.bind_some] at ho; exact lookup_mem ho
    split at h
    · rename_i hneg
      have hacc : o.accepts .off = true := by simpa [Opt.accepts, Bool.and_comm] using hneg
      split at h
      · rw [← Except.ok.inj h]; exact fits_single hm hacc
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem readLong_mem {os : List Opt} {t n : String} {v x : Option String} {r : Read}
    (h : readLong os t n v x = .ok r) : ∀ p ∈ r.1, Fits os p := by
  unfold readLong at h
  split at h
  · rename_i o ho
    have hm : o ∈ os := lookup_mem ho
    split at h
    · rename_i htv; rw [← Except.ok.inj h]; exact fits_single hm (by simp [Opt.accepts, htv])
    · exact absurd h (by simp)
    · rename_i htv; rw [← Except.ok.inj h]; exact fits_single hm (by simp [Opt.accepts, htv])
    · rename_i htv; exact valueFromNext_mem hm htv h
  · exact readNo_mem h

theorem readShort_mem {os : List Opt} {t n : String} {x : Option String} {r : Read}
    (h : readShort os t n x = .ok r) : ∀ p ∈ r.1, Fits os p := by
  unfold readShort at h
  split at h
  · rename_i o ho
    have hm : o ∈ os := lookup_mem ho
    split at h
    · rename_i htv; exact valueFromNext_mem hm htv h
    · rename_i htv
      rw [← Except.ok.inj h]
      exact fits_single hm (by simp [Opt.accepts, htv])
  · exact readCluster_mem h

/-- **What an option token reads are occurrences of options of the table, fitting them.** -/
theorem readOpt_mem {os : List Opt} {t : String} {x : Option String} {r : Read}
    (h : readOpt os t x = .ok r) : ∀ p ∈ r.1, Fits os p := by
  unfold readOpt at h
  split at h
  · exact readLong_mem h
  · exact readShort_mem h
  · exact absurd h (by simp)

theorem valid_consOpts {c : Command} {f : Frame} {fs : Invocation} {ps : List (String × Given)}
    (hv : Valid c (f :: fs))
    (hk : ∀ p ∈ ps, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true) :
    Valid c ({ f with opts := ps ++ f.opts } :: fs) := by
  obtain ⟨⟨hcmd, hopts⟩, hrest⟩ := hv
  refine ⟨⟨hcmd, ?_⟩, hrest⟩
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hk p hp
  · exact hopts p hp

theorem valid_sub_ne {c : Command} {f g : Frame} {gs : Invocation}
    (hv : Valid c (f :: g :: gs)) : c.subs.isEmpty = false := by
  obtain ⟨_, _, s, hs, _⟩ := hv
  have hmem : s ∈ c.subs := lookup_mem hs
  cases hsubs : c.subs with
  | nil => simp [hsubs] at hmem
  | cons _ _ => rfl

theorem fits_findId {c : Command} (h : c.LocalWF) {p : String × Given} (hp : Fits c.opts p) :
    ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true := by
  obtain ⟨o, ho, hid, hacc⟩ := hp
  exact ⟨o, hid ▸ findId_self h ho, hacc⟩

/-- **What a well-formed grammar parses is valid.** -/
theorem scans_valid {c : Command} {argv : List String} {r : Frame × Invocation}
    (h : Scans c argv r) (hwf : c.Good) : Valid c (r.1 :: r.2) := by
  induction h with
  | nil c => exact ⟨⟨rfl, by simp⟩, trivial⟩
  | dashdash _ => exact ⟨⟨rfl, by simp⟩, trivial⟩
  | opt hr _ ih =>
    exact valid_consOpts (ih hwf) fun p hp => fits_findId hwf.local (readOpt_mem hr p hp)
  | optNext hr _ ih =>
    exact valid_consOpts (ih hwf) fun p hp => fits_findId hwf.local (readOpt_mem hr p hp)
  | @arg c t w rest f fs _ hs _ ih =>
    show Valid c ({ f with args := w :: f.args } :: fs)
    have hv : Valid c (f :: fs) := ih hwf
    match fs, hv with
    | [], hv => exact ⟨⟨hv.1.1, hv.1.2⟩, trivial⟩
    | _ :: _, hv => exact absurd (valid_sub_ne hv) (by simp [hs])
  | @sub c t w s rest g gs _ _ hf _ ih =>
    show Valid c ({ cmd := c.name } :: g :: gs)
    have hs : s ∈ c.subs := lookup_mem hf
    have hg : Valid (c.child s) (g :: gs) := ih (hwf.sub hs)
    have hname : g.cmd = s.name := hg.1.1
    have hfind : findSub c.subs g.cmd = some s := hname ▸ findSub_name hwf.local hs
    exact ⟨⟨rfl, by simp⟩, rfl, s, hfind, hg⟩

/-- What `scan` returns for a well-formed grammar is valid. -/
theorem scan_valid {c : Command} (hwf : c.Good) {argv : List String} {fs : Invocation}
    (h : scan c argv = .ok fs) : Valid c fs := by
  obtain ⟨f, rest, rfl, hs⟩ := scan_eq_ok_iff.mp h
  exact scans_valid hs hwf

theorem error_of_consOpts {ps : List (String × Given)} {e : Except Located (Frame × Invocation)}
    {l : Located} (h : consOpts ps e = .error l) : e = .error l := by
  cases e <;> simp_all [consOpts, Except.map]

theorem error_of_consArg {w : String} {e : Except Located (Frame × Invocation)}
    {l : Located} (h : consArg w e = .error l) : e = .error l := by
  cases e <;> simp_all [consArg, Except.map]

theorem walk_underSub {c s : Command} (hwf : c.Good) (hsm : s ∈ c.subs)
    {e : Except Located (Frame × Invocation)}
    (ih : ∀ {p : List String} {err : ArgError}, (c.child s).Good → e = .error (p, err) →
      ∃ d, (c.child s).walk p = some d)
    {p : List String} {err : ArgError} (h : underSub c s.name e = .error (p, err)) :
    ∃ d, c.walk p = some d := by
  cases e with
  | ok a => exact absurd h (by simp [underSub])
  | error l =>
    obtain ⟨p', e'⟩ := l
    have hpe : p = s.name :: p' ∧ err = e' := by
      simp [underSub] at h; exact ⟨h.1.symm, h.2.symm⟩
    obtain ⟨d, hd⟩ := ih (p := p') (err := e') (hwf.sub hsm) rfl
    exact ⟨d, by rw [hpe.1]; simp [Command.walk, findSub_name hwf.local hsm, hd]⟩

/-- **Errors are located at a subcommand path of the grammar** (so `errorText` shows the usage
of the subcommand where the error was found). -/
theorem scanAux_error_walk {c : Command} {argv : List String} {p : List String} {e : ArgError}
    (hwf : c.Good) : scanAux c argv = .error (p, e) → ∃ d, c.walk p = some d := by
  fun_induction scanAux c argv generalizing p e with
  | case1 => intro h; exact absurd h (by simp)
  | case2 => intro h; exact absurd h (by simp)
  | case3 c t rest w hc hs ih => intro h; exact ih hwf (error_of_consArg h)
  | case4 => intro h; simp at h; obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩
  | case5 c t rest w hc hs s hf ih =>
    intro h
    exact walk_underSub hwf (lookup_mem hf) (fun hg hr => ih hg hr) h
  | case6 => intro h; simp at h; obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩
  | case7 => intro h; rename_i ih; exact ih hwf (error_of_consOpts h)
  | case8 => intro h; simp at h; obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩
  | case9 => intro h; rename_i ih; exact ih hwf (error_of_consOpts h)

/-- Errors of `scan` are located at a subcommand path of the grammar. -/
theorem scan_error_walk {c : Command} (hwf : c.Good) {argv : List String} {p : List String}
    {e : ArgError} (h : scan c argv = .error (p, e)) : ∃ d, c.walk p = some d := by
  exact scanAux_error_walk (e := e) hwf (argv := argv)
    (by cases hr : scanAux c argv <;> simp_all [scan, Except.map])

/-! ## Spellings -/

theorem splitEq_of_not_mem : ∀ {l : List Char}, '=' ∉ l → splitEq l = (l, none)
  | [], _ => rfl
  | ch :: l, h => by
    have hch : ch ≠ '=' := fun he => h (he ▸ List.mem_cons_self)
    have hl : '=' ∉ l := fun hm => h (List.mem_cons_of_mem _ hm)
    have ih := splitEq_of_not_mem hl
    unfold splitEq
    split <;> simp_all

theorem splitEq_append : ∀ {l : List Char} (r : List Char), '=' ∉ l →
    splitEq (l ++ '=' :: r) = (l, some r)
  | [], r, _ => by simp [splitEq]
  | ch :: l, r, h => by
    have hch : ch ≠ '=' := fun he => h (he ▸ List.mem_cons_self)
    have hl : '=' ∉ l := fun hm => h (List.mem_cons_of_mem _ hm)
    have ih := splitEq_append r hl
    rw [List.cons_append]
    unfold splitEq
    split <;> simp_all

theorem toList_ne_nil {n : String} (h : n ≠ "") : n.toList ≠ [] := by
  intro hn; exact h (String.toList_eq_nil_iff.mp hn)

theorem classify_long {n : String} (h : LongName n) : classify ("--" ++ n) = .long n none := by
  obtain ⟨hne, heq⟩ := h
  have hl : ("--" ++ n).toList = '-' :: '-' :: n.toList := by simp
  have hn := toList_ne_nil hne
  have hs := splitEq_of_not_mem heq
  unfold classify
  rw [hl]
  split <;> simp_all <;> subst_vars <;> simp_all

theorem classify_longEq {n : String} (h : LongName n) (x : String) :
    classify ("--" ++ n ++ "=" ++ x) = .long n (some x) := by
  obtain ⟨hne, heq⟩ := h
  have hl : ("--" ++ n ++ "=" ++ x).toList = '-' :: '-' :: (n.toList ++ '=' :: x.toList) := by
    simp
  have hs := splitEq_append x.toList heq
  unfold classify
  rw [hl]
  split <;> simp_all <;> subst_vars <;> simp_all

theorem classify_short {n : String} (h : ShortName n) : classify ("-" ++ n) = .short n := by
  obtain ⟨hne, hd⟩ := h
  have hl : ("-" ++ n).toList = '-' :: n.toList := by simp
  have hn := toList_ne_nil hne
  unfold classify
  rw [hl]
  split <;> simp_all <;> subst_vars <;> simp_all

theorem LongName.no {n : String} (h : LongName n) : LongName ("no-" ++ n) := by
  obtain ⟨_, heq⟩ := h
  refine ⟨fun he => by simpa using congrArg String.length he, ?_⟩
  simpa using heq

theorem stripNo_no (n : String) : stripNo ("no-" ++ n) = some n := by
  have hl : ("no-" ++ n).toList = 'n' :: 'o' :: '-' :: n.toList := by simp
  simp [stripNo, hl]

/-! ## The normal form reads back -/

/-- The options of a well-formed level. -/
theorem Command.LocalWF.opt {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) :
    o.LocalWF c.opts := h.2.2.2.2.1 o ho

theorem spelling_cases {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) :
    (∃ n, o.long.head? = some n ∧ o.spelling = "--" ++ n ∧ LongName n ∧
        findLong c.opts n = some o) ∨
      (o.long = [] ∧ ∃ n, o.spelling = "-" ++ n ∧ ShortName n ∧ findShort c.opts n = some o) := by
  have hw := h.opt ho
  match hl : o.long, hs : o.short with
  | n :: _, _ =>
    exact .inl ⟨n, rfl, by simp [Opt.spelling, hl], hw.2.1 n (by simp [hl]),
      (findLong_eq_some_iff h).mpr ⟨ho, by simp [hl]⟩⟩
  | [], n :: _ =>
    exact .inr ⟨rfl, n, by simp [Opt.spelling, hl, hs], hw.2.2.1 n (by simp [hs]),
      (findShort_eq_some_iff h).mpr ⟨ho, by simp [hs]⟩⟩
  | [], [] => exact absurd (by simp [hl, hs]) hw.1

theorem headD_of_head? {l : List String} {d n : String} (h : l.head? = some n) :
    l.headD d = n ∧ n ∈ l := by
  cases l with
  | nil => simp at h
  | cons m _ => simp at h; subst h; simp

/-- A flag, or an option with an optional value given without one, reads back from its
spelling. -/
theorem readOpt_on {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts)
    (hacc : o.accepts .on = true) (x : Option String) :
    readOpt c.opts o.spelling x = .ok ([(o.id, .on)], false) := by
  have hw := h.opt ho
  rcases spelling_cases h ho with ⟨n, -, hsp, hn, hf⟩ | ⟨hl, n, hsp, hn, hf⟩
  · rw [hsp]
    cases htv : o.takesValue <;> cases hvo : o.valueOptional <;>
      simp_all [readOpt, readLong, valueFromNext, classify_long hn, Opt.accepts]
  · have hvo : o.valueOptional = false := by
      cases hv : o.valueOptional
      · rfl
      · exact absurd (hw.2.2.2.1 hv).2 (by simp [hl])
    rw [hsp]
    simp_all [readOpt, readShort, classify_short hn, Opt.accepts, Opt.takesValue]

/-- An option with a value (not optional) reads back from its spelling and the value. -/
theorem readOpt_val {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts)
    (htv : o.takesValue = true) (hvo : o.valueOptional = false) (x : String) :
    readOpt c.opts o.spelling (some x) = .ok ([(o.id, .val x)], true) := by
  rcases spelling_cases h ho with ⟨n, -, hsp, hn, hf⟩ | ⟨-, n, hsp, hn, hf⟩
  · rw [hsp]; simp_all [readOpt, readLong, valueFromNext, classify_long hn]
  · rw [hsp]
    simp_all [readOpt, readShort, valueFromNext, classify_short hn, Opt.takesValue]

/-- An optional value reads back attached to the first long name. -/
theorem readOpt_valEq {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts)
    (hvo : o.valueOptional = true) (x : String) (y : Option String) :
    readOpt c.opts ("--" ++ o.long.headD o.id ++ "=" ++ x) y = .ok ([(o.id, .val x)], false) := by
  have hw := (h.opt ho).2.2.2.1 hvo
  rcases spelling_cases h ho with ⟨n, hhd, -, hn, hf⟩ | ⟨hl, -⟩
  · rw [(headD_of_head? (d := o.id) hhd).1]
    simp_all [readOpt, readLong, classify_longEq hn]
  · exact absurd hl hw.2

/-- A negated flag reads back from `--no-` and its first long name. -/
theorem readOpt_off {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts)
    (hacc : o.accepts .off = true) (y : Option String) :
    readOpt c.opts ("--no-" ++ o.long.headD o.id) y = .ok ([(o.id, .off)], false) := by
  have hneg : o.negatable = true := by simp_all [Opt.accepts]
  have hw := (h.opt ho).2.2.2.2 hneg
  rcases spelling_cases h ho with ⟨n, hhd, -, hn, hf⟩ | ⟨hl, -⟩
  · obtain ⟨hhead, hmem⟩ := headD_of_head? (d := o.id) hhd
    have hnone : findLong c.opts ("no-" ++ n) = none := hw.2.2 n hmem
    have hstr : "--no-" ++ n = "--" ++ ("no-" ++ n) := by simp [← String.append_assoc]
    rw [hhead, hstr]
    simp_all [readOpt, readLong, readNo, classify_long hn.no, stripNo_no]
  · exact absurd hl hw.2.1

/-- One occurrence in normal form scans back. -/
theorem scanAux_given {c : Command} (h : c.LocalWF) {o : Opt} (ho : o ∈ c.opts) {g : Given}
    (hacc : o.accepts g = true) (tail : List String) :
    scanAux c (renderGiven o g ++ tail) = consOpts [(o.id, g)] (scanAux c tail) := by
  cases g with
  | on => exact scanAux_opt (readOpt_on h ho hacc _)
  | off => exact scanAux_opt (readOpt_off h ho hacc _)
  | val x =>
    have htv : o.takesValue = true := by simpa [Opt.accepts] using hacc
    cases hvo : o.valueOptional with
    | false =>
      simp only [renderGiven, hvo]
      exact scanAux_optNext (readOpt_val h ho htv hvo x)
    | true =>
      simp only [renderGiven, hvo]
      exact scanAux_opt (readOpt_valEq h ho hvo x _)

theorem consOpts_consOpts (ps qs : List (String × Given))
    (e : Except Located (Frame × Invocation)) :
    consOpts ps (consOpts qs e) = consOpts (ps ++ qs) e := by
  cases e <;> simp [consOpts, Except.map]

/-- The options of a frame in normal form scan back. -/
theorem scanAux_renderOpts {c : Command} (h : c.LocalWF) {ps : List (String × Given)}
    (hps : ∀ p ∈ ps, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true)
    (tail : List String) :
    scanAux c (ps.flatMap (renderOpt c.opts) ++ tail) = consOpts ps (scanAux c tail) := by
  induction ps with
  | nil => cases h : scanAux c tail <;> simp [consOpts, Except.map, h]
  | cons p ps ih =>
    obtain ⟨o, hfo, hacc⟩ := hps p List.mem_cons_self
    have ho : o ∈ c.opts := lookup_mem hfo
    have hid : p.1 = o.id := by simpa using lookup_key hfo
    have hrest := ih fun q hq => hps q (List.mem_cons_of_mem _ hq)
    have hr : renderOpt c.opts p = renderGiven o p.2 := by simp [renderOpt, hfo]
    calc scanAux c ((p :: ps).flatMap (renderOpt c.opts) ++ tail)
        = scanAux c (renderGiven o p.2 ++ (ps.flatMap (renderOpt c.opts) ++ tail)) := by
          simp [hr]
      _ = consOpts [(o.id, p.2)] (scanAux c (ps.flatMap (renderOpt c.opts) ++ tail)) :=
          scanAux_given h ho hacc _
      _ = consOpts (p :: ps) (scanAux c tail) := by
          rw [hrest, consOpts_consOpts, ← hid]; rfl

/-- Positional words in normal form scan back. -/
theorem scanAux_renderArgs (c : Command) (args : List String) :
    scanAux c (renderArgs c args) = .ok ({ cmd := c.name, args := args }, []) := by
  by_cases he : args.isEmpty
  · have hnil : args = [] := List.isEmpty_iff.mp he
    simp [renderArgs, hnil, scanAux]
  · by_cases hg : !c.subs.isEmpty || !args.all isWord
    · simp only [renderArgs, he, hg]
      simp [scanAux, show classify "--" = .dashdash by decide]
    · have hsub : c.subs.isEmpty = true := by simp_all
      have hw : ∀ w ∈ args, classify w = .word w := by
        intro w hw
        have hiw : isWord w = true := by simp_all
        simpa [isWord] using hiw
      have hargs : renderArgs c args = args := by simp_all [renderArgs]
      rw [hargs]
      clear he hg hargs
      induction args with
      | nil => simp [scanAux]
      | cons w ws ih =>
        have hc : classify w = .word w := hw w List.mem_cons_self
        have hrest := ih fun x hx => hw x (List.mem_cons_of_mem _ hx)
        simp [scanAux, hc, hsub, hrest, consArg, Except.map]

theorem frame_eta {c : Command} {f : Frame} (h : f.cmd = c.name) :
    ({ cmd := c.name, opts := f.opts, args := f.args } : Frame) = f := by
  cases f; simp_all

theorem subs_isEmpty_of_mem {c s : Command} (hs : s ∈ c.subs) : c.subs.isEmpty = false := by
  cases hsubs : c.subs with
  | nil => exact absurd (hsubs ▸ hs) List.not_mem_nil
  | cons _ _ => rfl

/-- The step of the round trip through a subcommand. -/
theorem scanAux_render_cons {c s : Command} {f g : Frame} {gs : Invocation} (hwf : c.Good)
    (hcmd : f.cmd = c.name)
    (hopts : ∀ p ∈ f.opts, ∃ o, findId c.opts p.1 = some o ∧ o.accepts p.2 = true)
    (hargs : f.args = []) (hfind : findSub c.subs g.cmd = some s) (hgname : g.cmd = s.name)
    (hsub : scanAux (c.child s) (render (c.child s) (g :: gs)) = .ok (g, gs)) :
    scanAux c (render c (f :: g :: gs)) = .ok (f, g :: gs) := by
  have hs : s ∈ c.subs := lookup_mem hfind
  have hword : classify g.cmd = .word g.cmd := hgname ▸ hwf.local.2.2.2.2.2 s hs
  have hstep : scanAux c (g.cmd :: render (c.child s) (g :: gs)) =
      .ok ({ cmd := c.name }, g :: gs) := by
    simp [scanAux, hword, subs_isEmpty_of_mem hs, hfind, hsub, underSub]
  have hf : ({ cmd := c.name, opts := f.opts } : Frame) = f := by
    cases f; simp_all
  show scanAux c (f.opts.flatMap (renderOpt c.opts) ++ (match findSub c.subs g.cmd with
    | some s => g.cmd :: render (c.child s) (g :: gs) | none => [])) = .ok (f, g :: gs)
  rw [hfind, scanAux_renderOpts hwf.local hopts, hstep]
  simp [consOpts, Except.map, hf]

/-- **Round trip**: a valid invocation, rendered and parsed, comes back unchanged. -/
theorem scanAux_render (rest : Invocation) :
    ∀ (c : Command) (f : Frame), c.Good → Valid c (f :: rest) →
      scanAux c (render c (f :: rest)) = .ok (f, rest) := by
  induction rest with
  | nil =>
    intro c f hwf hv
    show scanAux c (f.opts.flatMap (renderOpt c.opts) ++ renderArgs c f.args) = .ok (f, [])
    rw [scanAux_renderOpts hwf.local hv.1.2, scanAux_renderArgs]
    simp [consOpts, Except.map, frame_eta hv.1.1]
  | cons g gs ih =>
    intro c f hwf hv
    obtain ⟨⟨hcmd, hopts⟩, hargs, s, hfind, hvs⟩ := hv
    have hs : s ∈ c.subs := lookup_mem hfind
    exact scanAux_render_cons hwf hcmd hopts hargs hfind hvs.1.1
      (ih (c.child s) g (hwf.sub hs) hvs)

/-- `scan` after `render` is the identity on valid invocations. -/
theorem scan_render {c : Command} (hwf : c.WF) {fs : Invocation} (hv : Valid c fs) :
    scan c (render c fs) = .ok fs := by
  match fs, hv with
  | f :: rest, hv => simp [scan, scanAux_render rest c f hwf.good hv, Except.map]

/-- Parse, render, parse: the same invocation. -/
theorem scan_render_scan {c : Command} (hwf : c.WF) {argv : List String} {fs : Invocation}
    (h : scan c argv = .ok fs) : scan c (render c fs) = .ok fs :=
  scan_render hwf (scan_valid hwf.good h)

/-- The normal form is a normal form: normalizing it changes nothing. -/
theorem normalize_idem {c : Command} (hwf : c.WF) {argv nf : List String}
    (h : normalize c argv = .ok nf) : normalize c nf = .ok nf := by
  unfold normalize at h ⊢
  exact except_map_ok (P := fun nf => (scan c nf).map (render c) = .ok nf) h fun fs hfs => by
    simp [scan_render_scan hwf hfs, Except.map]

end Silmaril.Cli
