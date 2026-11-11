module

public import Silmaril.Cli.Args.Defs
public import Silmaril.Proofs.Cli.Args.Scan

@[expose] public section

/-!
# Proofs: resolution

* `resolveOpt_cmdline`, `resolveOpt_env`, `resolveOpt_default`, `resolveOpt_absent`,
  `resolveOpt_flag`: values come from the command line, else the environment variable, else the
  default; a flag has one value per occurrence (`count_flag`: a counted flag counts them);
* `Matches.Equiv` (same path, same values for every identifier) and `ResolvesLike P d d'`
  (every invocation satisfying `P` that `d` resolves, `d'` resolves to equivalent matches);
* **compatibility along grammar extensions, at any depth**: `resolvesLike_addOpt` (a fresh
  option, local or global), `resolvesLike_addSub` (a subcommand), and the congruence
  `resolvesLike_subs` (a command whose subcommands resolve alike resolves alike), so an
  extension anywhere in the tree is reached level by level; `resolve_addOpt` at the root;
* `noId_of_valid`: what a grammar parses mentions only identifiers it declares.

A Silmaril addition.
-/

namespace Silmaril.Cli

theorem resolveOpt_eq (env : String → Option String) (occ : List Given) (o : Opt) :
    resolveOpt env occ o =
      if !o.repeated && occ.length > 1 then .error (.repeated o.id) else
      match o.arg with
      | none => .ok (o.id, occ.map fun | .off => .off | _ => .flag)
      | some t =>
        if occ.isEmpty then
          match o.env.bind env, o.default with
          | some s, _ => (parseAs o.id t s).map fun v => (o.id, [v])
          | none, some s => (parseAs o.id t s).map fun v => (o.id, [v])
          | none, none => if o.required then .error (.missingOption o.id) else .ok (o.id, [])
        else (occ.mapM (givenValue o.id t o.missing)).map fun vs => (o.id, vs) := rfl

/-- Values given on the command line win. -/
theorem resolveOpt_cmdline {env : String → Option String} {occ : List Given} {o : Opt}
    {t : ArgType} (ht : o.arg = some t) (hne : occ.isEmpty = false)
    (hrep : (!o.repeated && occ.length > 1) = false) :
    resolveOpt env occ o = (occ.mapM (givenValue o.id t o.missing)).map fun vs => (o.id, vs) := by
  rw [resolveOpt_eq]; simp [hrep, ht, hne]

/-- Absent from the command line, the environment variable wins. -/
theorem resolveOpt_env {env : String → Option String} {o : Opt} {t : ArgType}
    {e s : String} (ht : o.arg = some t) (he : o.env = some e) (hs : env e = some s) :
    resolveOpt env [] o = (parseAs o.id t s).map fun v => (o.id, [v]) := by
  rw [resolveOpt_eq]; simp [ht, he, hs]

/-- Absent from the command line and the environment, the default applies. -/
theorem resolveOpt_default {env : String → Option String} {o : Opt} {t : ArgType}
    {d : String} (ht : o.arg = some t) (he : o.env.bind env = none) (hd : o.default = some d) :
    resolveOpt env [] o = (parseAs o.id t d).map fun v => (o.id, [v]) := by
  rw [resolveOpt_eq]; simp [ht, he, hd]

/-- Absent everywhere: an error if required, else no value. -/
theorem resolveOpt_absent {env : String → Option String} {o : Opt} {t : ArgType}
    (ht : o.arg = some t) (he : o.env.bind env = none) (hd : o.default = none) :
    resolveOpt env [] o =
      if o.required then .error (.missingOption o.id) else .ok (o.id, []) := by
  rw [resolveOpt_eq]; simp [ht, he, hd]

/-- A flag has one value per occurrence (`off` for `--no-x`); repeated only if declared so. -/
theorem resolveOpt_flag {env : String → Option String} {occ : List Given} {o : Opt}
    (ht : o.arg = none) (hrep : (!o.repeated && occ.length > 1) = false) :
    resolveOpt env occ o = .ok (o.id, occ.map fun | .off => .off | _ => .flag) := by
  rw [resolveOpt_eq]; simp [hrep, ht]

/-- A counted flag counts its occurrences (`-vvv` is three). -/
theorem count_flag {env : String → Option String} {occ : List Given} {o : Opt}
    (ht : o.arg = none) (hrep : o.repeated = true) :
    resolveOpt env occ o = .ok (o.id, occ.map fun | .off => .off | _ => .flag) ∧
      (occ.map fun | .off => Value.off | _ => .flag).length = occ.length :=
  ⟨resolveOpt_flag ht (by simp [hrep]), List.length_map _⟩

/-! ## Matches up to the order of bindings -/

/-- Same path, same values for every identifier. -/
def Matches.Equiv (m m' : Matches) : Prop := m.path = m'.path ∧ ∀ k, m.get k = m'.get k

theorem Matches.Equiv.refl (m : Matches) : m.Equiv m := ⟨rfl, fun _ => rfl⟩

theorem Matches.Equiv.trans {m₁ m₂ m₃ : Matches} (h₁ : m₁.Equiv m₂) (h₂ : m₂.Equiv m₃) :
    m₁.Equiv m₃ :=
  ⟨h₁.1.trans h₂.1, fun k => (h₁.2 k).trans (h₂.2 k)⟩

theorem Matches.get_append (l l' : List (String × List Value)) (path : List String) (k : String) :
    ({ path, values := l ++ l' } : Matches).get k =
      ({ values := l } : Matches).get k ++ ({ values := l' } : Matches).get k := by
  simp [Matches.get, List.filter_append, List.flatMap_append]

/-- Equivalence is a congruence for the step of `resolveAux` through a subcommand. -/
theorem Matches.Equiv.under {m m' : Matches} (h : m.Equiv m') (w : String)
    (mine : List (String × List Value)) :
    ({ path := w :: m.path, values := m.values ++ mine } : Matches).Equiv
      { path := w :: m'.path, values := m'.values ++ mine } := by
  refine ⟨by rw [h.1], fun k => ?_⟩
  rw [Matches.get_append, Matches.get_append]
  have hk := h.2 k
  simp only [Matches.get] at hk ⊢
  rw [hk]

/-- **`d'` resolves like `d` on the invocations satisfying `P`**: whatever `d` resolves, `d'`
resolves to equivalent matches. -/
def ResolvesLike (P : Invocation → Prop) (d d' : Command) : Prop :=
  ∀ env fs m, P fs → resolveAux env d fs = .ok m →
    ∃ m', resolveAux env d' fs = .ok m' ∧ m.Equiv m'

theorem ResolvesLike.refl (P : Invocation → Prop) (d : Command) : ResolvesLike P d d :=
  fun _ _ m _ h => ⟨m, h, .refl m⟩

theorem ResolvesLike.trans {P : Invocation → Prop} {d₁ d₂ d₃ : Command}
    (h₁ : ResolvesLike P d₁ d₂) (h₂ : ResolvesLike P d₂ d₃) : ResolvesLike P d₁ d₃ := by
  intro env fs m hP h
  obtain ⟨m₂, h₂', he₁⟩ := h₁ env fs m hP h
  obtain ⟨m₃, h₃, he₂⟩ := h₂ env fs m₂ hP h₂'
  exact ⟨m₃, h₃, he₁.trans he₂⟩

theorem ResolvesLike.mono {P Q : Invocation → Prop} (hPQ : ∀ fs, Q fs → P fs) {d d' : Command}
    (h : ResolvesLike P d d') : ResolvesLike Q d d' :=
  fun env fs m hQ hd => h env fs m (hPQ fs hQ) hd

/-! ## The step of `resolveAux` -/

/-- What `resolveAux` does after resolving the options of the first frame. -/
def resolveTail (env : String → Option String) (c : Command) (f : Frame) (rest : Invocation)
    (mine : List (String × List Value)) : Except Located Matches :=
  match rest with
  | [] =>
    if !c.subs.isEmpty && c.subRequired && f.args.isEmpty then
      .error ([], .missingCommand c.name)
    else do
      let ps ← here (bindPos c.pos f.args)
      pure { path := [], values := ps ++ mine }
  | g :: _ =>
    match findSub c.subs g.cmd with
    | none => .error ([], .unknownCommand g.cmd)
    | some s => do
      let m ← below s.name (resolveAux env s rest)
      pure { path := g.cmd :: m.path, values := m.values ++ mine }

theorem resolveAux_cons (env : String → Option String) (c : Command) (f : Frame)
    (rest : Invocation) :
    resolveAux env c (f :: rest) =
      (here (c.opts.mapM fun o => resolveOpt env (occIn o f rest) o)).bind
        (resolveTail env c f rest) := by
  cases rest <;> rfl

theorem bind_ok {ε α β : Type} {e : Except ε α} {k : α → Except ε β} {b : β}
    (h : e.bind k = .ok b) : ∃ a, e = .ok a ∧ k a = .ok b := by
  cases e with
  | error x => exact absurd h (by simp [Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Fresh options -/

/-- An option that can only be absent resolves to no value. -/
def Opt.Fresh (o : Opt) : Prop := o.env = none ∧ o.default = none ∧ o.required = false

/-- No frame mentions the identifier `k`. -/
def NoId (k : String) (fs : Invocation) : Prop := ∀ g ∈ fs, ∀ p ∈ g.opts, p.1 ≠ k

theorem NoId.tail {k : String} {f : Frame} {rest : Invocation} (h : NoId k (f :: rest)) :
    NoId k rest := fun g hg => h g (List.mem_cons_of_mem _ hg)

theorem occOf_nil {f : Frame} {k : String} (h : ∀ p ∈ f.opts, p.1 ≠ k) : occOf f k = [] := by
  simp only [occOf, List.filterMap_eq_nil_iff]
  intro p hp
  simp [h p hp]

theorem occIn_nil {o : Opt} {f : Frame} {rest : Invocation} (h : NoId o.id (f :: rest)) :
    occIn o f rest = [] := by
  have hf : occOf f o.id = [] := occOf_nil (h f List.mem_cons_self)
  have hr : rest.flatMap (occOf · o.id) = [] := by
    simp only [List.flatMap_eq_nil_iff]
    intro g hg
    exact occOf_nil (h g (List.mem_cons_of_mem _ hg))
  simp [occIn, hf, hr]

theorem resolveOpt_fresh {env : String → Option String} {o : Opt} (ho : o.Fresh) :
    resolveOpt env [] o = .ok (o.id, []) := by
  rw [resolveOpt_eq]
  cases ht : o.arg <;> simp [ho.1, ho.2.1, ho.2.2]

/-- Add an empty binding at the end. -/
def Matches.addFresh (m : Matches) (k : String) : Matches :=
  { m with values := m.values ++ [(k, [])] }

theorem Matches.get_addFresh (m : Matches) (k id : String) :
    (m.addFresh k).get id = m.get id := by
  by_cases h : k = id <;> simp [Matches.addFresh, Matches.get, List.filter_append, h]

theorem Matches.equiv_addFresh (m : Matches) (k : String) : m.Equiv (m.addFresh k) :=
  ⟨rfl, fun id => (Matches.get_addFresh m k id).symm⟩

theorem mapM_append_one {α β : Type} {g : α → Except ArgError β} {l : List α} {a : α} {b : β}
    (hb : g a = .ok b) : (l ++ [a]).mapM g = (l.mapM g).map (· ++ [b]) := by
  rw [List.mapM_append]
  cases l.mapM g <;> simp [hb, Except.map] <;> rfl

theorem resolveTail_addFresh (env : String → Option String) (c : Command) (f : Frame)
    (rest : Invocation) (mine : List (String × List Value)) (k : String) :
    resolveTail env c f rest (mine ++ [(k, [])]) =
      (resolveTail env c f rest mine).map (·.addFresh k) := by
  match rest with
  | [] =>
    simp only [resolveTail]
    split
    · rfl
    · cases here (bindPos c.pos f.args) <;> simp [Except.map, Matches.addFresh, bind,
        Except.bind, pure, Except.pure]
  | g :: gs =>
    simp only [resolveTail]
    cases findSub c.subs g.cmd with
    | none => rfl
    | some s =>
      cases hb : below s.name (resolveAux env s (g :: gs)) <;> simp [hb, Except.map,
        Matches.addFresh, bind, Except.bind, pure, Except.pure]

/-- **Adding a fresh option** (local or global) adds an empty binding for it and changes nothing
else, on invocations that do not mention it. -/
theorem resolve_addOpt {c : Command} {o : Opt} (ho : o.Fresh) (env : String → Option String)
    {f : Frame} {rest : Invocation} (hf : NoId o.id (f :: rest)) :
    resolveAux env (c.addOpt o) (f :: rest) =
      (resolveAux env c (f :: rest)).map (·.addFresh o.id) := by
    have hmap : (c.opts ++ [o]).mapM (fun o => resolveOpt env (occIn o f rest) o) =
        (c.opts.mapM fun o => resolveOpt env (occIn o f rest) o).map (· ++ [(o.id, [])]) := by
      apply mapM_append_one
      rw [occIn_nil hf]; exact resolveOpt_fresh ho
    have htail : resolveTail env (c.addOpt o) f rest = resolveTail env c f rest := rfl
    rw [resolveAux_cons, resolveAux_cons, htail]
    show (here ((c.opts ++ [o]).mapM _)).bind _ = _
    rw [hmap]
    cases c.opts.mapM fun o => resolveOpt env (occIn o f rest) o with
    | error e => rfl
    | ok mine => exact resolveTail_addFresh env c f rest mine o.id

/-- A fresh option resolves alike, at any level where it is added. -/
theorem resolvesLike_addOpt {o : Opt} (ho : o.Fresh) (d : Command) :
    ResolvesLike (NoId o.id) d (d.addOpt o) := by
  intro env fs m hP h
  match fs, hP, h with
  | [], _, h => exact ⟨m, h, .refl m⟩
  | f :: rest, hP, h =>
    refine ⟨m.addFresh o.id, ?_, Matches.equiv_addFresh m o.id⟩
    rw [resolve_addOpt ho env hP, h]; rfl

/-! ## Subcommands -/

theorem findSub_append_of_some {l l' : List Command} {w : String} {t : Command}
    (h : findSub l w = some t) : findSub (l ++ l') w = some t := by
  simp [findSub, lookupKey, List.find?_append] at h ⊢
  simp [h]

theorem resolveTail_addSub {d : Command} (hne : d.subs ≠ []) (s : Command)
    {env : String → Option String} {f : Frame} {rest : Invocation}
    {mine : List (String × List Value)} {m : Matches}
    (ht : resolveTail env d f rest mine = .ok m) : resolveTail env (d.addSub s) f rest mine = .ok m := by
  have hempty : (d.subs ++ [s]).isEmpty = d.subs.isEmpty := by
    cases hc : d.subs with
    | nil => exact absurd hc hne
    | cons _ _ => rfl
  match rest, ht with
  | [], ht =>
    simp only [resolveTail, Command.addSub, hempty] at ht ⊢
    exact ht
  | g :: gs, ht =>
    cases hf : findSub d.subs g.cmd with
    | none => simp [resolveTail, hf] at ht
    | some t =>
      have hf' : findSub (d.addSub s).subs g.cmd = some t := findSub_append_of_some hf
      simpa [resolveTail, hf, hf'] using ht

/-- **Adding a subcommand** to a command that has some changes nothing that resolved. -/
theorem resolvesLike_addSub {d : Command} (hne : d.subs ≠ []) (s : Command) :
    ResolvesLike (fun _ => True) d (d.addSub s) := by
  intro env fs m _ h
  refine ⟨m, ?_, .refl m⟩
  match fs, h with
  | [], h => exact h
  | f :: rest, h =>
    rw [resolveAux_cons] at h ⊢
    obtain ⟨mine, hmine, ht⟩ := bind_ok h
    have hmine' : here ((d.addSub s).opts.mapM fun o => resolveOpt env (occIn o f rest) o) =
        .ok mine := hmine
    rw [hmine']
    exact resolveTail_addSub hne s ht

/-- Two subcommand lists, pairwise with the same names and related by `R`. -/
inductive SubsRel (R : Command → Command → Prop) : List Command → List Command → Prop where
  | nil : SubsRel R [] []
  | cons {s s' : Command} {l l' : List Command} : s'.names = s.names ∧ R s s' → SubsRel R l l' →
      SubsRel R (s :: l) (s' :: l')

theorem SubsRel.isEmpty_eq {R : Command → Command → Prop} {l l' : List Command}
    (h : SubsRel R l l') : l'.isEmpty = l.isEmpty := by
  cases h <;> rfl

/-- Related subcommand lists find related subcommands. -/
theorem findSub_forall₂ {R : Command → Command → Prop} {l l' : List Command}
    (h : SubsRel R l l') (w : String) :
    (findSub l w = none ∧ findSub l' w = none) ∨
      ∃ s s', findSub l w = some s ∧ findSub l' w = some s' ∧ s'.names = s.names ∧ R s s' := by
  induction h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @cons s s' l l' hss _ ih =>
    by_cases hw : w ∈ s.names
    · have hw' : w ∈ s'.names := by rw [hss.1]; exact hw
      refine .inr ⟨s, s', ?_, ?_, hss.1, hss.2⟩
      · simp [findSub, lookupKey, hw]
      · simp [findSub, lookupKey, hw']
    · have hw' : w ∉ s'.names := by rw [hss.1]; exact hw
      have e1 : findSub (s :: l) w = findSub l w := by
        simp [findSub, lookupKey, hw]
      have e2 : findSub (s' :: l') w = findSub l' w := by
        simp [findSub, lookupKey, hw']
      rw [e1, e2]; exact ih

theorem resolveTail_sub {P : Invocation → Prop} {c c' : Command}
    (hs : SubsRel (ResolvesLike P) c.subs c'.subs) {env : String → Option String}
    {f g : Frame} {gs : Invocation} (hPgs : P (g :: gs)) {mine : List (String × List Value)}
    {m : Matches} (ht : resolveTail env c f (g :: gs) mine = .ok m) :
    ∃ m', resolveTail env c' f (g :: gs) mine = .ok m' ∧ m.Equiv m' := by
  rcases findSub_forall₂ hs g.cmd with ⟨h1, -⟩ | ⟨s, s', h1, h2, -, hR⟩
  · simp [resolveTail, h1] at ht
  · cases hsub : resolveAux env s (g :: gs) with
    | error l => simp [resolveTail, h1, hsub, below, bind, Except.bind] at ht
    | ok ms =>
      have hm : { path := g.cmd :: ms.path, values := ms.values ++ mine } = m := by
        simpa [resolveTail, h1, hsub, below, bind, Except.bind, pure, Except.pure] using ht
      obtain ⟨ms', hs', heq⟩ := hR env (g :: gs) ms hPgs hsub
      refine ⟨{ path := g.cmd :: ms'.path, values := ms'.values ++ mine }, ?_, ?_⟩
      · simp [resolveTail, h2, hs', below, bind, Except.bind, pure, Except.pure]
      · rw [← hm]; exact heq.under g.cmd mine

/-- **Congruence**: a command with the same options and positionals whose subcommands resolve
alike resolves alike. With `resolvesLike_addOpt` and `resolvesLike_addSub`, an extension at any
depth of the tree resolves alike. -/
theorem resolvesLike_subs {P : Invocation → Prop} (hP : ∀ f rest, P (f :: rest) → P rest)
    {c c' : Command} (hn : c'.name = c.name) (ho : c'.opts = c.opts) (hp : c'.pos = c.pos)
    (hr : c'.subRequired = c.subRequired)
    (hs : SubsRel (ResolvesLike P) c.subs c'.subs) :
    ResolvesLike P c c' := by
  intro env fs m hPfs h
  match fs, h with
  | [], h => exact ⟨m, h, .refl m⟩
  | f :: rest, h =>
    rw [resolveAux_cons] at h ⊢
    obtain ⟨mine, hmine, ht⟩ := bind_ok h
    rw [ho, hmine]
    show ∃ m', resolveTail env c' f rest mine = .ok m' ∧ m.Equiv m'
    match rest, ht with
    | [], ht =>
      refine ⟨m, ?_, .refl m⟩
      simp only [resolveTail, hs.isEmpty_eq, hr, hn, hp] at ht ⊢
      exact ht
    | g :: gs, ht => exact resolveTail_sub hs (hP f _ hPfs) ht

/-! ## Identifiers in parsed invocations -/

/-- What a grammar parses mentions only identifiers declared along its path: a fresh identifier
(declared nowhere in the tree as the parser sees it) is not mentioned. -/
theorem noId_of_valid {k : String} :
    ∀ (fs : Invocation) (c : Command), Valid c fs →
      (∀ ws d, c.walk ws = some d → k ∉ d.opts.map (·.id)) → NoId k fs := by
  intro fs
  induction fs with
  | nil => intro c _ _ g hg; cases hg
  | cons f rest ih =>
    intro c hv hk g hg p hp hpk
    rcases List.mem_cons.mp hg with rfl | hg
    · obtain ⟨o, hfo, _⟩ := hv.1.2 p hp
      have hid : p.1 = o.id := by simpa using lookup_key hfo
      exact hk [] c rfl (List.mem_map.mpr ⟨o, lookup_mem hfo, hid ▸ hpk ▸ rfl⟩)
    · match rest, hv, hg with
      | g' :: gs, hv, hg =>
        obtain ⟨-, -, s, hfind, hvs⟩ := hv
        exact ih (c.child s) hvs (fun ws d hd => hk (g'.cmd :: ws) d
          (by simp [Command.walk, hfind, hd])) g hg p hp hpk

end Silmaril.Cli
