module

public import Silmaril.Proofs.Wasm.Game.GamesAux.Basic
public import Silmaril.Games.Inst.Thms
public import Silmaril.Games.LTS.Thms
public import Silmaril.Wasm.Game.Start.Defs

/-!
# Auxiliary facts about strategies, composition and instantiation phases

* `strategy_ext_isP`: strategies with the same plays ending in a Proponent move are equal
  (plays alternate and strategies are receptive);
* `comp_noEv_isP`, `comp_noEv_of_traces`: a play ending in a Proponent move of the
  composite of the strategies of two transition systems, the lower one without lower
  events, is the upper projection of a trace of the upper system whose lower projection is a
  trace of the lower one (and conversely, for legal traces);
* `InstSystem.traces_legal`, `InstSystem.consumer_traces_legal`: traces of the transition
  systems of `Silmaril.Games.Inst` are legal (positions read off the states);
* `InstSystem.IRun`: the instantiation phase of an `InstSystem` with its import calls;
  `InstSystem.toLTS_ready_iff`, `toLTS_fail_iff`, `toLTS_trace_cases` (instantiation with no
  import call, e.g. a closed component) and `consumer_inst_split`, `consumer_run_ready`,
  `consumer_run_fail`, `consumer_trace_cases` (the consumer system of a link).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.GamesAux

open Silmaril.Games Silmaril.Games.Inst

universe u

variable {E F X : Sig.{u}}

/-! ## Runs and plays (restated from `Silmaril.Proofs.Games.Inst.Basic`, layout rules) -/

theorem silent_run_stuck {L : LTS E F} {x y : L.State} (hx : ∀ z, ¬ L.step x none z)
    (h : L.Run x [] y) : y = x := by
  cases h with
  | nil => rfl
  | tau hst _ => exact (hx _ hst).elim

theorem silent_run_map {L : LTS E F} {A : Type u} (f : A → L.State) (r : A → A → Prop)
    (hf : ∀ a z, L.step (f a) none z → ∃ b, r a b ∧ z = f b) {a : A} {y : L.State}
    (h : L.Run (f a) [] y) : ∃ b, y = f b ∧ Relation.ReflTransGen r a b := by
  generalize hx : f a = x at h
  generalize hs : ([] : List (Move E F)) = s at h
  induction h generalizing a with
  | nil => subst hx; exact ⟨a, rfl, .refl⟩
  | tau hst _ ih =>
    subst hx
    obtain ⟨b, hab, rfl⟩ := hf a _ hst
    obtain ⟨c, rfl, hc⟩ := ih rfl hs
    exact ⟨c, rfl, Relation.ReflTransGen.head hab hc⟩
  | vis _ _ _ => cases hs

theorem run_of_rtg {L : LTS E F} {A : Type u} (f : A → L.State) {r : A → A → Prop}
    (hf : ∀ a b, r a b → L.step (f a) none (f b)) {a b : A} (h : Relation.ReflTransGen r a b) :
    L.Run (f a) [] (f b) := by
  induction h with
  | refl => exact .nil _
  | tail _ hst ih => simpa using ih.append (LTS.Run.of_step (hf _ _ hst))

/-- A play of `Strategy.ofLTS L` ending in a Proponent move is a trace of `L`. -/
theorem trace_of_mem_ofLTS {L : LTS E F} {s : List (Move E F)} {o : Move E F}
    (h : s ++ [o] ∈ Strategy.ofLTS L) (ho : o.IsP) : s ++ [o] ∈ L.Traces := by
  obtain ⟨-, u, hu, hp⟩ := Strategy.mem_generate.1 h
  have hO : ∀ p₀ o', s ++ [o] = p₀ ++ [o'] → ¬ o'.IsO := by
    intro p₀ o' he
    obtain ⟨-, h'⟩ := List.append_inj' he rfl
    obtain rfl : o = o' := by simpa using h'
    exact Move.not_isO_of_isP ho
  rcases hu with rfl | ⟨hu, -⟩
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · simpa using hp.length_le
    · exact (hO p₀ o' he ho').elim
  · rcases hp with hp | ⟨p₀, o', he, -, ho'⟩
    · exact LTS.traces_of_prefix hu hp
    · exact (hO p₀ o' he ho').elim

/-! ## Strategies are determined by their Proponent-ending plays -/

/-- **Strategies with the same Proponent-ending plays are equal.** -/
theorem strategy_ext_isP {σ τ : Strategy E F}
    (h : ∀ (w : List (Move E F)) (o : Move E F), o.IsP → (w ++ [o] ∈ σ ↔ w ++ [o] ∈ τ)) :
    σ = τ := by
  have key : ∀ {σ τ : Strategy E F},
      (∀ (w : List (Move E F)) (o : Move E F), o.IsP → w ++ [o] ∈ σ → w ++ [o] ∈ τ) →
      ∀ p, p ∈ σ → p ∈ τ := by
    intro σ τ hP p
    induction p using List.reverseRecOn with
    | nil => exact fun _ => τ.nil_mem
    | append_singleton w o ih =>
      intro hp
      obtain ⟨z, hz⟩ := σ.legal hp
      obtain ⟨x, hx, hxo⟩ := Path.concat_iff.1 hz
      rcases Step.isO_or_isP hxo with hO | hP'
      · exact τ.receptive (ih (σ.of_prefix hp (List.prefix_append w [o]))) hx hxo hO
      · exact hP w o hP' hp
  ext p
  exact ⟨key (fun w o ho => (h w o ho).1) p, key (fun w o ho => (h w o ho).2) p⟩

/-! ## Splitting lists at their last left or right element -/

theorem split_last_right {α β : Type*} {b : β} :
    ∀ {l : List (α ⊕ β)} {u : List β}, l.filterMap Sum.getRight? = u ++ [b] →
      ∃ l₁ l₂, l = l₁ ++ .inr b :: l₂ ∧ l₁.filterMap Sum.getRight? = u ∧
        l₂.filterMap Sum.getRight? = [] := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro u h; simp at h
  | append_singleton l m ih =>
    intro u h
    rcases m with a | b'
    · have h' : l.filterMap Sum.getRight? = u ++ [b] := by
        simpa [List.filterMap_cons] using h
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h'
      exact ⟨l₁, l₂ ++ [.inl a], by simp, h₁, by simpa using h₂⟩
    · have h' : l.filterMap Sum.getRight? ++ [b'] = u ++ [b] := by
        simpa [List.filterMap_cons] using h
      obtain ⟨hu, hb⟩ := List.append_inj' h' rfl
      have hb' : b' = b := by simpa using hb
      subst hb'
      exact ⟨l, [], by simp, hu, rfl⟩

theorem split_last_left {α β : Type*} {a : α} :
    ∀ {l : List (α ⊕ β)} {u : List α}, l.filterMap Sum.getLeft? = u ++ [a] →
      ∃ l₁ l₂, l = l₁ ++ .inl a :: l₂ ∧ l₁.filterMap Sum.getLeft? = u ∧
        l₂.filterMap Sum.getLeft? = [] := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro u h; simp at h
  | append_singleton l m ih =>
    intro u h
    rcases m with a' | b
    · have h' : l.filterMap Sum.getLeft? ++ [a'] = u ++ [a] := by
        simpa [List.filterMap_cons] using h
      obtain ⟨hu, ha⟩ := List.append_inj' h' rfl
      have ha' : a' = a := by simpa using ha
      subst ha'
      exact ⟨l, [], by simp, hu, rfl⟩
    · have h' : l.filterMap Sum.getLeft? = u ++ [a] := by
        simpa [List.filterMap_cons] using h
      obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih h'
      exact ⟨l₁, l₂ ++ [.inr b], by simp, h₁, by simpa using h₂⟩

/-- In a legal play, a lower question is answered before the next upper move. -/
theorem legal_last_lower_ans {a b : List (Move E F)} {m : E.Op} {g : Ev F}
    (hl : Legal (a ++ .inl (.ask m) :: b ++ [.inr g])) (hb : lower b = []) : False := by
  obtain ⟨z, hz⟩ := hl
  have hz' : Path .idle ((a ++ [.inl (.ask m)]) ++ (b ++ [.inr g])) z := by simpa using hz
  obtain ⟨x, hx, hrest⟩ := Path.append_iff.1 hz'
  obtain ⟨y, -, hy⟩ := Path.concat_iff.1 hx
  cases hy with
  | call q _ =>
    cases b with
    | nil => cases hrest with | cons hs _ => cases hs
    | cons m' b' =>
      rcases m' with e | e
      · simp at hb
      · cases hrest with | cons hs _ => cases hs

/-! ## Composition with a closed lower component -/

/-- The lower projection of a legal play ending in an upper answer, if it is a play of the
strategy of `L₁`, is a trace of `L₁`: its last lower event is an answer. -/
theorem lower_trace_of_ans {L₁ : LTS X E} {t₁ : List (Move E F)} {q : F.Op} {r : F.Ar q}
    (hleg : Legal (t₁ ++ [.inr (.ans q r)]))
    (hl₁ : (lower t₁).map (.inr : Ev E → Move X E) ∈ Strategy.ofLTS L₁) :
    (lower t₁).map (.inr : Ev E → Move X E) ∈ L₁.Traces := by
  rcases List.eq_nil_or_concat' (lower t₁) with hlt | ⟨l, ev, hlt⟩
  · rw [hlt]
    exact ⟨_, .nil _⟩
  · obtain ⟨a, b, ht₁, -, hb⟩ := split_last_left (l := t₁) hlt
    rcases ev with m | ⟨m, n⟩
    · have hleg' : Legal (a ++ .inl (.ask m) :: b ++ [.inr (.ans q r)]) := by
        rw [← ht₁]
        exact hleg
      exact (legal_last_lower_ans hleg' hb).elim
    · have hl₁' : l.map (.inr : Ev E → Move X E) ++ [.inr (.ans m n)] ∈ Strategy.ofLTS L₁ := by
        rw [hlt] at hl₁
        simpa using hl₁
      have htr : l.map (.inr : Ev E → Move X E) ++ [.inr (.ans m n)] ∈ L₁.Traces :=
        trace_of_mem_ofLTS hl₁' trivial
      rw [hlt]
      simpa using htr

/-- The last move of a Proponent-ending play over a closed lower interface is an upper
answer. -/
theorem isP_noEv (h₀ : Ev X → False) {o : Move X F} (ho : o.IsP) :
    ∃ q r, o = .inr (.ans q r) := by
  rcases o with (_ | _) | (_ | ⟨q, r⟩)
  · exact (h₀ (.ask ‹_›)).elim
  · exact (h₀ (.ans ‹_› ‹_›)).elim
  · exact absurd ho (by simp [Move.IsP])
  · exact ⟨q, r, rfl⟩

/-- **A Proponent-ending play of a composite with a closed lower component** is the upper
projection of a trace of the upper system whose lower projection is a trace of the lower
system. -/
theorem comp_noEv_isP (h₀ : Ev X → False) {L₁ : LTS X E} {L₂ : LTS E F}
    {w : List (Move X F)} {o : Move X F} (ho : o.IsP)
    (h : w ++ [o] ∈ (Strategy.ofLTS L₁).comp (Strategy.ofLTS L₂)) :
    ∃ t, t ∈ L₂.Traces ∧ (lower t).map .inr ∈ L₁.Traces ∧ w ++ [o] = (upper t).map .inr ∧
      ∃ (q : F.Op) (r : F.Ar q) (t₀ : List (Move E F)), t = t₀ ++ [.inr (.ans q r)] := by
  obtain ⟨t, ht, hl, hp⟩ := (mem_comp_noEv_iff h₀).1 h
  obtain ⟨q, r, ho'⟩ := isP_noEv h₀ ho
  have hu : upper t = (upper w) ++ [Ev.ans q r] := by
    have h1 : (upper t).map .inr = (w ++ [.inr (.ans q r)] : List (Move X F)) := ho' ▸ hp.symm
    have h2 : upper ((upper t).map .inr : List (Move X F)) = upper t := upper_map_inr _
    rw [← h2, h1, upper_append]
    rfl
  obtain ⟨t₁, t₂, htt, -, ht₂⟩ := split_last_right (l := t) hu
  have ht₂' : upper t₂ = [] := ht₂
  have hpre : t₁ ++ [.inr (.ans q r)] <+: t := ⟨t₂, by rw [htt]; simp⟩
  have hmem : t₁ ++ [.inr (.ans q r)] ∈ Strategy.ofLTS L₂ := (Strategy.ofLTS L₂).of_prefix ht hpre
  have htr : t₁ ++ [.inr (.ans q r)] ∈ L₂.Traces :=
    trace_of_mem_ofLTS hmem trivial
  have hlow : lower (t₁ ++ [.inr (.ans q r)] : List (Move E F)) = lower t₁ := by
    simp [lower_append]
  have hlpre : (lower t₁).map (.inr : Ev E → Move X E) <+: (lower t).map .inr := by
    rw [htt, lower_append]
    exact (List.prefix_append _ _).map _
  have hltr : (lower t₁).map (.inr : Ev E → Move X E) ∈ L₁.Traces :=
    lower_trace_of_ans ((Strategy.ofLTS L₂).legal hmem) ((Strategy.ofLTS L₁).of_prefix hl hlpre)
  refine ⟨t₁ ++ [.inr (.ans q r)], htr, hlow ▸ hltr, ?_, q, r, t₁, rfl⟩
  rw [hp, htt, upper_append, upper_append]
  simp [ht₂']

/-- **Conversely**, legal traces with matching projections give plays of the composite. -/
theorem comp_noEv_of_traces (h₀ : Ev X → False) {L₁ : LTS X E} {L₂ : LTS E F}
    {t : List (Move E F)} (ht : t ∈ L₂.Traces) (hlt : Legal t)
    (hl : (lower t).map .inr ∈ L₁.Traces) (hll : Legal ((lower t).map .inr : List (Move X E))) :
    (upper t).map .inr ∈ (Strategy.ofLTS L₁).comp (Strategy.ofLTS L₂) :=
  (mem_comp_noEv_iff h₀).2
    ⟨t, Strategy.mem_ofLTS_of_mem_traces ht hlt, Strategy.mem_ofLTS_of_mem_traces hl hll, rfl⟩

/-! ## Instantiation phases -/

namespace InstSystem

variable {E F : Sig.{0}} {R : Type} (S : InstSystem E F R)

/-- The game position of a state of `S.toLTS`. -/
def pos : S.St → Pos E (F.withInst R)
  | .fresh => .idle
  | .inst _ => .run none
  | .iwait m _ => .wait none m
  | .ready _ => .idle
  | .run q _ => .run (some q)
  | .wait q m _ => .wait (some q) m
  | .dead => .idle
  | .pstart => .idle
  | .pwait => .idle
  | .pfail _ => .idle

/-- The game position of a state of `S.consumerLTS`. -/
def cpos : S.St → Pos (E.withInst R) (F.withInst R)
  | .fresh => .idle
  | .inst _ => .run none
  | .iwait m _ => .wait none (some m)
  | .ready _ => .idle
  | .run q _ => .run (some q)
  | .wait q m _ => .wait (some q) (some m)
  | .dead => .idle
  | .pstart => .run none
  | .pwait => .wait none none
  | .pfail _ => .run none

theorem run_path {x y : S.toLTS.State} {w : List (Move E (F.withInst R))} (h : S.toLTS.Run x w y) :
    Path (pos S x) w (pos S y) := by
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => cases hs <;> exact ih
  | @vis x' y' z' o s hs _ ih =>
    show Path (pos S x') (o :: s) (pos S z')
    refine .cons ?_ ih
    cases hs with
    | askInst => exact Step.ask (E := E) (F := F.withInst R) none
    | icall _ => exact Step.call (E := E) (F := F.withInst R) none _
    | iresume m k n => exact Step.reply (E := E) (F := F.withInst R) none m n
    | iready _ => exact Step.ret (E := E) (F := F.withInst R) none (InstAns.ready : InstAns R)
    | ifail _ => exact Step.ret (E := E) (F := F.withInst R) none (InstAns.fail _ : InstAns R)
    | askEx st q => exact Step.ask (E := E) (F := F.withInst R) (some q)
    | call _ => exact Step.call (E := E) (F := F.withInst R) (some _) _
    | resume q m k n => exact Step.reply (E := E) (F := F.withInst R) (some q) m n
    | ret _ => exact Step.ret (E := E) (F := F.withInst R) (some _) _

/-- **Traces of an instantiable system are legal.** -/
theorem traces_legal {w : List (Move E (F.withInst R))} (h : w ∈ S.toLTS.Traces) : Legal w := by
  obtain ⟨y, hy⟩ := h
  exact ⟨_, run_path S hy⟩

theorem consumer_run_path {x y : S.consumerLTS.State} {w : List (Move (E.withInst R) (F.withInst R))}
    (h : S.consumerLTS.Run x w y) : Path (cpos S x) w (cpos S y) := by
  induction h with
  | nil => exact .nil _
  | tau hs _ ih => cases hs <;> exact ih
  | @vis x' y' z' o s hs _ ih =>
    show Path (cpos S x') (o :: s) (cpos S z')
    refine .cons ?_ ih
    cases hs with
    | askInst => exact Step.ask (E := E.withInst R) (F := F.withInst R) none
    | pcall => exact Step.call (E := E.withInst R) (F := F.withInst R) none none
    | pready =>
      exact Step.reply (E := E.withInst R) (F := F.withInst R) none none (InstAns.ready : InstAns R)
    | pfail r =>
      exact Step.reply (E := E.withInst R) (F := F.withInst R) none none (InstAns.fail r : InstAns R)
    | preport r =>
      exact Step.ret (E := E.withInst R) (F := F.withInst R) none (InstAns.fail r : InstAns R)
    | icall _ => exact Step.call (E := E.withInst R) (F := F.withInst R) none (some _)
    | iresume m k n => exact Step.reply (E := E.withInst R) (F := F.withInst R) none (some m) n
    | iready _ =>
      exact Step.ret (E := E.withInst R) (F := F.withInst R) none (InstAns.ready : InstAns R)
    | ifail _ =>
      exact Step.ret (E := E.withInst R) (F := F.withInst R) none (InstAns.fail _ : InstAns R)
    | askEx st q => exact Step.ask (E := E.withInst R) (F := F.withInst R) (some q)
    | call _ => exact Step.call (E := E.withInst R) (F := F.withInst R) (some _) (some _)
    | resume q m k n => exact Step.reply (E := E.withInst R) (F := F.withInst R) (some q) (some m) n
    | ret _ => exact Step.ret (E := E.withInst R) (F := F.withInst R) (some _) _

/-- **Traces of the consumer system of a link are legal.** -/
theorem consumer_traces_legal {w : List (Move (E.withInst R) (F.withInst R))}
    (h : w ∈ S.consumerLTS.Traces) : Legal w := by
  obtain ⟨y, hy⟩ := h
  exact ⟨_, consumer_run_path S hy⟩

/-- Runs of the instantiation phase with its import calls `l` (questions and answers). -/
inductive IRun : S.IConf → List (Ev E) → S.IConf → Prop where
  /-- No step. -/
  | refl (c : S.IConf) : IRun c [] c
  /-- A silent step. -/
  | step {c c₁ c' : S.IConf} {l : List (Ev E)} : S.istep c c₁ → IRun c₁ l c' → IRun c l c'
  /-- An import call answered `n`. -/
  | call {c c' : S.IConf} {m : E.Op} {k : E.Ar m → S.IConf} {n : E.Ar m} {l : List (Ev E)} :
      S.icall c m k → IRun (k n) l c' → IRun c (.ask m :: .ans m n :: l) c'

/-- The lower moves of the consumer system: lower events lifted to instantiable imports. -/
def liftL (ev : Ev E) : Move (E.withInst R) (F.withInst R) := .inl (Silmaril.Wasm.Game.liftEv ev)

theorem dead_run {L : LTS E F} {x : L.State} (hd : ∀ l y, ¬ L.step x l y) {w : List (Move E F)} {z : L.State}
    (h : L.Run x w z) : w = [] ∧ z = x := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | tau hs _ => exact (hd _ _ hs).elim
  | vis hs _ => exact (hd _ _ hs).elim

theorem silent_inst {c : S.IConf} {y : S.St} (h : S.toLTS.Run (.inst c) [] y) :
    ∃ c', y = .inst c' ∧ Relation.ReflTransGen S.istep c c' :=
  silent_run_map (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St)) S.istep
    (fun _ _ h => by cases h with | itau hc => exact ⟨_, hc, rfl⟩) h

theorem rtg_run {c c' : S.IConf} (h : Relation.ReflTransGen S.istep c c') :
    S.toLTS.Run (.inst c) [] (.inst c') :=
  run_of_rtg (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St))
    (fun _ _ h => InstSystem.Step.itau h) h

/-! ### Instantiation without import calls -/

theorem toLTS_inst_run {c : S.IConf} {a : InstAns R} {w : List (Move E (F.withInst R))}
    {z : S.St} (h : S.toLTS.Run (.inst c) (ansInst a :: w) z) :
    ∃ c', Relation.ReflTransGen S.istep c c' ∧
      ((a = .ready ∧ ∃ st, S.iready c' st ∧ S.toLTS.Run (.ready st) w z) ∨
        ∃ r, a = .fail r ∧ S.ifail c' r ∧ w = []) := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  obtain ⟨c', rfl, hc'⟩ := silent_inst S h₁
  refine ⟨c', hc', ?_⟩
  cases a with
  | ready => cases h₂ with | iready hr => exact .inl ⟨rfl, _, hr, h₃⟩
  | fail r =>
    cases h₂ with
    | ifail hr =>
      exact .inr ⟨r, rfl, hr, (dead_run (L := S.toLTS) (fun _ _ h => by cases h) h₃).1⟩

/-- **Ready traces**: after a successful instantiation, the export phase from the state
instantiation left. -/
theorem toLTS_ready_iff {w : List (Move E (F.withInst R))} :
    [askInst, ansInst .ready] ++ w ∈ S.toLTS.Traces ↔
      ∃ c st z, Relation.ReflTransGen S.istep S.istart c ∧ S.iready c st ∧
        S.toLTS.Run (.ready st) w z := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hz
    cases silent_run_stuck (L := S.toLTS) (fun _ h => by cases h) h₁
    cases h₂
    obtain ⟨c, hc, h | ⟨r, hr, -⟩⟩ := toLTS_inst_run S h₃
    · obtain ⟨-, st, hst, hrun⟩ := h
      exact ⟨c, st, z, hc, hst, hrun⟩
    · cases hr
  · rintro ⟨c, st, z, hc, hst, hrun⟩
    exact ⟨z, .vis InstSystem.Step.askInst
      ((rtg_run S hc).append
        (.vis (InstSystem.Step.iready hst) hrun))⟩

/-- **Failing traces**: a failed instantiation is the end of the play. -/
theorem toLTS_fail_iff {r : R} {w : List (Move E (F.withInst R))} :
    [askInst, ansInst (.fail r)] ++ w ∈ S.toLTS.Traces ↔
      (∃ c, Relation.ReflTransGen S.istep S.istart c ∧ S.ifail c r) ∧ w = [] := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hz
    cases silent_run_stuck (L := S.toLTS) (fun _ h => by cases h) h₁
    cases h₂
    obtain ⟨c, hc, ⟨h, -⟩ | ⟨r', hr, hf, hw⟩⟩ := toLTS_inst_run S h₃
    · cases h
    · cases hr
      exact ⟨⟨c, hc, hf⟩, hw⟩
  · rintro ⟨⟨c, hc, hf⟩, rfl⟩
    exact ⟨_, .vis InstSystem.Step.askInst
      ((rtg_run S hc).append
        (.vis (InstSystem.Step.ifail hf) (.nil _)))⟩

/-- **The traces of a system whose instantiation makes no import call** start with the
instantiation question and its answer. -/
theorem toLTS_trace_cases (hcl : ∀ c m k, ¬ S.icall c m k) {w : List (Move E (F.withInst R))}
    (h : w ∈ S.toLTS.Traces) :
    w = [] ∨ w = [askInst] ∨ ∃ a w', w = [askInst, ansInst a] ++ w' := by
  obtain ⟨z, hz⟩ := h
  cases w with
  | nil => exact .inl rfl
  | cons o w₁ =>
    obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv hz
    cases silent_run_stuck (L := S.toLTS) (fun _ h => by cases h) h₁
    cases h₂
    cases w₁ with
    | nil => exact .inr (.inl rfl)
    | cons o' w₂ =>
      obtain ⟨y₁, y₂, g₁, g₂, -⟩ := LTS.Run.cons_inv h₃
      obtain ⟨c', rfl, -⟩ := silent_inst S g₁
      cases g₂ with
      | icall hc => exact (hcl _ _ _ hc).elim
      | iready _ => exact .inr (.inr ⟨.ready, w₂, rfl⟩)
      | ifail _ => exact .inr (.inr ⟨.fail _, w₂, rfl⟩)

/-! ### The consumer system of a link -/

theorem irun_of_rtg {c c' : S.IConf} (h : Relation.ReflTransGen S.istep c c') :
    IRun S c [] c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head hs _ ih => exact .step hs ih

/-- An instantiation run of the consumer system along its import calls. -/
theorem consumer_irun_run {c c' : S.IConf} {l : List (Ev E)} (h : IRun S c l c') :
    S.consumerLTS.Run (.inst c) (l.map liftL) (.inst c') := by
  induction h with
  | refl => exact .nil _
  | step hs _ ih => exact .tau (InstSystem.LinkStep.itau hs) ih
  | call hc _ ih =>
    exact .vis (InstSystem.LinkStep.icall hc) (.vis (InstSystem.LinkStep.iresume _ _ _) ih)

/-- What a consumer run from the instantiation configuration `c` along `w` (with an upper
move) consists of: an instantiation run along import calls, then the answer to the
instantiation question. -/
def ISplit (c : S.IConf) (w : List (Move (E.withInst R) (F.withInst R))) (z : S.St) : Prop :=
  ∃ (l : List (Ev E)) (a : InstAns R) (w' : List (Move (E.withInst R) (F.withInst R)))
    (c' : S.IConf), w = l.map liftL ++ .inr (.ans (m := none) a) :: w' ∧ IRun S c l c' ∧
    ((a = .ready ∧ ∃ st, S.iready c' st ∧ S.consumerLTS.Run (.ready st) w' z) ∨
      ∃ r, a = .fail r ∧ S.ifail c' r ∧ w' = [])

theorem ISplit.step {c c₁ : S.IConf} {w : List (Move (E.withInst R) (F.withInst R))} {z : S.St}
    (hs : S.istep c c₁) (h : ISplit S c₁ w z) : ISplit S c w z := by
  obtain ⟨l, a, w', c', rfl, hl, ha⟩ := h
  exact ⟨l, a, w', c', rfl, .step hs hl, ha⟩

theorem ISplit.call {c : S.IConf} {m : E.Op} {k : E.Ar m → S.IConf} {n : E.Ar m}
    {w : List (Move (E.withInst R) (F.withInst R))} {z : S.St}
    (hc : S.icall c m k) (h : ISplit S (k n) w z) :
    ISplit S c (liftL (.ask m) :: liftL (.ans m n) :: w) z := by
  obtain ⟨l, a, w', c', rfl, hl, ha⟩ := h
  exact ⟨.ask m :: .ans m n :: l, a, w', c', rfl, .call hc hl, ha⟩

/-- What a consumer run from a state of the instantiation phase consists of. -/
def ConsSplit (x : S.St) (w : List (Move (E.withInst R) (F.withInst R))) (z : S.St) : Prop :=
  match x with
  | .inst c => ISplit S c w z
  | .iwait m k => ∃ n w₁, w = liftL (.ans m n) :: w₁ ∧ ISplit S (k n) w₁ z
  | _ => True

theorem consumer_split_aux {x z : S.consumerLTS.State} {w : List (Move (E.withInst R) (F.withInst R))}
    (h : S.consumerLTS.Run x w z) (hu : upper w ≠ []) : ConsSplit S x w z := by
  induction h with
  | nil => exact absurd rfl hu
  | tau hs hr ih =>
    cases hs with
    | itau hc => exact ISplit.step S hc (ih hu)
    | tau _ => trivial
  | vis hs hr ih =>
    cases hs with
    | icall hc =>
      obtain ⟨n, w₁, hw, hsp⟩ := ih (by simpa using hu)
      show ISplit S _ (_ :: _) _
      rw [hw]
      exact ISplit.call S hc hsp
    | iresume m k n => exact ⟨n, _, rfl, ih (by simpa using hu)⟩
    | iready hst => exact ⟨[], .ready, _, _, rfl, .refl _, .inl ⟨rfl, _, hst, hr⟩⟩
    | ifail hf =>
      exact ⟨[], .fail _, _, _, rfl, .refl _,
        .inr ⟨_, rfl, hf, (dead_run (L := S.consumerLTS) (fun _ _ h => by cases h) hr).1⟩⟩
    | _ => trivial

/-- **Consumer runs from the instantiation phase** to its first upper move: an instantiation
run along import calls, then the answer to the instantiation question. -/
theorem consumer_inst_split {c : S.IConf} {w : List (Move (E.withInst R) (F.withInst R))}
    {z : S.St} (h : S.consumerLTS.Run (.inst c) w z) (hu : upper w ≠ []) : ISplit S c w z :=
  consumer_split_aux S h hu

/-- **The consumer's ready traces**, read back: the provider ready, an instantiation run along
import calls, ready, and the export phase. -/
theorem consumer_run_ready {c c' : S.IConf} {l : List (Ev E)} {st : S.State}
    {w : List (Move (E.withInst R) (F.withInst R))} {z : S.St} (hl : IRun S c l c')
    (hst : S.iready c' st) (hw : S.consumerLTS.Run (.ready st) w z) :
    S.consumerLTS.Run (.inst c) (l.map liftL ++ .inr (.ans (m := none) .ready) :: w) z :=
  (consumer_irun_run S hl).append (.vis (InstSystem.LinkStep.iready hst) hw)

/-- **The consumer's failing traces.** -/
theorem consumer_run_fail {c c' : S.IConf} {l : List (Ev E)} {r : R} (hl : IRun S c l c')
    (hf : S.ifail c' r) :
    S.consumerLTS.Run (.inst c) (l.map liftL ++ [.inr (.ans (m := none) (.fail r))]) .dead :=
  (consumer_irun_run S hl).append (.vis (InstSystem.LinkStep.ifail hf) (.nil _))

theorem run_cons_nosilent {L : LTS E F} {x z : L.State} {o : Move E F} {w : List (Move E F)}
    (hx : ∀ y, ¬ L.step x none y) (h : L.Run x (o :: w) z) :
    ∃ y, L.step x (some o) y ∧ L.Run y w z := by
  cases h with
  | tau hs _ => exact (hx _ hs).elim
  | vis hs hr => exact ⟨_, hs, hr⟩

/-- **The first moves of the consumer system**, in a trace ending with an upper answer: the
instantiation question, the provider's instantiation question and its answer, then either
the provider's failure reported, or the consumer's instantiation phase. -/
theorem consumer_trace_start {w : List (Move (E.withInst R) (F.withInst R))} {z : S.St}
    (h : S.consumerLTS.Run .fresh w z) {q : (F.withInst R).Op} {r : (F.withInst R).Ar q}
    {w₀ : List (Move (E.withInst R) (F.withInst R))} (hw : w = w₀ ++ [.inr (.ans q r)]) :
    (∃ r', w = [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (.fail r')),
      .inr (.ans (m := none) (.fail r'))]) ∨
    ∃ w', w = [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) .ready)] ++ w' ∧
      S.consumerLTS.Run (.inst S.istart) w' z := by
  have hlast : w.getLast? = some (.inr (.ans q r)) := by rw [hw]; simp
  match w, h, hlast with
  | [], _, hl => cases hl
  | o₁ :: w₁, h, hl =>
    obtain ⟨y₁, hs₁, hr₁⟩ := run_cons_nosilent (fun _ h => by cases h) h
    cases hs₁ with
    | askInst =>
      match w₁, hr₁, hl with
      | [], _, hl => simp at hl
      | o₂ :: w₂, hr₁, hl =>
        obtain ⟨y₂, hs₂, hr₂⟩ := run_cons_nosilent (fun _ h => by cases h) hr₁
        cases hs₂ with
        | pcall =>
          match w₂, hr₂, hl with
          | [], _, hl => simp at hl
          | o₃ :: w₃, hr₂, hl =>
            obtain ⟨y₃, hs₃, hr₃⟩ := run_cons_nosilent (fun _ h => by cases h) hr₂
            cases hs₃ with
            | pready => exact .inr ⟨w₃, rfl, hr₃⟩
            | pfail r' =>
              match w₃, hr₃, hl with
              | [], _, hl => simp at hl
              | o₄ :: w₄, hr₃, _ =>
                obtain ⟨y₄, hs₄, hr₄⟩ := run_cons_nosilent (fun _ h => by cases h) hr₃
                cases hs₄ with
                | preport =>
                  obtain ⟨rfl, -⟩ := dead_run (L := S.consumerLTS) (fun _ _ h => by cases h) hr₄
                  exact .inl ⟨r', rfl⟩

/-! ### Plays of a link with a closed provider -/

theorem lower_map_liftL' (l : List (Ev E)) :
    lower (l.map (liftL (F := F) (R := R))) = l.map Silmaril.Wasm.Game.liftEv := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [liftL, ih]

theorem upper_map_liftL' (l : List (Ev E)) :
    upper (l.map (liftL (F := F) (R := R))) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [liftL, ih]

section Link

variable {X : Sig.{0}} (h₀ : Ev X → False) {L₁ : LTS X (E.withInst R)}
  (hleg : ∀ w ∈ L₁.Traces, Legal w)
include h₀ hleg

/-- **A link play after the consumer's instantiation phase**: the provider ready, the
consumer's instantiation run along import calls `l` answered by the provider, its answer `a`,
and the rest `Y` of the consumer's play. -/
theorem link_comp_start {l L : List (Ev E)} {U : List (Ev F)} {a : InstAns R}
    {Y : List (Move (E.withInst R) (F.withInst R))} {z : S.St}
    (hrun : S.consumerLTS.Run (.inst S.istart) (l.map liftL ++ .inr (.ans (m := none) a) :: Y) z)
    (hY : lower Y = L.map Silmaril.Wasm.Game.liftEv) (hU : upper Y = U.map Silmaril.Wasm.Game.liftEv)
    (hp : [.inr (.ask none), .inr (.ans (m := none) .ready)] ++
      ((l ++ L).map Silmaril.Wasm.Game.liftEv).map .inr ∈ L₁.Traces) :
    [.inr (.ask none), .inr (.ans (m := none) a)] ++ (U.map Silmaril.Wasm.Game.liftEv).map .inr ∈
      (Strategy.ofLTS L₁).comp (Strategy.ofLTS S.consumerLTS) := by
  have ht : [.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) .ready)] ++
      (l.map liftL ++ .inr (.ans (m := none) a) :: Y) ∈ S.consumerLTS.Traces :=
    ⟨z, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
      (.vis InstSystem.LinkStep.pready hrun))⟩
  have hlow : (lower ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) .ready)] ++
      (l.map liftL ++ .inr (.ans (m := none) a) :: Y) : List (Move (E.withInst R) (F.withInst R)))).map
        (.inr : Ev (E.withInst R) → Move X (E.withInst R)) =
      [.inr (.ask none), .inr (.ans (m := none) .ready)] ++
        ((l ++ L).map Silmaril.Wasm.Game.liftEv).map .inr := by
    simp [lower_append, lower_map_liftL', hY]
  have hup : (upper ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) .ready)] ++
      (l.map liftL ++ .inr (.ans (m := none) a) :: Y) : List (Move (E.withInst R) (F.withInst R)))).map
        (.inr : Ev (F.withInst R) → Move X (F.withInst R)) =
      [.inr (.ask none), .inr (.ans (m := none) a)] ++ (U.map Silmaril.Wasm.Game.liftEv).map .inr := by
    simp [upper_append, upper_map_liftL', hU]
  rw [← hup]
  rw [← hlow] at hp
  exact comp_noEv_of_traces h₀ ht (consumer_traces_legal S ht) hp (hleg _ hp)

/-- **A link play whose provider fails.** -/
theorem link_comp_fail {b : R}
    (hp : [.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] ∈ L₁.Traces) :
    ([.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] : List (Move X (F.withInst R))) ∈
      (Strategy.ofLTS L₁).comp (Strategy.ofLTS S.consumerLTS) := by
  have ht : ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (InstAns.fail b)),
      .inr (.ans (m := none) (InstAns.fail b))] : List (Move (E.withInst R) (F.withInst R))) ∈
      S.consumerLTS.Traces :=
    ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
      (.vis (InstSystem.LinkStep.pfail b) (.vis (InstSystem.LinkStep.preport b) (.nil _))))⟩
  exact comp_noEv_of_traces h₀ ht (consumer_traces_legal S ht) hp (hleg _ hp)

omit hleg in
/-- **Proponent-ending plays of a link with a closed provider**: the provider failed, or the
consumer ran its instantiation phase along import calls answered by the provider, answered
the instantiation question, and went on. -/
theorem link_comp_cases {w : List (Move X (F.withInst R))} {o : Move X (F.withInst R)}
    (ho : o.IsP) (h : w ++ [o] ∈ (Strategy.ofLTS L₁).comp (Strategy.ofLTS S.consumerLTS)) :
    (∃ b, [.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))] ∈ L₁.Traces ∧
      w ++ [o] = [.inr (.ask none), .inr (.ans (m := none) (InstAns.fail b))]) ∨
    ∃ (l : List (Ev E)) (a : InstAns R) (Y : List (Move (E.withInst R) (F.withInst R)))
      (c' : S.IConf), IRun S S.istart l c' ∧
      ((a = .ready ∧ ∃ st z, S.iready c' st ∧ S.consumerLTS.Run (.ready st) Y z) ∨
        ∃ b, a = .fail b ∧ S.ifail c' b ∧ Y = []) ∧
      [.inr (.ask none), .inr (.ans (m := none) .ready)] ++
        (l.map Silmaril.Wasm.Game.liftEv ++ lower Y).map .inr ∈ L₁.Traces ∧
      w ++ [o] = [.inr (.ask none), .inr (.ans (m := none) a)] ++ (upper Y).map .inr := by
  obtain ⟨t, ⟨z, ht⟩, hl, hp, q, r, t₀, rfl⟩ := comp_noEv_isP h₀ ho h
  rcases consumer_trace_start S ht rfl with ⟨b, hb⟩ | ⟨w', hw', hrun⟩
  · left
    refine ⟨b, ?_, ?_⟩
    · rw [hb] at hl
      exact hl
    · rw [hp, hb]
      rfl
  · right
    have hu : upper w' ≠ [] := by
      intro hu
      have h1 : upper (t₀ ++ [.inr (.ans q r)]) = [Ev.ask none] := by
        rw [hw', upper_append, hu]
        rfl
      have h2 := congrArg List.getLast? h1
      simp [upper_append] at h2
    obtain ⟨l, a, Y, c', rfl, hl', ha⟩ := consumer_inst_split S hrun hu
    have hlow : (lower (t₀ ++ [.inr (.ans q r)])).map (.inr : Ev (E.withInst R) → Move X _) =
        [.inr (.ask none), .inr (.ans (m := none) .ready)] ++
          (l.map Silmaril.Wasm.Game.liftEv ++ lower Y).map .inr := by
      rw [hw']
      simp [lower_append, lower_map_liftL']
    have hup : (upper (t₀ ++ [.inr (.ans q r)])).map (.inr : Ev (F.withInst R) → Move X _) =
        [.inr (.ask none), .inr (.ans (m := none) a)] ++ (upper Y).map .inr := by
      rw [hw']
      simp [upper_append, upper_map_liftL']
    refine ⟨l, a, Y, c', hl', ?_, hlow ▸ hl, hp.trans hup⟩
    rcases ha with ⟨rfl, st, hst, hY⟩ | ⟨b, rfl, hf, rfl⟩
    · exact .inl ⟨rfl, st, z, hst, hY⟩
    · exact .inr ⟨b, rfl, hf, rfl⟩

end Link

end InstSystem

end Silmaril.Proofs.Wasm.Game.GamesAux
