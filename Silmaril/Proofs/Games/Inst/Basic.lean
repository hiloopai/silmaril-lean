module

public import Silmaril.Games.Inst.Defs
public import Silmaril.Games.DivComp.Thms

/-!
# Instantiation phases: proofs

* Generic facts about silent runs (`silent_run_stuck`, `silent_run_map`,
  `run_of_rtg`), restated from `Silmaril.Proofs.Games.DivLTS.Sim` (layout rules).
* A play of `Strategy.ofLTS L` ending in a Proponent move is a trace of `L`
  (`trace_of_mem_ofLTS`).
* The instantiation outcomes of `DStrategy.ofInst S`, read off the
  instantiation run of `S`.
* Linking propagates provider failure and divergence, and instantiates the
  provider before the consumer.
-/

public section

namespace Silmaril.Proofs.Games.Inst

open Silmaril.Games Silmaril.Games.Inst

universe u

variable {E F X : Sig.{u}} {R : Type u}

/-! ## Silent runs -/

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

theorem diverges_map_iff {L : LTS E F} {A : Type u} (f : A → L.State) (r : A → A → Prop)
    (hf : ∀ a z, L.step (f a) none z → ∃ b, r a b ∧ z = f b)
    (hf' : ∀ a b, r a b → L.step (f a) none (f b)) {a : A} :
    L.Diverges (f a) ↔ Silmaril.InfiniteTrace r a := by
  constructor
  · intro h
    refine Silmaril.InfiniteTrace.of_map f (fun _ => True) ?_ trivial h
    intro a b _ hab
    obtain ⟨c, hc, rfl⟩ := hf a b hab
    exact ⟨c, hc, trivial, rfl⟩
  · exact Silmaril.InfiniteTrace.map f hf'

/-! ## Plays ending with a Proponent move -/

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

/-! ## Instantiation outcomes of `ofInst` -/

namespace OfInst

variable {S : InstSystem E F R}

theorem run_fresh_ask {y : S.St} (h : S.toLTS.Run .fresh [askInst] y) :
    ∃ c, y = .inst c ∧ Relation.ReflTransGen S.istep S.istart c := by
  obtain ⟨x₁, x₂, h₁, h₂, h₃⟩ := LTS.Run.cons_inv h
  cases silent_run_stuck (L := S.toLTS) (fun _ h => by cases h) h₁
  cases h₂
  exact silent_run_map (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St)) S.istep
    (fun _ _ h => by cases h with | itau hc => exact ⟨_, hc, rfl⟩) h₃

theorem silent_inst {c : S.IConf} {y : S.St} (h : S.toLTS.Run (.inst c) [] y) :
    ∃ c', y = .inst c' ∧ Relation.ReflTransGen S.istep c c' :=
  silent_run_map (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St)) S.istep
    (fun _ _ h => by cases h with | itau hc => exact ⟨_, hc, rfl⟩) h

theorem rtg_run {c c' : S.IConf} (h : Relation.ReflTransGen S.istep c c') :
    S.toLTS.Run (.inst c) [] (.inst c') :=
  run_of_rtg (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St))
    (fun _ _ h => InstSystem.Step.itau h) h

theorem traces_inst_iff {a : InstAns R} :
    [askInst, ansInst a] ∈ S.toLTS.Traces ↔ ∃ c, Relation.ReflTransGen S.istep S.istart c ∧
      ((a = .ready ∧ ∃ st, S.iready c st) ∨ ∃ r, a = .fail r ∧ S.ifail c r) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hr⟩ := LTS.Run.of_append (s := [askInst]) (t := [ansInst a]) hy
    obtain ⟨c, rfl, hc⟩ := run_fresh_ask hx
    obtain ⟨x₁, x₂, h₁, h₂, -⟩ := LTS.Run.cons_inv hr
    obtain ⟨c', rfl, hc'⟩ := silent_inst h₁
    refine ⟨c', hc.trans hc', ?_⟩
    cases a with
    | ready => cases h₂ with | iready h => exact .inl ⟨rfl, _, h⟩
    | fail r => cases h₂ with | ifail h => exact .inr ⟨r, rfl, h⟩
  · rintro ⟨c, hc, ⟨rfl, st, h⟩ | ⟨r, rfl, h⟩⟩
    · exact ⟨_, .vis InstSystem.Step.askInst
        (by simpa using (rtg_run hc).append (LTS.Run.of_step (L := S.toLTS)
          (InstSystem.Step.iready h)))⟩
    · exact ⟨_, .vis InstSystem.Step.askInst
        (by simpa using (rtg_run hc).append (LTS.Run.of_step (L := S.toLTS)
          (InstSystem.Step.ifail h)))⟩

theorem legal_inst (a : InstAns R) : Legal ([askInst, ansInst a] : List (Move E (F.withInst R))) :=
  ⟨_, .cons (Step.ask (E := E) (F := F.withInst R) none)
    (.cons (Step.ret (E := E) (F := F.withInst R) none a) (.nil _))⟩

theorem mem_inst_iff {a : InstAns R} :
    [askInst, ansInst a] ∈ (DStrategy.ofInst S).toStrategy ↔
      [askInst, ansInst a] ∈ S.toLTS.Traces := by
  constructor
  · intro h
    exact trace_of_mem_ofLTS (s := [askInst]) (o := ansInst a) h trivial
  · intro h
    exact Strategy.mem_ofLTS_of_mem_traces h (legal_inst a)

theorem instDiverges_iff :
    (DStrategy.ofInst S).InstDiverges ↔ Silmaril.InfiniteTrace S.istep S.istart := by
  have hd : ∀ c, S.toLTS.Diverges (.inst c) ↔ Silmaril.InfiniteTrace S.istep c := fun c =>
    diverges_map_iff (L := S.toLTS) (fun c => (InstSystem.St.inst c : S.St)) S.istep
      (fun _ _ h => by cases h with | itau hc => exact ⟨_, hc, rfl⟩)
      (fun _ _ h => InstSystem.Step.itau h)
  constructor
  · rintro ⟨⟨y, hy, hdy⟩, -⟩
    obtain ⟨c, rfl, hc⟩ := run_fresh_ask hy
    exact Silmaril.InfiniteTrace.of_steps hc ((hd c).1 hdy)
  · intro h
    exact ⟨⟨_, LTS.Run.of_step (L := S.toLTS) InstSystem.Step.askInst, (hd _).2 h⟩,
      none, Path.single (Step.ask (E := E) (F := F.withInst R) none)⟩

end OfInst

/-! ## Linking -/

namespace Link

variable {δ : DStrategy X (E.withInst R)} {S : InstSystem E F R}

theorem link_instFails {r : R} (h : δ.InstFails r) : (δ.link S).InstFails r := by
  have ht : ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) (.fail r)),
      .inr (.ans (m := none) (.fail r))] : List (Move (E.withInst R) (F.withInst R))) ∈
      (DStrategy.ofLTS S.consumerLTS).toStrategy :=
    Strategy.mem_ofLTS_of_mem_traces
      ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
        (.vis (InstSystem.LinkStep.pfail r) (.vis (InstSystem.LinkStep.preport r) (.nil _))))⟩
      ⟨_, .cons (Step.ask (F := F.withInst R) none)
        (.cons (Step.call (E := E.withInst R) (F := F.withInst R) none none)
        (.cons (Step.reply (E := E.withInst R) (F := F.withInst R) none none (.fail r))
        (.cons (Step.ret (E := E.withInst R) (F := F.withInst R) none (.fail r)) (.nil _))))⟩
  exact ⟨_, h, _, ht, .right _ (.sync _ (.sync _ (.right _ .nil)))⟩

theorem link_instDiverges (h : δ.InstDiverges) : (δ.link S).InstDiverges := by
  have ht : ([.inr (.ask none), .inl (.ask none)] : List (Move (E.withInst R) (F.withInst R))) ∈
      (DStrategy.ofLTS S.consumerLTS).toStrategy :=
    Strategy.mem_ofLTS_of_mem_traces
      ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall (.nil _))⟩
      ⟨_, .cons (Step.ask (F := F.withInst R) none)
        (.cons (Step.call (E := E.withInst R) (F := F.withInst R) none none) (.nil _))⟩
  exact DStrategy.mem_div_comp_of_left h ht (.right _ (.sync _ .nil))

theorem link_instReady (h : δ.InstReady) {c : S.IConf} {st : S.State}
    (hc : Relation.ReflTransGen S.istep S.istart c) (hr : S.iready c st) : (δ.link S).InstReady := by
  have hrun : S.consumerLTS.Run (.inst S.istart) [] (.inst c) :=
    run_of_rtg (L := S.consumerLTS) (fun c => (InstSystem.St.inst c : S.St))
      (fun _ _ h => InstSystem.LinkStep.itau h) hc
  have ht : ([.inr (.ask none), .inl (.ask none), .inl (.ans (m := none) .ready),
      .inr (.ans (m := none) .ready)] : List (Move (E.withInst R) (F.withInst R))) ∈
      (DStrategy.ofLTS S.consumerLTS).toStrategy :=
    Strategy.mem_ofLTS_of_mem_traces
      ⟨_, .vis InstSystem.LinkStep.askInst (.vis InstSystem.LinkStep.pcall
        (.vis InstSystem.LinkStep.pready
          (by simpa using hrun.append (LTS.Run.of_step (L := S.consumerLTS)
            (InstSystem.LinkStep.iready hr)))))⟩
      ⟨_, .cons (Step.ask (F := F.withInst R) none)
        (.cons (Step.call (E := E.withInst R) (F := F.withInst R) none none)
        (.cons (Step.reply (E := E.withInst R) (F := F.withInst R) none none .ready)
        (.cons (Step.ret (E := E.withInst R) (F := F.withInst R) none .ready) (.nil _))))⟩
  exact ⟨_, h, _, ht, .right _ (.sync _ (.sync _ (.right _ .nil)))⟩

end Link

end Silmaril.Proofs.Games.Inst
