module

public import Silmaril.Wasi.Spec.Defs
public import Silmaril.Wasi.Versions.Stateful.Thms
public import Silmaril.Wasi.Versions.P2.World.Thms
public import Silmaril.Wasi.Versions.P3OverP2.Theory.Thms
public import Silmaril.Wasi.Versions.P3OverP2.Bounds.Thms
public import Silmaril.Wasm.Resource.Protocol.Thms
public import Silmaril.Logic.Inst.Graph.Thms
public import Silmaril.Logic.Institution.Hets.Decomposition

@[expose] public section

/-!
# WASI specifications as Hets structured specifications: results

## WIT `include`

* `nonempty_hom_union_iff`, `nonempty_union_hom_iff`: there is a `WasiInst` signature morphism
  `W ⟶ W ∪ V` iff `V.imports ⊆ W.imports`, and `W ∪ V ⟶ W` iff `V.exports ⊆ W.exports`;
  `not_include_hom`: a pair of worlds with neither.
* `IncInst.toWasi_modelExpansive`: the comorphism `IncInst → WasiInst` is model-expansive.
* `reduct_toOpen_mem_compSpec`: every component of `W`, read with open imports, is a model of
  `compSpec W` (it calls only `W`'s imports).
* `exists_reduct_of_mem_compSpec`, `mem_compSpec_iff`: conversely, every model of `compSpec W`
  is such a reduct. General form `reduct_pull`: a component of the imports `I' ⊇ I` that calls
  only `I` is the reduct along `widen h X` of `pull h τ` (its plays seen through `fwd`).

## Version theories

* `mem_thSpec_iff`, `models_thSpec_prod` (a product of theories is a union),
  `refines_thSpec` (a weaker theory is refined by a stronger one), `refines_agSpec` (on the
  component side, a weaker host theory gives a stronger specification).
* Slices: `refines_translate_thSpec` (a slice translated to more functions is refined by the
  theory at the larger world) and `refines_union_translate` (two slices, each translated, then
  united, are refined by the product theory at the combined world); the instance
  `p2Spec_refines_io_clock` (the 0.2 io and clock slices, translated and united, are refined by
  `p2Spec r`).
* Versions: `models_p2Spec` (WASI 0.2 is the union of its four slices), `p2Spec_loose_strict`
  (the strict 0.2 reading refines the loose one), and the weakenings of the 0.3 corrections as
  refinements: `refines_stdoutTh3w`, `refines_clockTh3s`, `refines_fsReadTh3w`, and
  `p3Spec_corr` (the corrected 0.3 theory without reads is refined by the 0.3 theory of
  `P2OverP3`).
* The development graph `p3Dev`: `p3Dev_typed_orig` (a global theorem link by Subsumption) and
  `p3Dev_corr_orig` (the corrections as a global theorem link).

## The logic graph with the game institutions

* `wasiSpec_allModelExpansive`; `wasi_entails_translatePath_iff` and
  `wasi_refines_translatePath_iff`: heterogeneous borrowing along every path of `wasiGraph`.
-/

namespace Silmaril.Wasi.Spec

open CategoryTheory Silmaril.Games Silmaril.Logic.Institution
open Silmaril.Wasm.Resource (Protocol)
open Silmaril.Wasi.Versions (retG retAsImp accepts_retG)
open Silmaril.Logic.Institution.Hets

/-! ## WIT `include` -/

/-- `W ⟶ W ∪ V` in `WasiInst` iff `V` adds no import. -/
theorem nonempty_hom_union_iff (W V : World) :
    Nonempty (W ⟶ W.union V) ↔ V.imports ⊆ W.imports :=
  ⟨fun ⟨f⟩ => Set.subset_union_right.trans f.down.1,
    fun h => ⟨⟨Set.union_subset subset_rfl h, Set.subset_union_left⟩⟩⟩

/-- `W ∪ V ⟶ W` in `WasiInst` iff `V` adds no export. -/
theorem nonempty_union_hom_iff (W V : World) :
    Nonempty (W.union V ⟶ W) ↔ V.exports ⊆ W.exports :=
  ⟨fun ⟨f⟩ => Set.subset_union_right.trans f.down.2,
    fun h => ⟨⟨Set.subset_union_left, Set.union_subset subset_rfl h⟩⟩⟩

/-- **WIT `include` is not a signature morphism of `WasiInst`**: including a world with an
import and an export into the empty world gives no morphism in either direction. -/
theorem not_include_hom :
    ∃ W V : World, ¬ Nonempty (W ⟶ W.union V) ∧ ¬ Nonempty (W.union V ⟶ W) := by
  refine ⟨⟨∅, ∅⟩, ⟨Set.univ, Set.univ⟩, fun h => ?_, fun h => ?_⟩
  · exact (nonempty_hom_union_iff _ _).1 h (Set.mem_univ (⟨"", ""⟩ : FnName))
  · exact (nonempty_union_hom_iff _ _).1 h (Set.mem_univ (⟨"", ""⟩ : FnName))

/-- The comorphism `IncInst → WasiInst` is model-expansive. -/
theorem IncInst.toWasi_modelExpansive : IncInst.toWasi.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- The import events of a play of a component of `I` name functions of `I`. -/
theorem callsWithin_wtrace {I X : Set FnName} (s : List (Move (nsig I) (nsig X))) :
    CallsWithin I (wtrace s) := by
  intro e he f hf
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 he
  rcases m with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩) <;>
    simp only [wev, callee, Option.mem_def, Option.some.injEq, reduceCtorEq] at hf
  · exact hf ▸ m.1.2
  · exact hf ▸ m.1.2

/-- **Components of `W` are models of `compSpec W`**: read with open imports, a component of
`W` calls only `W`'s imports. -/
theorem reduct_toOpen_mem_compSpec (W : World) (σ : W.Model) :
    (WasiInst.I.map (toOpen W)).mod.obj σ ∈ (compSpec ⟨W⟩).models := by
  rintro _ rfl p hp -
  obtain ⟨-, s, -, hr⟩ := (Game.mem_reduct_iff_rel (G := World.toGame.obj _)
    (G' := World.toGame.obj W) (World.toGame.map (toOpen W)) σ p).1 hp
  have h := World.wtrace_rel (toOpen W) hr
  exact fun e he => callsWithin_wtrace s e (h ▸ he)

/-! ## Every model of `compSpec` is a component -/

section Pull

variable {I I' X : Set FnName} (h : I ⊆ I')

/-- The move relation of `widen` is the map `fwd`. -/
theorem rel_widen_iff (a : Move (nsig I) (nsig X)) (b : Move (nsig I') (nsig X)) :
    Game.Rel (World.toGame.map (widen h X)) a b ↔ b = fwd h a := by
  constructor
  · intro hr
    cases hr <;> rfl
  · rintro rfl
    rcases a with (⟨m⟩ | ⟨m, n⟩) | (⟨q⟩ | ⟨q, n⟩)
    · exact .lask m
    · exact .lans (lo := nsigHom h) (up := nsigHom (subset_rfl : X ⊆ X)) m n
    · exact .uask (lo := nsigHom h) (up := nsigHom (subset_rfl : X ⊆ X)) q
    · exact .uans (lo := nsigHom h) (up := nsigHom (subset_rfl : X ⊆ X)) q n

/-- Plays related by `widen` are images under `fwd`. -/
theorem forall₂_rel_widen_iff (s : List (Move (nsig I) (nsig X)))
    (p : List (Move (nsig I') (nsig X))) :
    List.Forall₂ (Game.Rel (World.toGame.map (widen h X))) s p ↔ p = s.map (fwd h) := by
  induction s generalizing p with
  | nil => exact List.forall₂_nil_left_iff
  | cons a s ih =>
    cases p with
    | nil => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    | cons b p =>
      refine List.forall₂_cons.trans ((and_congr (rel_widen_iff h a b) (ih p)).trans ?_)
      simp only [List.map_cons, List.cons.injEq]

/-- `fwd` preserves Opponent moves. -/
theorem isO_fwd {o : Move (nsig I) (nsig X)} (ho : o.IsO) : (fwd h o).IsO := by
  rcases o with (_ | _) | (_ | _) <;> exact ho

/-- `fwd` preserves steps. -/
theorem step_fwd {x y : Pos (nsig I) (nsig X)} {a : Move (nsig I) (nsig X)} (hs : Step x a y) :
    Step (posFwd h x) (fwd h a) (posFwd h y) := by
  cases hs <;> constructor

/-- `fwd` reflects steps. -/
theorem step_fwd_inv {x : Pos (nsig I) (nsig X)} {a : Move (nsig I) (nsig X)}
    {y' : Pos (nsig I') (nsig X)} (hs : Step (posFwd h x) (fwd h a) y') :
    ∃ y, Step x a y ∧ y' = posFwd h y := by
  rcases a with (⟨m⟩ | ⟨⟨⟨f, hf⟩, args⟩, n⟩) | (⟨q⟩ | ⟨q, n⟩) <;>
    rcases x with _ | q₀ | ⟨q₀, ⟨⟨f₀, hf₀⟩, args₀⟩⟩ <;> cases hs <;>
    exact ⟨_, by constructor, rfl⟩

/-- `fwd` preserves paths. -/
theorem path_fwd {x y : Pos (nsig I) (nsig X)} {s : List (Move (nsig I) (nsig X))}
    (hp : Path x s y) : Path (posFwd h x) (s.map (fwd h)) (posFwd h y) := by
  induction hp with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (step_fwd h hs) ih

/-- `fwd` reflects paths. -/
theorem path_fwd_inv {s : List (Move (nsig I) (nsig X))} :
    ∀ {x : Pos (nsig I) (nsig X)} {y' : Pos (nsig I') (nsig X)},
      Path (posFwd h x) (s.map (fwd h)) y' → ∃ y, Path x s y := by
  induction s with
  | nil => intro x _ _; exact ⟨x, .nil _⟩
  | cons a s ih =>
    intro x y' hp
    cases hp with
    | cons hs hp =>
      obtain ⟨y, hy, rfl⟩ := step_fwd_inv h hs
      obtain ⟨z, hz⟩ := ih hp
      exact ⟨z, .cons hy hz⟩

/-- A play is legal iff its image under `fwd` is. -/
theorem legal_fwd_iff {s : List (Move (nsig I) (nsig X))} : Legal (s.map (fwd h)) ↔ Legal s :=
  ⟨fun ⟨_, hp⟩ => path_fwd_inv h (x := .idle) hp, fun ⟨_, hp⟩ => ⟨_, path_fwd h hp⟩⟩

/-- A move whose import is in `I` is the image of a move with the imports `I`. -/
theorem exists_fwd_eq (a : Move (nsig I') (nsig X)) (ha : ∀ f ∈ callee (wev a), f ∈ I) :
    ∃ b, fwd h b = a :=
  match a, ha with
  | .inl (.ask ⟨⟨f, _⟩, args⟩), ha => ⟨.inl (.ask ⟨⟨f, ha f rfl⟩, args⟩), rfl⟩
  | .inl (.ans ⟨⟨f, _⟩, args⟩ n), ha => ⟨.inl (.ans ⟨⟨f, ha f rfl⟩, args⟩ n), rfl⟩
  | .inr e, _ => ⟨.inr e, rfl⟩

/-- A play that calls only functions of `I` is the image of a play with the imports `I`. -/
theorem exists_map_fwd {s : List (Move (nsig I') (nsig X))} (hs : CallsWithin I (wtrace s)) :
    ∃ t : List (Move (nsig I) (nsig X)), t.map (fwd h) = s := by
  induction s with
  | nil => exact ⟨[], rfl⟩
  | cons a s ih =>
    obtain ⟨t, rfl⟩ := ih fun e he => hs e (List.mem_cons_of_mem _ he)
    obtain ⟨b, rfl⟩ := exists_fwd_eq h a (hs (wev a) (by simp [wtrace]))
    exact ⟨b :: t, rfl⟩

/-- The component of the imports `I` whose plays are those of `τ` seen through `fwd`. -/
def pull (τ : Strategy (nsig I') (nsig X)) : Strategy (nsig I) (nsig X) where
  plays := {s | Legal s ∧ s.map (fwd h) ∈ τ}
  nil_mem := ⟨Legal.nil, τ.nil_mem⟩
  legal hs := hs.1
  of_prefix ht hst := ⟨ht.1.of_prefix hst, τ.of_prefix ht.2 (hst.map _)⟩
  receptive := by
    rintro s x y o ⟨-, hs⟩ hx hxy ho
    refine ⟨⟨y, hx.append (Path.single hxy)⟩, ?_⟩
    rw [List.map_append]
    exact τ.receptive hs (path_fwd h hx) (step_fwd h hxy) (isO_fwd h ho)

/-- **A component with wider imports that calls only `I` is the reduct of a component of
`I`**: `pull`. -/
theorem reduct_pull (τ : Strategy (nsig I') (nsig X))
    (hτ : ∀ s ∈ τ, CallsWithin I (wtrace s)) :
    Game.reduct (World.toGame.map (widen h X)) (pull h τ) = τ := by
  ext p
  refine (Game.mem_reduct_iff_rel (G := World.toGame.obj ⟨I', X⟩) (G' := World.toGame.obj ⟨I, X⟩)
    (World.toGame.map (widen h X)) (pull h τ) p).trans ⟨?_, ?_⟩
  · rintro ⟨-, s, ⟨-, hs⟩, hr⟩
    rwa [(forall₂_rel_widen_iff h s p).1 hr]
  · intro hp
    obtain ⟨t, rfl⟩ := exists_map_fwd h (hτ _ hp)
    exact ⟨τ.legal hp, t, ⟨(legal_fwd_iff h).1 (τ.legal hp), hp⟩,
      (forall₂_rel_widen_iff h t _).2 rfl⟩

end Pull

/-- **Every model of `compSpec W` is a component of `W`**, read with open imports: the converse
of `reduct_toOpen_mem_compSpec`. -/
theorem exists_reduct_of_mem_compSpec (W : World) {τ : (IWorld.openWorld ⟨W⟩).Model}
    (hτ : τ ∈ (compSpec ⟨W⟩).models) :
    ∃ σ : W.Model, (WasiInst.I.map (toOpen W)).mod.obj σ = τ :=
  ⟨pull (Set.subset_univ _) τ, reduct_pull _ τ fun s hs => hτ _ rfl s hs trivial⟩

/-- **The models of `compSpec W` are exactly the components of `W`**, read with open
imports. -/
theorem mem_compSpec_iff (W : World) (τ : (IWorld.openWorld ⟨W⟩).Model) :
    τ ∈ (compSpec ⟨W⟩).models ↔ ∃ σ : W.Model, (WasiInst.I.map (toOpen W)).mod.obj σ = τ :=
  ⟨exists_reduct_of_mem_compSpec W, fun ⟨σ, hσ⟩ => hσ ▸ reduct_toOpen_mem_compSpec W σ⟩

/-! ## Version theories -/

variable {SG SG' : Type}

/-- A closed host satisfies the sentence of `T` iff the returns of its plays satisfy `T`. -/
theorem sat_thSen_iff {I : Set FnName} {T : Protocol SG WEv} (η : (hostWorld I).Model) :
    (WasiInst.I.obj (hostWorld I)).Sat η (thSen I T) ↔
      ∀ s ∈ η, T.Accepts (retAsImp (wtrace s)) :=
  ⟨fun h s hs => (accepts_retG _ _).1 (h s hs trivial),
    fun h s hs _ => (accepts_retG _ _).2 (h s hs)⟩

/-- The sentence of a theory implies that of a weaker one. -/
theorem sat_thSen_mono {I : Set FnName} {T : Protocol SG WEv} {T' : Protocol SG' WEv}
    (h : ∀ t, T.Accepts t → T'.Accepts t) {η : (hostWorld I).Model}
    (hη : (WasiInst.I.obj (hostWorld I)).Sat η (thSen I T)) :
    (WasiInst.I.obj (hostWorld I)).Sat η (thSen I T') :=
  (sat_thSen_iff η).2 fun s hs => h _ ((sat_thSen_iff η).1 hη s hs)

/-- The models of a theory: the closed hosts whose returns satisfy it. -/
theorem mem_thSpec_iff {I : Set FnName} {T : Protocol SG WEv} (η : (hostWorld I).Model) :
    η ∈ (thSpec I T).models ↔ ∀ s ∈ η, T.Accepts (retAsImp (wtrace s)) :=
  ⟨fun h => (sat_thSen_iff η).1 (h _ rfl), fun h _ he => he ▸ (sat_thSen_iff η).2 h⟩

/-- Membership in a union of WASI specifications. -/
theorem mem_union_iff {W : World} (SP SQ : WSpec W) (η : W.Model) :
    η ∈ (StrSpec.union SP SQ).models ↔ η ∈ SP.models ∧ η ∈ SQ.models :=
  Iff.rfl

/-- The models of a product of theories. -/
theorem mem_thSpec_prod_iff {I : Set FnName} {T : Protocol SG WEv} {T' : Protocol SG' WEv}
    (η : (hostWorld I).Model) :
    η ∈ (thSpec I (T.prod T')).models ↔ η ∈ (thSpec I T).models ∧ η ∈ (thSpec I T').models := by
  rw [mem_thSpec_iff, mem_thSpec_iff, mem_thSpec_iff]
  simp only [Protocol.accepts_prod_iff]
  exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
    fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩

/-- **A product of theories is the union of their specifications.** -/
theorem models_thSpec_prod (I : Set FnName) (T : Protocol SG WEv) (T' : Protocol SG' WEv) :
    (thSpec I (T.prod T')).models = (StrSpec.union (thSpec I T) (thSpec I T')).models :=
  Set.ext fun η => (mem_thSpec_prod_iff η).trans (mem_union_iff _ _ η).symm

/-- **A weaker theory is refined by a stronger one.** -/
theorem refines_thSpec {I : Set FnName} {T : Protocol SG WEv} {T' : Protocol SG' WEv}
    (h : ∀ t, T.Accepts t → T'.Accepts t) : (thSpec I T').Refines (thSpec I T) :=
  fun η hη => (mem_thSpec_iff η).2 fun s hs => h _ ((mem_thSpec_iff η).1 hη s hs)

/-- On the component side, a weaker host theory gives a stronger specification. -/
theorem refines_agSpec {SG'' : Type} {W : World} {T : Protocol SG WEv} {T' : Protocol SG' WEv}
    {G : Protocol SG'' WEv} (h : ∀ t, T.Accepts t → T'.Accepts t) :
    (agSpec W T G).Refines (agSpec W T' G) := by
  rintro σ hσ _ rfl s hs hA
  exact hσ _ rfl s hs (h _ hA)

/-- **A slice translated to more functions is refined by the theory at the larger world.** -/
theorem refines_translate_thSpec {I I' : Set FnName} (h : I ⊆ I') (T : Protocol SG WEv) :
    (StrSpec.translate (hostIncl h) (thSpec I T)).Refines (thSpec I' T) := by
  rintro η hη _ rfl
  exact World.ag_reduct (A := fun _ => True) (G := (retG T).Accepts) (hostIncl h) (hη _ rfl)

/-- **Slices combined by translation and union** are refined by the product theory at the
combined world. -/
theorem refines_union_translate {I₁ I₂ I : Set FnName} (h₁ : I₁ ⊆ I) (h₂ : I₂ ⊆ I)
    (T₁ : Protocol SG WEv) (T₂ : Protocol SG' WEv) :
    (StrSpec.union (StrSpec.translate (hostIncl h₁) (thSpec I₁ T₁))
      (StrSpec.translate (hostIncl h₂) (thSpec I₂ T₂))).Refines (thSpec I (T₁.prod T₂)) := by
  intro η hη
  have h := (mem_thSpec_prod_iff η).1 hη
  exact ⟨refines_translate_thSpec h₁ T₁ h.1, refines_translate_thSpec h₂ T₂ h.2⟩

/-- The io functions are 0.2 imports. -/
theorem ioImports_sub_p2 : Versions.P2.ioImports ⊆ Versions.P2.p2Command.imports :=
  Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left)

/-- The clock functions are 0.2 imports. -/
theorem clockImports_sub_p2 : Versions.P2.clockImports ⊆ Versions.P2.p2Command.imports :=
  Set.subset_union_right.trans Set.subset_union_left

/-- **WASI 0.2 refines its io and clock slices**: the 0.2 io theory at the io functions and the
clock theory at the clock functions, each translated to the 0.2 host world and united, are
refined by `p2Spec r` (an instance of `refines_union_translate`). -/
theorem p2Spec_refines_io_clock (r : Versions.P2.Reading) :
    (StrSpec.union
      (StrSpec.translate (hostIncl ioImports_sub_p2)
        (thSpec Versions.P2.ioImports (Versions.P2.ioTh r)))
      (StrSpec.translate (hostIncl clockImports_sub_p2)
        (thSpec Versions.P2.clockImports clockTh))).Refines (p2Spec r) := by
  refine fun η hη => refines_union_translate _ _ _ _ (refines_thSpec (fun t ht => ?_) hη)
  obtain ⟨hio, hrest⟩ := (Protocol.accepts_prod_iff _ _ t).1 ht
  exact (Protocol.accepts_prod_iff _ _ t).2 ⟨hio, ((Protocol.accepts_prod_iff _ _ t).1 hrest).1⟩

/-- **WASI 0.2 is the union of its four slices** (io, clock, cli typing, filesystem typing). -/
theorem models_p2Spec (r : Versions.P2.Reading) :
    (p2Spec r).models = (StrSpec.union (thSpec _ (Versions.P2.ioTh r))
      (StrSpec.union (thSpec _ clockTh) (StrSpec.union (thSpec _ (pointwise Versions.P2.p2Ok))
        (thSpec _ fsTyped)))).models := by
  ext η
  exact (mem_thSpec_prod_iff η).trans (and_congr Iff.rfl
    ((mem_thSpec_prod_iff η).trans (and_congr Iff.rfl (mem_thSpec_prod_iff η))))

/-- The strict reading of WASI 0.2 refines the loose one. -/
theorem p2Spec_loose_strict : (p2Spec .loose).Refines (p2Spec .strict) :=
  refines_thSpec fun _ => Versions.P2.p2_loose_of_strict

/-- The loose 0.3 stdout correction is a weakening: refined by the original. -/
theorem refines_stdoutTh3w (I : Set FnName) :
    (thSpec I Versions.P3OverP2.stdoutTh3w).Refines (thSpec I Versions.P3.stdoutTh3) :=
  refines_thSpec fun _ => Versions.P3OverP2.stdoutTh3w_of

/-- The saturated 0.3 clock correction is a weakening: refined by the original. -/
theorem refines_clockTh3s (I : Set FnName) :
    (thSpec I Versions.P3OverP2.clockTh3s).Refines (thSpec I Versions.P3.clockTh3) :=
  refines_thSpec fun _ => Versions.P3OverP2.clockTh3s_of

/-- The 0.3 read correction is a weakening: refined by the original. -/
theorem refines_fsReadTh3w (I : Set FnName) (F : BitVec 32 → List (BitVec 8)) :
    (thSpec I (Versions.P3OverP2.fsReadTh3w F)).Refines (thSpec I (Versions.P3.fsReadTh3 F)) :=
  refines_thSpec fun _ => Versions.P3OverP2.fsReadTh3w_of F

/-- **The corrected 0.3 theory without reads is refined by the 0.3 theory of `P2OverP3`.** -/
theorem p3Spec_corr :
    (StrSpec.union (thSpec _ Versions.P3.typed3) (StrSpec.union
      (thSpec _ Versions.P3OverP2.clockTh3s) (thSpec _ Versions.P3OverP2.stdoutTh3w))).Refines
      p3Spec := by
  intro η hη
  have h := (mem_thSpec_prod_iff η).1 hη
  have h' := (mem_thSpec_prod_iff η).1 h.2
  exact ⟨h.1, refines_clockTh3s _ h'.1, refines_stdoutTh3w _ h'.2⟩

/-! ## The development graph of the 0.3 theories -/

/-- **Subsumption**: the typing slice, linked into the 0.3 theory, is a global theorem. -/
theorem p3Dev_typed_orig : p3Dev.GlobalThm .typed .orig (𝟙 _) :=
  DevGraph.subsumption p3Dev
    (DevGraph.GlobReach.of_globalDef (G := p3Dev) (M := .typed) (N := .orig) (Set.mem_univ _))

/-- **The corrections as a global theorem link**: every host of the 0.3 theory of `P2OverP3`
is a host of the corrected theory without reads. -/
theorem p3Dev_corr_orig : p3Dev.GlobalThm .corr .orig (𝟙 _) := by
  intro m hm
  have hax := ((p3Dev.mem_models_iff _ _).1 hm).1 _ (Set.mem_singleton _)
  have e : DevGraph.reduct (I := WasiInst.I) (𝟙 p3HW) m = m := DevGraph.reduct_id m
  refine (congrArg (· ∈ p3Dev.models P3Node.corr) e).mpr ((p3Dev.mem_models_iff _ _).2 ?_)
  have hp := fun t (ht : Versions.P2OverP3.p3Th.Accepts t) => (Protocol.accepts_prod_iff _ _ t).1 ht
  have hq := fun t ht => (Protocol.accepts_prod_iff _ _ t).1 (hp t ht).2
  refine ⟨?_, fun K _ hσ => ?_, fun K _ hσ => absurd hσ (Set.notMem_empty _),
    fun K _ hσ => absurd hσ (Set.notMem_empty _)⟩
  · rintro φ (rfl | rfl | rfl)
    · exact sat_thSen_mono (fun t ht => (hp t ht).1) hax
    · exact sat_thSen_mono (fun t ht => Versions.P3OverP2.clockTh3s_of (hq t ht).1) hax
    · exact sat_thSen_mono (fun t ht => Versions.P3OverP2.stdoutTh3w_of (hq t ht).2) hax
  · cases K <;> exact absurd hσ (Set.notMem_empty _)

/-! ## The logic graph with the game institutions -/

/-- The comorphism `WasiInst₁ → GInst` is model-expansive. -/
theorem wasiToGInst_modelExpansive : wasiToGInst.ModelExpansive := fun _ M => ⟨M, rfl⟩

/-- Every listed comorphism of `wasiSpec` is model-expansive. -/
theorem wasiSpec_allModelExpansive : wasiSpec.AllModelExpansive := by
  intro e he
  simp only [wasiSpec, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact wasiToGInst_modelExpansive
  · exact GInstRef.toGInst_modelExpansive
  · exact GInst.toDGInst_modelExpansive

/-- **Borrowing of structured entailment along every path of `wasiGraph`.** -/
theorem wasi_entails_translatePath_iff {a b : wasiGraph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst wasiGraph.indexed (wasiGraph.pt a)).Sign)
    (SP : StrSpec (IndexedCoInst.flat wasiGraph.indexed) (wasiGraph.sigOf a S))
    (φ : ((IndexedCoInst.flat wasiGraph.indexed).obj (wasiGraph.sigOf a S)).Sen) :
    SP.Entails φ ↔ (StructuredPaths.translate wasiGraph p S SP).Entails
      (((IndexedCoInst.flat wasiGraph.indexed).map (StructuredPaths.lift wasiGraph p S)).sen φ) :=
  wasiSpec.entails_translatePath_iff wasiSpec_allModelExpansive p S SP φ

/-- **Borrowing of refinement along every path of `wasiGraph`.** -/
theorem wasi_refines_translatePath_iff {a b : wasiGraph.Idx} (p : Quiver.Path a b)
    (S : (IndexedCoInst.inst wasiGraph.indexed (wasiGraph.pt a)).Sign)
    (SP SQ : StrSpec (IndexedCoInst.flat wasiGraph.indexed) (wasiGraph.sigOf a S)) :
    SP.Refines SQ ↔ (StructuredPaths.translate wasiGraph p S SP).Refines
      (StructuredPaths.translate wasiGraph p S SQ) :=
  wasiSpec.refines_translatePath_iff wasiSpec_allModelExpansive p S SP SQ

end Silmaril.Wasi.Spec
