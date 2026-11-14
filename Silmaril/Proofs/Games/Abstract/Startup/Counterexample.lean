module

public import Silmaril.Games.Abstract.Startup.Defs
import Silmaril.Proofs.Games.Abstract.Startup.Basic

/-!
# Startup erasure forgets failure and startup dependence

Over the phased game whose startup moves are environment inputs (`Bool`) and
whose run moves are component outputs (`Bool`):

* `⊤` against the model without startup failures: both startup-independent,
  equal startup-erased observations, different startup parts;
* the component that outputs its startup input against the one that outputs
  its negation: equal startup parts, equal startup-erased observations,
  different models (neither is startup-independent).
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Startup.Counterexample

open Silmaril.Games.Abstract Silmaril.Games.Abstract.Startup Silmaril.Games.Abstract.TraceModel

/-- Startup inputs. -/
abbrev S : Game.{0} := Game.free Bool fun _ => True
/-- Run outputs. -/
abbrev G : Game.{0} := Game.free Bool fun _ => False
/-- The phased game. -/
abbrev P : Game.{0} := Game.phased S G Unit

theorem shape_after {a : List (PMove S G Unit)} (ha : ∀ x ∈ a, x.IsStart) (g : List G.Move) :
    PMove.Shape (after a g) :=
  ⟨a, _, rfl, ha, .inr (.inr ⟨_, rfl, fun x hx => by
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨m, rfl⟩⟩)⟩

theorem legal_iff {p : List (PMove S G Unit)} : p ∈ P.Legal ↔ PMove.Shape p :=
  ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩

theorem legal_after {a : List (PMove S G Unit)} (ha : ∀ x ∈ a, x.IsStart) (g : List G.Move) :
    after a g ∈ P.Legal := legal_iff.2 (shape_after ha g)

/-! ## Failure is forgotten -/

/-- The plays without a startup failure. -/
def noFail : TraceModel P where
  plays := {p | p ∈ P.Legal ∧ ∀ r, PMove.fail r ∉ p}
  closed := {
    nil_mem := ⟨P.nil_legal, by simp⟩
    legal := fun h => h.1
    of_prefix := fun ⟨ht, h⟩ hst => ⟨P.legal_of_prefix ht hst, fun r hr => h r (hst.subset hr)⟩
    receptive := fun {s o} ⟨_, h⟩ hl ho => ⟨hl, fun r hr => by
      rcases List.mem_append.1 hr with hr | hr
      · exact h r hr
      · rw [← List.mem_singleton.1 hr] at ho; exact ho⟩ }

theorem not_fail_mem_after {a : List (PMove S G Unit)} (ha : ∀ x ∈ a, x.IsStart)
    (g : List G.Move) (r : Unit) : PMove.fail r ∉ after a g := by
  intro h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨m, hm⟩ := ha _ h; cases hm
  · rcases List.mem_cons.1 h with h | h
    · cases h
    · obtain ⟨m, -, hm⟩ := List.mem_map.1 h; cases hm

theorem top_indep : StartupIndep (⊤ : TraceModel P) := fun _ _ g ha ha' _ _ =>
  ⟨fun _ => mem_top.2 (legal_after ha' g), fun _ => mem_top.2 (legal_after ha g)⟩

theorem noFail_indep : StartupIndep noFail := fun _ _ g ha ha' _ _ =>
  ⟨fun _ => ⟨legal_after ha' g, not_fail_mem_after ha' g⟩,
    fun _ => ⟨legal_after ha g, not_fail_mem_after ha g⟩⟩

theorem erased_top_eq : erased (⊤ : TraceModel P) = erased noFail := by
  refine le_antisymm (generate_le_iff.2 ?_) (hide_mono _ le_top)
  rintro _ ⟨q, hq, rfl⟩ -
  rcases legal_cases ((⊤ : TraceModel P).closed.legal hq) with hr | ⟨a, g, ha, rfl⟩
  · have : q.filterMap PMove.runOf = [] := filterMap_runOf_eq_nil hr
    change q.filterMap PMove.runOf ∈ erased noFail
    rw [this]
    exact (erased noFail).closed.nil_mem
  · exact filterMap_mem_hide (f := erase) ⟨legal_after ha g, not_fail_mem_after ha g⟩

theorem startPart_ne : startPart (⊤ : TraceModel P) ≠ startPart noFail := by
  intro h
  have hm : [PMove.fail ()] ∈ startPart (⊤ : TraceModel P) :=
    ⟨mem_top.2 (legal_iff.2 ⟨[], _, rfl, by simp, .inr (.inl ⟨(), rfl⟩)⟩), by
      rintro x hx ⟨m, rfl⟩; simp at hx⟩
  rw [h] at hm
  exact hm.1.2 () (by simp)

/-! ## Dependence on startup inputs is forgotten -/

/-- Every run output is `f` of the first startup input. -/
def Compat (f : Bool → Bool) (p : List (PMove S G Unit)) : Prop :=
  ∀ y ∈ p.filterMap PMove.runOf, ∃ (x : Bool) (t : List (PMove S G Unit)),
    p = PMove.start x :: t ∧ y = f x

theorem last_after_ne_start {a : List (PMove S G Unit)} {g : List G.Move} {p : List (PMove S G Unit)}
    {m : Bool} (h : p ++ [PMove.start m] = after a g) : False := by
  unfold after at h
  rcases List.eq_nil_or_concat g with rfl | ⟨g', o, rfl⟩
  · simp only [List.map_nil] at h
    simpa using (List.append_inj' h rfl).2
  · rw [List.concat_eq_append, List.map_append, List.map_singleton, ← List.cons_append,
      ← List.append_assoc] at h
    simpa using (List.append_inj' h rfl).2

/-- The component that outputs `f` of its first startup input. -/
def outF (f : Bool → Bool) : TraceModel P where
  plays := {p | p ∈ P.Legal ∧ Compat f p}
  closed := {
    nil_mem := ⟨P.nil_legal, by simp [Compat]⟩
    legal := fun h => h.1
    of_prefix := fun {s t} ⟨ht, h⟩ hst => ⟨P.legal_of_prefix ht hst, fun y hy => by
      obtain ⟨x, u, rfl, hx⟩ := h y ((hst.filterMap _).subset hy)
      rcases s with _ | ⟨z, s⟩
      · simp at hy
      · obtain ⟨rfl, -⟩ := List.cons_prefix_cons.1 hst
        exact ⟨x, s, rfl, hx⟩⟩
    receptive := fun {s o} ⟨hs, h⟩ hl ho => ⟨hl, by
      cases o with
      | start m =>
        rcases legal_cases hl with hr | ⟨a, g, -, he⟩
        · intro y hy
          rw [filterMap_runOf_eq_nil hr] at hy
          simp at hy
        · exact (last_after_ne_start he).elim
      | run m => exact ho.elim
      | ready => exact ho.elim
      | fail r => exact ho.elim⟩ }

/-- Swap the first startup input. -/
def swapFirst : List (PMove S G Unit) → List (PMove S G Unit)
  | PMove.start x :: t => PMove.start (!x) :: t
  | p => p

theorem filterMap_swapFirst (p : List (PMove S G Unit)) :
    (swapFirst p).filterMap PMove.runOf = p.filterMap PMove.runOf := by
  rcases p with _ | ⟨_ | _ | _ | _, t⟩ <;> simp [swapFirst, PMove.runOf, List.filterMap_cons]

theorem shape_swapFirst {p : List (PMove S G Unit)} (h : PMove.Shape p) :
    PMove.Shape (swapFirst p) := by
  obtain ⟨a, b, rfl, ha, hb⟩ := h
  rcases a with _ | ⟨x, a⟩
  · rcases hb with rfl | ⟨r, rfl⟩ | ⟨c, rfl, hc⟩
    · exact ⟨[], [], rfl, by simp, .inl rfl⟩
    · exact ⟨[], _, rfl, by simp, .inr (.inl ⟨r, rfl⟩)⟩
    · exact ⟨[], _, rfl, by simp, .inr (.inr ⟨c, rfl, hc⟩)⟩
  · obtain ⟨m, rfl⟩ := ha x (by simp)
    exact ⟨PMove.start (!m) :: a, b, rfl, fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨_, rfl⟩
      · exact ha y (by simp [hy]), hb⟩

theorem swapFirst_mem {f g : Bool → Bool} (hfg : ∀ x, f x = g (!x)) {p : List (PMove S G Unit)}
    (hp : p ∈ outF f) : swapFirst p ∈ outF g := by
  refine ⟨legal_iff.2 (shape_swapFirst hp.1.1), fun y hy => ?_⟩
  rw [filterMap_swapFirst] at hy
  obtain ⟨x, t, rfl, rfl⟩ := hp.2 y hy
  exact ⟨!x, t, rfl, hfg x⟩

theorem image_subset {f g : Bool → Bool} (hfg : ∀ x, f x = g (!x)) :
    (List.filterMap erase.map) '' (SetLike.coe (outF f)) ⊆
      (List.filterMap erase.map) '' (SetLike.coe (outF g)) := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨swapFirst p, swapFirst_mem hfg hp, filterMap_swapFirst p⟩

theorem erased_outF_eq : erased (outF id) = erased (outF not) := by
  unfold erased hide
  congr 1
  exact Set.Subset.antisymm (image_subset (by simp)) (image_subset (by simp))

theorem startPart_outF (f : Bool → Bool) :
    startPart (outF f) = {p | p ∈ P.Legal ∧ ∀ x ∈ p, ¬ x.IsRun} := by
  ext p
  constructor
  · rintro ⟨⟨hl, -⟩, hr⟩
    exact ⟨hl, hr⟩
  · rintro ⟨hl, hr⟩
    refine ⟨⟨hl, fun y hy => ?_⟩, hr⟩
    rw [filterMap_runOf_eq_nil hr] at hy
    simp at hy

theorem outF_ne : outF id ≠ outF not := by
  intro h
  have hs : ∀ x ∈ [PMove.start (S := S) (G := G) (R := Unit) true], x.IsStart :=
    fun x hx => ⟨true, List.mem_singleton.1 hx⟩
  have hr := filterMap_runOf_ready hs [true]
  have hm : after [PMove.start true] [true] ∈ outF id :=
    ⟨legal_after hs _, fun y hy => ⟨true, _, rfl, by
      rw [hr] at hy; exact List.mem_singleton.1 hy⟩⟩
  rw [h] at hm
  obtain ⟨x, t, he, hy⟩ := hm.2 true (by rw [hr]; exact List.mem_singleton_self _)
  simp only [after, List.cons_append, List.nil_append, List.cons.injEq] at he
  cases he.1
  simp at hy

end Silmaril.Proofs.Games.Abstract.Startup.Counterexample
