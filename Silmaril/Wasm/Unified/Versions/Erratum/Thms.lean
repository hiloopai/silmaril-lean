module

public import Silmaril.Wasm.Unified.Versions.Erratum.Defs
public import Silmaril.Wasm.Unified.Versions.Run.Thms

/-!
# Spec errata: agreement off the opcode, disagreement at it

* `behavioursR_dropAt_sub`, `behavioursR_dropAt_eq`: dropping the steps at `At` loses
  observations, and loses none from a configuration none of whose runs reaches `At`;
* `err_refines_core`: **the erratum model refines Core 3.0**;
* `err_obs_eq`: **the erratum model and Core 3.0 agree on every call none of whose runs reaches a
  `table.grow` redex**;
* `grow_core_returns`, `grow_err_empty`: **they disagree at the opcode**: at a `table.grow` redex
  whose table exists, Core 3.0 (with the nondeterministic grow policy of `Profile.spec`) returns
  `-1` (`Step/table.grow-fail`), and the erratum has no observation at all.

The agreement is dynamic (no run reaches the opcode), not static (the code does not contain
it): code without `table.grow` can call a store function that uses it.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Unified.Versions

open Silmaril Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Atlas
open Silmaril.Wasm.Unified.Core30
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

theorem behavioursR_dropAt_sub (R : Config H → Config H → Prop) (At : Config H → Prop)
    (c : Config H) : Variant.behavioursR (dropAt R At) c ⊆ Variant.behavioursR R c :=
  Variant.behavioursR_mono (fun _ _ h => h.1) c

/-- Runs that avoid `At` are runs of `dropAt R At`. -/
theorem rtg_dropAt {R : Config H → Config H → Prop} {At : Config H → Prop} {c₀ c : Config H}
    (h : ∀ c', Relation.ReflTransGen R c₀ c' → ¬ At c') (hs : Relation.ReflTransGen R c₀ c) :
    Relation.ReflTransGen (dropAt R At) c₀ c := by
  induction hs with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail ⟨hbc, h _ hab⟩

/-- The points of an infinite run are reachable. -/
theorem trace_reach {R : Config H → Config H → Prop} {c₀ : Config H} {tr : Nat → Config H}
    (h₀ : tr 0 = c₀) (ht : ∀ n, R (tr n) (tr (n + 1))) (n : Nat) :
    Relation.ReflTransGen R c₀ (tr n) := by
  induction n with
  | zero => exact h₀ ▸ .refl
  | succ n ih => exact ih.tail (ht n)

/-- **No run reaches `At`: nothing is lost.** -/
theorem behavioursR_dropAt_eq {R : Config H → Config H → Prop} {At : Config H → Prop}
    {c₀ : Config H} (h : ∀ c', Relation.ReflTransGen R c₀ c' → ¬ At c') :
    Variant.behavioursR (dropAt R At) c₀ = Variant.behavioursR R c₀ := by
  refine Set.Subset.antisymm (behavioursR_dropAt_sub R At c₀) ?_
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, tr, h₀, ht⟩)
  · exact Or.inl ⟨c', r, rtg_dropAt h hs, hc, rfl⟩
  · exact Or.inr ⟨rfl, tr, h₀, fun n => ⟨ht n, h _ (trace_reach h₀ ht n)⟩⟩

/-- **The erratum model refines Core 3.0.** -/
theorem err_refines_core (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) : Refines (errR P host s f okc) (model30 P host s f okc) :=
  modelR_mono (fun _ _ h => h.1) s f okc

/-- **Agreement off the opcode**: on a call none of whose runs reaches a `table.grow` redex. -/
theorem err_obs_eq (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (okc : List Instr → Prop) (c : sig30.Code) (vs : UIn)
    (h : ∀ is ∈ evalC30 c, ∀ c', Relation.ReflTransGen (Step P host) (cfgOf s f is vs) c' →
      ¬ AtGrow c') :
    (errR P host s f okc).obs (c, vs) = (model30 P host s f okc).obs (c, vs) := by
  ext b
  refine and_congr Iff.rfl ⟨fun ⟨is, his, hok, hb⟩ => ⟨is, his, hok, ?_⟩,
    fun ⟨is, his, hok, hb⟩ => ⟨is, his, hok, ?_⟩⟩
  · exact behavioursR_dropAt_sub _ _ _ hb
  · exact (behavioursR_dropAt_eq (h is his)).symm ▸ hb

/-- The `table.grow` redex configuration. -/
def growCfg (s : Store H) (f : Frame) (r : Ref) (a : AddrType) (n : BitVec a.intType.width)
    (x : TableIdx) : Config H :=
  ⟨s, f, [.ref r, .plain (.intConst a.intType n), .plain (.tableGrow x)]⟩

/-- **Core 3.0 at a `table.grow` redex** (table present, nondeterministic grow policy): the
grow may fail and return `-1`. -/
theorem grow_core_returns {P : Profile} (hP : P.grow = .nondet) (host : HostSemantics H)
    {s : Store H} {f : Frame} {x : TableIdx} {ta : Nat} {ti : TableInst}
    (ht : s.table? f x = some (ta, ti)) (r : Ref) (a : AddrType) (n : BitVec a.intType.width) :
    Behaviour.returns [.num ⟨.int a.intType, BitVec.allOnes _⟩] ∈
      Variant.behavioursR (Step P host) (growCfg s f r a n x) := by
  have hfail : P.growMayFail .table ta ti.refs.length n.toNat := by
    simp [Profile.growMayFail, hP]
  have hstep : Step P host (growCfg s f r a n x)
      ⟨s, f, [.plain (.intConst a.intType (BitVec.allOnes _))]⟩ :=
    .table (.growFail ht (Or.inl hfail))
  exact Or.inl ⟨_, .values [.num ⟨.int a.intType, BitVec.allOnes _⟩],
    Relation.ReflTransGen.single hstep, rfl, rfl⟩

/-- The `table.grow` redex configuration is not a result. -/
theorem growCfg_not_result (s : Store H) (f : Frame) (r : Ref) (a : AddrType)
    (n : BitVec a.intType.width) (x : TableIdx) (res : Result) :
    (growCfg s f r a n x).code ≠ res.toAdmin := by
  intro he
  cases res with
  | values vs =>
    have hm : Admin.plain (.tableGrow x) ∈ (growCfg s f r a n x).code := by simp [growCfg]
    rw [he] at hm
    obtain ⟨v, -, hv⟩ := List.mem_map.mp hm
    cases v with
    | num v => obtain ⟨t, b⟩ := v; cases t <;> simp [Val.toAdmin] at hv
    | vec b => simp [Val.toAdmin] at hv
    | ref r => simp [Val.toAdmin] at hv
  | throw a => simp [growCfg, Result.toAdmin] at he
  | trap => simp [growCfg, Result.toAdmin] at he

/-- **The erratum at a `table.grow` redex has no observation.** -/
theorem grow_err_empty (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (r : Ref) (a : AddrType) (n : BitVec a.intType.width) (x : TableIdx) :
    Variant.behavioursR (growErr P host) (growCfg s f r a n x) = ∅ := by
  have hat : AtGrow (growCfg s f r a n x) :=
    ⟨growCfg s f r a n x, .base ⟨r, a, n, x, rfl⟩⟩
  have hstuck : ∀ c', ¬ growErr P host (growCfg s f r a n x) c' := fun _ h => h.2 hat
  refine Set.eq_empty_of_forall_notMem fun b hb => ?_
  rcases hb with ⟨c', res, hs, hc, -⟩ | ⟨-, tr, h₀, ht⟩
  · rcases hs.cases_head with rfl | ⟨c'', h, -⟩
    · exact growCfg_not_result s f r a n x res hc
    · exact hstuck c'' h
  · exact hstuck _ (h₀ ▸ ht 0)

end Silmaril.Wasm.Unified.Versions
