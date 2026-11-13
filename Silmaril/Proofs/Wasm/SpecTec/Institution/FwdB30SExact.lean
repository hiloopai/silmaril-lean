module

public import Silmaril.Wasm.SpecTec.Institution.FwdB30S.Defs
public import Silmaril.Wasm.SpecTec.Institution.FwdB30X.Thms

/-!
# Exactness: `CfgRel` at a rigid code is equality

`SpecTec.CfgRel hn (configV hn c) w` says that `w` is the image of a configuration that agrees
with `c` up to `Bwd.ConfigEq`: the same store and frame, and code that agrees up to the
annotations of `CALL_REF`s in active position (`Bwd.AdminEq`). `AdminEq` relates two different
instructions only at a `CALL_REF` or inside a label, handler or frame. So when no instruction of
the code has one of these constructors at the top (`RigidV`), the relation is equality.

* `adminEq_rigid`, `codeEq_rigid`: `AdminEq` and `CodeEq` from a rigid code are equality.
* `cfgRel_exact`: **`CfgRel` from the image of a configuration with rigid code is equality.**
* `exact_of_cfgRel`: an existence statement up to `CfgRel` at a rigid successor is existence at
  its image.
* `rigidV_of_heads`, `rigid_val`, `rigid_trap`: rigidity from the instructions' heads.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.FwdB30S

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Atlas
open Silmaril.Wasm.SpecTec.Sim

variable {H : Type}

/-- `RigidV` of a cons. -/
theorem rigidV_cons {x : Value} {l : List Value} (h : RigidV (x :: l)) :
    RigidV [x] ∧ RigidV l :=
  ⟨fun y hy => h y (by rw [List.mem_singleton.1 hy]; exact List.mem_cons_self),
    fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **`AdminEq` from a rigid instruction is equality.** -/
theorem adminEq_rigid {a b : Admin} (h : Bwd.AdminEq a b) (hr : RigidV [adminToV a]) : b = a := by
  have hr' : ∀ op w, adminToV a = .case op w → op ∉ ctxTags :=
    fun op w e => hr _ (List.mem_singleton_self _) op w e
  cases h with
  | refl => rfl
  | call ha _ =>
    rcases Bwd.isCallRef_cases ha with ⟨y, rfl⟩ | ⟨d, rfl⟩
    · exact ((hr' _ _ rfl) (by simp [ctxTags])).elim
    · exact ((hr' _ _ rfl) (by simp [ctxTags])).elim
  | label _ => exact ((hr' _ _ rfl) (by simp [ctxTags])).elim
  | handler _ => exact ((hr' _ _ rfl) (by simp [ctxTags])).elim
  | frame _ => exact ((hr' _ _ rfl) (by simp [ctxTags])).elim

/-- **`CodeEq` from a rigid code is equality.** -/
theorem codeEq_rigid : ∀ {l l' : List Admin}, Bwd.CodeEq l l' → RigidV (adminsToV l) → l' = l
  | [], _, h, _ => by cases h; rfl
  | a :: l, _, h, hr => by
    cases h with
    | cons hab hrest =>
      rw [adminsToV_eq_map, List.map_cons, ← adminsToV_eq_map] at hr
      obtain ⟨ha, hl⟩ := rigidV_cons hr
      rw [adminEq_rigid hab ha, codeEq_rigid hrest hl]

/-- **`CfgRel` from the image of a configuration with rigid code is equality.** -/
theorem cfgRel_exact {hn : H → String} {c : Config H} {w : Value}
    (hrel : SpecTec.CfgRel hn (configV hn c) w) (hr : RigidV (adminsToV c.code)) :
    w = configV hn c := by
  obtain ⟨c₁, d, ⟨hs, hf, hce⟩, h₁, rfl⟩ := hrel
  rw [Bwd.configV_eq, Bwd.configV_eq] at h₁
  obtain ⟨hz, hl⟩ := Bwd.cfgV_inj h₁
  have hd : d.code = c₁.code := codeEq_rigid hce (hl ▸ hr)
  rw [Bwd.configV_eq, Bwd.configV_eq, ← hs, ← hf, hd, ← hz, ← hl]

/-- **Existence up to `CfgRel` at a rigid successor is existence at its image.** -/
theorem exact_of_cfgRel {hn : H → String} {s : Store H} {f : Frame} {is' : List Admin}
    {Q : List Value → Prop}
    (h : ∃ js, Q js ∧ SpecTec.CfgRel hn (configV hn ⟨s, f, is'⟩) (cfgV (stateV hn s f) js))
    (hr : RigidV (adminsToV is')) : Q (adminsToV is') := by
  obtain ⟨js, hq, hrel⟩ := h
  have e := cfgRel_exact hrel hr
  rw [Bwd.configV_eq] at e
  exact (Bwd.cfgV_inj e).2 ▸ hq

/-- Rigidity from the heads of the instructions. -/
theorem rigidV_of_heads {l : List Admin} (h : ∀ a ∈ l, Typing.adminHead a ∉ ctxTags) :
    RigidV (adminsToV l) := by
  intro x hx op w hxe
  rw [adminsToV_eq_map, List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [Typing.adminToV_case hxe]
  exact h a ha

/-- A value is rigid. -/
theorem rigid_val (v : Val) : Typing.adminHead v.toAdmin ∉ ctxTags := by
  have hv := FwdB30X.adminHead_toAdmin v
  intro hc
  simp only [FwdB30X.valTags, ctxTags, List.mem_cons, List.mem_nil_iff, or_false] at hv hc
  rcases hc with hc | hc | hc | hc <;> rw [hc] at hv <;> simp at hv

/-- `TRAP` is rigid. -/
theorem rigid_trap : Typing.adminHead .trap ∉ ctxTags := by
  simp [Typing.adminHead, ctxTags]

/-- A list of values is rigid. -/
theorem rigidV_vals (vs : List Val) : RigidV (adminsToV (vals vs)) :=
  rigidV_of_heads fun a ha => by
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 ha
    exact rigid_val v

/-- A reference is rigid. -/
theorem rigid_ref (r : Ref) : Typing.adminHead (.ref r) ∉ ctxTags :=
  rigid_val (.ref r)

/-- One instruction of a literal is rigid. -/
syntax "rigid_one" : tactic
macro_rules
  | `(tactic| rigid_one) => `(tactic| first
    | exact rigid_val _
    | exact rigid_ref _
    | exact rigid_trap
    | exact fun v _ => rigid_val v
    | exact fun r _ => rigid_ref r
    | (simp [Typing.adminHead, Typing.instrHead, ctxTags, store8, load8u]; done))

/-- The heads of a code built from list literals, `vals` and `++` are rigid. -/
syntax "rigid_tac" : tactic
macro_rules
  | `(tactic| rigid_tac) => `(tactic| (
    apply rigidV_of_heads
    simp only [vals, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map,
      List.not_mem_nil, false_implies, implies_true, and_true]
    all_goals repeat' apply And.intro
    all_goals rigid_one))

end Silmaril.Wasm.SpecTec.Institution.FwdB30S
