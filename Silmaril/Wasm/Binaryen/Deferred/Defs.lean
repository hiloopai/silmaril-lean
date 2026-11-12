module

public import Silmaril.Wasm.Binaryen.CoalesceLocalsCompletion
public import Silmaril.Wasm.Binaryen.CoalesceLocalsClosure
public import Silmaril.Wasm.Binaryen.RedundantSetLineSim
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro

@[expose] public section

/-! # Frame-aware simulation through forced local steps: definitions

* `fwRank`: a payload-independent code rank in which `local.tee` weighs 4,
  `local.get` weighs 2 and every other instruction and value weighs 1;
* `Forced`: one forced local step (an in-bounds `local.set`, a `local.get` of a set
  local, a `local.tee` expansion), under value prefixes and suffixes and under labels,
  handlers and frames;
* `Normalizes`: a finite chain of forced steps;
* `DeferredMatched`, `DeferredBaseSim`: a matched step whose left successor may still
  run a forced chain, and the base obligations of a stage;
* `DeferredCfgRel`: the configuration relation of the deferred simulation.

Results are in `Silmaril.Wasm.Binaryen.Deferred.Thms`.
-/

namespace Silmaril.Wasm.Binaryen.Deferred

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Sim Silmaril.Wasm.Validation Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile}

mutual
  /-- `local.tee` pays for its expansion, `local.get` for the value it pushes. -/
  def fwAdminRank : Admin → Nat
    | .plain (.localTee _) => 4
    | .plain (.localGet _) => 2
    | .label _ _ b | .handler _ _ b | .frame _ _ b => 1 + fwRank b
    | _ => 1

  /-- Values and indices have bounded weight regardless of their payloads. -/
  def fwRank : List Admin → Nat
    | [] => 0
    | a :: l => fwAdminRank a + fwRank l
end

@[simp] theorem fwRank_nil : fwRank [] = 0 := rfl
@[simp] theorem fwRank_cons (a : Admin) (l : List Admin) :
    fwRank (a :: l) = fwAdminRank a + fwRank l := rfl

@[simp] theorem fwRank_append (a b : List Admin) : fwRank (a ++ b) = fwRank a + fwRank b := by
  induction a with
  | nil => simp
  | cons x a ih => simp [ih, Nat.add_assoc]

theorem fwAdminRank_pos (a : Admin) : 0 < fwAdminRank a := by
  cases a with
  | plain i => cases i <;> simp [fwAdminRank]
  | _ => simp [fwAdminRank]

@[simp] theorem fwAdminRank_val (v : Val) : fwAdminRank v.toAdmin = 1 := by
  cases v with
  | num n => cases n with | mk t x => cases t <;> rfl
  | _ => rfl

@[simp] theorem fwRank_vals (vs : List Val) : fwRank (vals vs) = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change fwAdminRank v.toAdmin + fwRank (vals vs) = vs.length + 1
    rw [fwAdminRank_val, ih]
    omega

/-- One forced local step, possibly under runtime execution contexts. -/
inductive Forced : Config H → Config H → Prop where
  | set (s : Store H) (f : Frame) (vs : List Val) (w : Val) (x : LocalIdx)
      (rest : List Admin) (hx : x.toNat < f.locals.length) :
      Forced ⟨s, f, vals vs ++ [w.toAdmin, .plain (.localSet x)] ++ rest⟩
        ⟨s, f.setLocal x w, vals vs ++ rest⟩
  | get (s : Store H) (f : Frame) (vs : List Val) (x : LocalIdx) (v : Val)
      (rest : List Admin) (hv : f.local? x = some (some v)) :
      Forced ⟨s, f, vals vs ++ [.plain (.localGet x)] ++ rest⟩
        ⟨s, f, vals vs ++ [v.toAdmin] ++ rest⟩
  | tee (s : Store H) (f : Frame) (vs : List Val) (w : Val) (x : LocalIdx)
      (rest : List Admin) :
      Forced ⟨s, f, vals vs ++ [w.toAdmin, .plain (.localTee x)] ++ rest⟩
        ⟨s, f, vals vs ++ [w.toAdmin, w.toAdmin, .plain (.localSet x)] ++ rest⟩
  | label {s : Store H} {f f' : Frame} {b b' : List Admin}
      (h : Forced ⟨s, f, b⟩ ⟨s, f', b'⟩)
      (vs : List Val) (n : Nat) (cont : List Instr) (rest : List Admin) :
      Forced ⟨s, f, vals vs ++ [.label n cont b] ++ rest⟩
        ⟨s, f', vals vs ++ [.label n cont b'] ++ rest⟩
  | handler {s : Store H} {f f' : Frame} {b b' : List Admin}
      (h : Forced ⟨s, f, b⟩ ⟨s, f', b'⟩)
      (vs : List Val) (n : Nat) (cs : List Catch) (rest : List Admin) :
      Forced ⟨s, f, vals vs ++ [.handler n cs b] ++ rest⟩
        ⟨s, f', vals vs ++ [.handler n cs b'] ++ rest⟩
  | frame {s : Store H} {fi fi' : Frame} {b b' : List Admin}
      (h : Forced ⟨s, fi, b⟩ ⟨s, fi', b'⟩)
      (f : Frame) (vs : List Val) (n : Nat) (rest : List Admin) :
      Forced ⟨s, f, vals vs ++ [.frame n fi b] ++ rest⟩
        ⟨s, f, vals vs ++ [.frame n fi' b'] ++ rest⟩

namespace Forced

/-- A forced step is a step, for every host. -/
theorem step {host : HostSemantics H} {c d : Config H} (h : Forced c d) : Step P host c d := by
  induction h with
  | set s f vs w x rest hx =>
    simpa using Step.append_right (Step.vals_left (.variable (.localSet hx)) vs) rest
  | get s f vs x v rest hv =>
    exact Step.append_right (Step.vals_left (.variable (.localGet hv)) vs) rest
  | tee s f vs w x rest =>
    exact Step.append_right (Step.vals_left (.variable .localTee) vs) rest
  | label _ vs n cont rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtLabel ih) vs) rest
  | handler _ vs n cs rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtHandler ih) vs) rest
  | frame _ f vs n rest ih =>
    exact Step.append_right (Step.vals_left (.ctxtFrame ih) vs) rest

theorem store {c d : Config H} (h : Forced c d) : d.store = c.store := by
  cases h <;> rfl

end Forced

/-- A finite chain of forced steps. -/
inductive Normalizes : Config H → Config H → Prop where
  | refl (c : Config H) : Normalizes c c
  | cons {c d e : Config H} : Forced c d → Normalizes d e → Normalizes c e

namespace Normalizes

theorem single {c d : Config H} (h : Forced c d) : Normalizes c d := .cons h (.refl d)

theorem trans {c d e : Config H} (h₁ : Normalizes c d) (h₂ : Normalizes d e) :
    Normalizes c e := by
  induction h₁ with
  | refl => exact h₂
  | cons hf _ ih => exact .cons hf (ih h₂)

theorem store {c d : Config H} (h : Normalizes c d) : d.store = c.store := by
  induction h with
  | refl => rfl
  | cons hf _ ih => exact ih.trans hf.store

/-- Chains lift along any map that lifts single forced steps. -/
theorem map (g : Config H → Config H) (hg : ∀ {a b : Config H}, Forced a b → Forced (g a) (g b))
    {c d : Config H} (h : Normalizes c d) : Normalizes (g c) (g d) := by
  induction h with
  | refl => exact .refl _
  | cons hf _ ih => exact .cons (hg hf) ih

end Normalizes

/-- A matched step whose actual left successor may still run a forced chain. -/
def DeferredMatched (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c' d : Config H) (m : Nat) : Prop :=
  ∃ c₁ d', Normalizes c' c₁ ∧
    (Relation.TransGen (Step P closedHost) d d' ∨ (d' = d ∧ fwRank c'.code < m)) ∧
    CfgRel F (AdminsRel BI (WithCuts B)) c₁ d'

variable {F : FuncInst H → FuncInst H → Prop}
  {BI : List Instr → List Instr → Prop} {B : List Admin → List Admin → Prop}

/-- Base laws that permit a chain of forced steps before synchronising frames. -/
structure DeferredBaseSim (P : Profile) (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop) : Prop where
  facts : BaseFacts P closedHost F BI B fwRank
  step : ∀ {s t s' : Store H} {f f' : Frame} {vs : List Val}
    {x y rest rest' es' : List Admin},
    StoreRel F s t → B x y → AdminsRel BI (WithCuts B) rest rest' →
    Step P closedHost ⟨s, f, vals vs ++ x ++ rest⟩ ⟨s', f', es'⟩ →
    DeferredMatched P F BI B ⟨s', f', es'⟩ ⟨t, f, vals vs ++ y ++ rest'⟩
      (fwRank (vals vs ++ x ++ rest))

/-- The left side may still run a forced chain before equal-frame synchronisation. -/
def DeferredCfgRel (F : FuncInst H → FuncInst H → Prop)
    (BI : List Instr → List Instr → Prop) (B : List Admin → List Admin → Prop)
    (c d : Config H) : Prop :=
  ∃ c₁, Normalizes c c₁ ∧ CfgRel F (AdminsRel BI (WithCuts B)) c₁ d

end Silmaril.Wasm.Binaryen.Deferred
