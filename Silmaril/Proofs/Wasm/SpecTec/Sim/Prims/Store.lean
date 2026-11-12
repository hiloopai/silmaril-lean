module

public import Silmaril.Wasm.SpecTec.Sim.Prims.Defs
public import Silmaril.Wasm.SpecTec.Sim.State.Thms
public import Silmaril.Wasm.SpecTec.Sim.Control.Thms
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Thms
public import Silmaril.Wasm.SpecTec.Sim.RefsGC.Thms
public import Silmaril.Wasm.SpecTec.Sim.Exn.Thms

/-!
# The concrete `B`: the state projections

The store/frame projections the families assumed (`$funcinst`, `$moduleinst`, `$structinst`,
`$arrayinst`, `$exninst`, `$tagaddr`, `$tag`, `$elem`, `$add_exninst`) are single premise-free
clauses of the script; they are evaluated here on encoded states, for every `B` (none of them
reaches the builtins on the images). `$tag` is also inverted: it denotes something only where
Core's `Store.tag?` does, given that `B` has no entry for it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Prims

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef not_tryClauses_and_undef)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tagInstToValue elemInstToValue moduleInstToValue)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open State (HasClause1 statePat zxPat storeAccBody)

/-! ## Generic: a one-clause definition -/

/-- A call of a single premise-free clause, as an `Applies` fact. -/
theorem applies_of_clause1 {env : Env} {x : IL.Id} {pats : List Arg} {body : Exp}
    {ws : List ArgV} {ρ₀ : VarEnv} {v : Value} (hd : HasClause1 env x pats body)
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (he : EvalExp env ρ₀ body v) :
    Applies env x ws v := by
  obtain ⟨ps, t, q, hf⟩ := hd
  exact ⟨ps, t, _, hf, Or.inl (tryClauses_hit hm premsHold_nil he)⟩

/-- Matching is deterministic. -/
theorem matchArgs_unique {env : Env} {ρ : VarEnv} {pats : List Arg} {ws : List ArgV}
    {ρ₁ ρ₂ : VarEnv} (h₁ : MatchArgs env ρ pats ws ρ₁) (h₂ : MatchArgs env ρ pats ws ρ₂) :
    ρ₁ = ρ₂ := by
  obtain ⟨n₁, h₁⟩ := h₁
  obtain ⟨n₂, h₂⟩ := h₂
  have e₁ := matchArgs_ok_of_le (Nat.le_max_left n₁ n₂) h₁
  have e₂ := matchArgs_ok_of_le (Nat.le_max_right n₁ n₂) h₂
  rw [e₁] at e₂
  exact Except.ok.inj e₂

/-- A clause list that applies: the first clause fires, or definitely fails and the rest apply
(the argument of `Equiv.V1Binary.tryClauses_cons_elim_v1`, which this module does not import). -/
theorem tryClauses_cons_elim {env : Env} {q : List Param} {pats : List Arg} {e : Exp}
    {prems : List Prem} {cs : List Clause} {ws : List ArgV} {v : Value} {n : Nat}
    (h : tryClauses n env (.defD q pats e prems :: cs) ws = .ok v) :
    (∃ ρ₀ ρ₁, MatchArgs env VarEnv.empty pats ws ρ₀ ∧ PremsHold env ρ₀ prems ρ₁ ∧
        EvalExp env ρ₁ e v) ∨ TryClauses env cs ws v := by
  cases n with
  | zero => simp [tryClauses] at h
  | succ m =>
      rw [tryClauses] at h
      cases hA : (do let ρ₀ ← matchArgs m env VarEnv.empty pats ws
                     premsHold m env ρ₀ prems : Res VarEnv) with
      | ok ρ₁ =>
          rw [hA, Res.elimUndef_ok] at h
          obtain ⟨ρ₀, hm, hp⟩ := Res.bind_eq_ok.mp hA
          exact Or.inl ⟨ρ₀, ρ₁, ⟨m, hm⟩, ⟨m, hp⟩, ⟨m, h⟩⟩
      | error err =>
          cases err with
          | undef =>
              rw [hA, Res.elimUndef_undef] at h
              exact Or.inr ⟨m, h⟩
          | outOfFuel =>
              rw [hA, Res.elimUndef_oof] at h
              exact absurd h (by simp)

/-- **Inverting a one-clause definition.** If it applies, its body evaluates, in the scope the
match builds, to the result — or the clause definitely fails and `B` answers. -/
theorem applies_clause1_inv {env : Env} {x : IL.Id} {pats : List Arg} {body : Exp}
    {ws : List ArgV} {ρ₀ : VarEnv} {v : Value} (hd : HasClause1 env x pats body)
    (hm : MatchArgs env VarEnv.empty pats ws ρ₀) (h : Applies env x ws v) :
    EvalExp env ρ₀ body v ∨ env.builtins.call x ws = some v := by
  obtain ⟨ps, t, q, hf⟩ := hd
  obtain ⟨ps', t', cs, hf', hc⟩ := h
  rw [hf] at hf'
  cases hf'
  rcases hc with ⟨n, hn⟩ | ⟨_, hb⟩
  · rcases tryClauses_cons_elim hn with
      ⟨ρ₀', ρ₁, hm', hp, he⟩ | ⟨k, hk⟩
    · obtain rfl := matchArgs_unique hm hm'
      obtain rfl := premsHold_nil_iff.1 hp
      exact Or.inl he
    · cases k <;> simp [tryClauses] at hk
  · exact Or.inr hb

/-! ## The environment facts -/

/-- The projections of the script this file evaluates, each a single premise-free clause. -/
structure ProjDefs (env : Env) : Prop where
  funcinst : HasClause1 env "funcinst" statePat (.dotE (.varE "s") "FUNCS")
  moduleinst : HasClause1 env "moduleinst" statePat (.dotE (.varE "f") "MODULE")
  structinst : HasClause1 env "structinst" statePat (.dotE (.varE "s") "STRUCTS")
  arrayinst : HasClause1 env "arrayinst" statePat (.dotE (.varE "s") "ARRAYS")
  exninst : HasClause1 env "exninst" statePat (.dotE (.varE "s") "EXNS")
  tagaddr : HasClause1 env "tagaddr" statePat (.dotE (.dotE (.varE "f") "MODULE") "TAGS")
  tag : HasClause1 env "tag" zxPat (storeAccBody "TAGS")
  addExn : HasClause1 env "add_exninst"
    [.expA (.varE "z"), .expA (.iterE (.varE "exn") (.mk .list [.mk "exn" (.varE "exn*")]))]
    (.caseE "%;%" (.tupE [.extE (.callE "sof" [.expA (.varE "z")]) (.dotP .rootP "EXNS")
      (.iterE (.varE "exn") (.mk .list [.mk "exn" (.varE "exn*")])),
      .callE "fof" [.expA (.varE "z")]]))

set_option maxRecDepth 100000 in
/-- `baseEnv` has them. -/
theorem projDefs_baseEnv : ProjDefs baseEnv :=
  ⟨⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩,
    ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩, ⟨_, _, _, rfl⟩⟩

/-- So has every `simEnv B`. -/
theorem projDefs_simEnv (B : Builtins) : ProjDefs (simEnv B) :=
  let D := projDefs_baseEnv
  ⟨D.funcinst.withBuiltins B, D.moduleinst.withBuiltins B, D.structinst.withBuiltins B,
    D.arrayinst.withBuiltins B, D.exninst.withBuiltins B, D.tagaddr.withBuiltins B,
    D.tag.withBuiltins B, D.addExn.withBuiltins B⟩

/-! ## The projections on encoded states -/

variable {H : Type} {env : Env} (P : ProjDefs env) (hn : H → String)
include P

/-- The scope `(s; f)` builds. -/
abbrev stScope (S F : Value) : VarEnv := (VarEnv.empty.bindVal "s" S).bindVal "f" F

omit P in
/-- A store field, read through `(s; f)`. -/
theorem applies_storeField {x : IL.Id} {Fl : AtomS} (hd : HasClause1 env x statePat
    (.dotE (.varE "s") Fl)) (s : Store H) (f : Frame) {v : Value}
    (hv : (storeV hn s).field? Fl = some v) : Applies env x [.val (stateV hn s f)] v :=
  applies_of_clause1 hd State.matchArgs_statePat (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, hv⟩)

/-- `$funcinst(s; f) = s.FUNCS`. -/
theorem applies_funcinst (s : Store H) (f : Frame) :
    Applies env "funcinst" [.val (stateV hn s f)] (.list (s.funcs.map (funcInstV hn))) :=
  applies_storeField hn P.funcinst s f rfl

/-- `$structinst(s; f) = s.STRUCTS`. -/
theorem applies_structinst (s : Store H) (f : Frame) :
    Applies env "structinst" [.val (stateV hn s f)] (.list (s.structs.map structInstV)) :=
  applies_storeField hn P.structinst s f rfl

/-- `$arrayinst(s; f) = s.ARRAYS`. -/
theorem applies_arrayinst (s : Store H) (f : Frame) :
    Applies env "arrayinst" [.val (stateV hn s f)] (.list (s.arrays.map arrayInstV)) :=
  applies_storeField hn P.arrayinst s f rfl

/-- `$exninst(s; f) = s.EXNS`. -/
theorem applies_exninst (s : Store H) (f : Frame) :
    Applies env "exninst" [.val (stateV hn s f)] (.list (s.exns.map exnInstV)) :=
  applies_storeField hn P.exninst s f rfl

/-- `$moduleinst(s; f) = f.MODULE`. -/
theorem applies_moduleinst (s : Store H) (f : Frame) :
    Applies env "moduleinst" [.val (stateV hn s f)] (moduleInstToValue CT f.module) :=
  applies_of_clause1 P.moduleinst State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, rfl⟩)

/-- `$tagaddr(s; f) = f.MODULE.TAGS`. -/
theorem applies_tagaddr (s : Store H) (f : Frame) :
    Applies env "tagaddr" [.val (stateV hn s f)]
      (.list (f.module.tags.map fun a => .num (.natN a))) :=
  applies_of_clause1 P.tagaddr State.matchArgs_statePat
    (evalExp_dotE_iff.2 ⟨_, evalExp_dotE_iff.2 ⟨_, evalExp_var rfl, rfl⟩, rfl⟩)

end Silmaril.Wasm.SpecTec.Sim.Prims
