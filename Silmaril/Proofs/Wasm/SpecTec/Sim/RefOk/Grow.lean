module

public import Silmaril.Wasm.SpecTec.Sim.Prims.Thms
public import Silmaril.Wasm.SpecTec.Sim.Memory.Thms

/-!
# Track refok: `$growtable` and `$growmem` in the concrete `B` (gap 5, `Extra.grow`)

`$growtable(tableinst, n, r) = tableinst'` and `$growmem(meminst, n) = meminst'` each have one
clause, whose first premise `if tableinst = {TYPE (at [i .. j?] rt), REFS r'*}` (resp.
`{TYPE (at [i .. j?] PAGE), BYTES b*}`) mentions `at`, which nothing binds. Under the evaluator
that premise definitely fails, so `callDef` falls back to `B` (gap G3). `Prims.builtins` answers
with the images of Core's `TableInst.grow?`/`MemInst.grow?` (`Prims.growtableCall`,
`Prims.growmemCall`), so `Memory.GrowFuns` holds for it (`growFuns_builtins`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.RefOk

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies TryClausesUndef applies_iff_callDef)
open Silmaril.SpecTec.Equiv.RuntimeBridge (tableInstToValue memInstToValue refToValue
  tableInstToValue_inj memInstToValue_inj refToValue_inj)
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Prims (EvalExpUndef)

variable {H : Type} {prof : Silmaril.Wasm.Numerics.Profile}

/-! ## A record whose first field fails -/

/-- A record whose first field definitely fails definitely fails. -/
theorem evalExpUndef_strHead {env : Env} {ρ : VarEnv} {a : AtomS} {e : Exp} {fs : List ExpField}
    (h : EvalExpUndef env ρ e) : EvalExpUndef env ρ (.strE (.mk a e :: fs)) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n + 2, by simp [evalExp, evalExpFields, h, Bind.bind, Except.bind]⟩

/-! ## The clauses -/

/-- The common shape of the first premise: `if x = {TYPE (C (at, …)), …}`. -/
def growPrem (x : IL.Id) (C : MixopS) (tl : List Exp) (fs : List ExpField) : Prem :=
  .ifPr (.cmpE .eqOp .boolT (.varE x) (.strE (.mk "TYPE" (.caseE C (.tupE (.varE "at" :: tl))) :: fs)))

/-- The two definitions, as the script has them (up to the parts the proofs do not read). -/
structure GrowDefs (env : Env) : Prop where
  growtable : ∃ ps t q body tl fs rest, env.findDef? "growtable" = some (ps, t,
    [.defD q [.expA (.varE "tableinst"), .expA (.varE "n"), .expA (.varE "r")] body
      (growPrem "tableinst" "%%%" tl fs :: rest)])
  growmem : ∃ ps t q body tl fs rest, env.findDef? "growmem" = some (ps, t,
    [.defD q [.expA (.varE "meminst"), .expA (.varE "n")] body
      (growPrem "meminst" "%%PAGE" tl fs :: rest)])

set_option maxRecDepth 100000 in
/-- `simEnv B` has them. -/
theorem growDefs_simEnv (B : Builtins) : GrowDefs (simEnv B) :=
  ⟨⟨_, _, _, _, _, _, _, rfl⟩, ⟨_, _, _, _, _, _, _, rfl⟩⟩

/-- The first premise definitely fails in a scope binding `x` but not `at`. -/
theorem premsUndef_grow {env : Env} {ρ : VarEnv} {x : IL.Id} {C : MixopS} {tl : List Exp}
    {fs : List ExpField} {rest : List Prem} {v : Value} (hx : ρ.findVal? x = some v)
    (hat : ρ.findVal? "at" = none) : PremsUndef env ρ (growPrem x C tl fs :: rest) :=
  Prims.premsUndef_if (Prims.evalExpUndef_cmpR (evalExp_var hx) (evalExpUndef_strHead
    (Prims.evalExpUndef_case (Prims.evalExpUndef_tup (pre := []) evalExps_nil
      (Prims.evalExpUndef_var hat)))))

/-- `$growtable`'s clause definitely fails on every argument triple. -/
theorem growtable_undef {env : Env} (D : GrowDefs env) (T N R : Value) :
    ∃ ps t cs, env.findDef? "growtable" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val T, .val N, .val R] := by
  obtain ⟨ps, t, q, body, tl, fs, rest, hd⟩ := D.growtable
  exact ⟨ps, t, _, hd, IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons (matchArg_expA (matchExp_varE rfl))
        matchArgs_nil)))
    (premsUndef_grow rfl rfl) IntNumeric.tryClausesUndef_nil⟩

/-- `$growmem`'s clause definitely fails on every argument pair. -/
theorem growmem_undef {env : Env} (D : GrowDefs env) (M N : Value) :
    ∃ ps t cs, env.findDef? "growmem" = some (ps, t, cs) ∧
      TryClausesUndef env cs [.val M, .val N] := by
  obtain ⟨ps, t, q, body, tl, fs, rest, hd⟩ := D.growmem
  exact ⟨ps, t, _, hd, IntNumeric.tryClausesUndef_skip_prem
    (matchArgs_cons (matchArg_expA (matchExp_varE rfl)) (matchArgs_cons
      (matchArg_expA (matchExp_varE rfl)) matchArgs_nil))
    (premsUndef_grow rfl rfl) IntNumeric.tryClausesUndef_nil⟩

/-! ## What `B` answers -/

/-- `growtableCall` on images is the image of Core's `grow?`. -/
theorem growtableCall_image (ti : TableInst) (n : Nat) (r : Ref) :
    Prims.growtableCall (tableInstToValue CT ti) (.num (.natN n)) (refToValue r) =
      (ti.grow? n r).map (tableInstToValue CT) := by
  classical
  have hex : ∃ p : TableInst × Nat × Ref, tableInstToValue CT ti = tableInstToValue CT p.1 ∧
      Value.num (.natN n) = .num (.natN p.2.1) ∧ refToValue r = refToValue p.2.2 :=
    ⟨(ti, n, r), rfl, rfl, rfl⟩
  unfold Prims.growtableCall
  split
  · rename_i h
    obtain ⟨h₁, h₂, h₃⟩ := h.choose_spec
    have e₁ : h.choose.1 = ti := (tableInstToValue_inj (C := CT) h₁).symm
    have e₂ : h.choose.2.1 = n := by injection h₂ with h₂; injection h₂ with h₂; exact h₂.symm
    have e₃ : h.choose.2.2 = r := (refToValue_inj h₃).symm
    rw [e₁, e₂, e₃]
  · contradiction

/-- `growmemCall` on images is the image of Core's `grow?`. -/
theorem growmemCall_image (mi : MemInst) (n : Nat) :
    Prims.growmemCall (memInstToValue mi) (.num (.natN n)) = (mi.grow? n).map memInstToValue := by
  classical
  have hex : ∃ p : MemInst × Nat, memInstToValue mi = memInstToValue p.1 ∧
      Value.num (.natN n) = .num (.natN p.2) := ⟨(mi, n), rfl, rfl⟩
  unfold Prims.growmemCall
  split
  · rename_i h
    obtain ⟨h₁, h₂⟩ := h.choose_spec
    have e₁ : h.choose.1 = mi := (memInstToValue_inj h₁).symm
    have e₂ : h.choose.2 = n := by injection h₂ with h₂; injection h₂ with h₂; exact h₂.symm
    rw [e₁, e₂]
  · contradiction

/-- `B` answers `$growtable` by `growtableCall`. -/
theorem call_growtable (hn : H → String) (host : HostSemantics H) (T N R : Value) :
    (Prims.builtins prof hn host).call "growtable" [.val T, .val N, .val R] =
      Prims.growtableCall T N R := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-- `B` answers `$growmem` by `growmemCall`. -/
theorem call_growmem (hn : H → String) (host : HostSemantics H) (M N : Value) :
    (Prims.builtins prof hn host).call "growmem" [.val M, .val N] = Prims.growmemCall M N := by
  simp [Prims.builtins, Prims.call, IntNumeric.intCall, Floats.floatCall, Floats.floatNames]

/-! ## `GrowFuns` -/

/-- **`Memory.GrowFuns` holds for the concrete `B`.** -/
theorem growFuns_builtins (hn : H → String) (host : HostSemantics H) :
    Memory.GrowFuns (simEnv (Prims.builtins prof hn host)) := by
  have D := growDefs_simEnv (Prims.builtins prof hn host)
  constructor
  · intro ρ hρ e₁ e₂ e₃ ti ti' n r hg h₁ h₂ h₃
    obtain ⟨ps, t, cs, hd, hu⟩ := growtable_undef D (tableInstToValue CT ti) (.num (.natN n))
      (refToValue r)
    have ha := Equiv.evalArgs_cons h₁ (Equiv.evalArgs_cons h₂ (Equiv.evalArgs_cons h₃
      Equiv.evalArgs_nil))
    refine evalExp_callE_iff.2 ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
      ha).1 ⟨ps, t, cs, hd, Or.inr ⟨hu, ?_⟩⟩)
    rw [simEnv, Env.builtins_withBuiltins, call_growtable, growtableCall_image, hg]
    rfl
  · intro ρ hρ e₁ e₂ mi mi' n hg h₁ h₂
    obtain ⟨ps, t, cs, hd, hu⟩ := growmem_undef D (memInstToValue mi) (.num (.natN n))
    have ha := Equiv.evalArgs_cons h₁ (Equiv.evalArgs_cons h₂ Equiv.evalArgs_nil)
    refine evalExp_callE_iff.2 ((applies_iff_callDef (Prims.findDef_none_of_valsOnly hρ _)
      ha).1 ⟨ps, t, cs, hd, Or.inr ⟨hu, ?_⟩⟩)
    rw [simEnv, Env.builtins_withBuiltins, call_growmem, growmemCall_image, hg]
    rfl

end Silmaril.Wasm.SpecTec.Sim.RefOk
