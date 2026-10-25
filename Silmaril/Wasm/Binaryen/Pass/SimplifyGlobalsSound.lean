module

public import Silmaril.Wasm.Binaryen.Exe.StageContract
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobals
public import Silmaril.Wasm.Binaryen.Pass.SimplifyGlobalsSim

@[expose] public section

namespace Silmaril.Wasm.Binaryen.SimplifyGlobals

open Execution.Core Numerics

/-- Every successful literal lookup comes from an immutable singleton initializer. -/
theorem constant?_spec {g : Global} {i : Instr} (h : constant? g = some i) :
    g.type.mutability = .const ∧ g.init = [i] ∧ ∃ t b, i = .intConst t b := by
  unfold constant? at h
  split at h
  · next t b hm hi =>
    split at h
    · cases h
      exact ⟨hm, hi, t, b, rfl⟩
    · cases h
  · cases h

/-- Imported globals cannot be replaced using a defined global's initializer. -/
theorem lookup_import {m : BModule} {x : GlobalIdx} (h : x.toNat < m.numImportedGlobals) :
    lookup m x = none := by simp [lookup, h]

/-- A successful lookup identifies the exact declaration and its literal. -/
theorem lookup_spec {m : BModule} {x : GlobalIdx} {i : Instr} (h : lookup m x = some i) :
    m.numImportedGlobals ≤ x.toNat ∧ ∃ g,
      m.base.globals[x.toNat - m.numImportedGlobals]? = some g ∧
      g.type.mutability = .const ∧ g.init = [i] ∧ ∃ t b, i = .intConst t b := by
  unfold lookup at h
  split at h
  · cases h
  · next hx =>
    obtain ⟨g, hg, hi⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨by omega, g, hg, constant?_spec hi⟩

theorem instr_profile (m : BModule) (i : Instr) :
    profileInstr (instr m i) = profileInstr i := by
  cases i <;> try rfl
  rename_i x
  cases hl : lookup m x with
  | none => simp [instr, hl, profileInstr]
  | some c =>
    obtain ⟨_, g, _, _, _, t, b, rfl⟩ := lookup_spec hl
    simp [instr, hl, profileInstr]

mutual
theorem expr_profile (m : BModule) : ∀ e : BExpr,
    (expr m e).inProfile = e.inProfile
  | .op i args => by simp only [expr, BExpr.inProfile, instr_profile, exprs_profile]
  | .block bt b => by simp only [expr, BExpr.inProfile, exprs_profile]
  | .loop bt b => by simp only [expr, BExpr.inProfile, exprs_profile]
  | .if_ bt c t e => by simp only [expr, BExpr.inProfile, exprs_profile]
  | .tryTable .. => rfl
theorem exprs_profile (m : BModule) : ∀ es : List BExpr,
    BExpr.inProfileList (exprs m es) = BExpr.inProfileList es
  | [] => rfl
  | e :: es => by simp only [exprs, BExpr.inProfileList, expr_profile, exprs_profile]
end

theorem instr_profileT (m : BModule) (i : Instr) :
    profileInstrT (instr m i) = profileInstrT i := by
  cases i <;> try rfl
  rename_i x
  cases hl : lookup m x with
  | none => simp [instr, hl, profileInstrT, profileInstr]
  | some c =>
    obtain ⟨_, g, _, _, _, t, b, rfl⟩ := lookup_spec hl
    simp [instr, hl, profileInstrT, profileInstr]

mutual
theorem expr_profileT (m : BModule) : ∀ e : BExpr,
    (expr m e).inProfileT = e.inProfileT
  | .op i args => by simp only [expr, BExpr.inProfileT, instr_profileT, exprs_profileT]
  | .block bt b => by simp only [expr, BExpr.inProfileT, exprs_profileT]
  | .loop bt b => by simp only [expr, BExpr.inProfileT, exprs_profileT]
  | .if_ bt c t e => by simp only [expr, BExpr.inProfileT, exprs_profileT]
  | .tryTable .. => rfl
theorem exprs_profileT (m : BModule) : ∀ es : List BExpr,
    BExpr.inProfileListT (exprs m es) = BExpr.inProfileListT es
  | [] => rfl
  | e :: es => by simp only [exprs, BExpr.inProfileListT, expr_profileT, exprs_profileT]
end

theorem instr_gcProfile (m : BModule) (i : Instr) : gcInstr (instr m i) = gcInstr i := by
  cases i <;> try rfl
  rename_i x
  cases hl : lookup m x with
  | none => simp [instr, hl]
  | some c =>
    obtain ⟨_, g, _, _, _, t, b, rfl⟩ := lookup_spec hl
    simp [instr, hl, gcInstr, gcExtraInstr, profileInstrT, profileInstr]

mutual
theorem expr_gcProfile (m : BModule) : ∀ e : BExpr,
    (expr m e).inGcProfile = e.inGcProfile
  | .op i args => by simp only [expr, BExpr.inGcProfile, instr_gcProfile, exprs_gcProfile]
  | .block bt b => by simp only [expr, BExpr.inGcProfile, exprs_gcProfile]
  | .loop bt b => by simp only [expr, BExpr.inGcProfile, exprs_gcProfile]
  | .if_ bt c t e => by simp only [expr, BExpr.inGcProfile, exprs_gcProfile]
  | .tryTable bt cs b => by simp only [expr, BExpr.inGcProfile, exprs_gcProfile]
theorem exprs_gcProfile (m : BModule) : ∀ es : List BExpr,
    BExpr.inGcProfileList (exprs m es) = BExpr.inGcProfileList es
  | [] => rfl
  | e :: es => by simp only [exprs, BExpr.inGcProfileList, expr_gcProfile, exprs_gcProfile]
end

/-- Literal propagation preserves the executable profile check exactly. -/
theorem simplifyGlobals_profileOk (m : BModule) :
    Exe.profileOk (simplifyGlobals m) = Exe.profileOk m := by
  simp [Exe.profileOk, Exe.typesInGcProfile, BModule.inGcProfile, simplifyGlobals,
    List.all_map, Function.comp_def, exprs_gcProfile]
  rfl

/-- Core store extension preserves an immutable global's entire instance. -/
theorem immutable_global_extend {H : Type} {s s' : Store H} (he : Extend s s')
    {a : Nat} {g : GlobalInst} (hg : s.globals[a]? = some g)
    (hc : g.type.mutability = .const) : s'.globals[a]? = some g := by
  obtain ⟨g', hg', ht, hv⟩ := he.globals.get hg
  have hv' : g.value = g'.value := hv.resolve_left (by simp [hc])
  have eg : g = g' := by
    cases g
    cases g'
    simp_all
  simpa [← eg] using hg'

/-- The module-specific invariant needed by the global-read rewrite. It records
values, not merely the types guaranteed by `ModuleInstOk`. -/
def ValuesAgree {H : Type} (m : BModule) (mi : ModuleInst) (s : Store H) : Prop :=
  ∀ (x : GlobalIdx) (t : IntType) (b : BitVec t.width), lookup m x = some (.intConst t b) →
    ∃ a g, mi.globals[x.toNat]? = some a ∧ s.globals[a]? = some g ∧
      g.type.mutability = .const ∧ g.value = .num ⟨.int t, b⟩

/-- Once established at allocation, the invariant survives Core store extension. -/
theorem ValuesAgree.extend {H : Type} {m : BModule} {mi : ModuleInst} {s s' : Store H}
    (h : ValuesAgree m mi s) (he : Extend s s') : ValuesAgree m mi s' := by
  intro x t b hx
  obtain ⟨a, g, ha, hg, hc, hv⟩ := h x t b hx
  exact ⟨a, g, ha, immutable_global_extend he hg hc, hc, hv⟩

/-- The local semantic step once the runtime global is known to contain the literal.
The missing module invariant must establish `hv` after instantiation and preserve it
across calls and successive export invocations. -/
theorem globalGet_step {H : Type} {P : Profile} {host : HostSemantics H}
    {s : Store H} {f : Frame} {x : GlobalIdx} {a : Nat} {g : GlobalInst}
    {t : IntType} {b : BitVec t.width}
    (hg : s.global? f x = some (a, g)) (hv : g.value = .num ⟨.int t, b⟩) :
    Step P host ⟨s, f, [.plain (.globalGet x)]⟩
      ⟨s, f, [.plain (.intConst t b)]⟩ := by
  have h := Step.variable (P := P) (host := host) (VariableStep.globalGet hg)
  simpa [hv, Val.toAdmin] using h

/-- The invariant supplies the premise of the local semantic step. -/
theorem ValuesAgree.globalGet_step {H : Type} {P : Profile} {host : HostSemantics H}
    {m : BModule} {s : Store H} {f : Frame} (h : ValuesAgree m f.module s)
    {x : GlobalIdx} {t : IntType} {b : BitVec t.width}
    (hx : lookup m x = some (.intConst t b)) :
    Step P host ⟨s, f, [.plain (.globalGet x)]⟩
      ⟨s, f, [.plain (.intConst t b)]⟩ := by
  obtain ⟨a, g, ha, hg, _, hv⟩ := h x t b hx
  exact SimplifyGlobals.globalGet_step (a := a) (g := g)
    (by simp [Store.global?, ha, hg]) hv

end Silmaril.Wasm.Binaryen.SimplifyGlobals

namespace Silmaril.Wasm.Binaryen.Exe

open Execution.Core Numerics

/-- **SimplifyGlobals preserves validity and observations** under the closed host, for
arbitrary host-state types. The proof is the global-read simulation
(`Binaryen/GlobReadSim.lean`), one function at a time (`SimplifyGlobals.simplifyGlobals_sound`):
the invariant `ValuesAgree` is established at instantiation and carried along typed runs by
store extension (`ValuesAgree.extend`); under it each rewritten read is
`ValuesAgree.globalGet_step`. -/
theorem simplifyGlobals_stageOk {o : GrowKind → Nat → Nat → Nat → Bool} {H : Type} :
    StageOk o H simplifyGlobals := by
  intro m hm
  exact SimplifyGlobals.simplifyGlobals_sound m hm.ok o H

end Silmaril.Wasm.Binaryen.Exe
