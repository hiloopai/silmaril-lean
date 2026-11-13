module

public import Silmaril.Wasm.LimeCompile.HandleTr.Defs
public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.NoHost
public import Silmaril.Wasm.Binaryen.Equiv

/-!
# Instantiating a module of functions only

For a module with only types, functions and exports (`HandleTr.onlyFuncs`):

* `allocMany_funcs`, `allocModule?_only`: allocation appends one function instance per
  function and changes nothing else;
* `instantiate_only`: instantiation needs no imports, allocates, and leaves empty code;
* `not_step_nil`: empty code does not step, for any host;
* `moduleObs_only`: an observation is `returns []` followed by a session from the allocated
  store and instance.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (moduleObs Session)
open Silmaril.Wasm.SingleThreaded.Det (noHost not_step_vals)
open Silmaril.Wasm.LimeCompile.HandleTr

variable {H : Type}

theorem allocMany_funcs (mi : ModuleInst) :
    ∀ (s : Store H) (L : List (DefType × Func)),
      (allocMany (fun s (p : DefType × Func) => allocFunc s p.1 (.wasm p.2) mi) s L).1 =
        { s with funcs := s.funcs ++ L.map fun p => ⟨p.1, mi, .wasm p.2⟩ }
  | s, [] => by simp [allocMany]
  | s, p :: L => by
    simp only [allocMany]
    rw [allocMany_funcs mi _ L]
    simp [allocFunc]

/-- The module instance of a module of functions only. -/
def onlyInst (s : Store H) (M : Module) (xi : List ExportInst) : ModuleInst :=
  { types := allocTypes M.types,
    funcs := (List.range M.funcs.length).map (s.funcs.length + ·), exports := xi }

/-- The export-allocation instance. -/
def onlyExpInst (s : Store H) (M : Module) : ModuleInst :=
  { funcs := (List.range M.funcs.length).map (s.funcs.length + ·) }

theorem onlyFuncs_fields {M : Module} (hM : onlyFuncs M = true) :
    M.imports = [] ∧ M.tags = [] ∧ M.globals = [] ∧ M.memories = [] ∧ M.tables = [] ∧
      M.data = [] ∧ M.elems = [] ∧ M.start = none := by
  simp only [onlyFuncs, Bool.and_eq_true, List.isEmpty_iff, Option.isNone_iff_eq_none] at hM
  tauto

/-- **Allocation of a module of functions only.** -/
theorem allocModule?_only {M : Module} (hM : onlyFuncs M = true) (s : Store H) :
    allocModule? s M [] [] [] [] =
      (M.funcs.mapM fun fn => (allocTypes M.types)[fn.type.toNat]?).bind fun fts =>
        (M.exports.mapM (allocExport? (onlyExpInst s M))).bind fun xi =>
          some ({ s with funcs := s.funcs ++
              (fts.zip M.funcs).map fun p => ⟨p.1, onlyInst s M xi, .wasm p.2⟩ },
            onlyInst s M xi) := by
  obtain ⟨hi, ht, hg, hm, htb, hd, he, hs⟩ := onlyFuncs_fields hM
  cases M
  simp only at hi ht hg hm htb hd he hs
  subst hi ht hg hm htb hd he hs
  simp only [allocModule?, List.mapM_nil, Option.pure_def, Option.bind_some, allocMany,
    List.map_nil, List.zip_nil_right, ExternAddr.tags, ExternAddr.globals, ExternAddr.mems,
    ExternAddr.tables, ExternAddr.funcs, List.nil_append, Option.bind_eq_bind]
  simp only [onlyExpInst, onlyInst, allocMany_funcs]

theorem moduleOk_only {M : Module} (hM : onlyFuncs M = true) {xtI xtE : List CExternType}
    (h : ModuleOk M ⟨xtI, xtE⟩) : xtI = [] := by
  obtain ⟨hi, -⟩ := onlyFuncs_fields hM
  cases h with
  | mk _ himports =>
    rw [hi] at himports
    cases himports
    rfl

/-- **Instantiation of a module of functions only.** -/
theorem instantiate_only {P : Profile} {host : HostSemantics H} {M : Module}
    (hM : onlyFuncs M = true) {s : Store H} {xas : List ExternAddr} {c : Config H} :
    Instantiate P host s M xas c ↔ (∃ xtE, ModuleOk M ⟨[], xtE⟩) ∧ xas = [] ∧
      ∃ s' mi, allocModule? s M [] [] [] [] = some (s', mi) ∧ c = ⟨s', { module := mi }, []⟩ := by
  obtain ⟨hi, ht, hg, hm, htb, hd, he, hs⟩ := onlyFuncs_fields hM
  constructor
  · rintro ⟨⟨xtE, xtI, hok, hxa⟩, -, ⟨s₁, s₂, s₃, s₄, f₁, f₂, f₃, valsG, refsT, refsE, mi, hG, hT, hE,
      hal, rfl⟩⟩
    obtain rfl := moduleOk_only hM hok
    cases hxa
    rw [hg] at hG
    cases hG
    rw [htb] at hT
    cases hT
    rw [he] at hE
    cases hE
    refine ⟨⟨xtE, hok⟩, rfl, s₄, mi, hal, ?_⟩
    simp [he, hd, hs, expression]
  · rintro ⟨⟨xtE, hok⟩, rfl, s', mi, hal, rfl⟩
    refine ⟨⟨xtE, [], hok, .nil⟩, by simp [he, hd], ?_⟩
    refine ⟨s, s, s, s', ⟨[], ModuleInst.initial s M []⟩, ⟨[], ModuleInst.initial s M []⟩,
      ⟨[], ModuleInst.initial s M []⟩, [], [], [], mi, ?_, ?_, ?_, hal, ?_⟩
    · rw [hg]; exact .nil
    · rw [htb]; exact .nil
    · rw [he]; exact .nil
    · simp [he, hd, hs, expression]

/-- Empty code does not step. -/
theorem not_step_nil {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
    {c' : Config H} (h : Step P host ⟨s, f, []⟩ c') : False := by
  have h' := Step.noHost_of h (fun a ha => by cases ha <;> simp_all)
  exact not_step_vals (W := []) h'

theorem steps_nil {P : Profile} {host : HostSemantics H} {c c' : Config H} (hc : c.code = [])
    (h : Steps P host c c') : c' = c := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hst, -⟩
  · rfl
  · rcases c with ⟨s, f, code⟩
    simp only at hc
    subst hc
    exact (not_step_nil hst).elim

theorem result_toAdmin_nil {r : Result} (h : ([] : List Admin) = r.toAdmin) : r = .values [] := by
  cases r with
  | values vs =>
    simp only [Result.toAdmin, vals] at h
    rw [List.map_eq_nil_iff.mp h.symm]
  | throw a => simp [Result.toAdmin] at h
  | trap => simp [Result.toAdmin] at h

theorem instantiate_code {P : Profile} {host : HostSemantics H} {M : Module}
    (hM : onlyFuncs M = true) {s : Store H} {xas : List ExternAddr} {c : Config H}
    (hc : Instantiate P host s M xas c) : c.code = [] := by
  obtain ⟨-, -, s', mi, -, hc'⟩ := (instantiate_only hM).mp hc
  rw [hc']

theorem not_diverges_nil {P : Profile} {host : HostSemantics H} {c : Config H}
    (hc : c.code = []) (hd : Diverges P host c) : False := by
  obtain ⟨b, hb, -⟩ := Silmaril.InfiniteTrace.unfold hd
  have hb' : Step P host ⟨c.store, c.frame, []⟩ b := hc ▸ hb
  exact not_step_nil hb'

/-- **Observations of a module of functions only.** -/
theorem moduleObs_only {P : Profile} {host : HostSemantics H} {M : Module}
    (hM : onlyFuncs M = true) {s : Store H} {xas : List ExternAddr} {script : List Binaryen.Call}
    {bs : List (Behaviour Val)} :
    bs ∈ moduleObs P host s xas M script ↔ ∃ c, Instantiate P host s M xas c ∧
      ∃ bs', Session P host c.frame.module c.store script bs' ∧ bs = .returns [] :: bs' := by
  constructor
  · rintro ⟨c, hc, hcases⟩
    have hcode : c.code = [] := instantiate_code hM hc
    rcases hcases with ⟨c', bs', hs, -, hss, hbs⟩ | ⟨c', r, hs, hr, hne, -⟩ | ⟨hd, -⟩
    · have hcc : c' = c := steps_nil hcode hs
      exact ⟨c, hc, bs', hcc ▸ hss, hbs⟩
    · have hcc : c' = c := steps_nil hcode hs
      have hr' : ([] : List Admin) = r.toAdmin := hcode ▸ hcc ▸ hr
      exact (hne (result_toAdmin_nil hr')).elim
    · exact (not_diverges_nil hcode hd).elim
  · rintro ⟨c, hc, bs', hss, hbs⟩
    exact ⟨c, hc, .inl ⟨c, bs', .refl, instantiate_code hM hc, hss, hbs⟩⟩

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
