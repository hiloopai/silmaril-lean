module

public import Silmaril.Proofs.Wasm.LimeCompile.HandleTr.Sess

/-!
# The handle compiler on forwarders: sessions and module equivalence

* `sess_tgt`, `sess_src`: a session of the target (source) is matched by a session of the
  source (target) on related scripts, behaviours related by `Handle.BehRel σ`;
* `alloc_src`, `alloc_tgt`, `fts_iff`: allocation of the source and of the target;
* **`fwd_equiv`**: a valid module of forwarders over 2.0 function types, whose rewrite
  `tgtM M` is valid, is `EquivUpToT σ` its rewrite, for every handle table, profile and host.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.LimeCompile.HandleTr

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Binaryen (exportFunc? Session SessionRel moduleObs)
open Silmaril.Wasm.LimeCompile.HandleTr
open Silmaril.Wasm.LimeCompile.Handle (handleRef ResRel BehRel paramsOf)
open Silmaril.Wasm.LimeCompile.Preserve.Module (exportApi)

variable {H : Type}

theorem script_cons_left {σ : List Val} {A : List (String × Option Silmaril.Wasm.LimeCompile.Preserve.ApiTy)} {x : String}
    {ws : List Val} {rest sc : List Binaryen.Call} (h : ScriptRelT σ A ((x, ws) :: rest) sc) :
    ∃ vs rest₀, sc = (x, vs) :: rest₀ ∧ CallRelT σ A (x, ws) (x, vs) ∧ ScriptRelT σ A rest rest₀ := by
  obtain ⟨⟨x₀, vs⟩, rest₀, hrel, hrest, hsc⟩ := List.forall₂_cons_left_iff.mp h
  have hx : x = x₀ := hrel.1
  subst hx
  exact ⟨vs, rest₀, hsc, hrel, hrest⟩

theorem script_cons_right {σ : List Val} {A : List (String × Option Silmaril.Wasm.LimeCompile.Preserve.ApiTy)} {x : String}
    {vs : List Val} {rest sc' : List Binaryen.Call} (h : ScriptRelT σ A sc' ((x, vs) :: rest)) :
    ∃ ws rest', sc' = (x, ws) :: rest' ∧ CallRelT σ A (x, ws) (x, vs) ∧
      ScriptRelT σ A rest' rest := by
  obtain ⟨⟨x₀, ws⟩, rest', hrel, hrest, hsc⟩ := List.forall₂_cons_right_iff.mp h
  have hx : x₀ = x := hrel.1
  subst hx
  exact ⟨ws, rest', hsc, hrel, hrest⟩

section
variable {s : Store H} {M : Module} {ts : List V2.FuncType} {fts fts' : List DefType}
  {xi : List ExportInst} {P : Profile} {host : HostSemantics H} {σ : List Val}

/-- **Target sessions are matched by source sessions.** -/
theorem sess_tgt (hS : Setup s M ts fts fts' xi) {S₀ : Store H} {sc' : List Binaryen.Call}
    {bs : List (Behaviour Val)} (h : Session P host (onlyInst s (tgtM M) xi) S₀ sc' bs)
    (hS₀ : S₀ = tgtStore s M fts' xi) :
    ∀ sc, ScriptRelT σ (exportApi M) sc' sc →
      ∃ bs', Session P host (onlyInst s M xi) (srcStore s M fts xi) sc bs' ∧
        SessionRel (BehRel σ) bs bs' := by
  induction h with
  | nil =>
    intro sc hsc
    have hsc0 : sc = [] := List.forall₂_nil_left_iff.mp hsc
    exact ⟨[], hsc0 ▸ .nil, .nil⟩
  | @stop S₁ x ws rest hstop =>
    show ∀ sc, ScriptRelT σ (exportApi M) ((x, ws) :: rest) sc →
      ∃ bs', Session P host (onlyInst s M xi) (srcStore s M fts xi) sc bs' ∧
        SessionRel (BehRel σ) [] bs'
    intro sc hsc
    obtain ⟨vs, rest₀, hsc0, hrel, -⟩ : ∃ vs rest₀, sc = (x, vs) :: rest₀ ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest rest₀ :=
      script_cons_left hsc
    have hstop' : ∀ a, exportFunc? (onlyInst s M xi) x = some a →
        ¬ InvokeOk (srcStore s M fts xi) a vs := fun a ha hok =>
      hstop a ((exportFunc_tgt s M xi x).trans ha)
        (hS₀ ▸ (call_src (P := P) (host := host) hS ha hrel hok).1)
    exact ⟨[], hsc0 ▸ .stop hstop', .nil⟩
  | @done S₁ x ws rest a c r bs₁ ha hok run hr _ ih =>
    show ∀ sc, ScriptRelT σ (exportApi M) ((x, ws) :: rest) sc →
      ∃ bs', Session P host (onlyInst s M xi) (srcStore s M fts xi) sc bs' ∧
        SessionRel (BehRel σ) (r.toBehaviour :: bs₁) bs'
    intro sc hsc
    obtain ⟨vs, rest₀, hsc0, hrel, hrest⟩ : ∃ vs rest₀, sc = (x, vs) :: rest₀ ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest rest₀ :=
      script_cons_left hsc
    have ha' : exportFunc? (onlyInst s M xi) x = some a := (exportFunc_tgt s M xi x).symm.trans ha
    obtain ⟨hok', -, hres⟩ := call_tgt (P := P) (host := host) hS ha' hrel (hS₀ ▸ hok)
    obtain ⟨hst, us', us, hreq, hrun, hrelu⟩ : c.store = tgtStore s M fts' xi ∧ ∃ us' us,
        r = .values us' ∧ Steps P host (invoke (srcStore s M fts xi) a vs)
          ⟨srcStore s M fts xi, {}, vals us⟩ ∧ List.Forall₂ (ResRel σ) us' us :=
      hres c r (hS₀ ▸ run) hr
    obtain ⟨bs', hss, hsr⟩ := ih hst rest₀ hrest
    have hbeh : BehRel σ r.toBehaviour (Result.values us).toBehaviour := by
      rw [hreq]
      exact .inr ⟨us', us, rfl, rfl, hrelu⟩
    exact ⟨_, hsc0 ▸ .done ha' hok' hrun (r := .values us) rfl hss, .cons hbeh hsr⟩
  | @diverge S₁ x ws rest a ha hok hd =>
    intro sc hsc
    obtain ⟨vs, rest₀, -, hrel, -⟩ : ∃ vs rest₀, sc = (x, vs) :: rest₀ ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest rest₀ :=
      script_cons_left hsc
    have ha' : exportFunc? (onlyInst s M xi) x = some a := (exportFunc_tgt s M xi x).symm.trans ha
    exact ((call_tgt (P := P) (host := host) hS ha' hrel (hS₀ ▸ hok)).2.1 (hS₀ ▸ hd)).elim

/-- **Source sessions are matched by target sessions.** -/
theorem sess_src (hS : Setup s M ts fts fts' xi) {S₀ : Store H} {sc : List Binaryen.Call}
    {bs' : List (Behaviour Val)} (h : Session P host (onlyInst s M xi) S₀ sc bs')
    (hS₀ : S₀ = srcStore s M fts xi) :
    ∀ sc', ScriptRelT σ (exportApi M) sc' sc →
      ∃ bs, Session P host (onlyInst s (tgtM M) xi) (tgtStore s M fts' xi) sc' bs ∧
        SessionRel (fun b' b => BehRel σ b b') bs' bs := by
  induction h with
  | nil =>
    intro sc' hsc
    have hsc0 : sc' = [] := List.forall₂_nil_right_iff.mp hsc
    exact ⟨[], hsc0 ▸ .nil, .nil⟩
  | @stop S₁ x vs rest hstop =>
    show ∀ sc', ScriptRelT σ (exportApi M) sc' ((x, vs) :: rest) →
      ∃ bs, Session P host (onlyInst s (tgtM M) xi) (tgtStore s M fts' xi) sc' bs ∧
        SessionRel (fun b' b => BehRel σ b b') [] bs
    intro sc' hsc
    obtain ⟨ws, rest', hsc0, hrel, -⟩ : ∃ ws rest', sc' = (x, ws) :: rest' ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest' rest :=
      script_cons_right hsc
    have hstop' : ∀ a, exportFunc? (onlyInst s (tgtM M) xi) x = some a →
        ¬ InvokeOk (tgtStore s M fts' xi) a ws := fun a ha hok =>
      hstop a ((exportFunc_tgt s M xi x).symm.trans ha)
        (hS₀ ▸ (call_tgt (P := P) (host := host) hS ((exportFunc_tgt s M xi x).symm.trans ha)
          hrel hok).1)
    exact ⟨[], hsc0 ▸ .stop hstop', .nil⟩
  | @done S₁ x vs rest a c r bs₁ ha hok run hr _ ih =>
    show ∀ sc', ScriptRelT σ (exportApi M) sc' ((x, vs) :: rest) →
      ∃ bs, Session P host (onlyInst s (tgtM M) xi) (tgtStore s M fts' xi) sc' bs ∧
        SessionRel (fun b' b => BehRel σ b b') (r.toBehaviour :: bs₁) bs
    intro sc' hsc
    obtain ⟨ws, rest', hsc0, hrel, hrest⟩ : ∃ ws rest', sc' = (x, ws) :: rest' ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest' rest :=
      script_cons_right hsc
    obtain ⟨hok', -, hres⟩ := call_src (P := P) (host := host) hS ha hrel (hS₀ ▸ hok)
    obtain ⟨hst, us, us', hreq, hrun, hrelu⟩ : c.store = srcStore s M fts xi ∧ ∃ us us',
        r = .values us ∧ Steps P host (invoke (tgtStore s M fts' xi) a ws)
          ⟨tgtStore s M fts' xi, {}, vals us'⟩ ∧ List.Forall₂ (ResRel σ) us' us :=
      hres c r (hS₀ ▸ run) hr
    obtain ⟨bs, hss, hsr⟩ := ih hst rest' hrest
    have hbeh : BehRel σ (Result.values us').toBehaviour r.toBehaviour := by
      rw [hreq]
      exact .inr ⟨us', us, rfl, rfl, hrelu⟩
    exact ⟨_, hsc0 ▸ .done ((exportFunc_tgt s M xi x).trans ha) hok' hrun (r := .values us') rfl hss,
      .cons hbeh hsr⟩
  | @diverge S₁ x vs rest a ha hok hd =>
    intro sc' hsc
    obtain ⟨ws, rest', -, hrel, -⟩ : ∃ ws rest', sc' = (x, ws) :: rest' ∧
        CallRelT σ (exportApi M) (x, ws) (x, vs) ∧ ScriptRelT σ (exportApi M) rest' rest :=
      script_cons_right hsc
    exact ((call_src (P := P) (host := host) hS ha hrel (hS₀ ▸ hok)).2.1 (hS₀ ▸ hd)).elim

end

theorem mapM_isSome {α β : Type} {g : α → Option β} :
    ∀ {l : List α}, (l.mapM g).isSome = true ↔ ∀ a ∈ l, (g a).isSome = true
  | [] => by simp
  | a :: l => by
    have ih := mapM_isSome (g := g) (l := l)
    rw [List.mapM_cons]
    simp only [List.mem_cons, forall_eq_or_imp]
    cases hg : g a with
    | none => simp
    | some b =>
      rw [← ih]
      cases l.mapM g <;> simp

theorem fts_isSome {M : Module} {L L' : List DefType} (hl : L.length = L'.length) :
    (M.funcs.mapM fun fn => L[fn.type.toNat]?).isSome = true ↔
      (M.funcs.mapM fun fn => L'[fn.type.toNat]?).isSome = true := by
  rw [mapM_isSome, mapM_isSome]
  simp [hl]

theorem srcTypes {M : Module} {ts : List V2.FuncType} (hts : M.types = ts.map V2.FuncType.toCoreRec) :
    allocTypes M.types = ts.map V2.FuncType.toDefType := by
  rw [hts, allocTypes_v2]

theorem tgtTypes {M : Module} {ts : List V2.FuncType} (hts : M.types = ts.map V2.FuncType.toCoreRec) :
    allocTypes (tgtM M).types = (ts.map hV2FT).map V2.FuncType.toDefType := by
  have : (tgtM M).types = (ts.map hV2FT).map V2.FuncType.toCoreRec := by
    simp [tgtM, hts, List.map_map, Function.comp_def, hRec_toCoreRec]
  rw [this, allocTypes_v2]

theorem alloc_src {s : Store H} {M : Module} (hM : onlyFuncs M = true) {S : Store H}
    {mi : ModuleInst} :
    allocModule? s M [] [] [] [] = some (S, mi) ↔ ∃ fts xi,
      M.funcs.mapM (fun fn => (allocTypes M.types)[fn.type.toNat]?) = some fts ∧
      M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi ∧
      S = srcStore s M fts xi ∧ mi = onlyInst s M xi := by
  rw [allocModule?_only hM]
  constructor
  · intro h
    obtain ⟨fts, hf, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xi, hx, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨fts, xi, hf, hx, h.1.symm, h.2.symm⟩
  · rintro ⟨fts, xi, hf, hx, rfl, rfl⟩
    simp [hf, hx, srcStore]

theorem alloc_tgt {s : Store H} {M : Module} (hM : onlyFuncs M = true) {S : Store H}
    {mi : ModuleInst} :
    allocModule? s (tgtM M) [] [] [] [] = some (S, mi) ↔ ∃ fts' xi,
      M.funcs.mapM (fun fn => (allocTypes (tgtM M).types)[fn.type.toNat]?) = some fts' ∧
      M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi ∧
      S = tgtStore s M fts' xi ∧ mi = onlyInst s (tgtM M) xi :=
  alloc_src (M := tgtM M) hM

/-- Instantiation of the source, unfolded. -/
theorem inst_src {P : Profile} {host : HostSemantics H} {s : Store H} {M : Module}
    {ts : List V2.FuncType} (hM : onlyFuncs M = true) (hts : M.types = ts.map V2.FuncType.toCoreRec)
    {xas : List ExternAddr} {c : Config H} (hc : Instantiate P host s M xas c) :
    xas = [] ∧ ∃ fts xi,
      M.funcs.mapM (fun fn => (ts.map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts ∧
      M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi ∧
      c = ⟨srcStore s M fts xi, { module := onlyInst s M xi }, []⟩ := by
  obtain ⟨-, hxas, S, mi, hal, hc'⟩ := (instantiate_only hM).mp hc
  obtain ⟨fts, xi, hf, hx, hS, hmi⟩ := (alloc_src hM).mp hal
  refine ⟨hxas, fts, xi, srcTypes hts ▸ hf, hx, ?_⟩
  rw [hc', hS, hmi]

/-- Instantiation of the target, unfolded. -/
theorem inst_tgt {P : Profile} {host : HostSemantics H} {s : Store H} {M : Module}
    {ts : List V2.FuncType} (hM : onlyFuncs M = true) (hts : M.types = ts.map V2.FuncType.toCoreRec)
    {xas : List ExternAddr} {c : Config H} (hc : Instantiate P host s (tgtM M) xas c) :
    xas = [] ∧ ∃ fts' xi,
      M.funcs.mapM (fun fn => ((ts.map hV2FT).map V2.FuncType.toDefType)[fn.type.toNat]?) =
        some fts' ∧
      M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi ∧
      c = ⟨tgtStore s M fts' xi, { module := onlyInst s (tgtM M) xi }, []⟩ := by
  obtain ⟨-, hxas, S, mi, hal, hc'⟩ := (instantiate_only (M := tgtM M) hM).mp hc
  obtain ⟨fts', xi, hf, hx, hS, hmi⟩ := (alloc_tgt hM).mp hal
  refine ⟨hxas, fts', xi, tgtTypes hts ▸ hf, hx, ?_⟩
  rw [hc', hS, hmi]

theorem inst_src_mk {P : Profile} {host : HostSemantics H} {s : Store H} {M : Module}
    {ts : List V2.FuncType} (hM : onlyFuncs M = true) (hts : M.types = ts.map V2.FuncType.toCoreRec)
    {xtE : List CExternType} (hv : ModuleOk M ⟨[], xtE⟩) {fts : List DefType}
    {xi : List ExportInst}
    (hf : M.funcs.mapM (fun fn => (ts.map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts)
    (hx : M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi) :
    Instantiate P host s M [] ⟨srcStore s M fts xi, { module := onlyInst s M xi }, []⟩ :=
  (instantiate_only hM).mpr ⟨⟨xtE, hv⟩, rfl, _, _,
    (alloc_src hM).mpr ⟨fts, xi, srcTypes hts ▸ hf, hx, rfl, rfl⟩, rfl⟩

theorem inst_tgt_mk {P : Profile} {host : HostSemantics H} {s : Store H} {M : Module}
    {ts : List V2.FuncType} (hM : onlyFuncs M = true) (hts : M.types = ts.map V2.FuncType.toCoreRec)
    {xtE : List CExternType} (hv : ModuleOk (tgtM M) ⟨[], xtE⟩) {fts' : List DefType}
    {xi : List ExportInst}
    (hf : M.funcs.mapM
      (fun fn => ((ts.map hV2FT).map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts')
    (hx : M.exports.mapM (allocExport? (onlyExpInst s M)) = some xi) :
    Instantiate P host s (tgtM M) [] ⟨tgtStore s M fts' xi, { module := onlyInst s (tgtM M) xi }, []⟩ :=
  (instantiate_only (M := tgtM M) hM).mpr ⟨⟨xtE, hv⟩, rfl, _, _,
    (alloc_tgt hM).mpr ⟨fts', xi, tgtTypes hts ▸ hf, hx, rfl, rfl⟩, rfl⟩

theorem fts_tgt_of_src {M : Module} {ts : List V2.FuncType} {fts : List DefType}
    (h : M.funcs.mapM (fun fn => (ts.map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts) :
    ∃ fts', M.funcs.mapM
      (fun fn => ((ts.map hV2FT).map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts' :=
  Option.isSome_iff_exists.mp ((fts_isSome (L := ts.map V2.FuncType.toDefType)
    (L' := (ts.map hV2FT).map V2.FuncType.toDefType) (by simp)).mp (by rw [h]; rfl))

theorem fts_src_of_tgt {M : Module} {ts : List V2.FuncType} {fts' : List DefType}
    (h : M.funcs.mapM
      (fun fn => ((ts.map hV2FT).map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts') :
    ∃ fts, M.funcs.mapM (fun fn => (ts.map V2.FuncType.toDefType)[fn.type.toNat]?) = some fts :=
  Option.isSome_iff_exists.mp ((fts_isSome (L := ts.map V2.FuncType.toDefType)
    (L' := (ts.map hV2FT).map V2.FuncType.toDefType) (by simp)).mpr (by rw [h]; rfl))

/-- **The forwarder fragment, module level.** -/
theorem fwd_equiv {M : Module} {ts : List V2.FuncType} (hM : onlyFuncs M = true)
    (hfwd : ∀ f ∈ M.funcs, fwdFunc f = true) (hts : M.types = ts.map V2.FuncType.toCoreRec)
    (hvM : ∃ mt, ModuleOk M mt) (hvT : ∃ mt, ModuleOk (tgtM M) mt) (σ : List Val) (P : Profile)
    (host : HostSemantics H) : EquivUpToT σ P host (tgtM M) M := by
  have hT : onlyFuncs (tgtM M) = true := hM
  obtain ⟨⟨xtI, xtE⟩, hvM⟩ := hvM
  obtain ⟨⟨xtI', xtE'⟩, hvT⟩ := hvT
  have hvM' : ModuleOk M ⟨[], xtE⟩ := moduleOk_only hM hvM ▸ hvM
  have hvT' : ModuleOk (tgtM M) ⟨[], xtE'⟩ := moduleOk_only hT hvT ▸ hvT
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro s xas c _ hc
    obtain ⟨hxas, fts, xi, hf, hx, -⟩ := inst_src (P := P) (host := host) hM hts hc
    obtain ⟨fts', hf'⟩ := fts_tgt_of_src hf
    exact ⟨_, hxas ▸ inst_tgt_mk hM hts hvT' hf' hx⟩
  · show ∀ (s : Store H) xas sc' sc, StoreOk s → ScriptRelT σ (exportApi M) sc' sc →
      ∀ bs ∈ moduleObs P host s xas (tgtM M) sc',
        ∃ bs' ∈ moduleObs P host s xas M sc, SessionRel (BehRel σ) bs bs'
    intro s xas sc' sc _ hsc bs hbs
    obtain ⟨c', hc', bs₀, hss, hbs₀⟩ := (moduleObs_only hT).mp hbs
    obtain ⟨hxas, fts', xi, hf', hx, hc'eq⟩ := inst_tgt hM hts hc'
    obtain ⟨fts, hf⟩ := fts_src_of_tgt hf'
    have hS : Setup s M ts fts fts' xi := ⟨hM, hfwd, hts, hx, hf, hf'⟩
    obtain ⟨bs', hss', hsr⟩ := sess_tgt (σ := σ) hS (hc'eq ▸ hss) rfl sc hsc
    have hobs : .returns [] :: bs' ∈ moduleObs P host s xas M sc :=
      (moduleObs_only hM).mpr ⟨_, hxas ▸ inst_src_mk hM hts hvM' hf hx, bs', hss', rfl⟩
    exact ⟨_, hobs, hbs₀ ▸ .cons (.inl rfl) hsr⟩
  · intro s xas c' _ hc'
    obtain ⟨hxas, fts', xi, hf', hx, -⟩ := inst_tgt (P := P) (host := host) hM hts hc'
    obtain ⟨fts, hf⟩ := fts_src_of_tgt hf'
    exact ⟨_, hxas ▸ inst_src_mk hM hts hvM' hf hx⟩
  · show ∀ (s : Store H) xas sc' sc, StoreOk s → ScriptRelT σ (exportApi M) sc' sc →
      ∀ bs' ∈ moduleObs P host s xas M sc, ∃ bs ∈ moduleObs P host s xas (tgtM M) sc',
        SessionRel (fun b' b => BehRel σ b b') bs' bs
    intro s xas sc' sc _ hsc bs' hbs'
    obtain ⟨c, hc, bs₀, hss, hbs₀⟩ := (moduleObs_only hM).mp hbs'
    obtain ⟨hxas, fts, xi, hf, hx, hceq⟩ := inst_src hM hts hc
    obtain ⟨fts', hf'⟩ := fts_tgt_of_src hf
    have hS : Setup s M ts fts fts' xi := ⟨hM, hfwd, hts, hx, hf, hf'⟩
    obtain ⟨bs, hss', hsr⟩ := sess_src (σ := σ) hS (hceq ▸ hss) rfl sc' hsc
    have hobs : .returns [] :: bs ∈ moduleObs P host s xas (tgtM M) sc' :=
      (moduleObs_only hT).mpr ⟨_, hxas ▸ inst_tgt_mk hM hts hvT' hf' hx, bs, hss', rfl⟩
    exact ⟨_, hobs, hbs₀ ▸ .cons (.inl rfl) hsr⟩

end Silmaril.Proofs.Wasm.LimeCompile.HandleTr
