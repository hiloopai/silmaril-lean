module

public import Silmaril.Wasm.Binaryen.Toolkit.MetaDCERuntime
public import Silmaril.Wasm.Binaryen.Pass.RUMESim.ObsOn

@[expose] public section

namespace Silmaril.Wasm.Binaryen.Toolkit.MetaDCE

open Execution.Core Validation Numerics RUMESim
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile}

theorem tree_lower (m : Module) : (tree m).lower = m := by
  have h : (m.funcs.map (Declaration.Func.mapBody liftInstrs)).map
      (Declaration.Func.mapBody BExpr.lowerList) = m.funcs := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id m.funcs]
    apply List.map_congr_left
    intro f _
    cases f
    simp [Declaration.Func.mapBody, lowerList_liftInstrs]
  change {m with funcs := ((m.funcs.map (Declaration.Func.mapBody liftInstrs)).map
    (Declaration.Func.mapBody BExpr.lowerList))} = m
  rw [h]

def bare (types : List RecType) (funcs : List Func) (exports : List Export) : Module :=
  {types, funcs, exports}

theorem supported_bare {m : Module} (h : supported m = true) :
    m = bare m.types m.funcs m.exports := by
  simp only [supported, Bool.and_eq_true, and_assoc, List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  rcases h with ⟨hi, ht, hg, hm, hta, hd, he, hs, _⟩
  cases m
  simp_all [bare]

theorem startCode_bare (ts : List RecType) (fs : List Func) (es : List Export) :
    startCode (bare ts fs es) = [] := rfl

theorem bare_profiled (ts : List RecType) (fs : List Func) (es : List Export) :
    Profiled (bare ts fs es) :=
  ⟨rfl, rfl, rfl, by simp [bare], by simp [bare], by simp [bare]⟩

theorem no_imports {m : Module} (hi : m.imports = []) {s : Store H}
    {imports : List ExternAddr} {c : Config H}
    (h : Instantiate P closedHost s m imports c) : imports = [] := by
  obtain ⟨xtE, xtI, hm, hxa⟩ := h.valid
  cases hm with
  | mk _ himp =>
    rw [hi] at himp
    cases himp
    cases hxa
    rfl

theorem valid_closed {m : Module} (hi : m.imports = []) (h : ModuleValid m) :
    ∃ xtE, ModuleOk m ⟨[], xtE⟩ := by
  obtain ⟨⟨xtI, xtE⟩, hm⟩ := h
  cases hm with
  | mk htypes himp hC' hC ht hg hm hta hf hd he hs hex hdis =>
    rw [hi] at himp
    have hi' := List.forall₂_nil_left_iff.mp himp
    subst hi'
    exact ⟨xtE, .mk htypes (by simpa only [hi] using himp) hC' hC ht hg hm hta hf hd he hs hex hdis⟩

theorem allocExport_name {mi : ModuleInst} {e : Export} {ei : ExportInst}
    (h : allocExport? mi e = some ei) : ei.name = e.name := by
  cases e with
  | mk name index =>
    cases index <;> simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h <;>
      obtain ⟨a, _, rfl⟩ := h <;> rfl

theorem allocExports_project (mi : ModuleInst) (names : List String) :
    ∀ {es : List Export} {xi : List ExportInst}, es.mapM (allocExport? mi) = some xi →
    (es.filter fun e => names.contains e.name).mapM (allocExport? mi) =
      some (xi.filter fun e => names.contains e.name)
  | [], xi, h => by
    have he : xi = [] := by simpa using h.symm
    subst xi
    rfl
  | e :: es, xi, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨ei, he, rest, hr, rfl⟩ := h
    have hn := allocExport_name he
    have ih := allocExports_project mi names hr
    by_cases hk : e.name ∈ names
    · simp only [List.filter_cons, hn, List.contains_iff_mem, hk, ite_true,
        List.mapM_cons, he]
      rw [ih]
      rfl
    · simp only [List.filter_cons, hn, List.contains_iff_mem, hk, ite_false]
      exact ih

theorem exportFunc_filter (names : List String) (mi : ModuleInst) {x : String} (hx : x ∈ names) :
    exportFunc? {mi with exports := mi.exports.filter fun e => names.contains e.name} x =
      exportFunc? mi x := by
  unfold exportFunc?
  congr 1
  rw [List.find?_filter]
  congr 1
  funext e
  by_cases he : e.name = x
  · simp [he, hx]
  · simp [he]

theorem rename_identity (i : Instr) : (Ren.mk id id).instr i = i := by
  cases i <;> try rfl
  case block bt body =>
    rw [Ren.instr_block]
    congr 1
    exact (List.map_congr_left (fun j (_ : j ∈ body) => rename_identity j)).trans (List.map_id body)
  case loop bt body =>
    rw [Ren.instr_loop]
    congr 1
    exact (List.map_congr_left (fun j (_ : j ∈ body) => rename_identity j)).trans (List.map_id body)
  case if_ bt a b =>
    rw [Ren.instr_if]
    congr 1
    · exact (List.map_congr_left (fun j (_ : j ∈ a) => rename_identity j)).trans (List.map_id a)
    · exact (List.map_congr_left (fun j (_ : j ∈ b) => rename_identity j)).trans (List.map_id b)
  case tryTable bt cs body =>
    rw [Ren.instr_tryTable]
    congr 1
    exact (List.map_congr_left (fun j (_ : j ∈ body) => rename_identity j)).trans (List.map_id body)
  all_goals simp [Ren.instr, Ren.funcIdx, Ren.globalIdx]
termination_by sizeOf i
decreasing_by
  all_goals have := List.sizeOf_lt_of_mem ‹_›
  all_goals simp only [Instr.block.sizeOf_spec, Instr.loop.sizeOf_spec,
    Instr.if_.sizeOf_spec, Instr.tryTable.sizeOf_spec]
  all_goals omega

theorem irels_identity (X : SimCtx) (hf : ∀ x, X.KF x x) (hg : ∀ x, X.KG x x)
    (body : List Instr) (hp : ∀ i ∈ body, instrInProfile i) : IRels X body body := by
  have h := irels_ren_fwd X ⟨id, id⟩ (fun _ => True) (fun _ => True)
    (fun x _ => by simpa [Ren.funcIdx] using hf x.toNat)
    (fun x _ => by simpa [Ren.globalIdx] using hg x.toNat) body hp
    (fun _ _ => trivial) (fun _ _ => trivial)
  simpa [Ren.instrs, List.map_congr_left (fun i _ => rename_identity i)] using h

def instanceOf (s : Store H) (ts : List RecType) (fs : List Func) (xi : List ExportInst) :
    ModuleInst :=
  {types := allocTypes ts, funcs := (List.range fs.length).map (s.funcs.length + ·), exports := xi}

def installed (s : Store H) (fs : List Func) (ft : List DefType) (mi : ModuleInst) : Store H :=
  {s with funcs := s.funcs ++ (ft.zip fs).map fun p => ⟨p.1, mi, .wasm p.2⟩}

theorem MIrec_bare (s : Store H) (ts : List RecType) (fs : List Func)
    (es : List Export) (xi : List ExportInst) :
    MIrec s (bare ts fs es) [] [] xi = instanceOf s ts fs xi := by
  simp [MIrec, tmpStore, gtys, bare, instanceOf, ExternAddr.tags,
    ExternAddr.globals, ExternAddr.mems, ExternAddr.tables, ExternAddr.funcs]

theorem STrec_bare (s : Store H) (ts : List RecType) (fs : List Func)
    (es : List Export) (ft : List DefType) (mi : ModuleInst) :
    STrec s (bare ts fs es) [] ft mi = installed s fs ft mi := by
  simp [STrec, tmpStore, gtys, bare, installed]

def projectionCtx (s : Store H) (ts : List RecType) (fs : List Func)
    (xiA xiB : List ExportInst) : SimCtx :=
  mkCtx s.funcs.length s.globals.length Eq Eq (instanceOf s ts fs xiA) (instanceOf s ts fs xiB)

theorem projectionCtx_wf (s : Store H) (ts : List RecType) (fs : List Func)
    (xiA xiB : List ExportInst) : (projectionCtx s ts fs xiA xiB).WF := by
  unfold projectionCtx
  refine mkCtx_wf (MA := instanceOf s ts fs xiA) (MB := instanceOf s ts fs xiB)
    rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_
  · rintro x y a rfl ha
    exact ⟨a, ha⟩
  · rintro x y a rfl ha
    exact ⟨a, ha⟩
  · exact fun _ _ _ h h' => h.symm.trans h'
  · exact fun _ _ _ h h' => h.trans h'.symm
  · exact .nil
  · exact .nil

theorem instance_func_lookup {s : Store H} {ts : List RecType} {fs : List Func}
    {xi : List ExportInst} {x a : Nat} (h : (instanceOf s ts fs xi).funcs[x]? = some a) :
    x < fs.length ∧ a = s.funcs.length + x := by
  obtain ⟨hx, he⟩ := List.getElem?_eq_some_iff.mp h
  have hx' : x < fs.length := by simpa [instanceOf] using hx
  refine ⟨hx', ?_⟩
  simpa [instanceOf] using he.symm

theorem installed_func {s : Store H} {fs : List Func} {ft : List DefType}
    {mi : ModuleInst} {x : Nat} {d : DefType} {fn : Func}
    (hd : ft[x]? = some d) (hf : fs[x]? = some fn) :
    (installed s fs ft mi).funcs[s.funcs.length + x]? = some ⟨d, mi, .wasm fn⟩ :=
  STrec_hi_funcs (N := bare [] fs []) (vals := []) hd hf

theorem installed_related {s : Store H} (hs : StoreOk s) {ts : List RecType} {fs : List Func}
    {ft : List DefType} (hft : fs.mapM (fun fn => (allocTypes ts)[fn.type.toNat]?) = some ft)
    (hnum : ∀ d ∈ allocTypes ts, NumParams d)
    (hbody : ∀ fn ∈ fs, ∀ i ∈ fn.body, instrInProfile i) (xiA xiB : List ExportInst) :
    StoreRel (projectionCtx s ts fs xiA xiB)
      (installed s fs ft (instanceOf s ts fs xiA))
      (installed s fs ft (instanceOf s ts fs xiB)) := by
  have hl := mapM_length hft
  have own : ∀ x, x < fs.length → ∃ fn d, fs[x]? = some fn ∧ ft[x]? = some d ∧
      d ∈ allocTypes ts := by
    intro x hx
    obtain ⟨fn, hfn⟩ : ∃ fn, fs[x]? = some fn := ⟨_, List.getElem?_eq_getElem hx⟩
    obtain ⟨d, hd⟩ : ∃ d, ft[x]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have ht := mapM_getElem? hft x
    rw [hd, hfn, Option.bind_some] at ht
    exact ⟨fn, d, hfn, hd, List.mem_of_getElem? ht.symm⟩
  refine ⟨rfl, ?_, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact (List.getElem?_append_left ha).trans (List.getElem?_append_left ha).symm
  · rintro a b ⟨x, y, rfl, ha, hb⟩
    obtain ⟨hx, rfl⟩ := instance_func_lookup ha
    obtain ⟨_, hbe⟩ := instance_func_lookup hb
    subst b
    obtain ⟨fn, d, hf, hd, _⟩ := own x hx
    refine .inr ⟨by change s.funcs.length ≤ _; omega,
      by change s.funcs.length ≤ _; omega, _, _, fn, fn,
      installed_func hd hf, installed_func hd hf, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    exact irels_identity _ (fun _ => rfl) (fun _ => rfl) _
      (hbody fn (List.mem_of_getElem? hf))
  · rintro a b ⟨x, y, _, ha, _⟩
    simp [instanceOf] at ha
  · have h := STrec_storeF (N := bare ts fs []) (vals := []) (ft := ft)
      (mi := instanceOf s ts fs xiA) hs (bare_profiled ts fs []) (by simp)
    rw [STrec_bare] at h
    exact h
  · rintro a b ⟨x, y, rfl, ha, _⟩ fi hfi
    obtain ⟨hx, rfl⟩ := instance_func_lookup ha
    obtain ⟨fn, d, hf, hd, hmem⟩ := own x hx
    rw [installed_func hd hf] at hfi
    cases hfi
    exact hnum d hmem

theorem allocated_export_self {E : ModuleInst} {F : Nat → Nat → Prop}
    (hf : ∀ x : FuncIdx, ∀ a, E.funcs[x.toNat]? = some a → F a a)
    {e : Export} {ei : ExportInst} (h : allocExport? E e = some ei) : XRel F ei ei := by
  cases e with
  | mk name index =>
    cases index with
    | func x =>
      simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨rfl, .inl ⟨a, a, rfl, rfl, hf x a ha⟩⟩
    | _ =>
      simp only [allocExport?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h
      obtain ⟨a, _, rfl⟩ := h
      exact ⟨rfl, .inr ⟨by simp, by simp⟩⟩

theorem allocated_exports_self {E : ModuleInst} {F : Nat → Nat → Prop}
    (hf : ∀ x : FuncIdx, ∀ a, E.funcs[x.toNat]? = some a → F a a) :
    ∀ {es : List Export} {xi : List ExportInst}, es.mapM (allocExport? E) = some xi →
      List.Forall₂ (XRel F) xi xi
  | [], xi, h => by
    have he : xi = [] := by simpa using h.symm
    subst xi
    exact .nil
  | e :: es, xi, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨ei, he, rest, hr, rfl⟩ := h
    exact .cons (allocated_export_self hf he) (allocated_exports_self hf hr)

theorem projection_exports {s : Store H} {ts : List RecType} {fs : List Func}
    {es : List Export} {xi : List ExportInst}
    (hxi : es.mapM (allocExport? (EIrec s (bare ts fs es) [] [])) = some xi)
    (names : List String) :
    ExportsRelOn (· ∈ names)
      (projectionCtx s ts fs xi (xi.filter fun e => names.contains e.name)) ∧
    ExportsRelOn (· ∈ names)
      (projectionCtx s ts fs (xi.filter fun e => names.contains e.name) xi) := by
  have self : ∀ x a, exportFunc? (instanceOf s ts fs xi) x = some a →
      (projectionCtx s ts fs xi xi).F a a := by
    intro x a ha
    have rel := allocated_exports_self (F := (projectionCtx s ts fs xi xi).F)
      (fun idx addr had => ⟨idx.toNat, idx.toNat, rfl, had, had⟩) hxi
    obtain ⟨b, hb, hab⟩ := (exportFunc?_rel rel x).1 a ha
    change exportFunc? (instanceOf s ts fs xi) x = some b at hb
    rw [ha] at hb
    cases hb
    exact hab
  have lookup : ∀ x ∈ names,
      exportFunc? (instanceOf s ts fs (xi.filter fun e => names.contains e.name)) x =
        exportFunc? (instanceOf s ts fs xi) x :=
    fun _ hx => exportFunc_filter names (instanceOf s ts fs xi) hx
  constructor
  · refine ⟨?_, ?_⟩
    · intro x hx a ha
      exact ⟨a, (lookup x hx).trans ha, self x a ha⟩
    · intro x hx b hb
      exact ⟨b, (lookup x hx).symm.trans hb⟩
  · refine ⟨?_, ?_⟩
    · intro x hx a ha
      have ha' := (lookup x hx).symm.trans ha
      exact ⟨a, ha', self x a ha'⟩
    · intro x hx b hb
      exact ⟨b, (lookup x hx).trans hb⟩

/-- Actual source and export-projected instantiations, related in both directions.
No whole-store equality is asserted: allocated functions capture different
module-instance export lists. -/
theorem bare_projection_pair (ts : List RecType) (fs : List Func) (es : List Export)
    (names : List String) (hp : (tree (bare ts fs es)).inProfileBase = true)
    (hn : numSigs (tree (bare ts fs es)) = true)
    (hA : ModuleValid (bare ts fs es)) (hB : ModuleValid (project names (bare ts fs es)))
    (s : Store H) (hs : StoreOk s) :
    ∃ (cA cB : Config H) (X Y : SimCtx),
      Instantiate P closedHost s (bare ts fs es) [] cA ∧
      Instantiate P closedHost s (project names (bare ts fs es)) [] cB ∧
      X.WF ∧ Y.WF ∧ ExportsRelOn (· ∈ names) X ∧ ExportsRelOn (· ∈ names) Y ∧
      ConfRel X .ours cA cB ∧ ConfRel Y .ours cB cA ∧
      cA.frame.module = X.MA ∧ cB.frame.module = X.MB ∧
      cB.frame.module = Y.MA ∧ cA.frame.module = Y.MB := by
  obtain ⟨xtE, hmA⟩ := valid_closed rfl hA
  obtain ⟨xtEB, hmB⟩ := valid_closed rfl hB
  have hmLift : ModuleOk (tree (bare ts fs es)).lower ⟨[], xtE⟩ := by
    rw [tree_lower]
    exact hmA
  obtain ⟨vals, ft, xi, hv, hf, hx⟩ := src_data hp rfl (s := s) hmLift (.nil)
  rw [tree_lower] at hv hf hx
  have hv0 : vals = [] := by simpa only [bare, List.map_nil, gv] using Option.some.inj hv.symm
  subst vals
  let xiB := xi.filter fun e => names.contains e.name
  have hxB : (project names (bare ts fs es)).exports.mapM
      (allocExport? (EIrec s (project names (bare ts fs es)) [] [])) = some xiB :=
    allocExports_project _ names hx
  have instA := inst_of_closed (P := P) (host := closedHost)
    (bare_profiled ts fs es) rfl ⟨xtE, [], hmA, .nil⟩ rfl hf hx
  have instB := inst_of_closed (P := P) (host := closedHost)
    (bare_profiled ts fs (es.filter fun e => names.contains e.name)) rfl
    ⟨xtEB, [], hmB, .nil⟩ rfl hf hxB
  let cA : Config H := ⟨installed s fs ft (instanceOf s ts fs xi),
    {module := instanceOf s ts fs xi}, []⟩
  let cB : Config H := ⟨installed s fs ft (instanceOf s ts fs xiB),
    {module := instanceOf s ts fs xiB}, []⟩
  have instA' : Instantiate P closedHost s (bare ts fs es) [] cA := by
    simpa only [MIrec_bare, STrec_bare, startCode_bare] using instA
  have instB' : Instantiate P closedHost s (project names (bare ts fs es)) [] cB := by
    change Instantiate P closedHost s
      (bare ts fs (es.filter fun e => names.contains e.name)) [] cB
    simpa only [MIrec_bare, STrec_bare, startCode_bare] using instB
  have hnum := numParams_types (m := tree (bare ts fs es)) (numSigs_sound hn)
  have hbody := (BModule.inProfileBase_sound hp).code
  rw [tree_lower] at hbody
  have hstore := installed_related hs hf hnum hbody xi xiB
  have hstore' := installed_related hs hf hnum hbody xiB xi
  obtain ⟨he, he'⟩ := projection_exports hx names
  refine ⟨cA, cB, projectionCtx s ts fs xi xiB, projectionCtx s ts fs xiB xi,
    instA', instB', projectionCtx_wf _ _ _ _ _, projectionCtx_wf _ _ _ _ _,
    he, he', ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact ⟨hstore, ⟨rfl, rfl, rfl, by simp [localsF, cA]⟩, .nil⟩
  · exact ⟨hstore', ⟨rfl, rfl, rfl, by simp [localsF, cB]⟩, .nil⟩

/-- Export projection preserves original-source observations exactly on selected
names, for every same (possibly nondeterministic) profile and valid ambient store. -/
theorem project_observations {m : Module} {names : List String} (hsup : supported m = true)
    (valid : ModuleValid m) (projectedValid : ModuleValid (project names m))
    (s : Store H) (imports : List ExternAddr) (hs : StoreOk s)
    (script : List Call) (on : ScriptOn (· ∈ names) script) :
    moduleObs P closedHost s imports m script =
      moduleObs P closedHost s imports (project names m) script := by
  have hm := supported_bare hsup
  have checks := hsup
  simp only [supported, Bool.and_eq_true, and_assoc] at checks
  obtain ⟨_, _, _, _, _, _, _, _, hp, hn⟩ := checks
  rw [hm] at valid projectedValid hp hn ⊢
  obtain ⟨cA, cB, X, Y, hiA, hiB, hX, hY, hE, hE', hrel, hrel', hMA, hMB, hMY, hMY'⟩ :=
    bare_projection_pair _ _ _ names hp hn valid projectedValid s hs
  apply Set.ext
  intro bs
  constructor
  · intro hb
    have empty := no_imports (m := bare m.types m.funcs m.exports) rfl hb.choose_spec.1
    subst imports
    exact obs_sim_on on (fun c hc => by
      obtain rfl := inst_det hc hiA
      exact ⟨X, cB, hX, hE, hiB, hrel, hMA, hMB⟩) bs hb
  · intro hb
    have empty := no_imports (m := project names (bare m.types m.funcs m.exports)) rfl hb.choose_spec.1
    subst imports
    exact obs_sim_on on (fun c hc => by
      obtain rfl := inst_det hc hiB
      exact ⟨Y, cA, hY, hE', hiA, hrel', hMY, hMY'⟩) bs hb

theorem project_admission {m : Module} {names : List String} (hsup : supported m = true)
    (valid : ModuleValid m) (projectedValid : ModuleValid (project names m))
    (s : Store H) (imports : List ExternAddr) (hs : StoreOk s) :
    (∃ c, Instantiate P closedHost s m imports c) ↔
      ∃ c, Instantiate P closedHost s (project names m) imports c := by
  have hm := supported_bare hsup
  have checks := hsup
  simp only [supported, Bool.and_eq_true, and_assoc] at checks
  obtain ⟨_, _, _, _, _, _, _, _, hp, hn⟩ := checks
  rw [hm] at valid projectedValid hp hn ⊢
  obtain ⟨cA, cB, _, _, hiA, hiB, _⟩ :=
    bare_projection_pair _ _ _ names hp hn valid projectedValid s hs
  constructor
  · rintro ⟨c, hi⟩
    obtain rfl := no_imports rfl hi
    exact ⟨cB, hiB⟩
  · rintro ⟨c, hi⟩
    obtain rfl := no_imports rfl hi
    exact ⟨cA, hiA⟩

end Silmaril.Wasm.Binaryen.Toolkit.MetaDCE
