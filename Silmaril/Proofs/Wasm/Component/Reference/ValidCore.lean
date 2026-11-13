module

public import Silmaril.Proofs.Wasm.Component.Reference.InstCore
public import Silmaril.Wasm.SingleThreaded.Soundness
public import Silmaril.Raw.Wasm.Component.Validation.Check
public import Silmaril.Raw.Wasm.Component.Reference

/-!
# The core export types the validator sees for `Simple.toRef`

The reference validator types `alias core export 0 n func` by the export `n` of the core module
type `core3ModuleType? c.mod.mod`. For a component whose module is instantiated as the IR assumes
(`Simple.Inst`) this export is the IR's flat function type of the lifted core export
(`coreExport_flat`): both the validator and the instance read the function's defined type from
the module's type section (`ModuleOk` and `allocModule?`), and the instance's export types are
the interface's (`IsInstance.exportTypes`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Component.Validation (core3ModuleType? core3FlatType? core3NumOf? Core3Extern)

/-! ## Numeric views of a defined type -/

/-- Two numeric readings of the same value types agree. -/
theorem numOf_eq_scalar : ∀ {ps : List CValType} {a : List NumType} {b : List NumType},
    ps.mapM core3NumOf? = some a →
      ps.mapM Silmaril.Wasm.Game.ScalarType.ofC? = some (b.map .num) → a = b
  | [], a, b, ha, hb => by
    have ha' : a = [] := (Option.some.inj ha).symm
    have hb' : b.map Silmaril.Wasm.Game.ScalarType.num = [] := (Option.some.inj hb).symm
    rw [ha', List.map_eq_nil_iff.1 hb']
  | p :: ps, a, b, ha, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ha hb
    obtain ⟨x, hx, xs, hxs, rfl⟩ := ha
    obtain ⟨y, hy, ys, hys, hb⟩ := hb
    cases p with
    | num t =>
      have hxt : x = t := (Option.some.inj hx).symm
      have hyt : y = .num t := (Option.some.inj hy).symm
      cases b with
      | nil => cases hb
      | cons b bs =>
        obtain ⟨h₁, h₂⟩ := List.cons.inj hb
        have hb₀ : b = t := by rw [hyt] at h₁; exact (Silmaril.Wasm.Game.ScalarType.num.inj h₁).symm
        rw [hxt, hb₀, numOf_eq_scalar hxs (h₂ ▸ hys)]
    | _ => cases hx

/-- The validator's flat view of a defined type whose game view is `fnOf ft` is `ft`. -/
theorem core3FlatType?_of_fn {d : DefType} {v : V1.FuncType} {ft : CoreFuncTy}
    (hv : core3FlatType? d = some v)
    (hf : Silmaril.Wasm.Game.FnType.ofDefType? d = some (fnOf ft)) :
    v = ⟨ft.params, ft.results⟩ := by
  unfold core3FlatType? at hv
  unfold Silmaril.Wasm.Game.FnType.ofDefType? at hf
  simp only [Option.bind_eq_bind] at hv hf
  obtain ⟨⟨ps, rs⟩, hd, hv'⟩ := Option.bind_eq_some_iff.1 hv
  obtain ⟨⟨ps', rs'⟩, hd', hf'⟩ := Option.bind_eq_some_iff.1 hf
  obtain ⟨rfl, rfl⟩ : ps' = ps ∧ rs' = rs := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hd'.symm.trans hd
  obtain ⟨a, ha, hv₂⟩ := Option.bind_eq_some_iff.1 hv'
  obtain ⟨b, hb, hv₃⟩ := Option.bind_eq_some_iff.1 hv₂
  obtain ⟨sa, hsa, hf₂⟩ := Option.bind_eq_some_iff.1 hf'
  obtain ⟨sb, hsb, hf₃⟩ := Option.bind_eq_some_iff.1 hf₂
  have hfn : (⟨sa, sb⟩ : Silmaril.Wasm.Game.FnType) = fnOf ft := Option.some.inj hf₃
  have hsa' : sa = ft.params.map .num := congrArg Silmaril.Wasm.Game.FnType.params hfn
  have hsb' : sb = ft.results.map .num := congrArg Silmaril.Wasm.Game.FnType.results hfn
  have hvv : v = ⟨a, b⟩ := by
    split at hv₃
    · exact (Option.some.inj hv₃).symm
    · cases hv₃
  rw [hvv, numOf_eq_scalar ha (hsa' ▸ hsa), numOf_eq_scalar hb (hsb' ▸ hsb)]

/-! ## Exports: allocation and validation side by side -/

/-- An allocated function export is at the instance's function of its index. -/
theorem allocExport?_func {ei : ModuleInst} {e : Silmaril.Wasm.Export} {x : ExportInst}
    {i : FuncIdx} (hx : allocExport? ei e = some x) (hidx : e.index = .func i) :
    ∃ b, ei.funcs[i.toNat]? = some b ∧ x.addr = .func b := by
  have hx' : (ei.funcs[i.toNat]?.map ExternAddr.func).map (⟨e.name, ·⟩) = some x := by
    unfold allocExport? at hx
    rw [hidx] at hx
    exact hx
  obtain ⟨v, hv', hxv⟩ := Option.map_eq_some_iff.1 hx'
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hv'
  exact ⟨b, hb, by rw [← hxv]⟩

/-- The head case of `lookup_alloc_valid`. -/
theorem lookup_alloc_head {ei : ModuleInst} {C : Context} {e : Silmaril.Wasm.Export} {x : ExportInst}
    {xt : CExternType} {es : List Silmaril.Wasm.Export} {xts : List CExternType} {n : String} {a : Nat}
    (hx : allocExport? ei e = some x) (hv : ExportOk C e xt) (hn : n = e.name)
    (hxa : x.addr = .func a) :
    ∃ (idx : Nat) (d : DefType), ei.funcs[idx]? = some a ∧ C.funcs[idx]? = some d ∧
      (((e :: es).zip (xt :: xts)).map fun p => (p.1.name, p.2)).lookup n = some (.func d) := by
  cases hidx : e.index with
  | func i =>
    obtain ⟨b, hb, hxb⟩ := allocExport?_func hx hidx
    have hab : b = a := ExternAddr.func.inj (hxb.symm.trans hxa)
    have hvx : ExternIdxOk C (.func i) xt := hidx ▸ hv
    cases hvx with
    | func hd =>
      refine ⟨i.toNat, _, hab ▸ hb, hd, ?_⟩
      simp only [List.zip_cons_cons, List.map_cons, List.lookup_cons, hn, beq_self_eq_true]
  | _ =>
    exact absurd hxa ((allocExport?_name hx).2.2 (fun i e' => by rw [hidx] at e'; cases e') a)

/-- The export named `n` of an instance allocated from `es` is a function `a` exactly where the
validator's export `n` of `es` is the function type of the same index. -/
theorem lookup_alloc_valid {ei : ModuleInst} {C : Context} :
    ∀ {es : List Silmaril.Wasm.Export} {xi : List ExportInst} {xts : List CExternType},
      List.Forall₂ (fun e x => allocExport? ei e = some x) es xi →
      List.Forall₂ (ExportOk C) es xts → (es.map (·.name)).Nodup →
      ∀ {n : String} {a : Nat}, (xi.map fun x => (x.name, x.addr)).lookup n = some (.func a) →
        ∃ (idx : Nat) (d : DefType), ei.funcs[idx]? = some a ∧ C.funcs[idx]? = some d ∧
          ((es.zip xts).map fun p => (p.1.name, p.2)).lookup n = some (.func d)
  | [], [], [], .nil, .nil, _, n, a, h => by simp at h
  | e :: es, x :: xi, xt :: xts, .cons hx hxi, .cons hv hvs, hnd, n, a, h => by
    have hnd' : e.name ∉ es.map (·.name) ∧ (es.map (·.name)).Nodup := List.nodup_cons.1 hnd
    have hxn : x.name = e.name := (allocExport?_name hx).1
    by_cases hn : n = e.name
    · have hxa : x.addr = .func a := by
        simpa only [List.map_cons, List.lookup_cons, hxn, hn, beq_self_eq_true,
          Option.some.injEq] using h
      exact lookup_alloc_head hx hv hn hxa
    · have hne : (n == e.name) = false := by simpa only [beq_eq_false_iff_ne] using hn
      have h' : (xi.map fun x => (x.name, x.addr)).lookup n = some (.func a) := by
        simpa only [List.map_cons, List.lookup_cons, hxn, hne] using h
      obtain ⟨idx, d, h₁, h₂, h₃⟩ := lookup_alloc_valid hxi hvs hnd'.2 h'
      refine ⟨idx, d, h₁, h₂, ?_⟩
      simpa only [List.zip_cons_cons, List.map_cons, List.lookup_cons, hne] using h₃

/-! ## The store of the instance -/

/-- `prepare?` ends with `allocModule?`. -/
theorem prepare?_allocModule {s : Store Nat} {m : Module} {xas : List ExternAddr} {c : Config Nat}
    {st : Option FuncIdx} (hp : prepare? evalConst? s m xas = some (c, st)) :
    ∃ s₃ vg rt re s₄ mi, allocModule? s₃ m xas vg rt re = some (s₄, mi) ∧ c.store = s₄ ∧
      c.frame.module = mi := by
  unfold prepare? at hp
  split at hp
  · split at hp
    · cases hp
    split at hp
    · cases hp
    split at hp
    · cases hp
    split at hp
    · cases hp
    next =>
      rename_i s₃ _ _ _ _ s₄ mi hM
      obtain ⟨hc, -⟩ := Prod.mk.inj (Option.some.inj hp)
      rw [← hc]
      exact ⟨s₃, _, _, _, s₄, mi, hM, rfl, rfl⟩
  · cases hp

/-- `prepare?` allocates the module's functions after the existing ones, with the defined
types of their type indices, and allocates the exports from an instance whose functions are
those addresses. -/
theorem prepare?_alloc {s : Store Nat} {m : Module} {xas : List ExternAddr} {c : Config Nat}
    {st : Option FuncIdx} (hx : ExternAddr.funcs xas = [])
    (hp : prepare? evalConst? s m xas = some (c, st)) :
    ∃ (ei : ModuleInst) (pre : List (FuncInst Nat)) (funcTypes : List DefType) (mi : ModuleInst),
      List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports c.frame.module.exports ∧
      ei.funcs = (List.range m.funcs.length).map (pre.length + ·) ∧
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes ∧
      c.store.funcs = pre ++ (funcTypes.zip m.funcs).map (fun p => ⟨p.1, mi, .wasm p.2⟩) := by
  obtain ⟨s₃, vg, rt, re, s₄, mi, hM, hs, hf⟩ := prepare?_allocModule hp
  obtain ⟨tagTypes, funcTypes, xi, -, hft, hX, hmi, hs₄⟩ := allocModule?_inv hM
  have hF := mapM_forall₂ hX
  have hex : c.frame.module.exports = xi := by rw [hf, hmi]
  have hfs : c.store.funcs = s₃.funcs ++
      (funcTypes.zip m.funcs).map (fun p => (⟨p.1, mi, .wasm p.2⟩ : FuncInst Nat)) := by
    rw [hs, hs₄]
  rw [hex]
  exact ⟨_, s₃.funcs, funcTypes, mi, hF, by simp only [hx, List.nil_append], hft, hfs⟩

/-- Host-free runs never change the function instances (as
`Silmaril.Proofs.Wasm.Game.steps_funcs_eq`, which is not exported by a header). -/
theorem steps_funcs_eq' {P : Silmaril.Wasm.Numerics.Profile} {c c' : Config Nat}
    (h : Steps P (fun _ _ _ _ => False) c c') : c'.store.funcs = c.store.funcs := by
  induction h with
  | refl => rfl
  | tail _ hst ih => exact (SingleThreaded.Step.framesLocal hst).1.trans ih

/-- The function store of an instance made in the empty store: the module's functions after a
prefix, with the defined types of their type indices; the exports are allocated from an
instance whose functions are their addresses. -/
theorem once_alloc {m : Module} {s' : Store Nat} {f : Frame} {st : Option FuncIdx}
    (h : instantiateOnce? ({} : Store Nat) m [] = some (s', f, st)) :
    ∃ (ei : ModuleInst) (pre : List (FuncInst Nat)) (funcTypes : List DefType) (mi : ModuleInst),
      List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports f.module.exports ∧
      ei.funcs = (List.range m.funcs.length).map (pre.length + ·) ∧
      m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some funcTypes ∧
      s'.funcs = pre ++ (funcTypes.zip m.funcs).map (fun p => ⟨p.1, mi, .wasm p.2⟩) := by
  unfold instantiateOnce? at h
  split at h
  · cases h
  · obtain ⟨c, hp, hf⟩ := prepareDirect?_frame h
    obtain ⟨c', hp', hS⟩ := prepareDirect?_steps
      (P := SingleThreaded.profile SingleThreaded.neverFail) (host := fun _ _ _ _ => False)
      evalConst?_evalSound h
    have hcc : c' = c := by
      rw [hp] at hp'
      exact (Prod.mk.inj (Option.some.inj hp')).1.symm
    have hfuncs : s'.funcs = c.store.funcs := hcc ▸ steps_funcs_eq' hS
    have hx : ExternAddr.funcs ([] ++ globalAddrs ({} : Store Nat).globals.length
        m.globals.length) = [] := by
      rw [ExternAddr.funcs_append, ExternAddr.funcs_globalAddrs]
      rfl
    obtain ⟨ei, pre, fts, mi, hF, hei, hft, hfs⟩ := prepare?_alloc hx hp
    exact ⟨ei, pre, fts, mi, hf ▸ hF, hei, hft, hfuncs.trans hfs⟩

/-! ## Assembling the two sides -/

theorem lookup_map_snd {α β : Type} (g : α → β) :
    ∀ (l : List (String × α)) (n : String),
      (l.map fun p => (p.1, g p.2)).lookup n = (l.lookup n).map g
  | [], _ => rfl
  | (k, a) :: l, n => by
    by_cases h : n = k
    · simp only [List.map_cons, List.lookup_cons, h, beq_self_eq_true, Option.map_some]
    · have hb : (n == k) = false := by simpa only [beq_eq_false_iff_ne] using h
      simp only [List.map_cons, List.lookup_cons, hb, lookup_map_snd g l n]

/-- The function allocated at address `a = ei.funcs[idx]` has the type `funcTypes[idx]`. -/
theorem store_type {ei : ModuleInst} {pre : List (FuncInst Nat)} {fts : List DefType}
    {mi : ModuleInst} {fs : List Func} {s' : Store Nat} {idx a : Nat}
    (hei : ei.funcs = (List.range fs.length).map (pre.length + ·)) (hlen : fts.length = fs.length)
    (hfs : s'.funcs = pre ++ (fts.zip fs).map (fun p => ⟨p.1, mi, .wasm p.2⟩))
    (hidx : ei.funcs[idx]? = some a) :
    ∃ fi, s'.funcs[a]? = some fi ∧ fts[idx]? = some fi.type := by
  have hia : idx < fs.length ∧ a = pre.length + idx := by
    rw [hei, List.getElem?_map] at hidx
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hidx
    obtain ⟨hl, hb'⟩ := List.getElem?_eq_some_iff.1 hb
    rw [List.getElem_range] at hb'
    rw [List.length_range] at hl
    exact ⟨hl, by rw [hb']⟩
  obtain ⟨hlt, rfl⟩ := hia
  have hlt' : idx < fts.length := hlen ▸ hlt
  refine ⟨⟨fts[idx], mi, .wasm fs[idx]⟩, ?_, by rw [List.getElem?_eq_getElem hlt']⟩
  have hz : (fts.zip fs)[idx]? = some (fts[idx], fs[idx]) := by
    rw [List.getElem?_eq_getElem (by rw [List.length_zip, hlen, Nat.min_self]; exact hlt),
      List.getElem_zip]
  rw [hfs, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_map, hz]
  rfl

/-- The export types of an instance at interface export `k`. -/
theorem export_type_at {I : Silmaril.Wasm.Game.ScalarInstance} {ifc : CoreIface} {k : Nat}
    {nm : String} {ft : CoreFuncTy} {fi : FuncInst Nat} {d : DefType}
    (hT : List.Forall₂ (fun a ft => ∃ fi : FuncInst Nat, I.store.funcs[a]? = some fi ∧
      Silmaril.Wasm.Game.FnType.ofDefType? fi.type = some ft) I.addrs I.exports)
    (hexp : I.exports = ifc.map fun p => fnOf p.2) (hk : ifc[k]? = some (nm, ft))
    (hfi : I.store.funcs[I.addrs.getD k 0]? = some fi) (hd : fi.type = d) :
    Silmaril.Wasm.Game.FnType.ofDefType? d = some (fnOf ft) := by
  have hke : I.exports[k]? = some (fnOf ft) := by
    rw [hexp, List.getElem?_map, hk]
    rfl
  have hkl : k < I.exports.length := (List.getElem?_eq_some_iff.1 hke).1
  have hka : k < I.addrs.length := hT.length_eq ▸ hkl
  have hget := hT.get hka hkl
  obtain ⟨fi', hfi', hty'⟩ := hget
  have hga : I.addrs.getD k 0 = I.addrs[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hka, Option.getD_some]
  have hfi₂ : I.store.funcs[I.addrs[k]]? = some fi := by rw [← hga]; exact hfi
  have hfe : fi' = fi := Option.some.inj (hfi'.symm.trans hfi₂)
  have hex : I.exports[k] = fnOf ft := Option.some.inj ((List.getElem?_eq_getElem hkl).symm.trans hke)
  rw [← hd, ← hfe]
  simpa only [List.get_eq_getElem, hex] using hty'

/-- **The instance side**: the export named by interface export `k` is a function `a` of the
instance, allocated (as `ei.funcs[idx]`) with the defined type of its type index, whose game
view is the interface type. -/
theorem inst_export_type {c : Simple} (hi : c.Inst) {k : Nat} {nm : String} {ft : CoreFuncTy}
    (hk : c.mod.exports[k]? = some (nm, ft)) :
    ∃ (mt : CModuleType) (xi : List ExportInst) (ei : ModuleInst) (fts : List DefType) (a : Nat),
      validate? c.mod.mod = some mt ∧ mt.imports = [] ∧
      List.Forall₂ (fun e x => allocExport? ei e = some x) c.mod.mod.exports xi ∧
      (xi.map fun x => (x.name, x.addr)).lookup nm = some (.func a) ∧
      c.mod.mod.funcs.mapM (fun fn => (allocTypes c.mod.mod.types)[fn.type.toNat]?) = some fts ∧
      ∀ idx : Nat, ei.funcs[idx]? = some a → ∀ d : DefType, fts[idx]? = some d →
        Silmaril.Wasm.Game.FnType.ofDefType? d = some (fnOf ft) := by
  obtain ⟨I, ⟨mt, hIs⟩, himp, hexp⟩ := hi.inst
  have hmt : mt.imports = [] :=
    nil_of_funcs_nil hIs.funcImports (List.forall₂_nil_right_iff.1 (himp ▸ hIs.importTypes))
  obtain ⟨f, hf, haddr⟩ := hIs.instantiated
  have hf₀ : instantiateOnce? ({} : Store Nat) c.mod.mod [] = some (I.store, f, none) := by
    rw [← hf, hmt]
    rfl
  have hlk := lookup_funcExport hi hIs.valid hf₀ haddr hk
  obtain ⟨ei, pre, fts, mi, hF, hei, hft, hfs⟩ := once_alloc hf₀
  refine ⟨mt, _, ei, fts, _, hIs.valid, hmt, hF, hlk, hft, fun idx hidx d hd => ?_⟩
  have hlen : fts.length = c.mod.mod.funcs.length := (mapM_forall₂ hft).length_eq.symm
  obtain ⟨fi, hfi, hty⟩ := store_type hei hlen hfs hidx
  exact export_type_at hIs.exportTypes hexp hk hfi (Option.some.inj (hty.symm.trans hd))

/-- The `idx`-th function of an import-free valid module has the defined type of its type index,
as validation types it (`FuncOk`) and as instantiation allocates it (`allocTypes`). -/
theorem funcs_type {m : Module} {dts fdts fts : List DefType} {C : Context} {idx : Nat}
    {d : DefType} (htypes : TypesOk {} m.types dts) (hCt : C.types = dts)
    (hfuncs : List.Forall₂ (FuncOk C) m.funcs fdts) (hd : fdts[idx]? = some d)
    (hft : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some fts) :
    fts[idx]? = some d := by
  have hl₁ : idx < fdts.length := (List.getElem?_eq_some_iff.1 hd).1
  have hl₀ : idx < m.funcs.length := hfuncs.length_eq ▸ hl₁
  have hF := mapM_forall₂ hft
  have hl₂ : idx < fts.length := hF.length_eq ▸ hl₀
  have hok : FuncOk C m.funcs[idx] fdts[idx] := hfuncs.get hl₀ hl₁
  have hA : (allocTypes m.types)[m.funcs[idx].type.toNat]? = some fts[idx] := hF.get hl₀ hl₂
  have hdd : fdts[idx] = d := Option.some.inj ((List.getElem?_eq_getElem hl₁).symm.trans hd)
  cases hok with
  | mk hty _ _ _ =>
    have hty' : dts[m.funcs[idx].type.toNat]? = some fdts[idx] := by
      rw [← hCt]
      exact hty
    rw [allocTypes_eq htypes, hty'] at hA
    rw [List.getElem?_eq_getElem hl₂, ← Option.some.inj hA, hdd]

/-- **The validator side**: the validator's export named `nm` of an import-free module is the
function type of the function allocated at its address. -/
theorem valid_export_type {m : Module} {mt : CModuleType} {ei : ModuleInst}
    {xi : List ExportInst} {fts : List DefType} {nm : String} {a : Nat}
    (hv : validate? m = some mt) (hmt : mt.imports = [])
    (hF : List.Forall₂ (fun e x => allocExport? ei e = some x) m.exports xi)
    (hlk : (xi.map fun x => (x.name, x.addr)).lookup nm = some (.func a))
    (hft : m.funcs.mapM (fun fn => (allocTypes m.types)[fn.type.toNat]?) = some fts) :
    ∃ (idx : Nat) (d : DefType), ei.funcs[idx]? = some a ∧ fts[idx]? = some d ∧
      ((m.exports.zip mt.exports).map fun p => (p.1.name, p.2)).lookup nm = some (.func d) := by
  have hmok : ModuleOk m ⟨mt.imports, mt.exports⟩ := validate?_sound hv
  cases hmok with
  | mk htypes _ hC' hC _ _ _ _ hfuncs _ _ _ hexports hdisjoint =>
    obtain ⟨idx, d, h₁, h₂, h₃⟩ := lookup_alloc_valid hF hexports hdisjoint hlk
    subst hC hC'
    have h₂' : _ := h₂
    rw [hmt] at h₂'
    exact ⟨idx, d, h₁, funcs_type htypes rfl hfuncs h₂' hft, h₃⟩

/-- **The flat type of the aliased core export**: in the core module type of `Simple.Inst`
component's module, the export named by interface export `k` is a function whose flat view is
the interface type. -/
theorem coreExport_flat {c : Simple} (hi : c.Inst) {k : Nat} {nm : String} {ft : CoreFuncTy}
    (hk : c.mod.exports[k]? = some (nm, ft))
    {t : Silmaril.Wasm.Component.Types.CoreModuleType Core3Extern}
    (ht : core3ModuleType? c.mod.mod = some t) {y : Core3Extern} (hy : t.exports.lookup nm = some y)
    {v : V1.FuncType}
    (hv : Silmaril.Wasm.Component.Validation.core3Profile.view.core.funcType? y = some v) :
    v = ⟨ft.params, ft.results⟩ := by
  obtain ⟨mt, xi, ei, fts, a, hval, hmt, hF, hlk, hft, htyp⟩ := inst_export_type hi hk
  obtain ⟨idx, d, h₁, h₂, h₃⟩ := valid_export_type hval hmt hF hlk hft
  obtain ⟨mt', hv', -, hte⟩ := Silmaril.Wasm.Component.Validation.core3ModuleType?_spec ht
  have hmm : mt' = mt := Option.some.inj (hv'.symm.trans hval)
  have hyd : y.1 = .func d := by
    have hl := lookup_map_snd (fun z : Core3Extern => z.1) t.exports nm
    rw [hte, hmm, h₃, hy] at hl
    exact (Option.some.inj hl).symm
  have hcf : core3FlatType? d = some v := by
    have hv₁ : (match y.1 with
        | .func d => core3FlatType? d
        | _ => none) = some v := hv
    rw [hyd] at hv₁
    exact hv₁
  exact core3FlatType?_of_fn hcf (htyp idx h₁ d h₂)

end Silmaril.Proofs.Wasm.Component.Reference
