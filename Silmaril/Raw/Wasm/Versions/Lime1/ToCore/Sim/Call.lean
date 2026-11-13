module

public import Silmaril.Raw.Wasm.Versions.Lime1.ToCore.Runtime
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Validation.Subtyping.Check
-- Import lines are rewritten, and one `set_option linter.unusedTactic false in` is added

@[expose] public section

/-! # Lime1 → Core step simulation: calls

Head-rule lemmas for the call rules of `Lime1.Execution.Step`:

* `call`: Core `call` reads the callee's defined type from the store, giving
  exactly the image `[ref.func a, call_ref (type)]` of `.invoke a`;
* `callIndirect*`: Core `call_indirect x y` unfolds to
  `table.get x; ref.cast (ref null y); call_ref y`; Lime1's type mismatch is a
  cast failure (`V1.FuncType.toDefType_sub_iff`), a null entry passes the
  (nullable) cast and traps at `call_ref`;
* `invokeWasm`/`invokeHost`/`invokeHostDiverges`: Core `call_ref-func`,
  `call_ref-hostfunc-res`, `call_ref-hostfunc-div`.
-/

namespace Silmaril.Wasm.Lime1.Execution.ToCoreSim

open Silmaril.Wasm.Execution.Runtime
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

local notation "CStep" => Silmaril.Wasm.Execution.Core.Step Profile.spec

/-! ## Helpers -/

theorem call_parts {s : Store H} {f : Frame} {code : List Admin} {cs : ToCore.CStore H}
    {cf : ToCore.CFrame} {cl : List ToCore.CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    ToCore.Store.erase cs = s.toCore ∧ ToCore.Frame.erase cf = f.toCore ∧
      cl.map (ToCore.Admin.norm cf.module) = Admin.listToCore s code ∧ ConfigWF ⟨s, f, code⟩ := by
  obtain ⟨hn, hwf⟩ := hs
  obtain ⟨h1, h2, h3⟩ := ToCore.Config.norm_eq_toCore_iff.mp hn
  exact ⟨h1, h2, h3, hwf⟩

theorem call_sim_of {s : Store H} {f : Frame} {code : List Admin} {cs : ToCore.CStore H}
    {cf : ToCore.CFrame} {cl : List ToCore.CAdmin} (h1 : ToCore.Store.erase cs = s.toCore)
    (h2 : ToCore.Frame.erase cf = f.toCore)
    (h3 : cl.map (ToCore.Admin.norm cf.module) = Admin.listToCore s code)
    (hwf : ConfigWF ⟨s, f, code⟩) : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩ :=
  ⟨ToCore.Config.norm_eq_toCore_iff.mpr ⟨h1, h2, h3⟩, hwf⟩

theorem call_funcInst_toCore_type (fi : FuncInst Func H) : fi.toCore.type = fi.type.toDefType := by
  cases fi <;> rfl

theorem call_frame_funcs {cf : ToCore.CFrame} {f : Frame} (h : ToCore.Frame.erase cf = f.toCore) :
    cf.module.funcs = f.module.funcs.map Addr.value := by
  have := congrArg (fun g => g.module.funcs) h
  simpa [ToCore.Frame.erase, ToCore.ModuleInst.erase, Frame.toCore, ModuleInst.toCore] using this

theorem call_frame_types {cf : ToCore.CFrame} {f : Frame} (h : ToCore.Frame.erase cf = f.toCore) :
    cf.module.types = f.module.types.map V1.FuncType.toDefType := by
  have := congrArg (fun g => g.module.types) h
  simpa [ToCore.Frame.erase, ToCore.ModuleInst.erase, Frame.toCore, ModuleInst.toCore] using this

theorem call_frame_tables {cf : ToCore.CFrame} {f : Frame} (h : ToCore.Frame.erase cf = f.toCore) :
    cf.module.tables = f.module.tables.map Addr.value := by
  have := congrArg (fun g => g.module.tables) h
  simpa [ToCore.Frame.erase, ToCore.ModuleInst.erase, Frame.toCore, ModuleInst.toCore] using this

theorem call_store_tables {cs : ToCore.CStore H} {s : Store H} (h : ToCore.Store.erase cs = s.toCore) :
    cs.tables = s.tables.map TableInst.toCore := by
  have := congrArg (fun g => g.tables) h
  simpa [ToCore.Store.erase, Store.toCore] using this

theorem call_store_func {cs : ToCore.CStore H} {s : Store H} (h : ToCore.Store.erase cs = s.toCore)
    {a : Nat} {fL : FuncInst Func H} (hf : s.funcs[a]? = some fL) :
    ∃ fi, cs.funcs[a]? = some fi ∧ fi.type = fL.type.toDefType ∧
      ToCore.ModuleInst.erase fi.module = fL.toCore.module ∧ fi.code = fL.toCore.code := by
  have := congrArg (fun g => g.funcs[a]?) h
  simp only [ToCore.Store.erase, Store.toCore, List.getElem?_map, hf] at this
  cases hc : cs.funcs[a]? with
  | none => simp [hc] at this
  | some fi =>
    simp only [hc, Option.map_some, Option.some.injEq] at this
    refine ⟨fi, rfl, ?_, ?_, ?_⟩
    · rw [← call_funcInst_toCore_type, ← this]
    · rw [← this]
    · rw [← this]

theorem call_tyOk_ofList_num (Δ : TypeCtx) (ts : List NumType) :
    TyOk Δ (Ty.ofList (ts.map Ty.num)) := by
  induction ts with
  | nil => exact TyOk.nil
  | cons t ts ih => exact TyOk.cons (TyOk.num t) ih

theorem call_tyOk_toDefType (t : V1.FuncType) : TyOk ({} : TypeCtx) t.toDefType := by
  unfold V1.FuncType.toDefType
  simp only [liftRec, V1.FuncType.toCoreRec, List.map_cons, List.map_nil, liftSub, liftComp,
    V1.FuncType.toCore, V1.liftResult_toCore]
  refine TyOk.defn (GroupOk2.cons (SubOk2.noSuper (TyOk.func ?_ ?_)) GroupOk2.nil) (by simp [Ty.length])
  · exact call_tyOk_ofList_num _ _
  · exact call_tyOk_ofList_num _ _

theorem call_tyOk_ref (n : Bool) (t : V1.FuncType) :
    TyOk ({} : TypeCtx) (Ty.ref n (.use (.dt t.toDefType)) : CRefType) :=
  TyOk.ref (TyOk.use (TyOk.dt (call_tyOk_toDefType t)))

/-! ### Core context helpers -/

section
open Silmaril.Wasm.Execution.Core

theorem call_step_prefix {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
    {s s' : Silmaril.Wasm.Execution.Core.Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame}
    (v : Val) {is is' : List Silmaril.Wasm.Execution.Core.Admin}
    (h : Silmaril.Wasm.Execution.Core.Step Profile.spec host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Silmaril.Wasm.Execution.Core.Step Profile.spec host ⟨s, f, v.toAdmin :: is⟩
      ⟨s', f', v.toAdmin :: is'⟩ := by
  have := Silmaril.Wasm.Execution.Core.Step.ctxtInstrs (vs := [v]) (rest := []) h (.inl (by simp))
  simpa [vals] using this

theorem call_step_suffix {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
    {s s' : Silmaril.Wasm.Execution.Core.Store H} {f f' : Silmaril.Wasm.Execution.Core.Frame}
    {is is' rest : List Silmaril.Wasm.Execution.Core.Admin} (hr : rest ≠ [])
    (h : Silmaril.Wasm.Execution.Core.Step Profile.spec host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Silmaril.Wasm.Execution.Core.Step Profile.spec host ⟨s, f, is ++ rest⟩ ⟨s', f', is' ++ rest⟩ := by
  have := Silmaril.Wasm.Execution.Core.Step.ctxtInstrs (vs := []) (rest := rest) h (.inr hr)
  simpa [vals] using this

theorem call_trap_rest {host : Silmaril.Wasm.Execution.Core.HostSemantics H}
    {s : Silmaril.Wasm.Execution.Core.Store H} {f : Silmaril.Wasm.Execution.Core.Frame}
    {rest : List Silmaril.Wasm.Execution.Core.Admin} (hr : rest ≠ []) :
    Silmaril.Wasm.Execution.Core.Step Profile.spec host ⟨s, f, .trap :: rest⟩ ⟨s, f, [.trap]⟩ := by
  have := Silmaril.Wasm.Execution.Core.Step.trapInstrs (P := Profile.spec) (host := host)
    (s := s) (f := f) (vs := []) (rest := rest) (.inr hr)
  simpa [vals] using this

/-- Decompose a Core code sequence whose normalisation is the image of `values args ++ [.invoke a]`. -/
theorem call_decomp_invoke {m : ToCore.CModuleInst} {cl : List ToCore.CAdmin} {vs : List Val}
    {a : Nat} {d : DefType}
    (h : cl.map (ToCore.Admin.norm m) = vals vs ++ [.ref (.func a), .callRefType d]) :
    ∃ x, cl = vals vs ++ [.ref (.func a), x] ∧ x.IsCallRef := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.mp h
  rw [ToCore.map_norm_vals h₁]
  match l₂, h₂ with
  | [y, x], h₂ =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h₂
    obtain ⟨hy, hx⟩ := h₂
    rw [(show ToCore.Rigid (.ref (.func a)) from trivial).eq_of_norm hy]
    refine ⟨x, rfl, ?_⟩
    rcases ToCore.norm_eq_callRefType hx with rfl | ⟨y, rfl, -⟩ <;> trivial
  | [_], h₂ => simp at h₂
  | [], h₂ => simp at h₂
  | _ :: _ :: _ :: _, h₂ => simp at h₂

end

theorem call_listWF_expression (s : Store H) (es : Expr) : Admin.listWF s (expression es) := by
  induction es with
  | nil => simp [expression, Admin.listWF]
  | cons e es ih => simpa [expression, Admin.listWF, Admin.WF] using ih

theorem call_listWF_values (s : Store H) (vs : List Value) : Admin.listWF s (values vs) := by
  induction vs with
  | nil => simp [values, Admin.listWF]
  | cons v vs ih =>
    rcases v with ⟨⟨_ | _⟩, _⟩ <;> simpa [values, value, Admin.listWF, Admin.WF] using ih

theorem call_listWF_result (s : Store H) (r : Result) : Admin.listWF s (result r) := by
  cases r with
  | values vs => exact call_listWF_values s vs
  | trap => simp [result, Admin.listWF, Admin.WF]

/-! ## Head rules -/

theorem call {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame} {i : FuncIdx}
    {a : FuncAddr} (found : f.module.funcs[i.toNat]? = some a) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [.source (.call i)]⟩ c) :
    ∃ c', Relation.TransGen (CStep tgt) c c' ∧ Sim ⟨s, f, [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  have hcl' : cl = [.plain (Instr.call i).toCore] :=
    ToCore.map_norm_eq_of_rigid (by simp [ToCore.Rigid.toCore]) (by simpa using hcl)
  subst hcl'
  have ha : a.value < s.funcs.length := hwf.2.1 a (List.mem_of_getElem? found)
  obtain ⟨fL, hfL⟩ : ∃ fL, s.funcs[a.value]? = some fL := ⟨_, List.getElem?_eq_getElem ha⟩
  obtain ⟨fi, hfi, hty, -, -⟩ := call_store_func hst hfL
  have hx : cf.module.funcs[i.toNat]? = some a.value := by
    rw [call_frame_funcs hfr]; simp [found]
  refine ⟨_, .single (Silmaril.Wasm.Execution.Core.Step.call hx hfi), ?_⟩
  refine call_sim_of hst hfr ?_ ⟨hwf.1, hwf.2.1, ?_⟩
  · simp [hty, Store.funcDefType, hfL]
  · simp [Admin.listWF, Admin.WF, ha]

/-! ### `call_indirect` -/

theorem call_ci_code {s : Store H} {m : ToCore.CModuleInst} {cl : List ToCore.CAdmin}
    {c : BitVec 32} {i : TypeIdx}
    (h : cl.map (ToCore.Admin.norm m) =
      Admin.listToCore s [value (.int .i32 c), .source (.callIndirect i)]) :
    cl = [.plain (.intConst .i32 c), .plain (.callIndirect ⟨0⟩ i)] := by
  refine ToCore.map_norm_eq_of_rigid ?_ (h.trans ?_)
  · simp [ToCore.Rigid]
  · simp [value, Value.int, Instr.toCore]

theorem call_table {cs : ToCore.CStore H} {cf : ToCore.CFrame} {s : Store H} {f : Frame}
    (hst : ToCore.Store.erase cs = s.toCore) (hfr : ToCore.Frame.erase cf = f.toCore)
    {table : TableInst} (h : frameTable s f = some table) :
    ∃ ta, cs.table? cf ⟨0⟩ = some (ta, table.toCore) := by
  simp only [frameTable, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ta, hta, ht⟩ := h
  refine ⟨ta.value, ?_⟩
  have h0 : (⟨0⟩ : TableIdx).toNat = 0 := rfl
  simp [h0, Silmaril.Wasm.Execution.Core.Store.table?, call_frame_tables hfr, call_store_tables hst,
    hta, ht]

theorem call_instRef {m : ToCore.CModuleInst} {i : TypeIdx} {d : DefType}
    (h : m.types[i.toNat]? = some d) :
    m.instRef ⟨true, .typeIdx i⟩ = .ref true (.use (.dt d)) := by
  simp [Silmaril.Wasm.Execution.Core.ModuleInst.instRef, liftRef, liftHeap, liftTypeIdx,
    Ty.substAll, Ty.subst, Subst.all, h]

theorem call_not_refOk {cs : ToCore.CStore H} {a : Nat}
    {fi : Silmaril.Wasm.Execution.Core.FuncInst H} (hf : cs.funcs[a]? = some fi)
    {t₁ t₂ : V1.FuncType} (ht : fi.type = t₁.toDefType) (hne : t₁ ≠ t₂) :
    ¬ Silmaril.Wasm.Execution.Core.RefOk cs (.func a) (.ref true (.use (.dt t₂.toDefType))) := by
  intro h
  obtain ⟨rt₀, e, hsub, -⟩ :=
    (Silmaril.Wasm.Execution.Core.RefOk.iff_principal _ _ _ (call_tyOk_ref true t₂)).mp h
  simp only [Silmaril.Wasm.Execution.Core.Ref.type?, hf, Option.map_some, Option.some.injEq,
    ht] at e
  subst e
  have hc := Sub.check_complete TypeCtx.ok_empty rfl hsub (call_tyOk_ref false t₁)
    (call_tyOk_ref true t₂)
  simp [Sub.check, Sub.checkK, TypeCtx.checkRef, TypeCtx.checkHeap, TypeCtx.resolve,
    Ty.defHeap] at hc
  exact hne ((V1.FuncType.toDefType_sub_iff _ _ _).mp (TypeCtx.checkDef_sound hc))

theorem callIndirect {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame} {i : TypeIdx}
    {c : BitVec 32} {table : TableInst} {a : FuncAddr} {fn : FuncInst Func H} {ft : FuncType}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
    (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
    (typeMatch : fn.type = ft) {cc : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ cc) :
    ∃ c', Relation.TransGen (CStep tgt) cc c' ∧ Sim ⟨s, f, [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := cc
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain rfl := call_ci_code hcl
  obtain ⟨ta, hta⟩ := call_table hst hfr tableFound
  obtain ⟨fi, hfi, hty, -, -⟩ := call_store_func hst found
  have hty' : cf.module.types[i.toNat]? = some ft.toDefType := by
    rw [call_frame_types hfr]; simp [typeFound]
  have hrefs : table.toCore.refs[c.toNat]? = some (.func a.value) := by
    simp [TableInst.toCore, element]
  have hok : Silmaril.Wasm.Execution.Core.RefOk cs (.func a.value)
      (cf.module.instRef ⟨true, .typeIdx i⟩) := by
    rw [call_instRef hty']
    rw [typeMatch] at hty
    have h1 := Silmaril.Wasm.Execution.Core.RefOk.func hfi
    rw [hty] at h1
    exact .sub h1 (call_tyOk_ref true ft)
      (Sub.refNull (Sub.defDef ((V1.FuncType.toDefType_sub_iff _ _ _).mpr rfl)))
  refine ⟨⟨cs, cf, [.ref (.func a.value), .plain (.callRef i)]⟩, ?_, ?_⟩
  · refine .head (call_step_prefix (.num ⟨.int .i32, c⟩)
      Silmaril.Wasm.Execution.Core.Step.callIndirect) ?_
    refine .head (call_step_suffix (by simp) (Silmaril.Wasm.Execution.Core.Step.table
      (Silmaril.Wasm.Execution.Core.TableStep.getVal (a := .i32) (i := c) hta hrefs))) ?_
    exact .single (call_step_suffix (rest := [.plain (.callRef i)]) (by simp)
      (Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.castSucceed hok)))
  · refine call_sim_of hst hfr ?_ ⟨hwf.1, hwf.2.1, ?_⟩
    · simp [hty', Store.funcDefType, found, typeMatch]
    · simp [Admin.listWF, Admin.WF, (List.getElem?_eq_some_iff.mp found).1]

theorem call_sim_trap {s : Store H} {f : Frame} {code : List Admin} {cs : ToCore.CStore H}
    {cf : ToCore.CFrame} {cl : List ToCore.CAdmin} (hs : Sim ⟨s, f, code⟩ ⟨cs, cf, cl⟩) :
    Sim ⟨s, f, [.trap]⟩ ⟨cs, cf, [.trap]⟩ := by
  obtain ⟨hst, hfr, -, hwf⟩ := call_parts hs
  exact call_sim_of hst hfr (by simp) ⟨hwf.1, hwf.2.1, by simp [Admin.listWF, Admin.WF]⟩

theorem callIndirectBounds {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {i : TypeIdx} {c : BitVec 32} {table : TableInst}
    (tableFound : frameTable s f = some table) (outOfBounds : table.refs[c.toNat]? = none)
    {cc : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ cc) :
    ∃ c', Relation.TransGen (CStep tgt) cc c' ∧ Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := cc
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain rfl := call_ci_code hcl
  obtain ⟨ta, hta⟩ := call_table hst hfr tableFound
  have hlen : table.toCore.refs.length ≤ c.toNat := by
    simpa [TableInst.toCore] using List.getElem?_eq_none_iff.mp outOfBounds
  refine ⟨⟨cs, cf, [.trap]⟩, ?_, call_sim_trap hs⟩
  refine .head (call_step_prefix (.num ⟨.int .i32, c⟩)
    Silmaril.Wasm.Execution.Core.Step.callIndirect) ?_
  refine .head (call_step_suffix (by simp) (Silmaril.Wasm.Execution.Core.Step.table
    (Silmaril.Wasm.Execution.Core.TableStep.getOob (a := .i32) (i := c) hta hlen))) ?_
  exact .single (call_trap_rest (by simp))

theorem callIndirectNull {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame}
    {i : TypeIdx} {c : BitVec 32} {table : TableInst}
    (tableFound : frameTable s f = some table) (null : table.refs[c.toNat]? = some none)
    {cc : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ cc) :
    ∃ c', Relation.TransGen (CStep tgt) cc c' ∧ Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := cc
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain rfl := call_ci_code hcl
  obtain ⟨ta, hta⟩ := call_table hst hfr tableFound
  have hrefs : table.toCore.refs[c.toNat]? = some .null := by
    simp [TableInst.toCore, null]
  refine ⟨⟨cs, cf, [.trap]⟩, ?_, call_sim_trap hs⟩
  refine .head (call_step_prefix (.num ⟨.int .i32, c⟩)
    Silmaril.Wasm.Execution.Core.Step.callIndirect) ?_
  refine .head (call_step_suffix (by simp) (Silmaril.Wasm.Execution.Core.Step.table
    (Silmaril.Wasm.Execution.Core.TableStep.getVal (a := .i32) (i := c) hta hrefs))) ?_
  by_cases hok : Silmaril.Wasm.Execution.Core.RefOk cs .null (cf.module.instRef ⟨true, .typeIdx i⟩)
  · refine .head (call_step_suffix (rest := [.plain (.callRef i)]) (by simp)
      (Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.castSucceed hok))) ?_
    exact .single (Silmaril.Wasm.Execution.Core.Step.callRefNull (c := .plain (.callRef i)) trivial)
  · refine .head (call_step_suffix (rest := [.plain (.callRef i)]) (by simp)
      (Silmaril.Wasm.Execution.Core.Step.reference
      (Silmaril.Wasm.Execution.Core.RefStep.castFail hok))) ?_
    exact .single (call_trap_rest (by simp))

theorem callIndirectType {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame} {i : TypeIdx}
    {c : BitVec 32} {table : TableInst} {a : FuncAddr} {fn : FuncInst Func H} {ft : FuncType}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[i.toNat]? = some ft)
    (element : table.refs[c.toNat]? = some (some a)) (found : s.funcs[a.value]? = some fn)
    (typeMismatch : fn.type ≠ ft) {cc : ToCore.CConfig H}
    (hs : Sim ⟨s, f, [value (.int .i32 c), .source (.callIndirect i)]⟩ cc) :
    ∃ c', Relation.TransGen (CStep tgt) cc c' ∧ Sim ⟨s, f, [.trap]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := cc
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain rfl := call_ci_code hcl
  obtain ⟨ta, hta⟩ := call_table hst hfr tableFound
  obtain ⟨fi, hfi, hty, -, -⟩ := call_store_func hst found
  have hty' : cf.module.types[i.toNat]? = some ft.toDefType := by
    rw [call_frame_types hfr]; simp [typeFound]
  have hrefs : table.toCore.refs[c.toNat]? = some (.func a.value) := by
    simp [TableInst.toCore, element]
  have hnok : ¬ Silmaril.Wasm.Execution.Core.RefOk cs (.func a.value)
      (cf.module.instRef ⟨true, .typeIdx i⟩) := by
    rw [call_instRef hty']
    exact call_not_refOk hfi hty typeMismatch
  refine ⟨⟨cs, cf, [.trap]⟩, ?_, call_sim_trap hs⟩
  refine .head (call_step_prefix (.num ⟨.int .i32, c⟩)
    Silmaril.Wasm.Execution.Core.Step.callIndirect) ?_
  refine .head (call_step_suffix (by simp) (Silmaril.Wasm.Execution.Core.Step.table
    (Silmaril.Wasm.Execution.Core.TableStep.getVal (a := .i32) (i := c) hta hrefs))) ?_
  refine .head (call_step_suffix (rest := [.plain (.callRef i)]) (by simp)
      (Silmaril.Wasm.Execution.Core.Step.reference
    (Silmaril.Wasm.Execution.Core.RefStep.castFail hnok))) ?_
  exact .single (call_trap_rest (by simp))

/-! ### Invocation -/

theorem call_invoke_code {s : Store H} {m : ToCore.CModuleInst} {cl : List ToCore.CAdmin}
    {args : List Value} {a : FuncAddr}
    (h : cl.map (ToCore.Admin.norm m) = Admin.listToCore s (values args ++ [.invoke a])) :
    ∃ x, cl = Silmaril.Wasm.Execution.Core.vals (args.map Value.toCore) ++ [.ref (.func a.value), x] ∧
      x.IsCallRef := by
  rw [listToCore_append, values_toCore] at h
  simp only [listToCore_cons, invoke_toCore, listToCore_nil, List.append_nil] at h
  exact call_decomp_invoke h

-- Silmaril repair: the newer toolchain flags one `rfl` alternative below as unused.
set_option linter.unusedTactic false in
theorem call_forCall_erase {m : ToCore.CModuleInst} {module : ModuleInst}
    (hmod : ToCore.ModuleInst.erase m = module.toCore) (args : List Value) (locals : List NumType) :
    ToCore.Frame.erase (Silmaril.Wasm.Execution.Core.Frame.forCall m (args.map Value.toCore)
      (locals.map V1.ValType.toCore)) =
      Frame.toCore ⟨args ++ locals.map Value.zero, module⟩ := by
  simp only [ToCore.Frame.erase, Silmaril.Wasm.Execution.Core.Frame.forCall, Frame.toCore, hmod,
    List.map_append, List.map_map]
  congr 2
  all_goals refine List.map_congr_left (fun t _ => ?_)
  all_goals simp only [Function.comp_apply, V1.liftVal_toCore]
  all_goals first | rfl | (rcases t with t | t <;> rfl)

theorem invokeWasm {tgt : ToCore.CHostSemantics H} {s : Store H} {f : Frame} {a : FuncAddr}
    {ft : FuncType} {module : ModuleInst} {fn : Func} {args : List Value}
    (found : s.funcs[a.value]? = some (.wasm ft module fn))
    (arity : args.length = ft.params.length) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (CStep tgt) c c' ∧
      Sim ⟨s, f, [.frame ft.results.length ⟨args ++ fn.locals.map Value.zero, module⟩
        [.label ft.results.length [] (expression fn.body)]]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain ⟨x, rfl, hx⟩ := call_invoke_code hcl
  obtain ⟨fi, hfi, hty, hmod, hcode⟩ := call_store_func hst found
  simp only [FuncInst.type] at hty
  have he : Expand fi.type (.func (Ty.ofList (ft.params.map Ty.num))
      (Ty.ofList (ft.results.map Ty.num))) := by
    rw [hty]; exact Expand.iff.mpr (V1.FuncType.toDefType_expand _)
  have hcode' : fi.code = .wasm fn.toCore := hcode
  refine ⟨_, .single (Silmaril.Wasm.Execution.Core.Step.callRefFunc
    (vs := args.map Value.toCore) hx hfi he (by simp [Ty.length_ofList, arity]) hcode'), ?_⟩
  refine call_sim_of hst hfr ?_ ⟨hwf.1, hwf.2.1, ?_⟩
  · have hfe := call_forCall_erase hmod args fn.locals
    simp only [Func.toCore] at hfe ⊢
    simp [Ty.length_ofList, hfe, Expr.toCore_eq_map]
  · simp only [Admin.listWF, Admin.WF, and_true]
    exact ⟨hwf.1.1 _ _ _ _ found, call_listWF_expression s fn.body⟩

theorem invokeHost {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {s s' : Store H} {f : Frame} {a : FuncAddr} {ft : FuncType}
    {fn : H} {args : List Value} {r : Result}
    (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
    (behavior : src fn s args (.returned s' r)) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (CStep tgt) c c' ∧ Sim ⟨s', f, result r⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain ⟨x, rfl, hx⟩ := call_invoke_code hcl
  obtain ⟨fi, hfi, hty, -, hcode⟩ := call_store_func hst found
  simp only [FuncInst.type] at hty
  have he : Expand fi.type (.func (Ty.ofList (ft.params.map Ty.num))
      (Ty.ofList (ft.results.map Ty.num))) := by
    rw [hty]; exact Expand.iff.mpr (V1.FuncType.toDefType_expand _)
  have hcode' : fi.code = .host fn := hcode
  obtain ⟨outC, htgt, hout⟩ := hosts.2 fn s args _ cs behavior hst
  cases outC with
  | diverged => simp [HostOutcomeSim] at hout
  | returned sC rC =>
    simp only [HostOutcomeSim] at hout
    obtain ⟨hsC, rfl⟩ := hout
    refine ⟨_, .single (Silmaril.Wasm.Execution.Core.Step.callRefHost
      (vs := args.map Value.toCore) hx hfi he (by simp [Ty.length_ofList, arity]) hcode' htgt), ?_⟩
    obtain ⟨hwf', hext⟩ := hosts.1 fn s args s' r behavior hwf.1
    refine call_sim_of hsC hfr ?_ ⟨hwf', ?_, call_listWF_result s' r⟩
    · cases r <;> simp [Result.toCore, Silmaril.Wasm.Execution.Core.Result.toAdmin, result]
    · intro b hb
      obtain ⟨fi', h1, -⟩ := hext _ _ (List.getElem?_eq_getElem (hwf.2.1 b hb))
      exact (List.getElem?_eq_some_iff.mp h1).1

theorem invokeHostDiverges {src : HostSemantics H} {tgt : ToCore.CHostSemantics H}
    (hosts : HostCompatible src tgt) {s : Store H} {f : Frame} {a : FuncAddr} {ft : FuncType}
    {fn : H} {args : List Value}
    (found : s.funcs[a.value]? = some (.host ft fn)) (arity : args.length = ft.params.length)
    (behavior : src fn s args .diverged) {c : ToCore.CConfig H}
    (hs : Sim ⟨s, f, values args ++ [.invoke a]⟩ c) :
    ∃ c', Relation.TransGen (CStep tgt) c c' ∧ Sim ⟨s, f, values args ++ [.invoke a]⟩ c' := by
  obtain ⟨cs, cf, cl⟩ := c
  obtain ⟨hst, hfr, hcl, hwf⟩ := call_parts hs
  obtain ⟨x, rfl, hx⟩ := call_invoke_code hcl
  obtain ⟨fi, hfi, hty, -, hcode⟩ := call_store_func hst found
  simp only [FuncInst.type] at hty
  have he : Expand fi.type (.func (Ty.ofList (ft.params.map Ty.num))
      (Ty.ofList (ft.results.map Ty.num))) := by
    rw [hty]; exact Expand.iff.mpr (V1.FuncType.toDefType_expand _)
  have hcode' : fi.code = .host fn := hcode
  obtain ⟨outC, htgt, hout⟩ := hosts.2 fn s args _ cs behavior hst
  cases outC with
  | returned => simp [HostOutcomeSim] at hout
  | diverged =>
    exact ⟨_, .single (Silmaril.Wasm.Execution.Core.Step.callRefHostDiv
      (vs := args.map Value.toCore) hx hfi he (by simp [Ty.length_ofList, arity]) hcode' htgt), hs⟩

end Silmaril.Wasm.Lime1.Execution.ToCoreSim
