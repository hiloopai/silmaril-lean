module

public import Silmaril.Machine.SQLite.ConnectionSecurity.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.ConnectionSecurity

open Silmaril.Machine.SQLite.ConnectionSecurity

theorem functionUsable_eq_false_iff (flags : Flags) (site : Site) (fn : FunctionFlags) :
    functionUsable flags site fn = false ↔
      site.fromDdl = true ∧
        (fn.direct = true ∨ (fn.unsafeBit = true ∧ flags.trustedSchema = false)) := by
  obtain ⟨direct, unsafeBit⟩ := fn
  unfold functionUsable
  cases direct <;> cases unsafeBit <;> cases site.fromDdl <;> cases flags.trustedSchema <;>
    simp

theorem functionUsable_of_not_fromDdl {flags : Flags} {site : Site} (fn : FunctionFlags)
    (h : site.fromDdl = false) : functionUsable flags site fn = true := by
  cases hu : functionUsable flags site fn
  · rw [functionUsable_eq_false_iff, h] at hu
    simp at hu
  · rfl

theorem vtabReadUsable_of_not_fromDdl {flags : Flags} {site : Site} (risk : VtabRisk)
    (h : site.fromDdl = false) : vtabReadUsable flags site risk = true := by
  simp [vtabReadUsable, h]

theorem loadExtensionPermitted_dbConfig_zero (build : Build) (flags : Flags)
    (api : ExtensionApi) :
    loadExtensionPermitted build
      ((ClientOp.dbConfig .enableLoadExtension 0).apply flags) api = false := by
  cases api <;>
    simp [loadExtensionPermitted, ClientOp.apply, DbConfigOption.apply, setBit]

theorem attachOpenFlags_of_attachWrite_false {flags : Flags} (parsed : OpenFlags)
    (h : flags.attachWrite = false) :
    attachOpenFlags flags parsed = ⟨true, false, false⟩ := by
  simp [attachOpenFlags, h]

theorem attachOpenFlags_create_of_attachCreate_false {flags : Flags} (parsed : OpenFlags)
    (h : flags.attachCreate = false) : (attachOpenFlags flags parsed).create = false := by
  unfold attachOpenFlags
  cases flags.attachWrite <;> simp [h]

/-- One decision under the disabled profile never yields a forbidden effect. -/
theorem decideRequest_not_forbidden {build : Build} {flags : Flags} (hd : Disabled flags)
    {request : Request} {effect : Effect}
    (hr : decideRequest build flags request = some effect) : ¬ effect.Forbidden := by
  cases request with
  | callFunction site fn =>
      simp only [decideRequest] at hr
      split at hr
      · next hu =>
          cases hr
          intro ⟨hddl, hfn⟩
          have hfalse : functionUsable flags site fn = false :=
            (functionUsable_eq_false_iff flags site fn).2
              ⟨hddl, hfn.elim Or.inl fun hu' => Or.inr ⟨hu', hd.untrusted⟩⟩
          rw [hfalse] at hu
          cases hu
      · cases hr
  | readVtab site risk =>
      simp only [decideRequest] at hr
      split at hr
      · next hu =>
          cases hr
          intro ⟨hddl, hrisk⟩
          cases risk <;> simp_all [vtabReadUsable, allowedRisk, hd.untrusted, VtabRisk.level]
      · cases hr
  | writeVtab site risk =>
      simp only [decideRequest] at hr
      split at hr
      · next hu =>
          cases hr
          intro ⟨htrig, hrisk⟩
          cases risk <;> simp_all [vtabWriteUsable, allowedRisk, hd.untrusted, VtabRisk.level]
      · cases hr
  | loadExtension api =>
      simp only [decideRequest] at hr
      split at hr
      · next hp =>
          cases api <;> simp [loadExtensionPermitted, hd.noLoadApi] at hp
      · cases hr
  | attach parsed databases limit =>
      simp only [decideRequest] at hr
      split at hr
      · cases hr
        simp [Effect.Forbidden, attachOpenFlags_of_attachWrite_false parsed hd.noAttachWrite]
      · cases hr
  | beginWrite =>
      simp [decideRequest, hd.queryOnly] at hr

theorem run_append (build : Build) (flags : Flags) (xs ys : List Item) :
    run build flags (xs ++ ys) = run build flags xs ++ run build (after flags xs) ys := by
  induction xs generalizing flags with
  | nil => rfl
  | cons item rest ih =>
      cases item with
      | client op => simp [run, after, Item.apply, ih, List.foldl]
      | request request => simp [run, after, Item.apply, ih, List.foldl]

theorem run_disabled {build : Build} {flags : Flags} (hd : Disabled flags) {items : List Item}
    (hkeep : ∀ item ∈ items, item.KeepsDisabled) {phase : Phase} {effect : Effect}
    (hmem : Event.attempted phase effect ∈ run build flags items) : ¬ effect.Forbidden := by
  induction items generalizing flags with
  | nil => cases hmem
  | cons item rest ih =>
      have hrest : ∀ item ∈ rest, item.KeepsDisabled := fun i hi => hkeep i (.tail _ hi)
      cases item with
      | client op =>
          simp only [run, List.mem_cons, reduceCtorEq, false_or] at hmem
          exact ih (hkeep (.client op) (.head _) flags hd) hrest hmem
      | request request =>
          simp only [run, List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · unfold Request.event at hhead
            split at hhead
            · next he =>
                cases hhead
                exact decideRequest_not_forbidden hd he
            · cases hhead
          · exact ih hd hrest htail

end Silmaril.Proofs.Machine.SQLite.ConnectionSecurity
