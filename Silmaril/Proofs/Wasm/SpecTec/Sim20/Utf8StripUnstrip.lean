module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripTypCode
public import Silmaril.Proofs.Wasm.SpecTec.Sim20.Utf8StripMods

/-!
# Putting export lists back, in `utf8Env20 B`

Let `ModOk B m` say that `m` is a `moduleinst` of `utf8Env20 B`, exports included. In
`utf8Env20 B` a function instance, store, frame, state or code is typed exactly when its
non-module parts are typed and its module instances are `ModOk` (`typedV_funcInst_u20_iff`, …).
Removing exports changes only module instances, so:

* `modsQ_of_state_u20`, `adminsMods_of_u20`: the module instances of typed state and code are
  `ModOk`;
* **`typedV_state_unstrip`**, **`typedV_admins_unstrip`**: the stripped state and code typed in
  `utf8Env20 B`, and `ModOk` module instances, give the state and code typed.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.Utf8Strip

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.SpecTec.Sim (TypedV)
open Silmaril.Wasm.SpecTec.Sim20.StoreBulk (utf8Env20 types20_utf8Env20)
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- **`m` is a `moduleinst` of `utf8Env20 B`**, exports included. -/
def ModOk (B : Builtins) (m : ModuleInst) : Prop :=
  TypedV (utf8Env20 B) (.varT "moduleinst" []) (moduleInstV m)

/-- A type definition of `simEnv20`, in `utf8Env20 B`. -/
theorem findTyp_u20 {x : IL.Id} {r : Option TypDef}
    (hr : (simEnv20 StoreBulk.noBuiltins).findTyp? x = r) : (utf8Env20 B).findTyp? x = r :=
  (types20_utf8Env20 B).find hr

/-- The `CODE` field of a function instance's image. -/
def funcCodeV (hn : H → String) (fi : FuncInst H) : Value :=
  match fi.code with
  | .wasm fn => .case "FUNC" (.tuple [idxV fn.type,
      .list (fn.locals.map fun t => .case "LOCAL" (valTypeV t)), .list (instrsToV fn.body)])
  | .host h => .case "_HOSTFUNC" (.text (hn h))

theorem funcInstV_eq (fi : FuncInst H) : funcInstV hn fi =
    .struct [("TYPE", funcTypeV fi.type), ("MODULE", moduleInstV fi.module),
      ("CODE", funcCodeV hn fi)] := rfl

/-- **A function instance of `utf8Env20 B`, field by field.** -/
theorem typedV_funcInst_u20_iff {fi : FuncInst H} :
    TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi) ↔
      TypedV (utf8Env20 B) (.varT "functype" []) (funcTypeV fi.type) ∧ ModOk B fi.module ∧
        TypedV (utf8Env20 B) (.varT "func" []) (funcCodeV hn fi) := by
  rw [funcInstV_eq]
  constructor
  · intro h
    have hf := Whole.hasTypFields_of_closed (findTyp_u20 Whole.findTyp_funcinst20) h
    obtain ⟨hT, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
    obtain ⟨hM, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
    obtain ⟨hC, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
    exact ⟨Whole.typedV_of_empty20 hT, Whole.typedV_of_empty20 hM, Whole.typedV_of_empty20 hC⟩
  · rintro ⟨hT, hM, hC⟩
    exact Whole.typedV_structG (findTyp_u20 Whole.findTyp_funcinst20)
      (Whole.hasTypFields_consG hT (Whole.hasTypFields_consG hM (Whole.hasTypFields_oneG hC)))

/-- **A function instance without its module's exports, and its module `ModOk`, give the
function instance typed.** -/
theorem typedV_funcInst_unstrip {fi : FuncInst H}
    (h : TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn (stripFI20 fi)))
    (hm : ModOk B fi.module) : TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi) :=
  have h' := typedV_funcInst_u20_iff.1 h
  typedV_funcInst_u20_iff.2 ⟨h'.1, hm, h'.2.2⟩

/-- The five store fields other than `FUNCS`, typed in `utf8Env20 B`. -/
structure StoreRestU (B : Builtins) (s : Store H) : Prop where
  globals : TypedV (utf8Env20 B) (.iterT (.varT "globalinst" []) .list)
    (.list (s.globals.map globalInstV))
  tables : TypedV (utf8Env20 B) (.iterT (.varT "tableinst" []) .list)
    (.list (s.tables.map tableInstV))
  mems : TypedV (utf8Env20 B) (.iterT (.varT "meminst" []) .list) (.list (s.mems.map memInstV))
  elems : TypedV (utf8Env20 B) (.iterT (.varT "eleminst" []) .list)
    (.list (s.elems.map elemInstV))
  datas : TypedV (utf8Env20 B) (.iterT (.varT "datainst" []) .list)
    (.list (s.datas.map dataInstV))

/-- A typed store of `utf8Env20 B`, taken apart. -/
theorem storeParts_u20 {s : Store H} (h : TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s)) :
    (∀ fi ∈ s.funcs, TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi)) ∧
      StoreRestU B s := by
  have hf := Whole.hasTypFields_of_closed (findTyp_u20 Whole.findTyp_store20) h
  obtain ⟨hF, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
  obtain ⟨hG, hf₂⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
  obtain ⟨hT, hf₃⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₂
  obtain ⟨hM, hf₄⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₃
  obtain ⟨hE, hf₅⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₄
  obtain ⟨hD, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₅
  have hF' := Sim.typedV_list_iff.1 (Whole.typedV_list_of_empty20 hF)
  exact ⟨fun fi hfi => hF' _ (List.mem_map_of_mem hfi),
    ⟨Whole.typedV_list_of_empty20 hG, Whole.typedV_list_of_empty20 hT,
      Whole.typedV_list_of_empty20 hM, Whole.typedV_list_of_empty20 hE,
      Whole.typedV_list_of_empty20 hD⟩⟩

/-- A store of `utf8Env20 B` from its typed parts. -/
theorem typedV_store_u20_mk {s : Store H}
    (hF : ∀ fi ∈ s.funcs, TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi))
    (hR : StoreRestU B s) : TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s) := by
  have hF' : TypedV (utf8Env20 B) (.iterT (.varT "funcinst" []) .list)
      (.list (s.funcs.map (funcInstV hn))) := by
    refine Sim.typedV_list_iff.2 fun u hu => ?_
    obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hu
    exact hF fi hfi
  exact Whole.typedV_structG (findTyp_u20 Whole.findTyp_store20)
    (Whole.hasTypFields_consG hF' (Whole.hasTypFields_consG hR.globals
    (Whole.hasTypFields_consG hR.tables (Whole.hasTypFields_consG hR.mems
    (Whole.hasTypFields_consG hR.elems (Whole.hasTypFields_oneG hR.datas))))))

/-- **A store of `utf8Env20 B`, field by field.** -/
theorem typedV_store_u20_iff {s : Store H} :
    TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s) ↔
      (∀ fi ∈ s.funcs, TypedV (utf8Env20 B) (.varT "funcinst" []) (funcInstV hn fi)) ∧
        StoreRestU B s :=
  ⟨storeParts_u20, fun ⟨hF, hR⟩ => typedV_store_u20_mk hF hR⟩

/-- **A frame of `utf8Env20 B`, field by field.** -/
theorem typedV_frame_u20_iff {f : Frame} :
    TypedV (utf8Env20 B) (.varT "frame" []) (frameV f) ↔
      TypedV (utf8Env20 B) (.iterT (.varT "val" []) .list) (.list (f.locals.map valV)) ∧
        ModOk B f.module := by
  constructor
  · intro h
    have hf := Whole.hasTypFields_of_closed (findTyp_u20 Whole.findTyp_frame20) h
    obtain ⟨hL, hf₁⟩ := Whole.hasTypFields_cons_nil_iff.1 hf
    obtain ⟨hM, -⟩ := Whole.hasTypFields_cons_nil_iff.1 hf₁
    exact ⟨Whole.typedV_list_of_empty20 hL, Whole.typedV_of_empty20 hM⟩
  · rintro ⟨hL, hM⟩
    exact Whole.typedV_structG (findTyp_u20 Whole.findTyp_frame20)
      (Whole.hasTypFields_consG hL (Whole.hasTypFields_oneG hM))

/-- **A state of `utf8Env20 B` is a typed store and frame.** -/
theorem typedV_state_u20_iff {s : Store H} {f : Frame} :
    TypedV (utf8Env20 B) (.varT "state" []) (stateV hn s f) ↔
      TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s) ∧
        TypedV (utf8Env20 B) (.varT "frame" []) (frameV f) :=
  ⟨Whole.typedV_pair_inv (findTyp_u20 Whole.findTyp_state20),
    fun ⟨hs, hf⟩ => Pure.typedV_closedCase20 (findTyp_u20 Whole.findTyp_state20) rfl
      (Whole.hasTyp_tup2G hs hf)⟩

/-- **Putting the exports of a store back.** -/
theorem typedV_store_unstrip {s : Store H}
    (h : TypedV (utf8Env20 B) (.varT "store" []) (storeV hn (stripStore20 s)))
    (hm : ∀ fi ∈ s.funcs, ModOk B fi.module) :
    TypedV (utf8Env20 B) (.varT "store" []) (storeV hn s) := by
  obtain ⟨hF, hR⟩ := typedV_store_u20_iff.1 h
  have hR' : StoreRestU B s := ⟨hR.globals, hR.tables, hR.mems, hR.elems, hR.datas⟩
  refine typedV_store_u20_iff.2 ⟨fun fi hfi => ?_, hR'⟩
  exact typedV_funcInst_unstrip (hF _ (List.mem_map_of_mem hfi)) (hm fi hfi)

/-- **Putting the exports of a state back.** -/
theorem typedV_state_unstrip {s : Store H} {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "state" []) (stateV hn (stripStore20 s) (stripFrame20 f)))
    (hs : ∀ fi ∈ s.funcs, ModOk B fi.module) (hf : ModOk B f.module) :
    TypedV (utf8Env20 B) (.varT "state" []) (stateV hn s f) := by
  obtain ⟨h₁, h₂⟩ := typedV_state_u20_iff.1 h
  exact typedV_state_u20_iff.2 ⟨typedV_store_unstrip h₁ hs,
    typedV_frame_u20_iff.2 ⟨(typedV_frame_u20_iff.1 h₂).1, hf⟩⟩

/-- **The module instances of a typed state are `ModOk`.** -/
theorem modOk_of_state_u20 {s : Store H} {f : Frame}
    (h : TypedV (utf8Env20 B) (.varT "state" []) (stateV hn s f)) :
    (∀ fi ∈ s.funcs, ModOk B fi.module) ∧ ModOk B f.module := by
  obtain ⟨h₁, h₂⟩ := typedV_state_u20_iff.1 h
  exact ⟨fun fi hfi => (typedV_funcInst_u20_iff.1 ((typedV_store_u20_iff.1 h₁).1 fi hfi)).2.1,
    (typedV_frame_u20_iff.1 h₂).2⟩

/-- A typed label of `utf8Env20 B`, taken apart. -/
theorem typedV_label_u20 {n : Nat} {cont : List V2.Instr} {body : List Admin}
    (h : TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV (.label n cont body))) :
    TypedV (utf8Env20 B) Sim.nT (.num (.natN n)) ∧
      TypedV (utf8Env20 B) Sim.instrsT (.list (instrsToV cont)) ∧
      TypedV (utf8Env20 B) adminsTy (.list (adminsToV body)) := by
  obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCase_u20 Whole.findCase_label20 h)
  exact ⟨h₁, Whole.typedV_list_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩

/-- A typed frame of `utf8Env20 B`, taken apart. -/
theorem typedV_frameA_u20 {n : Nat} {f : Frame} {body : List Admin}
    (h : TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV (.frame n f body))) :
    TypedV (utf8Env20 B) Sim.nT (.num (.natN n)) ∧
      TypedV (utf8Env20 B) (.varT "frame" []) (frameV f) ∧
      TypedV (utf8Env20 B) adminsTy (.list (adminsToV body)) := by
  obtain ⟨h₁, h₂, h₃⟩ := Whole.hasTyp_tup3_inv20 (hasTyp_adminCase_u20 Whole.findCase_frame20 h)
  exact ⟨h₁, Whole.typedV_of_valsOnly20 ⟨rfl, rfl, rfl⟩ h₂, h₃⟩

mutual
/-- **Putting the exports of the frames inside an `admininstr` back.** -/
theorem typedV_admin_unstrip : ∀ a : Admin,
    TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV (stripAdmin20 a)) →
      AdminMods (ModOk B) a → TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV a)
  | .label _ _ body, h, hq => by
    obtain ⟨h₁, h₂, h₃⟩ := typedV_label_u20 h
    exact Pure.typedV_closedCase20 (findTyp_u20 Whole.findTyp_admininstr20) Whole.findCase_label20
      (Whole.hasTyp_tup3_mk20 h₁ h₂ (typedV_admins_unstrip body h₃ hq))
  | .frame _ f body, h, hq => by
    obtain ⟨h₁, h₂, h₃⟩ := typedV_frameA_u20 h
    have hf : TypedV (utf8Env20 B) (.varT "frame" []) (frameV f) :=
      typedV_frame_u20_iff.2 ⟨(typedV_frame_u20_iff.1 h₂).1, hq.1⟩
    exact Pure.typedV_closedCase20 (findTyp_u20 Whole.findTyp_admininstr20) Whole.findCase_frame20
      (Whole.hasTyp_tup3_mk20 h₁ hf (typedV_admins_unstrip body h₃ hq.2))
  | .plain _, h, _ => h
  | .trap, h, _ => h
  | .callAddr _, h, _ => h
  | .refFuncAddr _, h, _ => h
  | .refHostAddr _, h, _ => h

/-- `typedV_admin_unstrip` on a sequence. -/
theorem typedV_admins_unstrip : ∀ l : List Admin,
    TypedV (utf8Env20 B) adminsTy (.list (adminsToV (stripAdmins20 l))) →
      AdminsMods (ModOk B) l → TypedV (utf8Env20 B) adminsTy (.list (adminsToV l))
  | [], _, _ => typedV_listNil
  | a :: l, h, hq => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2
      ⟨typedV_admin_unstrip a ha hq.1, typedV_admins_unstrip l hl hq.2⟩
end

mutual
/-- **The frames inside a typed `admininstr` have `ModOk` modules.** -/
theorem adminMods_of_u20 : ∀ a : Admin,
    TypedV (utf8Env20 B) (.varT "admininstr" []) (adminToV a) → AdminMods (ModOk B) a
  | .label _ _ body, h => adminsMods_of_u20 body (typedV_label_u20 h).2.2
  | .frame _ _ body, h =>
    have h' := typedV_frameA_u20 h
    ⟨(typedV_frame_u20_iff.1 h'.2.1).2, adminsMods_of_u20 body h'.2.2⟩
  | .plain _, _ => trivial
  | .trap, _ => trivial
  | .callAddr _, _ => trivial
  | .refFuncAddr _, _ => trivial
  | .refHostAddr _, _ => trivial

/-- `adminMods_of_u20` on a sequence. -/
theorem adminsMods_of_u20 : ∀ l : List Admin,
    TypedV (utf8Env20 B) adminsTy (.list (adminsToV l)) → AdminsMods (ModOk B) l
  | [], _ => trivial
  | a :: l, h =>
    have h' := Sim.typedV_list_cons_iff.1 h
    ⟨adminMods_of_u20 a h'.1, adminsMods_of_u20 l h'.2⟩
end

end Silmaril.Wasm.SpecTec.Sim20.Utf8Strip
