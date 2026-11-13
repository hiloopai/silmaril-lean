module

public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Typ
public import Silmaril.Proofs.Wasm.SpecTec.Sim10.Utf8Strip10Mods

/-!
# Putting export lists back, in `utf8Env10T B`

The 1.0 form of `Sim20.Utf8Strip.typedV_state_unstrip` and `good20BU_succ`. Let `ModOk10 B m`
say that `m` is a `moduleinst` of `utf8Env10T B`, exports included. Removing exports changes
only module instances, and every 1.0 runtime structure is typed field by field
(`Utf8Strip10Typ`), so:

* **`modsQ10_of_typed`**: the module instances of a configuration typed in `utf8Env10T B` are
  `ModOk10`;
* **`typed10_unstrip`**: a stripped configuration typed in `utf8Env10T B`, whose module
  instances are `ModOk10`, is typed with its exports;
* **`typed10U_succ`**: the successor of a V1 step from a configuration typed in `utf8Env10T B`
  is typed in `utf8Env10T B` when its stripped form is typed in `simEnv10T B` (the 1.0 form of
  `Sim20.Utf8Strip.Task.goodUnstrip20`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V1.Execution (Admin Store Config HostSemantics Step)
open Silmaril.Wasm.Execution.Runtime (Frame ModuleInst FuncInst)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT storeT frameT)
open Silmaril.Wasm.SpecTec.Sim10.StoreFix (simEnv10T)
open Silmaril.Wasm.SpecTec.Sim10.Utf8Fix (utf8Env10T typed10_utf8_10T)
open Silmaril.Wasm.SpecTec.Sim10.Whole (adminsT adminT10)

variable {B : Builtins} {H : Type} {hn : H → String}

/-- **`m` is a `moduleinst` of `utf8Env10T B`**, exports included. -/
def ModOk10 (B : Builtins) (m : ModuleInst) : Prop :=
  TypedV (utf8Env10T B) (.varT "moduleinst" []) (moduleInstV m)

/-- A typed function instance has a `ModOk10` module. -/
theorem funcMod10_of_typed {fi : FuncInst V1.Func H}
    (h : TypedV (utf8Env10T B) (.varT "funcinst" []) (funcInstV hn fi)) :
    FuncMod10 (ModOk10 B) fi := by
  rintro t m fn rfl
  exact ((typedV_funcInst_iffE (sameTyps_utf8 B)).1 h).2.1

/-- **A stripped function instance with a `ModOk10` module is typed with its exports.** -/
theorem typedV_funcInst_unstrip10 {fi : FuncInst V1.Func H}
    (h : TypedV (utf8Env10T B) (.varT "funcinst" []) (funcInstV hn (stripFI10 fi)))
    (hm : FuncMod10 (ModOk10 B) fi) :
    TypedV (utf8Env10T B) (.varT "funcinst" []) (funcInstV hn fi) := by
  cases fi with
  | wasm t m fn =>
    obtain ⟨hT, -, hC⟩ := (typedV_funcInst_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_funcInst_iffE (sameTyps_utf8 B)).2 ⟨hT, hm t m fn rfl, hC⟩
  | host t hh => exact h

/-- **A stripped store whose defined functions have `ModOk10` modules is typed.** -/
theorem typedV_store_unstrip10 {s : Store H}
    (h : TypedV (utf8Env10T B) storeT (storeV hn (stripStore10 s)))
    (hm : ∀ fi ∈ s.funcs, FuncMod10 (ModOk10 B) fi) :
    TypedV (utf8Env10T B) storeT (storeV hn s) := by
  obtain ⟨hF, hG, hT, hM⟩ := (typedV_store_iffE (sameTyps_utf8 B)).1 h
  refine (typedV_store_iffE (sameTyps_utf8 B)).2 ⟨?_, hG, hT, hM⟩
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 hu
  have hs : funcInstV hn (stripFI10 fi) ∈ (stripStore10 s).funcs.map (funcInstV hn) := by
    simp only [stripStore10, List.map_map]
    exact List.mem_map_of_mem (f := funcInstV hn ∘ stripFI10) hfi
  exact typedV_funcInst_unstrip10 (Sim.typedV_list_iff.1 hF _ hs) (hm fi hfi)

/-- **A stripped frame with a `ModOk10` module is typed.** -/
theorem typedV_frame_unstrip10 {f : Frame}
    (h : TypedV (utf8Env10T B) frameT (frameV (stripFrame10 f))) (hm : ModOk10 B f.module) :
    TypedV (utf8Env10T B) frameT (frameV f) :=
  (typedV_frame_iffE (sameTyps_utf8 B)).2 ⟨((typedV_frame_iffE (sameTyps_utf8 B)).1 h).1, hm⟩

mutual
/-- **A stripped `admininstr` whose frames have `ModOk10` modules is typed.** -/
theorem typedV_admin_unstrip10 : ∀ a : Admin,
    TypedV (utf8Env10T B) adminT10 (adminToV (stripAdmin10 a)) → AdminMods10 (ModOk10 B) a →
      TypedV (utf8Env10T B) adminT10 (adminToV a)
  | .source _, h, _ => h
  | .invoke _, h, _ => h
  | .trap, h, _ => h
  | .label n cont body, h, hm => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_label_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_label_iffE (sameTyps_utf8 B)).2 ⟨h₁, h₂, typedV_admins_unstrip10 body h₃ hm⟩
  | .frame n f body, h, hm => by
    obtain ⟨h₁, h₂, h₃⟩ := (typedV_frameA_iffE (sameTyps_utf8 B)).1 h
    exact (typedV_frameA_iffE (sameTyps_utf8 B)).2
      ⟨h₁, typedV_frame_unstrip10 h₂ hm.1, typedV_admins_unstrip10 body h₃ hm.2⟩

/-- `typedV_admin_unstrip10` on a sequence. -/
theorem typedV_admins_unstrip10 : ∀ l : List Admin,
    TypedV (utf8Env10T B) adminsT (.list (adminsToV (stripAdmins10 l))) →
      AdminsMods10 (ModOk10 B) l → TypedV (utf8Env10T B) adminsT (.list (adminsToV l))
  | [], _, _ => typedV_listNil10
  | a :: l, h, hm => by
    obtain ⟨ha, hl⟩ := Sim.typedV_list_cons_iff.1 h
    exact Sim.typedV_list_cons_iff.2
      ⟨typedV_admin_unstrip10 a ha hm.1, typedV_admins_unstrip10 l hl hm.2⟩
end

mutual
/-- The frames of a typed `admininstr` have `ModOk10` modules. -/
theorem adminMods10_of_typed : ∀ a : Admin,
    TypedV (utf8Env10T B) adminT10 (adminToV a) → AdminMods10 (ModOk10 B) a
  | .source _, _ => trivial
  | .invoke _, _ => trivial
  | .trap, _ => trivial
  | .label _ _ body, h =>
    adminsMods10_of_typed body ((typedV_label_iffE (sameTyps_utf8 B)).1 h).2.2
  | .frame _ _ body, h =>
    have h' := (typedV_frameA_iffE (sameTyps_utf8 B)).1 h
    ⟨((typedV_frame_iffE (sameTyps_utf8 B)).1 h'.2.1).2, adminsMods10_of_typed body h'.2.2⟩

/-- `adminMods10_of_typed` on a sequence. -/
theorem adminsMods10_of_typed : ∀ l : List Admin,
    TypedV (utf8Env10T B) adminsT (.list (adminsToV l)) → AdminsMods10 (ModOk10 B) l
  | [], _ => trivial
  | a :: l, h =>
    have h' := Sim.typedV_list_cons_iff.1 h
    ⟨adminMods10_of_typed a h'.1, adminsMods10_of_typed l h'.2⟩
end

/-- **The module instances of a configuration typed in `utf8Env10T B` are `ModOk10`.** -/
theorem modsQ10_of_typed {c : Config H} (h : Typed10 (utf8Env10T B) hn c) :
    ModsQ10 (ModOk10 B) c := by
  obtain ⟨hz, hc⟩ := (typed10_iffE (sameTyps_utf8 B)).1 h
  obtain ⟨hs, hf⟩ := (typedV_stV_iffE (sameTyps_utf8 B)).1 hz
  obtain ⟨hF, -⟩ := (typedV_store_iffE (sameTyps_utf8 B)).1 hs
  exact ⟨fun fi hfi => funcMod10_of_typed (Sim.typedV_list_iff.1 hF _ (List.mem_map_of_mem hfi)),
    ((typedV_frame_iffE (sameTyps_utf8 B)).1 hf).2, adminsMods10_of_typed c.code hc⟩

/-- **A stripped configuration typed in `utf8Env10T B`, whose module instances are `ModOk10`, is
typed with its exports.** -/
theorem typed10_unstrip {c : Config H} (h : Typed10 (utf8Env10T B) hn (stripConfig10 c))
    (hm : ModsQ10 (ModOk10 B) c) : Typed10 (utf8Env10T B) hn c := by
  obtain ⟨hz, hc⟩ := (typed10_iffE (sameTyps_utf8 B)).1 h
  obtain ⟨hs, hf⟩ := (typedV_stV_iffE (sameTyps_utf8 B)).1 hz
  exact (typed10_iffE (sameTyps_utf8 B)).2
    ⟨(typedV_stV_iffE (sameTyps_utf8 B)).2
      ⟨typedV_store_unstrip10 hs hm.funcs, typedV_frame_unstrip10 hf hm.frame⟩,
      typedV_admins_unstrip10 c.code hc hm.code⟩

/-- **The successor half of leg 2 for 1.0**: the successor of a V1 step from a configuration
typed in `utf8Env10T B` is typed there when its stripped form is typed in `simEnv10T B`. -/
theorem typed10U_succ (hB : ∀ ws, B.call "utf8" ws = none) {host : HostSemantics H}
    {c c' : Config H} (hc : Typed10 (utf8Env10T B) hn c) (h : Step host c c')
    (h' : Typed10 (simEnv10T B) hn (stripConfig10 c')) : Typed10 (utf8Env10T B) hn c' :=
  typed10_unstrip (typed10_utf8_10T hB h')
    (modsQ10_step h (noHost10_of_strip (Whole.noHost10_of_typedT
      (Whole.typedV_state_of_typed10T (typed10_strip hB hc)))) (modsQ10_of_typed hc))

end Silmaril.Wasm.SpecTec.Sim10.Utf8Strip10
