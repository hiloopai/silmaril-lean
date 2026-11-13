module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.StoreAgreeStore

/-!
# The scalar stores forward in `simEnv20T`, under a value prefix and a suffix

* `sstepT_storeTop20`: each of V2's six top-level scalar store steps (`Whole.StoreTop20`) is a
  step of `simEnv20T B` between the images, at builtins answering `$nbytes_`, `$ibytes_` and the
  float primitives, from a state typed in `simEnv20 B`. It is round 3's `fwd_storeTop20` moved by
  `sstepB20T_of_fires20` (no hypothesis: the four store rules are plain);
* `typedV_storeRedex20T`: the redex and the result of such a step are typed `admininstr*` in
  `simEnv20T B`, when the pack size is below the width (`PackOk20`);
* **`fwdT_storeCtx`**: the same step under a value prefix `vs` and a suffix `rest` typed in
  `simEnv20T B` is a step of `simEnv20T B` (through `ctxt-instrs`, `StoreFix.sstepT_ctxtInstrs`).
  In `simEnv20S` there is no such step: `ctxt-instrs` asks for an `admininstr*`, which a `STORE`
  never is (`Whole.not_typed20_storeStep`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.StoreAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SpecTec.Sim (TypedV stateT)
open Silmaril.Wasm.SpecTec.Sim.Round6.Reading (SStepB)
open Silmaril.Wasm.SpecTec.Sim20.StoreFix
open Silmaril.Wasm.SpecTec.Sim20.StepFix (adminsTy valsTy)
open Silmaril.Wasm.SpecTec.Sim20.Whole (StoreTop20 storeB NBytes20 LaneCalls20 storeNumV_int
  storeNumV_float fires_storeNumTrap fires_storeNumVal fires_storePackTrap fires_storePackVal)

variable {H : Type} {B : Builtins} {hn : H → String}

/-- **The top-level stores, in `simEnv20T`.** -/
theorem sstepT_storeTop20 {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    (hN : NBytes20 B) {c c' : Config H}
    (hz : TypedV (simEnv20 B) stateT (stateV hn c.store c.frame)) (h : StoreTop20 c c') :
    SStepB (simEnv20T B) (configV hn c) (configV hn c') := by
  cases h with
  | intTrap ha hm h =>
    exact sstepB20T_of_fires20 B (by decide) (fires_storeNumTrap (storeNumV_int _ _) hz ha hm h)
  | intVal ha hm hw =>
    exact sstepB20T_of_fires20 B (by decide) (fires_storeNumVal hN (storeNumV_int _ _) hz ha hm hw)
  | floatTrap ha hm h =>
    exact sstepB20T_of_fires20 B (by decide) (fires_storeNumTrap (storeNumV_float _ _) hz ha hm h)
  | floatVal ha hm hw =>
    exact sstepB20T_of_fires20 B (by decide)
      (fires_storeNumVal hN (storeNumV_float _ _) hz ha hm hw)
  | packTrap ha hm h =>
    exact sstepB20T_of_fires20 B (by decide) (fires_storePackTrap hz ha hm h)
  | packVal ha hm hw =>
    exact sstepB20T_of_fires20 B (by decide) (fires_storePackVal hF hL hz ha hm hw)

/-- Every packed integer store in `code` packs below its width (2.0 validation). -/
def PackOk20 (code : List Admin) : Prop :=
  ∀ t sz ao, Admin.plain (.intStore t (some sz) ao) ∈ code → sz.width < t.width

theorem typedV_admin_num20T (n : NumVal) :
    TypedV (simEnv20T B) (.varT "admininstr" []) (valV (.num n)) :=
  typedV_to20T (by decide) (Whole.typedV_admin_num20 n)

theorem typedV_trap20T : TypedV (simEnv20T B) adminsTy (.list (adminsToV [.trap])) :=
  typedV_list_to20T (by decide) Whole.typedV_admins_trap20

theorem typedV_nil20T : TypedV (simEnv20T B) adminsTy (.list (adminsToV [])) :=
  Sim.typedV_list_iff.2 (by simp [adminsToV])

/-- A three-instruction store redex is typed. -/
theorem typedV_redex3_20T {i : BitVec 32} {a st : Admin}
    (ha : TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV a))
    (hst : TypedV (simEnv20T B) (.varT "admininstr" []) (adminToV st)) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV [constI32 i, a, st])) := by
  refine Sim.typedV_list_iff.2 fun u hu => ?_
  simp only [adminsToV, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact typedV_admin_num20T ⟨.int .i32, i⟩
  · exact ha
  · exact hst

theorem none_packOk (w : Nat) : ∀ sz : PackSize, (none : Option PackSize) = some sz → sz.width < w :=
  fun _ h => nomatch h

/-- **The redex and the result of a top-level store are typed in `simEnv20T`.** -/
theorem typedV_storeRedex20T {c c' : Config H} (h : StoreTop20 c c') (hp : PackOk20 c.code) :
    TypedV (simEnv20T B) adminsTy (.list (adminsToV c.code)) ∧
      TypedV (simEnv20T B) adminsTy (.list (adminsToV c'.code)) := by
  cases h with
  | @intTrap s f t ao i x =>
    exact ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.int t, x⟩)
      (typedV_intStore20T _ _ _ (none_packOk _)), typedV_trap20T⟩
  | @intVal s f t ao i x =>
    exact ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.int t, x⟩)
      (typedV_intStore20T _ _ _ (none_packOk _)), typedV_nil20T⟩
  | @floatTrap s f t ao i x =>
    exact ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.float t, x⟩) (typedV_floatStore20T _ _),
      typedV_trap20T⟩
  | @floatVal s f t ao i x =>
    exact ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.float t, x⟩) (typedV_floatStore20T _ _),
      typedV_nil20T⟩
  | @packTrap s f t sz ao i x =>
    refine ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.int t, x⟩) (typedV_intStore20T _ _ _ ?_),
      typedV_trap20T⟩
    rintro sz' ⟨⟩
    exact hp t sz ao (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  | @packVal s f t sz ao i x =>
    refine ⟨typedV_redex3_20T (typedV_admin_num20T ⟨.int t, x⟩) (typedV_intStore20T _ _ _ ?_),
      typedV_nil20T⟩
    rintro sz' ⟨⟩
    exact hp t sz ao (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- A top-level store keeps the frame. -/
theorem StoreTop20.frame_eq {c c' : Config H} (h : StoreTop20 c c') : c'.frame = c.frame := by
  cases h <;> rfl

/-- **A top-level store under a value prefix and a suffix is a step of `simEnv20T`.** -/
theorem fwdT_storeCtx {P : Profile} (hF : Sim.Floats.FloatB P B) (hL : LaneCalls20 B)
    (hN : NBytes20 B) {s s' : Store H} {f f' : Frame} {code code' : List Admin}
    (vs : List Val) (rest : List Admin)
    (hz : TypedV (simEnv20 B) stateT (stateV hn s f))
    (hrest : TypedV (simEnv20T B) adminsTy (.list (adminsToV rest))) (hp : PackOk20 code)
    (h : StoreTop20 ⟨s, f, code⟩ ⟨s', f', code'⟩) :
    SStepB (simEnv20T B) (configV hn ⟨s, f, vals vs ++ code ++ rest⟩)
      (configV hn ⟨s', f', vals vs ++ code' ++ rest⟩) := by
  have hin := sstepT_storeTop20 hF hL hN hz h
  by_cases hne : vs ≠ [] ∨ rest ≠ []
  · have hz' := Whole.typedV_state_storeTop20 hz h
    obtain ⟨hc, hc'⟩ := typedV_storeRedex20T (B := B) h hp
    have hvs : TypedV (simEnv20T B) valsTy (.list (adminsToV (vals vs))) := by
      rw [Pure.adminsToV_vals]
      exact typedV_list_to20T (by decide) (Whole.typedV_vals20 vs)
    have hs := sstepT_ctxtInstrs (typedV_to20T (by decide) hz) (typedV_to20T (by decide) hz') hvs
      hc hc' hrest (by simpa [Pure.adminsToV_eq_map, vals] using hne) ((sstepB20T_iff B).1 hin)
    refine (sstepB20T_iff B).2 ?_
    simpa only [configV, Pure.adminsToV_append] using hs
  · obtain ⟨rfl, rfl⟩ : vs = [] ∧ rest = [] := by simpa [not_or] using hne
    simpa [vals] using hin

end Silmaril.Wasm.SpecTec.Sim20.StoreAgree
