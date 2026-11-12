module

public import Silmaril.Wasm.SpecTec.Sim.Round4Int.Thms
public import Silmaril.Wasm.SpecTec.Sim.ConfigOk.Thms
public import Silmaril.Wasm.Validation.Check.Validate

/-!
# Round 5: `Parts.succTyped` is false for ill-typed hosts

`Round4Int.Parts.succTyped` asks that the bounded Core successor of a valid, bounded configuration
be `Typed`. It holds for `HostOk` hosts (`Round4Int.succTyped_of_hostOk`). It fails for a finite
host that returns an ill-typed store:

* `hostFn`: a host function of type `[] -> []` (`dt0`), the only function of `store0`;
* `badStore`: `store0` with a second, Wasm function whose body is `i32.extend32_s`, an
  instruction that is not valid at `i32` (`IntUnOp.valid`). `instrToV` sends it to the junk
  `.tuple []` (`IntNumeric.instrToV_intUnOp_invalid`), which no `instr` inhabits, so the store is
  not a typed `store`. The store is still `Bounded`: `instrBnd` only bounds `try_table` and the
  SIMD memory instructions;
* `badHost`: the host whose every call returns `badStore` and no values; it is `HostFinite`;
* `invoke store0 0 []` is valid (silmaril-lean's `invoke_ok`) and bounded, and steps by
  `call_ref-hostfunc-res` to `⟨badStore, {}, []⟩`, bounded and not `Typed` in any `simEnv B`.

So `not_succTyped` refutes the field for every `B`, and `not_parts_all` shows that the hypothesis
of `Round4Int.wholeStepValid_of_parts` is unsatisfiable.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Pos

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics

/-- The closed function type `[] -> []`, as a one-member recursive group. -/
def dt0 : DefType := .defn (.group (.cons (.sub true .nil (.func .nil .nil)) .nil)) 0

theorem tyOk_dt0 : TyOk {} dt0 := tyOkC_sound' _ _ (by decide)

theorem expand_dt0 : Expand dt0 (.func .nil .nil) := ⟨rfl⟩

theorem tyBnd_dt0 : Round4.tyBnd dt0 = true := by decide

/-- The host function `()` of type `dt0`. -/
def hostFn : FuncInst Unit := { type := dt0, module := {}, code := .host () }

/-- A Wasm function of type `dt0` whose body is `i32.extend32_s`, invalid at `i32`. -/
def badFn : FuncInst Unit :=
  { type := dt0, module := {}, code := .wasm ⟨⟨0⟩, [], [.intUnOp .i32 (.extend .i32)]⟩ }

/-- The store holding only `hostFn`. -/
def store0 : Store Unit := { funcs := [hostFn] }

/-- `store0` with `badFn` appended. -/
def badStore : Store Unit := { funcs := [hostFn, badFn] }

/-- The host whose every call returns `badStore` and no values. -/
def badHost : HostSemantics Unit := fun _ _ _ o => o = .returned badStore (.values [])

/-- The host-name encoding at `Unit`. -/
def hnU : Unit → String := fun _ => "h"

theorem hnU_injective : Function.Injective hnU := fun _ _ _ => rfl

theorem hostFinite_badHost : HostFinite badHost :=
  fun _ _ _ => ⟨[.returned badStore (.values [])], fun _ => by simp [badHost]⟩

theorem storeOk_store0 : StoreOk store0 where
  tags := by simp [store0]
  globals := by simp [store0]
  mems := by simp [store0]
  tables := by simp [store0]
  funcs := by
    simp only [store0, List.mem_singleton]
    rintro _ rfl
    exact .host tyOk_dt0 expand_dt0 rfl
  elems := by simp [store0]
  structs := by simp [store0]
  arrays := by simp [store0]
  exns := by simp [store0]
  acyclicStructs := by simp [store0]
  acyclicArrays := by simp [store0]
  acyclicExns := by simp [store0]
  structsClosed := by simp [store0]
  arraysClosed := by simp [store0]

/-- The source configuration: `ref.func 0; call_ref dt0` on `store0`. -/
def srcCfg : Config Unit := invoke store0 0 []

theorem srcCfg_eq : srcCfg = ⟨store0, {}, [.ref (.func 0), .callRefType dt0]⟩ := rfl

/-- **The source is valid.** -/
theorem configOk_srcCfg : ConfigOk srcCfg [] := by
  obtain ⟨fi, ps, rs, hfi, hex, hok⟩ :=
    invoke_ok (a := 0) (vs := []) storeOk_store0 ⟨hostFn, .nil, .nil, rfl, expand_dt0, .nil⟩
  obtain rfl : fi = hostFn := Option.some.inj hfi.symm
  have hrs : rs = .nil := by
    cases hex with
    | mk h =>
      simp only [hostFn, dt0] at h
      cases h
      rfl
  subst hrs
  exact hok

/-- The empty module instance is bounded. -/
theorem moduleBnd_empty : Round4.ModuleBnd ({} : ModuleInst) := ⟨by simp, by simp⟩

/-- **The source is bounded.** -/
theorem bounded_srcCfg : Round4.Bounded srcCfg where
  store := ⟨⟨by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0]⟩,
    ⟨by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0]⟩,
    by simp [srcCfg_eq, store0]⟩
  storeBnd := ⟨by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0],
    by simp [srcCfg_eq, store0],
    by
      simp only [srcCfg_eq, store0, List.mem_singleton]
      rintro _ rfl
      exact ⟨tyBnd_dt0, moduleBnd_empty, fun _ h => by cases h⟩,
    by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0], by simp [srcCfg_eq, store0]⟩
  frame := moduleBnd_empty
  code := by simp [srcCfg_eq, Round4.AdminsBnd, Round4.AdminBnd, tyBnd_dt0]

/-- The successor: `badStore`, the empty frame, no code. -/
def dstCfg : Config Unit := ⟨badStore, {}, []⟩

/-- **The successor is bounded.** -/
theorem bounded_dstCfg : Round4.Bounded dstCfg where
  store := ⟨⟨by simp [dstCfg, badStore], by simp [dstCfg, badStore]⟩,
    ⟨by simp [dstCfg, badStore], by simp [dstCfg, badStore], by simp [dstCfg, badStore]⟩,
    by simp [dstCfg, badStore]⟩
  storeBnd := ⟨by simp [dstCfg, badStore], by simp [dstCfg, badStore],
    by simp [dstCfg, badStore],
    by
      simp only [dstCfg, badStore, List.mem_cons, List.not_mem_nil, or_false]
      rintro _ (rfl | rfl)
      · exact ⟨tyBnd_dt0, moduleBnd_empty, fun _ h => by cases h⟩
      · refine ⟨tyBnd_dt0, moduleBnd_empty, fun fn h => ?_⟩
        cases h
        decide,
    by simp [dstCfg, badStore], by simp [dstCfg, badStore], by simp [dstCfg, badStore]⟩
  frame := moduleBnd_empty
  code := trivial

/-- **Core steps** from the source to the successor (`call_ref-hostfunc-res`), at every profile. -/
theorem step_srcCfg (P : Profile) : Step P badHost srcCfg dstCfg :=
  Step.callRefHost (vs := []) (a := 0) (fi := hostFn) (ps := .nil) (rs := .nil) (h := ())
    (r := .values []) trivial rfl expand_dt0 rfl rfl rfl

set_option maxRecDepth 100000 in
theorem findTyp_funccode {B : Builtins} : (simEnv B).findTyp? "funccode" = some ([],
    [.instD [] [] (.variantT [.mk "FUNC" (.tupT [.mk "typeidx" (.varT "typeidx" []),
      .mk "local*" (.iterT (.varT "local" []) .list), .mk "expr" (.varT "expr" [])]) [] [],
      .mk "_HOSTFUNC" .textT [] []])]) := rfl

set_option maxRecDepth 100000 in
theorem findTyp_expr {B : Builtins} : (simEnv B).findTyp? "expr" =
    some ([], [.instD [] [] (.aliasT (.iterT (.varT "instr" []) .list))]) := rfl

/-- `badFn` is not a typed `funcinst`: its body holds the junk `.tuple []`. -/
theorem not_typedV_badFn (B : Builtins) :
    ¬ TypedV (simEnv B) funcinstT (funcInstV hnU badFn) := by
  intro h
  have hF := ConfigOk.hasTypFields_of_closedStruct ConfigOk.valsOnly_empty
    ConfigOk.findTyp_funcinst (h _ ConfigOk.valsOnly_empty)
  simp only [badFn, List.forall₂_cons, ConfigOk.fieldTyp] at hF
  have hc := IntNumeric.hasTyp_of_hasTypCase
    (Typing.hasTypCase_of_closedVariant findTyp_funccode hF.2.2.1) (prems := []) rfl
  obtain ⟨-, -, he⟩ := ConfigOk.hasTyp_triple_inv hc
  have hl := ConfigOk.hasTyp_of_closedAlias ⟨rfl, rfl, rfl⟩ findTyp_expr he
  obtain ⟨l, hl', hall⟩ := hasTyp_iterT_list_iff.1 hl
  cases hl'
  have hj : instrsToV [.intUnOp .i32 (.extend .i32)] = [.tuple []] := by
    simp only [instrsToV, IntNumeric.instrToV_intUnOp_invalid .i32 (.extend .i32) rfl]
  rw [hj] at hall
  exact IntNumeric.not_hasTyp_instr_tuple B ConfigOk.valsOnly_empty []
    (hasTypList_iff.1 hall _ (List.mem_singleton_self _))

/-- **The successor is not `Typed`**, in any `simEnv B`. -/
theorem not_typed_dstCfg (B : Builtins) : ¬ Typed (simEnv B) hnU dstCfg := by
  intro h
  have hs := ConfigOk.store_of_state ((Typing.typingFacts_simEnv B hnU).config _ |>.1 h).1
  exact not_typedV_badFn B (ConfigOk.funcinst_of_store hnU badStore 1 badFn hs rfl)

/-- **`Parts.succTyped` fails for `badHost`**, for every `B` and profile. -/
theorem not_succTyped (B : Builtins) (P : Profile) :
    ¬ ∀ (c c' : Config Unit) (ts : List CValType), ConfigOk c ts → Round4.Bounded c →
      Round4.Bounded c' → Step P badHost c c' → Typed (simEnv B) hnU c' := fun h =>
  not_typed_dstCfg B (h srcCfg dstCfg [] configOk_srcCfg bounded_srcCfg bounded_dstCfg
    (step_srcCfg P))

/-- **The hypothesis of `Round4Int.wholeStepValid_of_parts` is unsatisfiable**: at `Unit`, the
injective `hnU` and the finite `badHost`, `Parts` fails for every profile. -/
theorem not_parts_all :
    ¬ ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → ∀ (nd : Bool) (r : RelaxedChoice),
        Round4Int.Parts hn (Profile.spec nd r) host := fun h =>
  not_succTyped _ _ (h Unit hnU hnU_injective badHost hostFinite_badHost false {}).succTyped

end Silmaril.Wasm.SpecTec.Sim.Round5.Pos
