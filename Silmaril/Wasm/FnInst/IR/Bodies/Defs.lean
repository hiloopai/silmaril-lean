module

public import Silmaril.Wasm.FnInst.IR.Lang.Defs
public import Silmaril.Wasm.SSA.Native.Thms

/-!
# Body languages of the `ir` track: fragment, native fragment, SSA, Binaryen IR

Five body languages (`Lang`), all denoting terminating outcomes (`Beh`):

| language | bodies at a hole `h` | environment | denotation |
| --- | --- | --- | --- |
| `frag E` | fragment functions `FragFunc` of type `h` | any `E` (ignored) | `FragFunc.Run` |
| `fragNative E` | the same, passing the arity check `FragFunc.native` | `E` | `FragFunc.Run` |
| `ssa E` | lambda-SSA functions `SFunc` of type `h` | `E` | `SFunc.Run` |
| `ssaDec E` | SSA functions on which out-of-SSA succeeds | `E` | `SFunc.Run` |
| `bir H` | Binaryen functions `BFunc` recognised at `h` with a native body | `Store H × ModuleInst` | `Binaryen.Eval` (`nativeOut`) |

Translations (`Lang.Tr`, each exact, so each a comorphism of the body institutions):

| translation | direction | body map | exactness from |
| --- | --- | --- | --- |
| `toSSA E` | `frag → ssa` | `compileFunc` | `compileFunc_iff` |
| `ofSSA E` | `ssaDec → frag` | `decompileFunc` | `decompileFunc_iff` |
| `ofBir H` | `bir → fragNative` | `ofBFunc?` (recognition) | `native_adequate` |
| `nativeIncl E` | `fragNative → frag` | inclusion | `rfl` |
| `decIncl E` | `ssaDec → ssa` | inclusion | `rfl` |

The lowering `toBFunc?` and the compile/decompile round trip are partial, so they are not
translations; `Thms` states them as theorems where they succeed (`lower_body`,
`equiv_lower_iff`).
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.IR

open Silmaril.Wasm.SSA
open Silmaril.Wasm
open Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Execution.Core

/-- Integer value types as Wasm value types. -/
def intVal (t : IntType) : ValType := .num (.int t)

/-- The Wasm function type of a hole. -/
def Hole.funcType (h : Hole) : FuncType := ⟨h.params.map intVal, resultTypes h.result⟩

/-- A fragment function has the type of the hole. -/
def HasType (f : FragFunc) (h : Hole) : Prop := f.params = h.params ∧ f.result = h.result

/-- The structured fragment, with any environment type. -/
def frag (E : Type) : Lang where
  Body h := {f : FragFunc // HasType f h}
  Env := E
  den _ _ b := b.1.Run

/-- The fragment functions that pass the native arity check. -/
def fragNative (E : Type) : Lang where
  Body h := {f : FragFunc // HasType f h ∧ f.native = true}
  Env := E
  den _ _ b := b.1.Run

/-- Lambda-SSA functions. -/
def ssa (E : Type) : Lang where
  Body h := {s : SFunc // s.params = h.params ∧ s.result = h.result}
  Env := E
  den _ _ b := b.1.Run

/-- Lambda-SSA functions on which out-of-SSA succeeds. -/
def ssaDec (E : Type) : Lang where
  Body h := {s : SFunc // (s.params = h.params ∧ s.result = h.result) ∧ (decompileFunc s).isSome}
  Env := E
  den _ _ b := b.1.Run

/-- A Binaryen function recognised at a hole, with a native-checked body. -/
def BirBody (h : Hole) : Type := {bf : BFunc // ∃ f, ofBFunc? h.funcType bf = some f ∧ f.native = true}

/-- Binaryen's folded IR under silmaril's native interpreter, in a store and module instance:
the outcomes of the body on typed arguments, through the recognised function's locals and
result type. -/
def bir (H : Type) : Lang where
  Body := BirBody
  Env := Store H × ModuleInst
  den e h bf args o := ∃ f, ofBFunc? h.funcType bf.1 = some f ∧ args.map WVal.type = f.params ∧
    nativeOut e.1 e.2 f bf.1.body args o

/-! ## Recognition of Binaryen bodies -/

theorem BirBody.isSome {h : Hole} (bf : BirBody h) : (ofBFunc? h.funcType bf.1).isSome := by
  obtain ⟨f, hf, -⟩ := bf.2
  rw [hf]; rfl

/-- The fragment function of a Binaryen body. -/
def BirBody.recog {h : Hole} (bf : BirBody h) : FragFunc := (ofBFunc? h.funcType bf.1).get bf.isSome

theorem BirBody.recog_spec {h : Hole} (bf : BirBody h) :
    ofBFunc? h.funcType bf.1 = some bf.recog := (Option.some_get _).symm

theorem BirBody.recog_native {h : Hole} (bf : BirBody h) : bf.recog.native = true := by
  obtain ⟨f, hf, hn⟩ := bf.2
  have e : f = bf.recog := Option.some.inj (hf.symm.trans bf.recog_spec)
  exact e ▸ hn

theorem intVal_injective : Function.Injective intVal := by
  intro a b hab
  cases a <;> cases b <;> first | rfl | cases hab

theorem resultTypes_injective : Function.Injective resultTypes := by
  intro a b hab
  rcases a with _ | a <;> rcases b with _ | b <;> simp only [resultTypes,
    List.cons.injEq, and_true, List.nil_eq, List.cons_ne_nil] at hab ⊢
  exact congrArg some (intVal_injective hab)

/-- A function recognised at a hole has the hole's type. -/
theorem hasType_of_ofBFunc? {h : Hole} {bf : BFunc} {f : FragFunc}
    (hf : ofBFunc? h.funcType bf = some f) : HasType f h := by
  obtain ⟨hp, hr⟩ := ofBFunc?_types hf
  exact ⟨(List.map_injective_iff.mpr intVal_injective hp).symm, (resultTypes_injective hr).symm⟩

/-! ## Translations -/

/-- Compilation into SSA. -/
def toSSA (E : Type) : Lang.Tr (frag E) (ssa E) where
  body _ f := ⟨compileFunc f.1, f.2⟩
  env e := e
  den_body _ _ _ := funext fun _ => funext fun _ => propext compileFunc_iff

/-- Out-of-SSA. -/
def ofSSA (E : Type) : Lang.Tr (ssaDec E) (frag E) where
  body _ s := ⟨(decompileFunc s.1).get s.2.2, by
    obtain ⟨hp, hr⟩ := decompileFunc_params (Option.some_get s.2.2).symm
    exact ⟨hp.trans s.2.1.1, hr.trans s.2.1.2⟩⟩
  env e := e
  den_body _ _ s := funext fun _ => funext fun _ =>
    propext (decompileFunc_iff (Option.some_get s.2.2).symm)

/-- Recognition of Binaryen bodies. -/
def ofBir (H : Type) : Lang.Tr (bir H) (fragNative (Store H × ModuleInst)) where
  body _ bf := ⟨bf.recog, hasType_of_ofBFunc? bf.recog_spec, bf.recog_native⟩
  env e := e
  den_body e _ bf := funext fun args => funext fun o => propext <| by
    constructor
    · intro hr
      exact ⟨bf.recog, bf.recog_spec, hr.1, (native_adequate e.1 e.2
        (ofBFunc?_body bf.recog_spec) bf.recog_native hr.1 o).mp hr⟩
    · rintro ⟨f, hf, hty, hn⟩
      obtain rfl : f = bf.recog := Option.some.inj (hf.symm.trans bf.recog_spec)
      exact (native_adequate e.1 e.2 (ofBFunc?_body hf) bf.recog_native hty o).mpr hn

/-- Native-checked fragment functions are fragment functions. -/
def nativeIncl (E : Type) : Lang.Tr (fragNative E) (frag E) where
  body _ f := ⟨f.1, f.2.1⟩
  env e := e
  den_body _ _ _ := rfl

/-- Decompilable SSA functions are SSA functions. -/
def decIncl (E : Type) : Lang.Tr (ssaDec E) (ssa E) where
  body _ s := ⟨s.1, s.2.1⟩
  env e := e
  den_body _ _ _ := rfl

end Silmaril.Wasm.FnInst.IR
