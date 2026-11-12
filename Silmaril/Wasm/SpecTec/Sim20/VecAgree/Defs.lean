module

public import Silmaril.Wasm.SpecTec.Sim20.VecFix.Defs
public import Silmaril.Wasm.SpecTec.Sim20.ElseAgree.Defs

/-!
# Typing across the 2.0 vector errata: the restriction (definitions)

`VecFix.simEnv20V` corrects two defects of the wasm-2.0 script on top of `StoreFix.simEnv20T`
(`docs/projects/spectec/README.md`):

* the `VEXTRACT_LANE` case of `instr` and `admininstr`, which no value inhabits in `simEnv20T`,
  is restated (`VecFix.extractCaseFix`);
* the instance lists of the three operator families `vunop_`, `vbinop_` and `vrelop_` gain two
  float instances in front (`VecFix.fixFamily`).

The first is a repair of uninhabited cases (round 4's `StoreAgree.TypRepair`), so typing only
grows. The second is not: at a float shape `F32 X M`, `simEnv20T` selects the integer instance and
`simEnv20V` the float one, and the integer instance has cases the float one lacks (`MIN sx`,
`LT sx`, …). Typing does not grow at every value. It grows at the values this header names:

* `simEnv20X B` is the intermediate environment: `simEnv20T B` with only the `VEXTRACT_LANE`
  correction. `VecFix.fixedV20` is `fixedX20` with the three families replaced (by `rfl`).
* `fams` are the three families, `opOf f` the instruction case whose payload is `payT f`
  (`shape` and then `f(shape)`), and `fNames f` the case names of the float instance.
* `FloatSh a`: `a` is a shape whose lane type is `F32` or `F64`, at any dimension. This is exactly
  where the two prepended patterns `F32 X M` and `F64 X M` match.
* `PayOk f w`: if `w` is a pair `(a, b)` with `a` a float shape, then `b` is a nullary case named
  in `fNames f`. `VOk v`: every `VUNOP`, `VBINOP` and `VRELOP` case inside `v` has a `PayOk`
  payload. Every image of a V2 instruction is `VOk` (V2's float vector operators are nullary
  and named as in the float instance).
* `ffT t`: `t` names no family directly (`ElseAgree.GoodT fams`).
* `TOk`, `BOk`, `DOk`, `CasesOk`, `InstsOk`: the shapes in which the script's type definitions
  mention the families: only as the payload `payT f` of the case `opOf f`. Case quantifiers are
  typed alike in both environments (`QEq`), in scopes whose type variables are not named like
  declared types (`TN`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Script (evTyp evBinds)
open Silmaril.Wasm.SpecTec.Sim20.ElseAgree (GoodT)

/-! ## The intermediate environment -/

/-- The wasm-2.0 script with the `Step`, `STORE` and `VEXTRACT_LANE` errata, but not the family
errata. -/
noncomputable def fixedX20 : Script :=
  replaceDefs VecFix.adminFixV20 (replaceDefs VecFix.instrFixV20 StoreFix.fixedT20)

/-- The lookup environment of `fixedX20`, with the primitives `B`. -/
noncomputable def simEnv20X (B : Builtins) : Env := (envOfScript fixedX20).withBuiltins B

/-! ## The families -/

/-- The three operator families. -/
def fams : List String := ["vunop_", "vbinop_", "vrelop_"]

/-- The instruction case that carries an operator of the family `f`. -/
def opOf : String → String
  | "vunop_" => "VUNOP"
  | "vbinop_" => "VBINOP"
  | "vrelop_" => "VRELOP"
  | _ => ""

/-- The case names of the float instance of the family `f`. -/
def fNames : String → List String
  | "vunop_" => ["ABS", "NEG", "SQRT", "CEIL", "FLOOR", "TRUNC", "NEAREST"]
  | "vbinop_" => ["ADD", "SUB", "MUL", "DIV", "MIN", "MAX", "PMIN", "PMAX"]
  | "vrelop_" => ["EQ", "NE", "LT", "GT", "LE", "GE"]
  | _ => []

/-- `f(shape)`. -/
def famT (f : String) : Typ := .varT f [.expA (.varE "shape")]

/-- The binders `shape : shape, _ : f(shape)`. -/
def payB (f : String) : List TypBind := [.mk "shape" (.varT "shape" []), .mk "_" (famT f)]

/-- The payload of the case `opOf f`. -/
def payT (f : String) : Typ := .tupT (payB f)

/-- A shape with lane type `F32` or `F64`, at any dimension. -/
def FloatSh (a : Value) : Prop :=
  ∃ c M, (c = "F32" ∨ c = "F64") ∧ a = .case "%X%" (.tuple [.case c (.tuple []), M])

/-- A nullary case named in `fNames f`. -/
def NullIn (f : String) (v : Value) : Prop := ∃ o ∈ fNames f, v = .case o (.tuple [])

/-- At a float shape, the operator is one of the float instance's. -/
def PayOk (f : String) (w : Value) : Prop :=
  ∀ a b, w = .tuple [a, b] → FloatSh a → NullIn f b

/-- `f(shape)` read in `ρ`: if `shape` is bound to a float shape, the operator is the float
instance's. -/
def FamAt (f : String) (ρ : VarEnv) (v : Value) : Prop :=
  ∀ a, ρ.findVal? "shape" = some a → FloatSh a → NullIn f v

/-- **Every operator case inside the value has a `PayOk` payload.** -/
inductive VOk : Value → Prop where
  | bool (b : Bool) : VOk (.bool b)
  | num (n : Num) : VOk (.num n)
  | text (t : Text) : VOk (.text t)
  | tuple {vs : List Value} : (∀ w ∈ vs, VOk w) → VOk (.tuple vs)
  | case (op : MixopS) {w : Value} : VOk w → (∀ f ∈ fams, op = opOf f → PayOk f w) →
      VOk (.case op w)
  | struct {gs : List (AtomS × Value)} : (∀ p ∈ gs, VOk p.2) → VOk (.struct gs)
  | list {vs : List Value} : (∀ w ∈ vs, VOk w) → VOk (.list vs)
  | opt {o : Option Value} : (∀ w ∈ o, VOk w) → VOk (.opt o)

/-! ## Where the families occur in types -/

/-- `t` names no family directly. -/
def ffT (t : Typ) : Prop := GoodT fams (evTyp t)

/-- Binders that name no family directly. -/
def ffB (bs : List TypBind) : Prop := GoodT fams (evBinds bs)

/-- A type checked at a value: family-free, a family read in the scope, or a family payload. -/
def TOk (ρ : VarEnv) (t : Typ) (v : Value) : Prop :=
  ffT t ∨ (∃ f ∈ fams, t = famT f ∧ FamAt f ρ v) ∨ (∃ f ∈ fams, t = payT f ∧ PayOk f v)

/-- Binders checked at values: family-free, a family payload, or its family half. -/
def BOk (ρ : VarEnv) (bs : List TypBind) (vs : List Value) : Prop :=
  ffB bs ∨ (∃ f ∈ fams, bs = payB f ∧ PayOk f (.tuple vs)) ∨
    (∃ f ∈ fams, bs = [.mk "_" (famT f)] ∧ ∀ b, vs = [b] → FamAt f ρ b)

/-- No type variable of `ρ` is named like a declared type of `env` (as `matchTypV` binds only
undeclared names). -/
def TN (env : Env) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, env.memTyp p.1 = false

/-- The typing of a quantifier type is the same in `e₁` and `e₂`, in `TN` scopes. -/
def QEq (e₁ e₂ : Env) (t : Typ) : Prop :=
  ∀ n ρ v, TN e₁ ρ → hasTyp n e₂ ρ t v = hasTyp n e₁ ρ t v

/-- Variant cases: each payload is family-free or the payload of its operator's family, and every
quantifier type types alike. -/
def CasesOk (e₁ e₂ : Env) (cs : List TypCase) : Prop :=
  ∀ c ∈ cs, match c with
    | .mk op t qs _ => (ffT t ∨ ∃ f ∈ fams, t = payT f ∧ op = opOf f) ∧
        ∀ x t', Param.expP x t' ∈ qs → QEq e₁ e₂ t'

/-- A type definition's body. -/
def DOk (e₁ e₂ : Env) : DefTyp → Prop
  | .aliasT t => ffT t
  | .structT fs => ∀ f ∈ fs, match f with | .mk _ t _ _ => ffT t
  | .variantT cs => CasesOk e₁ e₂ cs

/-- A type's instances. -/
def InstsOk (e₁ e₂ : Env) (is : List Inst) : Prop :=
  ∀ i ∈ is, match i with | .instD _ _ dt => DOk e₁ e₂ dt

end Silmaril.Wasm.SpecTec.Sim20.VecAgree
