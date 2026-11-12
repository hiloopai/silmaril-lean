module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs

/-!
# SpecTec ↔ Core 3.0, round 7: where typing cannot see `$utf8` (pass 8)

`Round7.Task.envAgreeNE` asks SpecTec's `Step` to read alike in `simEnv B` and `utf8Env B`.
Pass 7 proved the evaluator half (`Round7.Script.evalExp_utf8Env_eq`). The rest is in the
typing relation `Sem.hasTyp`, which the backend reading `SStepB` uses for every quantifier
(`QuantsOk`). In `simEnv B` the type `name` cannot type a non-empty name (its premise calls
`$utf8`, whose clauses run out of fuel); in `utf8Env B` it can. This header names the types and
values on which the two environments type alike.

* `tyA`: 141 reachable syntax types whose reference closure avoids `name`. Typing agrees on
  them at **every** value.
* `tyB`: `tyA` and the ten reachable types that reach `name` only through the `EXPORTS` field
  of `moduleinst` (`config`, `state`, `store`, `frame`, `funcinst`, `funccode`, `moduleinst`,
  `instr`, `expr`, `hostcallresult`). Typing agrees on them at every value whose `EXPORTS`
  fields are empty (`ExpFree`). Of the reachable types only `name` and `exportinst` are left out.
* `tyOk A S t`: every type that `t` names is in `S`, every type argument is `tyOk A A`, and every
  expression inside `t` is `goodEvsB` (calls only reachable definitions other than `$utf8`).
* `fieldsOk`, `casesOk`, `defTypOk`, `instsOk`, `typMapOk`: the same for type definitions.
  With the flag `b`, a record field named `EXPORTS` is exempt, provided its type is a list
  type; the values it is checked at are `[]` (`ExpFree`). Variant-case quantifiers are always
  `tyOk A A`: their values are computed, not taken from the typed value.

`TypsOk A ρ`: every type variable of `ρ` is bound to a `tyOk A A` type. `ExpFree v`: every
record inside `v` has an empty `EXPORTS` field, if it has one.

The kernel checks that the fixed wasm-3.0 script satisfies `typMapOk` for both sets
(`Round7.TypAgree.typMapOk_A`, `typMapOk_B`), and that every rule of a relation `Step` reaches
quantifies over `tyB` (`relQuantsOk_B`). The sets are lists computed outside Lean, and need no
trust.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.Wasm.SpecTec.Sim.Round7.Script

/-- **Harmless events, as a check**: every definition referred to is reachable and not `$utf8`,
and every relation referred to is reachable. -/
def goodEvsB (l : List Ev) : Bool := l.all fun e => match e with
  | .ref 1 x => stepReach.contains (1, x) && x != "utf8"
  | .ref 0 x => stepReach.contains (0, x)
  | _ => true

mutual
/-- **A type over the names `S`**, with type arguments over `A`. -/
def tyOk (A S : List String) : Typ → Bool
  | .varT x args => S.contains x && argsOk A args
  | .tupT bs => bindsOk A S bs
  | .iterT t it => tyOk A S t && goodEvsB (evIter it)
  | _ => true

/-- The arguments of a type reference: types over `A`, or harmless expressions. -/
def argsOk (A : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => tyOk A A t && argsOk A r
  | .expA e :: r => goodEvsB (evExp e) && argsOk A r
  | _ :: _ => false

/-- `tyOk` on tuple binders. -/
def bindsOk (A S : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => tyOk A S t && bindsOk A S bs
end

/-- A list type `t*`. -/
def isListT : Typ → Bool
  | .iterT _ .list => true
  | _ => false

/-- **Record fields over `S`**; with `b`, a field named `EXPORTS` is exempt if it is a list. -/
def fieldsOk (A S : List String) (b : Bool) : List TypField → Bool
  | [] => true
  | .mk a t _ prems :: fs =>
      (if b && a == "EXPORTS" then isListT t else tyOk A S t) && goodEvsB (evPrems prems) &&
        fieldsOk A S b fs

/-- Quantifiers typed over `S`. -/
def quantsOk (A S : List String) (qs : List Param) : Bool :=
  qs.all fun q => match q with
    | .expP _ t => tyOk A S t
    | _ => true

/-- **Variant cases over `S`**. -/
def casesOk (A S : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs =>
      tyOk A S t && quantsOk A A qs && goodEvsB (evPrems prems) && casesOk A S cs

/-- **A type definition's body over `S`.** -/
def defTypOk (A S : List String) (b : Bool) : DefTyp → Bool
  | .aliasT t => tyOk A S t
  | .structT fs => fieldsOk A S b fs
  | .variantT cs => casesOk A S cs

/-- **The instances of a type family over `S`**: harmless argument patterns and bodies. -/
def instsOk (A S : List String) (b : Bool) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ pats dt => goodEvsB (evArgs pats) && defTypOk A S b dt

/-- **Every type of `m` named in `S` is over `S`.** -/
def typMapOk (A S : List String) (b : Bool) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || instsOk A S b p.2.2

/-- **The rules of every relation of `m` that `Step` reaches quantify over `S`.** -/
def relQuantsOk (A S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !stepReach.contains (0, p.1) || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => quantsOk A S qs

/-- **The reachable types whose reference closure avoids `name`** (computed outside Lean by a
reference closure over `specs/spectec/wasm-3.0.ast`; checked by `typMapOk_A`). `X` is the
type parameter of `list`. -/
def tyA : List String :=
  ["absheaptype", "addr", "addrtype", "arrayaddr", "arrayinst", "binop_", "bit", "blocktype",
  "bshape", "byte", "catch", "char", "comptype", "consttype", "context", "cvtop__", "dataaddr",
  "dataidx", "datainst", "datatype", "deftype", "dim", "elemaddr", "elemidx", "eleminst",
  "elemtype", "exnaddr", "exninst", "exp", "externaddr", "fieldidx", "fieldtype", "fieldval",
  "final", "fN", "fNmag", "Fnn", "funcaddr", "funcidx", "globaladdr", "globalidx", "globalinst",
  "globaltype", "half", "heaptype", "hostaddr", "hostfunc", "idx", "iN", "init", "Inn",
  "instrtype", "ishape", "Jnn", "K", "labelidx", "lane_", "laneidx", "lanetype", "limits",
  "list", "lit_", "Lnn", "loadop_", "local", "localidx", "localtype", "m", "M", "memaddr",
  "memarg", "memidx", "meminst", "memtype", "mut", "n", "N", "null", "num_", "numtype",
  "oktypenat", "pack_", "packtype", "Pnn", "rectype", "ref", "reftype", "relaxed2", "relop_",
  "result", "resulttype", "shape", "storagetype", "storeop_", "structaddr", "structinst",
  "subtype", "sx", "sz", "tableaddr", "tableidx", "tableinst", "tabletype", "tagaddr", "tagidx",
  "taginst", "tagtype", "testop_", "typeidx", "typeuse", "typevar", "u31", "u32", "u64", "u8",
  "uN", "unop_", "val", "valtype", "vbinop_", "vcvtop__", "vec_", "vectype", "vextbinop__",
  "vextternop__", "vextunop__", "vloadop_", "vN", "Vnn", "vrelop_", "vshiftop_", "vswizzlop_",
  "vternop_", "vtestop_", "vunop_", "vvbinop", "vvternop", "vvtestop", "vvunop", "X", "zero"]

/-- **The reachable types other than `name` and `exportinst`**: `tyA` and the ten that reach
`name` only through `moduleinst`'s `EXPORTS` field. -/
def tyB : List String :=
  tyA ++ ["config", "expr", "frame", "funccode", "funcinst", "hostcallresult", "instr",
    "moduleinst", "state", "store"]

/-- **Every type variable of `ρ` is bound to a type over `A`.** -/
def TypsOk (A : List String) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.typs, tyOk A A p.2 = true

/-- **Every record inside the value has an empty `EXPORTS` field, if it has one.** -/
inductive ExpFree : Value → Prop where
  | bool (b : Bool) : ExpFree (.bool b)
  | num (n : Num) : ExpFree (.num n)
  | text (t : Text) : ExpFree (.text t)
  | tuple {vs : List Value} : (∀ w ∈ vs, ExpFree w) → ExpFree (.tuple vs)
  | case (op : MixopS) {w : Value} : ExpFree w → ExpFree (.case op w)
  | struct {gs : List (AtomS × Value)} :
      (∀ p ∈ gs, ExpFree p.2) → (∀ p ∈ gs, p.1 = "EXPORTS" → p.2 = .list []) →
        ExpFree (.struct gs)
  | list {vs : List Value} : (∀ w ∈ vs, ExpFree w) → ExpFree (.list vs)
  | opt {o : Option Value} : (∀ w ∈ o, ExpFree w) → ExpFree (.opt o)

end Silmaril.Wasm.SpecTec.Sim.Round7.TypAgree
