module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Roots.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer.Defs

/-!
# Round 9: the evaluator commutes with an injective re-encoding of `EXPORTS` fields (definitions)

Round 8's `Round8.CodeErase` (the evaluator-level erasure of round 3, copied for `CODE` fields
with an injective replacement) copied once more, for **`EXPORTS`** fields and an **arbitrary**
injective replacement:

* `XTau`: a class carrying a function `τ : Value → Value` and its injectivity. The replacement is
  a class so that the copied text needs no new argument.
* `swapX v`: `v` with the contents `u` of every record field named `EXPORTS` replaced by
  `XTau.τ u` (not recursively); everything else is kept. Since `τ` is injective, so is `swapX`, and
  `QInj Q` holds for every `Q` (`XSwap.Swap.qInj`). With `τ` the `Sim20.Utf8Swap` involution,
  `swapX` is `Utf8Swap.swapV τ` (`XSwap.Swap.swapX_eq_swapV`).
* The rest is round 3's machinery with `EXPORTS` as the field: the scope operations
  (`Erase.eraseScope`, `ScopeIn`, `EOK`, `FO`), the syntactic check (`EraseAll.xExp` …: no
  `.EXPORTS` projection, record field or path step, compositions only with `nilLit` left operands,
  updates only along `updOk` paths), the invariants (`SG`, `ArgIn`, `ER`), the hypotheses
  (`Hyps`) and the statement (`EraseAt`). `updOk` tests the last field step against `codeAtoms`,
  which is empty: the swap set used is every value, so no update can leave it.

The proof is `XSwap.EraseAll.eraseAt` (`Raw/…/Sim20/XSwap/EAll.lean`), for every environment that
satisfies `Hyps`; the 2.0 script is checked separately.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.concreteInstances false

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap

open Silmaril.SpecTec.Sem

/-! ## The replacement -/

/-- **An injective replacement for the contents of `EXPORTS` fields.** -/
class XTau where
  /-- The replacement. -/
  τ : Value → Value
  /-- It is injective. -/
  inj : ∀ {u v : Value}, τ u = τ v → u = v

end Silmaril.Wasm.SpecTec.Sim20.XSwap

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

variable [XTau]

/-! ## The re-encoding -/

mutual
/-- **Re-encode the export lists**: the contents `u` of every record field named `EXPORTS` become
`XTau.τ u`; the rest is kept, deeply. -/
def swapX : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (swapXs vs)
  | .case op w => .case op (swapX w)
  | .struct gs => .struct (swapXf gs)
  | .list vs => .list (swapXs vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (swapX w))

/-- `swapX` on a list of values. -/
def swapXs : List Value → List Value
  | [] => []
  | v :: vs => swapX v :: swapXs vs

/-- `swapX` on the fields of a record: an `EXPORTS` field `u` becomes `XTau.τ u`. -/
def swapXf : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, if a = "EXPORTS" then XTau.τ v else swapX v) :: swapXf gs
end

/-- The fields of a record include one named `EXPORTS`. -/
def hasExpX (gs : List (IL.AtomS × Value)) : Bool := gs.any fun g => g.1 == "EXPORTS"

mutual
/-- **No record of `v` has an `EXPORTS` field**, as a boolean. -/
def nxX : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => nxXs vs
  | .case _ w => nxX w
  | .struct gs => nxXf gs
  | .list vs => nxXs vs
  | .opt none => true
  | .opt (some w) => nxX w

/-- `nxX` on a list of values. -/
def nxXs : List Value → Bool
  | [] => true
  | v :: vs => nxX v && nxXs vs

/-- `nxX` on the fields of a record. -/
def nxXf : List (IL.AtomS × Value) → Bool
  | [] => true
  | (a, v) :: gs => nxX v && (a != "EXPORTS") && nxXf gs
end

mutual
/-- **Every record of `v` with an `EXPORTS` field satisfies `Q`.** -/
def AllIn (Q : Value → Prop) : Value → Prop
  | .bool _ => True
  | .num _ => True
  | .text _ => True
  | .tuple vs => AllIns Q vs
  | .case _ w => AllIn Q w
  | .struct gs => (hasExpX gs = true → Q (.struct gs)) ∧ AllInf Q gs
  | .list vs => AllIns Q vs
  | .opt none => True
  | .opt (some w) => AllIn Q w

/-- `AllIn` on a list of values. -/
def AllIns (Q : Value → Prop) : List Value → Prop
  | [] => True
  | v :: vs => AllIn Q v ∧ AllIns Q vs

/-- `AllIn` on the field values of a record. -/
def AllInf (Q : Value → Prop) : List (IL.AtomS × Value) → Prop
  | [] => True
  | (_, v) :: gs => AllIn Q v ∧ AllInf Q gs
end

mutual
/-- **Undo `swapX` along `Q`**: a record with an `EXPORTS` field that is the erasure of a
record satisfying `Q` goes back to (a chosen) one; elsewhere `unerase` recurses. Under `QInj Q`
it inverts `swapX` on `AllIn Q` values (`XSwap.Swap.unerase_eraseC`). -/
noncomputable def unerase (Q : Value → Prop) : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (uneraseS Q vs)
  | .case op w => .case op (unerase Q w)
  | .struct gs =>
    open Classical in
    if h : hasExpX gs = true ∧ ∃ r, Q r ∧ swapX r = .struct gs then h.2.choose
    else .struct (uneraseF Q gs)
  | .list vs => .list (uneraseS Q vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (unerase Q w))

/-- `unerase` on a list of values. -/
noncomputable def uneraseS (Q : Value → Prop) : List Value → List Value
  | [] => []
  | v :: vs => unerase Q v :: uneraseS Q vs

/-- `unerase` on the field values of a record. -/
noncomputable def uneraseF (Q : Value → Prop) : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, unerase Q v) :: uneraseF Q gs
end

/-- **`swapX` is injective on `Q`.** -/
def QInj (Q : Value → Prop) : Prop :=
  ∀ x y, Q x → Q y → swapX x = swapX y → x = y


end Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `swapX` on an argument: values are erased, the rest is kept. -/
def eraseA : ArgV → ArgV
  | .val v => .val (swapX v)
  | a => a

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap (swapX AllIn)


/-- **The erased scope**: `swapX` on every term binding. -/
def eraseScope (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.map fun p => (p.1, swapX p.2) }

/-- **The scope is in the swap set**: every term binding is `AllIn Q`. -/
def ScopeIn (Q : Value → Prop) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.vals, AllIn Q p.2

/-- `r'` is `r` with its answer erased, and every answer of `r` is `AllIn Q`. -/
def EOK (Q : Value → Prop) (r r' : Res Value) : Prop :=
  r' = swapX <$> r ∧ ∀ v, r = .ok v → AllIn Q v

mutual
/-- **First-order expressions**: no call, iteration, update, extension or composition, and no
atom `EXPORTS`. -/
inductive FO : Exp → Prop where
  | varE (x : IL.Id) : FO (.varE x)
  | boolE (b : Bool) : FO (.boolE b)
  | numE (m : Num) : FO (.numE m)
  | textE (t : Text) : FO (.textE t)
  | unE {op : UnOp} {t : OpTyp} {e : Exp} : FO e → FO (.unE op t e)
  | binE {op : BinOp} {t : OpTyp} {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.binE op t e₁ e₂)
  | cmpE {op : CmpOp} {t : OpTyp} {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.cmpE op t e₁ e₂)
  | tupE {es : List Exp} : FOs es → FO (.tupE es)
  | projE {e : Exp} {i : Int} : FO e → FO (.projE e i)
  | caseE {op : MixopS} {e : Exp} : FO e → FO (.caseE op e)
  | uncaseE {e : Exp} {op : MixopS} : FO e → FO (.uncaseE e op)
  | optNone : FO (.optE none)
  | optSome {e : Exp} : FO e → FO (.optE (some e))
  | theE {e : Exp} : FO e → FO (.theE e)
  | strE {fs : List ExpField} : FOf fs → FO (.strE fs)
  | dotE {e : Exp} {a : AtomS} : a ≠ "EXPORTS" → FO e → FO (.dotE e a)
  | listE {es : List Exp} : FOs es → FO (.listE es)
  | liftE {e : Exp} : FO e → FO (.liftE e)
  | memE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.memE e₁ e₂)
  | lenE {e : Exp} : FO e → FO (.lenE e)
  | catE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.catE e₁ e₂)
  | idxE {e₁ e₂ : Exp} : FO e₁ → FO e₂ → FO (.idxE e₁ e₂)
  | sliceE {e₁ e₂ e₃ : Exp} : FO e₁ → FO e₂ → FO e₃ → FO (.sliceE e₁ e₂ e₃)
  | cvtE {e : Exp} {t₁ t₂ : NumTyp} : FO e → FO (.cvtE e t₁ t₂)
  | subE {e : Exp} {t₁ t₂ : Typ} : FO e → FO (.subE e t₁ t₂)

/-- `FO` on a list. -/
inductive FOs : List Exp → Prop where
  | nil : FOs []
  | cons {e : Exp} {es : List Exp} : FO e → FOs es → FOs (e :: es)

/-- `FO` on record fields, none named `EXPORTS`. -/
inductive FOf : List ExpField → Prop where
  | nil : FOf []
  | cons {a : AtomS} {e : Exp} {fs : List ExpField} : a ≠ "EXPORTS" → FO e → FOf fs →
      FOf (.mk a e :: fs)
end

/-- **First-order paths**: index and slice bounds are first order and no step is `.EXPORTS`. -/
inductive FOp : Path → Prop where
  | rootP : FOp .rootP
  | idxP {p : Path} {e : Exp} : FOp p → FO e → FOp (.idxP p e)
  | sliceP {p : Path} {e₁ e₂ : Exp} : FOp p → FO e₁ → FO e₂ → FOp (.sliceP p e₁ e₂)
  | dotP {p : Path} {a : AtomS} : FOp p → a ≠ "EXPORTS" → FOp (.dotP p a)


end Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

variable [XTau]

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Swap (swapX swapXf AllIn QInj eraseA)
open Silmaril.Wasm.SpecTec.Sim20.XSwap.Erase (eraseScope ScopeIn)

/-- The field names an update path may not end in. Empty: the swap set used is every value. -/
def codeAtoms : List AtomS := []


/-! ## The syntactic check -/

/-- A record-literal field whose value evaluates to a list or to `ε`. -/
def nilShape : Exp → Bool
  | .listE [] => true
  | .optE none => true
  | .iterE _ (.mk .list _) => true
  | .iterE _ (.mk .list1 _) => true
  | .iterE _ (.mk (.listN _ _) _) => true
  | _ => false

/-- A record literal every field of which is `nilShape`: the left operand of a composition. -/
def nilLit : Exp → Bool
  | .strE fs => fs.all fun f => match f with | .mk _ e => nilShape e
  | _ => false

/-- The atom of the last field step of a path, if it has one. -/
def lastAtom? : Path → Option AtomS
  | .rootP => none
  | .idxP p _ => lastAtom? p
  | .sliceP p _ _ => lastAtom? p
  | .dotP _ a => some a

/-- **An update path whose last field step is not a field of `moduleinst`.** -/
def updOk (p : Path) : Bool :=
  match lastAtom? p with
  | none => true
  | some a => !(codeAtoms.contains a)

/-- No field step of the path is `EXPORTS`. -/
def dotsOk : Path → Bool
  | .rootP => true
  | .idxP p _ => dotsOk p
  | .sliceP p _ _ => dotsOk p
  | .dotP p a => a != "EXPORTS" && dotsOk p

mutual
/-- **The syntactic check** on an expression; see the module docstring. -/
def xExp (gr gd : String → Bool) : Exp → Bool
  | .varE _ => true
  | .boolE _ => true
  | .numE _ => true
  | .textE _ => true
  | .unE _ _ e => xExp gr gd e
  | .binE _ _ e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .cmpE _ _ e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .tupE es => xExps gr gd es
  | .projE e _ => xExp gr gd e
  | .caseE _ e => xExp gr gd e
  | .uncaseE e _ => xExp gr gd e
  | .optE eo => xOExp gr gd eo
  | .theE e => xExp gr gd e
  | .strE fs => xFields gr gd fs
  | .dotE e a => a != "EXPORTS" && xExp gr gd e
  | .compE e₁ e₂ => nilLit e₁ && xExp gr gd e₁ && xExp gr gd e₂
  | .listE es => xExps gr gd es
  | .liftE e => xExp gr gd e
  | .memE e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .lenE e => xExp gr gd e
  | .catE e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .idxE e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .sliceE e₁ e₂ e₃ => xExp gr gd e₁ && xExp gr gd e₂ && xExp gr gd e₃
  | .updE e₁ p e₂ => updOk p && xExp gr gd e₁ && xPath gr gd p && xExp gr gd e₂
  | .extE e₁ p e₂ => updOk p && xExp gr gd e₁ && xPath gr gd p && xExp gr gd e₂
  | .callE x args => gd x && xArgs gr gd args
  | .iterE e (.mk it ds) => xExp gr gd e && xIter gr gd it && xDoms gr gd ds
  | .cvtE e _ _ => xExp gr gd e
  | .subE e _ _ => xExp gr gd e

/-- `xExp` on a list. -/
def xExps (gr gd : String → Bool) : List Exp → Bool
  | [] => true
  | e :: es => xExp gr gd e && xExps gr gd es

/-- `xExp` on an option. -/
def xOExp (gr gd : String → Bool) : Option Exp → Bool
  | none => true
  | some e => xExp gr gd e

/-- `xExp` on record fields, none named `EXPORTS`. -/
def xFields (gr gd : String → Bool) : List ExpField → Bool
  | [] => true
  | .mk a e :: fs => a != "EXPORTS" && xExp gr gd e && xFields gr gd fs

/-- `xExp` on a path: its index and slice bounds, and no step `.EXPORTS`. -/
def xPath (gr gd : String → Bool) : Path → Bool
  | .rootP => true
  | .idxP p e => xPath gr gd p && xExp gr gd e
  | .sliceP p e₁ e₂ => xPath gr gd p && xExp gr gd e₁ && xExp gr gd e₂
  | .dotP p a => a != "EXPORTS" && xPath gr gd p

/-- `xExp` on an iterator: the bound of `ListN`. -/
def xIter (gr gd : String → Bool) : Iter → Bool
  | .listN e _ => xExp gr gd e
  | _ => true

/-- `xExp` on iteration domains. -/
def xDoms (gr gd : String → Bool) : List Dom → Bool
  | [] => true
  | .mk _ e :: ds => xExp gr gd e && xDoms gr gd ds

/-- `xExp` on an argument: a definition argument satisfies `gd`. -/
def xArg (gr gd : String → Bool) : Arg → Bool
  | .expA e => xExp gr gd e
  | .typA _ => true
  | .defA x => gd x
  | .gramA _ => true

/-- `xArg` on a list. -/
def xArgs (gr gd : String → Bool) : List Arg → Bool
  | [] => true
  | a :: l => xArg gr gd a && xArgs gr gd l

/-- `xExp` on a premise: a relation premise names a `gr` relation. -/
def xPrem (gr gd : String → Bool) : Prem → Bool
  | .rulePr x args _ e => gr x && xArgs gr gd args && xExp gr gd e
  | .ifPr e => xExp gr gd e
  | .letPr e₁ e₂ => xExp gr gd e₁ && xExp gr gd e₂
  | .elsePr => true
  | .iterPr pr (.mk it ds) => xPrem gr gd pr && xIter gr gd it && xDoms gr gd ds

/-- `xPrem` on a list. -/
def xPrems (gr gd : String → Bool) : List Prem → Bool
  | [] => true
  | pr :: prs => xPrem gr gd pr && xPrems gr gd prs
end

/-- `xExp` on a definition's clause: its argument patterns, body and premises. -/
def xClause (gr gd : String → Bool) : Clause → Bool
  | .defD _ args e prems => xArgs gr gd args && xExp gr gd e && xPrems gr gd prems

/-- `xExp` on a relation's rule: its conclusion and premises. -/
def xRule (gr gd : String → Bool) : Rule → Bool
  | .ruleD _ _ _ e prems => xExp gr gd e && xPrems gr gd prems

/-! ## The invariants -/

/-- Every definition variable of `ρ` names a `gd` definition. -/
def DefsG (gd : String → Bool) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.defs, gd p.2 = true

/-- **A scope in the invariant**: term bindings in the swap set, definition variables `gd`. -/
def SG (Q : Value → Prop) (gd : String → Bool) (ρ : VarEnv) : Prop := ScopeIn Q ρ ∧ DefsG gd ρ

/-- **An evaluated argument in the invariant.** -/
def ArgIn (Q : Value → Prop) (gd : String → Bool) : ArgV → Prop
  | .val v => AllIn Q v
  | .defName y => gd y = true
  | _ => True

/-- **Related results**: `r'` is `r` mapped by `f`, and every answer of `r` satisfies `P`. -/
def ER {α : Type} (f : α → α) (P : α → Prop) (r r' : Res α) : Prop :=
  r' = f <$> r ∧ ∀ a, r = .ok a → P a

/-- `swapX` on the value of a binding. -/
def eraseP (p : IL.Id × Value) : IL.Id × Value := (p.1, swapX p.2)

/-! ## The hypotheses -/

/-- **The builtins of `gd` names commute with erasure**, and keep the swap set. -/
def BIErase (Q : Value → Prop) (gd : String → Bool) (env : Env) : Prop :=
  ∀ x ws, gd x = true → (∀ w ∈ ws, ArgIn Q gd w) →
    env.builtins.call x (ws.map eraseA) = (env.builtins.call x ws).map swapX ∧
      ∀ u, env.builtins.call x ws = some u → AllIn Q u

/-- **Updates along `updOk` paths keep the swap set.** -/
def UpdSafe (Q : Value → Prop) (env : Env) : Prop :=
  ∀ m ρ v p w u, dotsOk p = true → updOk p = true → AllIn Q v → AllIn Q w →
    pathSet m env ρ v p w = .ok u → AllIn Q u

/-- **The hypotheses of the evaluator-level erasure.** -/
structure Hyps (Q : Value → Prop) (gr gd : String → Bool) (env : Env) : Prop where
  inj : QInj Q
  defs : ∀ x d, gd x = true → env.findDef? x = some d → ∀ c ∈ d.2.2, xClause gr gd c = true
  rels : ∀ x d, gr x = true → env.findRel? x = some d → ∀ r ∈ d.2.2.2, xRule gr gd r = true
  builtins : BIErase Q gd env
  upd : UpdSafe Q env

/-! ## The statement -/

section
variable (Q : Value → Prop) (gr gd : String → Bool) (env : Env)

/-- **Every member of the evaluator commutes with erasure at fuel `n`.** -/
structure EraseAt (n : Nat) : Prop where
  exp : ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
    ER swapX (AllIn Q) (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e)
  exps : ∀ ρ es, SG Q gd ρ → xExps gr gd es = true →
    ER (List.map swapX) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalExps n env ρ es) (evalExps n env (eraseScope ρ) es)
  expFields : ∀ ρ fs, SG Q gd ρ → xFields gr gd fs = true →
    ER (List.map eraseP) (fun gs => ∀ p ∈ gs, AllIn Q p.2 ∧ p.1 ≠ "EXPORTS")
      (evalExpFields n env ρ fs) (evalExpFields n env (eraseScope ρ) fs)
  arg : ∀ ρ a, SG Q gd ρ → xArg gr gd a = true →
    ER eraseA (ArgIn Q gd) (evalArg n env ρ a) (evalArg n env (eraseScope ρ) a)
  args : ∀ ρ l, SG Q gd ρ → xArgs gr gd l = true →
    ER (List.map eraseA) (fun ws => ∀ w ∈ ws, ArgIn Q gd w)
      (evalArgs n env ρ l) (evalArgs n env (eraseScope ρ) l)
  doms : ∀ ρ ds, SG Q gd ρ → xDoms gr gd ds = true →
    ER (List.map eraseP) (fun xvs => ∀ p ∈ xvs, AllIn Q p.2)
      (evalDoms n env ρ ds) (evalDoms n env (eraseScope ρ) ds)
  iterE : ∀ ρ e it ds, SG Q gd ρ → xExp gr gd e = true → xIter gr gd it = true →
    xDoms gr gd ds = true →
    ER swapX (AllIn Q) (evalIterE n env ρ e it ds) (evalIterE n env (eraseScope ρ) e it ds)
  iterList : ∀ ρ e xvs ido k, SG Q gd ρ → xExp gr gd e = true → (∀ p ∈ xvs, AllIn Q p.2) →
    ER swapX (AllIn Q) (evalIterList n env ρ e xvs ido k)
      (evalIterList n env (eraseScope ρ) e (xvs.map eraseP) ido k)
  rounds : ∀ ρ e rs, SG Q gd ρ → xExp gr gd e = true → (∀ r ∈ rs, ∀ p ∈ r, AllIn Q p.2) →
    ER (List.map swapX) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalRounds n env ρ e rs) (evalRounds n env (eraseScope ρ) e (rs.map (List.map eraseP)))
  pathGet : ∀ ρ v p, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    ER swapX (AllIn Q) (pathGet n env ρ v p) (pathGet n env (eraseScope ρ) (swapX v) p)
  pathSet : ∀ ρ v p w, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    pathSet n env (eraseScope ρ) (swapX v) p (swapX w) = swapX <$> pathSet n env ρ v p w
  patLen : ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
    patLen n env (eraseScope ρ) e = patLen n env ρ e
  matchExp : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchExp n env ρ e v) (matchExp n env (eraseScope ρ) e (swapX v))
  matchDefault : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchDefault n env ρ e v)
      (matchDefault n env (eraseScope ρ) e (swapX v))
  matchExps : ∀ ρ es vs, SG Q gd ρ → xExps gr gd es = true → (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchExps n env ρ es vs)
      (matchExps n env (eraseScope ρ) es (vs.map swapX))
  matchExpFields : ∀ ρ fs gs, SG Q gd ρ → xFields gr gd fs = true → (∀ p ∈ gs, AllIn Q p.2) →
    ER eraseScope (SG Q gd) (matchExpFields n env ρ fs gs)
      (matchExpFields n env (eraseScope ρ) fs (swapXf gs))
  matchIterE : ∀ ρ e it ds v, SG Q gd ρ → xExp gr gd e = true → xIter gr gd it = true →
    xDoms gr gd ds = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchIterE n env ρ e it ds v)
      (matchIterE n env (eraseScope ρ) e it ds (swapX v))
  matchIterList : ∀ ρ e ds ido vs, SG Q gd ρ → xExp gr gd e = true → xDoms gr gd ds = true →
    (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchIterList n env ρ e ds ido vs)
      (matchIterList n env (eraseScope ρ) e ds ido (vs.map swapX))
  matchRounds : ∀ ρ e xs ido i vs, SG Q gd ρ → xExp gr gd e = true → (∀ v ∈ vs, AllIn Q v) →
    ER (List.map (List.map swapX)) (fun rows => ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u)
      (matchRounds n env ρ e xs ido i vs)
      (matchRounds n env (eraseScope ρ) e xs ido i (vs.map swapX))
  matchArg : ∀ ρ a w, SG Q gd ρ → xArg gr gd a = true → ArgIn Q gd w →
    ER eraseScope (SG Q gd) (matchArg n env ρ a w) (matchArg n env (eraseScope ρ) a (eraseA w))
  matchArgs : ∀ ρ l ws, SG Q gd ρ → xArgs gr gd l = true → (∀ w ∈ ws, ArgIn Q gd w) →
    ER eraseScope (SG Q gd) (matchArgs n env ρ l ws)
      (matchArgs n env (eraseScope ρ) l (ws.map eraseA))
  callDef : ∀ ρ x l, SG Q gd ρ → gd x = true → xArgs gr gd l = true →
    ER swapX (AllIn Q) (callDef n env ρ x l) (callDef n env (eraseScope ρ) x l)
  tryClauses : ∀ cs ws, (∀ c ∈ cs, xClause gr gd c = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    ER swapX (AllIn Q) (tryClauses n env cs ws) (tryClauses n env cs (ws.map eraseA))
  premHolds : ∀ ρ pr, SG Q gd ρ → xPrem gr gd pr = true →
    ER eraseScope (SG Q gd) (premHolds n env ρ pr) (premHolds n env (eraseScope ρ) pr)
  premsHold : ∀ ρ prs, SG Q gd ρ → xPrems gr gd prs = true →
    ER eraseScope (SG Q gd) (premsHold n env ρ prs) (premsHold n env (eraseScope ρ) prs)
  premIter : ∀ ρ pr it ds, SG Q gd ρ → xPrem gr gd pr = true → xIter gr gd it = true →
    xDoms gr gd ds = true →
    ER eraseScope (SG Q gd) (premIter n env ρ pr it ds) (premIter n env (eraseScope ρ) pr it ds)
  premRounds : ∀ ρ pr xvs ido k, SG Q gd ρ → xPrem gr gd pr = true →
    (∀ p ∈ xvs, AllIn Q p.2) →
    ER eraseScope (SG Q gd) (premRounds n env ρ pr xvs ido k)
      (premRounds n env (eraseScope ρ) pr (xvs.map eraseP) ido k)
  derives : ∀ x op ws v, gr x = true → (∀ w ∈ ws, ArgIn Q gd w) → AllIn Q v →
    derives n env x op (ws.map eraseA) (swapX v) = derives n env x op ws v
  anyRule : ∀ op ps ws v rs, (∀ r ∈ rs, xRule gr gd r = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    AllIn Q v → anyRule n env op ps (ws.map eraseA) (swapX v) rs = anyRule n env op ps ws v rs

end



/-! ## Checking a script -/

/-- Every `gd` definition of `m` has clauses that pass the check. -/
def xDefsOk (gr gd : String → Bool) (m : Map DefDef) : Bool :=
  m.all fun p => !gd p.1 || p.2.2.2.all (xClause gr gd)

/-- Every `gr` relation of `m` has rules that pass the check. -/
def xRelsOk (gr gd : String → Bool) (m : Map RelDef) : Bool :=
  m.all fun p => !gr p.1 || p.2.2.2.2.all (xRule gr gd)

/-- Every `gr` relation of `m` has rules every further conclusion alternative of which passes the
check. -/
def xAltsOk (gr gd : String → Bool) (m : Map RelDef) : Bool :=
  m.all fun p => !gr p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ _ _ e _ =>
      (if Silmaril.Wasm.SpecTec.Sim.Round6.Reading.hasOptNil e then Silmaril.Wasm.SpecTec.Sim.Round6.Reading.optAlts e else []).all (xExp gr gd)

/-- The definitions and relations bound by the top-level definition `d` pass the check, and so
do the conclusion alternatives of the relations' rules. -/
def xDefOk (gr gd : String → Bool) (d : Def) : Bool :=
  xDefsOk gr gd (defsOfDef d) && xRelsOk gr gd (relsOfDef d) && xAltsOk gr gd (relsOfDef d)

/-! ## The 2.0 script -/

/-- **The names `Step` can reach** in the 2.0 script, by kind: relations (`0`), definitions (`1`),
syntax types (`2`). Computed outside Lean by a reference closure over `specs/spectec/wasm-2.0.ast`
from the relation `Step`; nothing depends on its being closed: the check `xExp` itself asks every
called definition to be `gd20` and every premise relation to be `gr20`. -/
def reach20 : List (Nat × String) :=
  [(0, "Step"), (0, "Step_pure"), (0, "Step_read"), (1, "E"), (1, "Ki"), (1, "M"), (1, "binop_"),
   (1, "blocktype"), (1, "bool"), (1, "concat_"), (1, "convert__"), (1, "cvtop__"), (1, "data"),
   (1, "default_"), (1, "demote__"), (1, "elem"), (1, "expon"), (1, "extend__"), (1, "fabs_"),
   (1, "fadd_"), (1, "fceil_"), (1, "fcopysign_"), (1, "fdiv_"), (1, "feq_"), (1, "ffloor_"),
   (1, "fge_"), (1, "fgt_"), (1, "fle_"), (1, "flt_"), (1, "fmax_"), (1, "fmin_"), (1, "fmul_"),
   (1, "fne_"), (1, "fnearest_"), (1, "fneg_"), (1, "fpmax_"), (1, "fpmin_"), (1, "fsqrt_"),
   (1, "fsub_"), (1, "ftrunc_"), (1, "funcaddr"), (1, "funcinst"), (1, "fzero"), (1, "global"),
   (1, "growmemory"), (1, "growtable"), (1, "half"), (1, "halfop"), (1, "iabs_"), (1, "iadd_"),
   (1, "iadd_sat_"), (1, "iand_"), (1, "iandnot_"), (1, "iavgr_"), (1, "ibits_"),
   (1, "ibitselect_"), (1, "ibytes_"), (1, "iclz_"), (1, "ictz_"), (1, "idiv_"), (1, "ieq_"),
   (1, "ieqz_"), (1, "ige_"), (1, "igt_"), (1, "ile_"), (1, "ilt_"), (1, "imax_"), (1, "imin_"),
   (1, "imul_"), (1, "ine_"), (1, "ineg_"), (1, "inot_"), (1, "inv_lanes_"), (1, "inv_signed_"),
   (1, "ior_"), (1, "ipopcnt_"), (1, "iq15mulr_sat_"), (1, "irem_"), (1, "irev_"), (1, "irotl_"),
   (1, "irotr_"), (1, "ishl_"), (1, "ishr_"), (1, "isize"), (1, "isub_"), (1, "isub_sat_"),
   (1, "ixor_"), (1, "jsize"), (1, "lanes_"), (1, "lanetype"), (1, "list_"), (1, "local"),
   (1, "lsize"), (1, "lsizenn"), (1, "lsizenn1"), (1, "lsizenn2"), (1, "mem"), (1, "memarg0"),
   (1, "narrow__"), (1, "nbytes_"), (1, "packnum_"), (1, "promote__"), (1, "psize"),
   (1, "reinterpret__"), (1, "relop_"), (1, "sat_s_"), (1, "sat_u_"), (1, "setproduct1_"),
   (1, "setproduct2_"), (1, "setproduct_"), (1, "signed_"), (1, "signif"), (1, "size"),
   (1, "sizenn"), (1, "sizenn1"), (1, "sizenn2"), (1, "table"), (1, "testop_"), (1, "trunc__"),
   (1, "trunc_sat__"), (1, "truncz"), (1, "type"), (1, "unop_"), (1, "unpack"), (1, "utf8"),
   (1, "vbinop_"), (1, "vbytes_"), (1, "vcvtop__"), (1, "vextbinop__"), (1, "vextunop__"),
   (1, "vrelop_"), (1, "vshiftop_"), (1, "vunop_"), (1, "vvbinop_"), (1, "vvternop_"),
   (1, "vvunop_"), (1, "with_data"), (1, "with_elem"), (1, "with_global"), (1, "with_local"),
   (1, "with_mem"), (1, "with_meminst"), (1, "with_table"), (1, "with_tableinst"), (1, "wrap__"),
   (1, "zero"), (1, "zeroop"), (2, "Fnn"), (2, "Inn"), (2, "Jnn"), (2, "Lnn"), (2, "M"),
   (2, "MUT"), (2, "N"), (2, "Pnn"), (2, "Vnn"), (2, "addr"), (2, "admininstr"), (2, "binop_"),
   (2, "bit"), (2, "blocktype"), (2, "byte"), (2, "char"), (2, "config"), (2, "cvtop"),
   (2, "dataaddr"), (2, "dataidx"), (2, "datainst"), (2, "dim"), (2, "elemaddr"), (2, "elemidx"),
   (2, "eleminst"), (2, "elemtype"), (2, "exp"), (2, "exportinst"), (2, "expr"),
   (2, "externaddr"), (2, "fN"), (2, "fNmag"), (2, "frame"), (2, "func"), (2, "funcaddr"),
   (2, "funcidx"), (2, "funcinst"), (2, "functype"), (2, "globaladdr"), (2, "globalidx"),
   (2, "globalinst"), (2, "globaltype"), (2, "half"), (2, "hostaddr"), (2, "iN"), (2, "idx"),
   (2, "instr"), (2, "ishape"), (2, "labelidx"), (2, "lane_"), (2, "laneidx"), (2, "lanetype"),
   (2, "limits"), (2, "list"), (2, "loadop_"), (2, "local"), (2, "localidx"), (2, "m"),
   (2, "memaddr"), (2, "memarg"), (2, "memidx"), (2, "meminst"), (2, "memtype"),
   (2, "moduleinst"), (2, "mut"), (2, "n"), (2, "name"), (2, "num_"), (2, "numtype"),
   (2, "pack_"), (2, "packtype"), (2, "ref"), (2, "reftype"), (2, "relop_"), (2, "resulttype"),
   (2, "shape"), (2, "state"), (2, "store"), (2, "sx"), (2, "sz"), (2, "tableaddr"),
   (2, "tableidx"), (2, "tableinst"), (2, "tabletype"), (2, "testop_"), (2, "typeidx"),
   (2, "u32"), (2, "u8"), (2, "uN"), (2, "unop_"), (2, "vN"), (2, "val"), (2, "valtype"),
   (2, "vbinop_"), (2, "vcvtop"), (2, "vec_"), (2, "vectype"), (2, "vextbinop_"),
   (2, "vextunop_"), (2, "vloadop"), (2, "vrelop_"), (2, "vshiftop_"), (2, "vtestop_"),
   (2, "vunop_"), (2, "vvbinop"), (2, "vvternop"), (2, "vvtestop"), (2, "vvunop"), (2, "zero")]

/-- The definitions of `reach20`. -/
def gd20 (x : String) : Bool := reach20.contains (1, x)

/-- The relations of `reach20`: `Step`, `Step_read` and `Step_pure`. -/
def gr20 (x : String) : Bool := reach20.contains (0, x)

/-- **The names `Step` can reach** in the 1.0 script, by kind, computed as `reach20`. -/
def reach10 : List (Nat × String) :=
  [(0, "Step"), (0, "Step_pure"), (0, "Step_read"), (1, "E"), (1, "Ki"), (1, "M"), (1, "binop_"),
   (1, "bool"), (1, "bytes_"), (1, "concat_"), (1, "convert__"), (1, "cvtop__"), (1, "default_"),
   (1, "demote__"), (1, "expon"), (1, "extend__"), (1, "fabs_"), (1, "fadd_"), (1, "fceil_"),
   (1, "fcopysign_"), (1, "fdiv_"), (1, "feq_"), (1, "ffloor_"), (1, "fge_"), (1, "fgt_"),
   (1, "fle_"), (1, "flt_"), (1, "fmax_"), (1, "fmin_"), (1, "fmul_"), (1, "fne_"),
   (1, "fnearest_"), (1, "fneg_"), (1, "fsqrt_"), (1, "fsub_"), (1, "ftrunc_"), (1, "funcaddr"),
   (1, "funcinst"), (1, "fzero"), (1, "global"), (1, "growmemory"), (1, "iadd_"), (1, "iand_"),
   (1, "ibytes_"), (1, "iclz_"), (1, "ictz_"), (1, "idiv_"), (1, "ieq_"), (1, "ieqz_"),
   (1, "ige_"), (1, "igt_"), (1, "ile_"), (1, "ilt_"), (1, "imul_"), (1, "ine_"),
   (1, "inv_signed_"), (1, "ior_"), (1, "ipopcnt_"), (1, "irem_"), (1, "irotl_"), (1, "irotr_"),
   (1, "ishl_"), (1, "ishr_"), (1, "isub_"), (1, "ixor_"), (1, "list_"), (1, "local"),
   (1, "mem"), (1, "promote__"), (1, "reinterpret__"), (1, "relop_"), (1, "signed_"),
   (1, "signif"), (1, "size"), (1, "table"), (1, "testop_"), (1, "trunc__"), (1, "truncz"),
   (1, "type"), (1, "unop_"), (1, "utf8"), (1, "with_global"), (1, "with_local"),
   (1, "with_mem"), (1, "with_meminst"), (1, "wrap__"), (2, "Fnn"), (2, "Inn"), (2, "M"),
   (2, "MUT"), (2, "N"), (2, "addr"), (2, "admininstr"), (2, "binop_"), (2, "blocktype"),
   (2, "byte"), (2, "char"), (2, "config"), (2, "cvtop"), (2, "exp"), (2, "exportinst"),
   (2, "expr"), (2, "externaddr"), (2, "fN"), (2, "fNmag"), (2, "frame"), (2, "func"),
   (2, "funcaddr"), (2, "funcidx"), (2, "funcinst"), (2, "functype"), (2, "globaladdr"),
   (2, "globalidx"), (2, "globalinst"), (2, "globaltype"), (2, "iN"), (2, "idx"), (2, "instr"),
   (2, "labelidx"), (2, "limits"), (2, "loadop_"), (2, "local"), (2, "localidx"), (2, "m"),
   (2, "memaddr"), (2, "memarg"), (2, "memidx"), (2, "meminst"), (2, "memtype"),
   (2, "moduleinst"), (2, "mut"), (2, "n"), (2, "name"), (2, "relop_"), (2, "state"),
   (2, "store"), (2, "sx"), (2, "sz"), (2, "tableaddr"), (2, "tableidx"), (2, "tableinst"),
   (2, "tabletype"), (2, "testop_"), (2, "typeidx"), (2, "u32"), (2, "uN"), (2, "unop_"),
   (2, "val"), (2, "val_"), (2, "valtype")]

/-- The definitions of `reach10`. -/
def gd10 (x : String) : Bool := reach10.contains (1, x)

/-- The relations of `reach10`: `Step`, `Step_read` and `Step_pure`. -/
def gr10 (x : String) : Bool := reach10.contains (0, x)

end Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll

/-! ## The check on types (round 8's `FiresC` check, at `EXPORTS`) -/

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (gr20 gd20 reach20 xExp xPrems xIter xArgs)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-- **The types checked**: every syntax type `Step` reaches in the 2.0 script, and the type
parameter `X` of `list`. -/
def tyC20 : List String := "X" :: (reach20.filter fun p => p.1 == 2).map (·.2)

mutual
/-- **A type over the names `S` whose expressions pass the evaluator-level check**; type
arguments are closed. -/
def xTy (S : List String) : Typ → Bool
  | .varT x args => S.contains x && xTyArgs S args
  | .tupT bs => xTyBinds S bs
  | .iterT t it => xTy S t && xIter gr20 gd20 it
  | _ => true

/-- `xTy` on the arguments of a type reference. -/
def xTyArgs (S : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => xTy S t && varsIn [] (freeTyp t) && xTyArgs S r
  | .expA e :: r => xExp gr20 gd20 e && xTyArgs S r
  | _ :: _ => false

/-- `xTy` on tuple binders. -/
def xTyBinds (S : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => xTy S t && xTyBinds S bs
end

/-- The type of `moduleinst`'s `EXPORTS` field, `exportinst*`. -/
def isExpT : Typ → Bool
  | .iterT (.varT "exportinst" []) .list => true
  | _ => false

/-- Record fields: an `EXPORTS` field has type `exportinst*` and no premises; every other field
is checked. -/
def xTFields (S : List String) : List TypField → Bool
  | [] => true
  | .mk a t _ prems :: fs =>
      (if a == "EXPORTS" then isExpT t && prems.isEmpty
        else xTy S t && xPrems gr20 gd20 prems) && xTFields S fs

/-- Variant cases: carried type, quantifier types and premises. -/
def xTCases (S : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs =>
      xTy S t && qs.all (fun q => match q with | .expP _ t => xTy S t | _ => true) &&
        xPrems gr20 gd20 prems && xTCases S cs

/-- A type definition's body. -/
def xDefTyp (S : List String) : DefTyp → Bool
  | .aliasT t => xTy S t
  | .structT fs => xTFields S fs
  | .variantT cs => xTCases S cs

/-- The record fields include one named `EXPORTS`. -/
def fieldsExp (fs : List TypField) : Bool :=
  fs.any fun f => match f with | .mk a _ _ _ => a == "EXPORTS"

/-- A type definition's body declares a record field named `EXPORTS`. -/
def defTypExp : DefTyp → Bool
  | .structT fs => fieldsExp fs
  | _ => false

/-- The instances of a type family: argument patterns and bodies; an instance whose body declares
an `EXPORTS` field has no argument patterns. -/
def xInsts (S : List String) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ pats dt => xArgs gr20 gd20 pats && xDefTyp S dt &&
        (!defTypExp dt || pats.isEmpty)

/-- **Every type of `m` named in `S` is checked.** -/
def xTypMap (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || xInsts S p.2.2

/-- **The quantifier types of every rule of a `gr20` relation are checked.** -/
def xRelQuants (S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !gr20 p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => qs.all fun q => match q with
      | .expP _ t => xTy S t
      | _ => true

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ

/-! ## The check on types, for the 1.0 script -/

namespace Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim20.XSwap.EraseAll (gr10 gd10 reach10 xExp xPrems xIter xArgs)
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer (varsIn)

/-- **The types checked**: every syntax type `Step` reaches in the 1.0 script, and the type
parameter `X` of `list`. -/
def tyC10 : List String := "X" :: (reach10.filter fun p => p.1 == 2).map (·.2)

mutual
/-- **A type over the names `S` whose expressions pass the evaluator-level check**; type
arguments are closed. -/
def xTy (S : List String) : Typ → Bool
  | .varT x args => S.contains x && xTyArgs S args
  | .tupT bs => xTyBinds S bs
  | .iterT t it => xTy S t && xIter gr10 gd10 it
  | _ => true

/-- `xTy` on the arguments of a type reference. -/
def xTyArgs (S : List String) : List Arg → Bool
  | [] => true
  | .typA t :: r => xTy S t && varsIn [] (freeTyp t) && xTyArgs S r
  | .expA e :: r => xExp gr10 gd10 e && xTyArgs S r
  | _ :: _ => false

/-- `xTy` on tuple binders. -/
def xTyBinds (S : List String) : List TypBind → Bool
  | [] => true
  | .mk _ t :: bs => xTy S t && xTyBinds S bs
end

/-- The type of `moduleinst`'s `EXPORTS` field, `exportinst*`. -/
def isExpT : Typ → Bool
  | .iterT (.varT "exportinst" []) .list => true
  | _ => false

/-- Record fields: an `EXPORTS` field has type `exportinst*` and no premises; every other field
is checked. -/
def xTFields (S : List String) : List TypField → Bool
  | [] => true
  | .mk a t _ prems :: fs =>
      (if a == "EXPORTS" then isExpT t && prems.isEmpty
        else xTy S t && xPrems gr10 gd10 prems) && xTFields S fs

/-- Variant cases: carried type, quantifier types and premises. -/
def xTCases (S : List String) : List TypCase → Bool
  | [] => true
  | .mk _ t qs prems :: cs =>
      xTy S t && qs.all (fun q => match q with | .expP _ t => xTy S t | _ => true) &&
        xPrems gr10 gd10 prems && xTCases S cs

/-- A type definition's body. -/
def xDefTyp (S : List String) : DefTyp → Bool
  | .aliasT t => xTy S t
  | .structT fs => xTFields S fs
  | .variantT cs => xTCases S cs

/-- The record fields include one named `EXPORTS`. -/
def fieldsExp (fs : List TypField) : Bool :=
  fs.any fun f => match f with | .mk a _ _ _ => a == "EXPORTS"

/-- A type definition's body declares a record field named `EXPORTS`. -/
def defTypExp : DefTyp → Bool
  | .structT fs => fieldsExp fs
  | _ => false

/-- The instances of a type family: argument patterns and bodies; an instance whose body declares
an `EXPORTS` field has no argument patterns. -/
def xInsts (S : List String) (insts : List Inst) : Bool :=
  insts.all fun i => match i with
    | .instD _ pats dt => xArgs gr10 gd10 pats && xDefTyp S dt &&
        (!defTypExp dt || pats.isEmpty)

/-- **Every type of `m` named in `S` is checked.** -/
def xTypMap (S : List String) (m : Map TypDef) : Bool :=
  m.all fun p => !S.contains p.1 || xInsts S p.2.2

/-- **The quantifier types of every rule of a `gr10` relation are checked.** -/
def xRelQuants (S : List String) (m : Map RelDef) : Bool :=
  m.all fun p => !gr10 p.1 || p.2.2.2.2.all fun r => match r with
    | .ruleD _ qs _ _ _ => qs.all fun q => match q with
      | .expP _ t => xTy S t
      | _ => true

end Silmaril.Wasm.SpecTec.Sim20.XSwap.Typ10
