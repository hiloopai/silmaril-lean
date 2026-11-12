module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Roots.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round7.Script.Defs
public import Mathlib.Data.Nat.Pairing

/-!
# Round 8, function code erasure: the evaluator commutes with erasing `CODE` fields (definitions)

Round 3's export erasure (`Round7.Swap`, `Round7.Erase`, `Round7.EraseAll`), copied for record
fields named `CODE` (the code of a function instance) instead of `EXPORTS`, with an injective
replacement instead of `[]`:

* `codeN : Value → ℕ` is injective (`Round8.CodeErase.Swap.codeN_inj`); `enc v` is the string of
  `codeN v` copies of `c`, and `hostC v = _HOSTFUNC (enc v)` is the code of a host function
  named by `v`. So `hostC` is injective.
* `eraseC v`: `v` with the contents `u` of every record field named `CODE` replaced by `hostC u`
  (not recursively); everything else is kept. Since `hostC` is injective, so is `eraseC`, and
  `QInj Q` holds for every `Q` (`Round8.CodeErase.Swap.qInj`).
* The rest is round 3's machinery, with `EXPORTS` read as `CODE`: the scope operations
  (`Erase.eraseScope`, `ScopeIn`, `EOK`, `FO`), the syntactic check (`EraseAll.xExp` …: no
  `.CODE` projection, record field or path step, compositions only with `nilLit` left operands,
  updates only along `updOk` paths), the invariants (`SG`, `ArgIn`, `ER`), the hypotheses
  (`Hyps`) and the statement (`EraseAt`). `updOk` tests the last field step against `codeAtoms`,
  which is empty: the swap set used is every value, so no update can leave it.

The proof is `Round8.CodeErase.EraseAll.eraseAt` (`Raw/…/Round8/CodeErase/EAll.lean`).

**On the wasm-3.0 script.** `gdC`, `grC`: the definitions and relations `Step` reaches
(`Round7.Script.stepReach`), without `$hostcall` and `Step`. The only rules of the script that read
a `CODE` field are three rules of `Step` (the `call_ref` rules that look at the callee's code);
`$hostcall` is the primitive those rules call with the whole store. `xDefOk` is round 3's
per-definition check (`Round7.EraseAll.xDefOk`) with this file's `xExp`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-! ## An injective code of values -/

/-- A code of a list of numbers. -/
def natsN : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.pair x (natsN xs) + 1

/-- A code of a string. -/
def strN (s : String) : ℕ := natsN (s.toList.map Char.toNat)

/-- A code of an integer. -/
def intN (i : Int) : ℕ := Nat.pair i.toNat (-i).toNat

/-- A code of a number. -/
def numN : IL.Num → ℕ
  | .natN n => Nat.pair 0 n
  | .intN i => Nat.pair 1 (intN i)
  | .ratN q => Nat.pair 2 (Nat.pair (intN q.num) q.den)
  | .realN s => Nat.pair 3 (strN s)

mutual
/-- **A code of a value.** It is injective (`codeN_inj`). -/
def codeN : Value → ℕ
  | .bool b => Nat.pair 0 (if b then 1 else 0)
  | .num n => Nat.pair 1 (numN n)
  | .text t => Nat.pair 2 (strN t)
  | .tuple vs => Nat.pair 3 (codeNs vs)
  | .case op w => Nat.pair 4 (Nat.pair (strN op) (codeN w))
  | .struct gs => Nat.pair 5 (codeNf gs)
  | .list vs => Nat.pair 6 (codeNs vs)
  | .opt none => Nat.pair 7 0
  | .opt (some w) => Nat.pair 8 (codeN w)

/-- `codeN` on a list of values. -/
def codeNs : List Value → ℕ
  | [] => 0
  | v :: vs => Nat.pair (codeN v) (codeNs vs) + 1

/-- `codeN` on the fields of a record. -/
def codeNf : List (IL.AtomS × Value) → ℕ
  | [] => 0
  | (a, v) :: gs => Nat.pair (Nat.pair (strN a) (codeN v)) (codeNf gs) + 1
end

/-- **The name of the host function standing for a code `v`**: `codeN v` copies of `c`. -/
def enc (v : Value) : String := String.ofList (List.replicate (codeN v) 'c')

/-- **The erased code**: the code of the host function named `enc v`. -/
def hostC (v : Value) : Value := .case "_HOSTFUNC" (.text (enc v))

/-! ## The erasure -/

mutual
/-- **Erase the function code**: the contents `u` of every record field named `CODE` become
`hostC u`, the code of a host function named by `u`; the rest is kept, deeply. -/
def eraseC : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (eraseCs vs)
  | .case op w => .case op (eraseC w)
  | .struct gs => .struct (eraseCf gs)
  | .list vs => .list (eraseCs vs)
  | .opt none => .opt none
  | .opt (some w) => .opt (some (eraseC w))

/-- `eraseC` on a list of values. -/
def eraseCs : List Value → List Value
  | [] => []
  | v :: vs => eraseC v :: eraseCs vs

/-- `eraseC` on the fields of a record: a `CODE` field `u` becomes `hostC u`. -/
def eraseCf : List (IL.AtomS × Value) → List (IL.AtomS × Value)
  | [] => []
  | (a, v) :: gs => (a, if a = "CODE" then hostC v else eraseC v) :: eraseCf gs
end

/-- The fields of a record include one named `CODE`. -/
def hasCode (gs : List (IL.AtomS × Value)) : Bool := gs.any fun g => g.1 == "CODE"

mutual
/-- **No record of `v` has a `CODE` field**, as a boolean. -/
def ncB : Value → Bool
  | .bool _ => true
  | .num _ => true
  | .text _ => true
  | .tuple vs => ncBs vs
  | .case _ w => ncB w
  | .struct gs => ncBf gs
  | .list vs => ncBs vs
  | .opt none => true
  | .opt (some w) => ncB w

/-- `ncB` on a list of values. -/
def ncBs : List Value → Bool
  | [] => true
  | v :: vs => ncB v && ncBs vs

/-- `ncB` on the fields of a record. -/
def ncBf : List (IL.AtomS × Value) → Bool
  | [] => true
  | (a, v) :: gs => ncB v && (a != "CODE") && ncBf gs
end

mutual
/-- **Every record of `v` with a `CODE` field satisfies `Q`.** -/
def AllIn (Q : Value → Prop) : Value → Prop
  | .bool _ => True
  | .num _ => True
  | .text _ => True
  | .tuple vs => AllIns Q vs
  | .case _ w => AllIn Q w
  | .struct gs => (hasCode gs = true → Q (.struct gs)) ∧ AllInf Q gs
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
/-- **Undo `eraseC` along `Q`**: a record with a `CODE` field that is the erasure of a
record satisfying `Q` goes back to (a chosen) one; elsewhere `unerase` recurses. Under `QInj Q`
it inverts `eraseC` on `AllIn Q` values (`Round8.CodeErase.Swap.unerase_eraseC`). -/
noncomputable def unerase (Q : Value → Prop) : Value → Value
  | .bool b => .bool b
  | .num n => .num n
  | .text t => .text t
  | .tuple vs => .tuple (uneraseS Q vs)
  | .case op w => .case op (unerase Q w)
  | .struct gs =>
    open Classical in
    if h : hasCode gs = true ∧ ∃ r, Q r ∧ eraseC r = .struct gs then h.2.choose
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

/-- **`eraseC` is injective on `Q`.** -/
def QInj (Q : Value → Prop) : Prop :=
  ∀ x y, Q x → Q y → eraseC x = eraseC y → x = y


end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem

/-- `eraseC` on an argument: values are erased, the rest is kept. -/
def eraseA : ArgV → ArgV
  | .val v => .val (eraseC v)
  | a => a

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap (eraseC AllIn)


/-- **The erased scope**: `eraseC` on every term binding. -/
def eraseScope (ρ : VarEnv) : VarEnv :=
  { ρ with vals := ρ.vals.map fun p => (p.1, eraseC p.2) }

/-- **The scope is in the swap set**: every term binding is `AllIn Q`. -/
def ScopeIn (Q : Value → Prop) (ρ : VarEnv) : Prop := ∀ p ∈ ρ.vals, AllIn Q p.2

/-- `r'` is `r` with its answer erased, and every answer of `r` is `AllIn Q`. -/
def EOK (Q : Value → Prop) (r r' : Res Value) : Prop :=
  r' = eraseC <$> r ∧ ∀ v, r = .ok v → AllIn Q v

mutual
/-- **First-order expressions**: no call, iteration, update, extension or composition, and no
atom `CODE`. -/
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
  | dotE {e : Exp} {a : AtomS} : a ≠ "CODE" → FO e → FO (.dotE e a)
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

/-- `FO` on record fields, none named `CODE`. -/
inductive FOf : List ExpField → Prop where
  | nil : FOf []
  | cons {a : AtomS} {e : Exp} {fs : List ExpField} : a ≠ "CODE" → FO e → FOf fs →
      FOf (.mk a e :: fs)
end

/-- **First-order paths**: index and slice bounds are first order and no step is `.CODE`. -/
inductive FOp : Path → Prop where
  | rootP : FOp .rootP
  | idxP {p : Path} {e : Exp} : FOp p → FO e → FOp (.idxP p e)
  | sliceP {p : Path} {e₁ e₂ : Exp} : FOp p → FO e₁ → FO e₂ → FOp (.sliceP p e₁ e₂)
  | dotP {p : Path} {a : AtomS} : FOp p → a ≠ "CODE" → FOp (.dotP p a)


end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase

namespace Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Swap (eraseC eraseCf AllIn QInj eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.Erase (eraseScope ScopeIn)

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

/-- No field step of the path is `CODE`. -/
def dotsOk : Path → Bool
  | .rootP => true
  | .idxP p _ => dotsOk p
  | .sliceP p _ _ => dotsOk p
  | .dotP p a => a != "CODE" && dotsOk p

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
  | .dotE e a => a != "CODE" && xExp gr gd e
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

/-- `xExp` on record fields, none named `CODE`. -/
def xFields (gr gd : String → Bool) : List ExpField → Bool
  | [] => true
  | .mk a e :: fs => a != "CODE" && xExp gr gd e && xFields gr gd fs

/-- `xExp` on a path: its index and slice bounds, and no step `.CODE`. -/
def xPath (gr gd : String → Bool) : Path → Bool
  | .rootP => true
  | .idxP p e => xPath gr gd p && xExp gr gd e
  | .sliceP p e₁ e₂ => xPath gr gd p && xExp gr gd e₁ && xExp gr gd e₂
  | .dotP p a => a != "CODE" && xPath gr gd p

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

/-- `eraseC` on the value of a binding. -/
def eraseP (p : IL.Id × Value) : IL.Id × Value := (p.1, eraseC p.2)

/-! ## The hypotheses -/

/-- **The builtins of `gd` names commute with erasure**, and keep the swap set. -/
def BIErase (Q : Value → Prop) (gd : String → Bool) (env : Env) : Prop :=
  ∀ x ws, gd x = true → (∀ w ∈ ws, ArgIn Q gd w) →
    env.builtins.call x (ws.map eraseA) = (env.builtins.call x ws).map eraseC ∧
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
    ER eraseC (AllIn Q) (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e)
  exps : ∀ ρ es, SG Q gd ρ → xExps gr gd es = true →
    ER (List.map eraseC) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalExps n env ρ es) (evalExps n env (eraseScope ρ) es)
  expFields : ∀ ρ fs, SG Q gd ρ → xFields gr gd fs = true →
    ER (List.map eraseP) (fun gs => ∀ p ∈ gs, AllIn Q p.2 ∧ p.1 ≠ "CODE")
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
    ER eraseC (AllIn Q) (evalIterE n env ρ e it ds) (evalIterE n env (eraseScope ρ) e it ds)
  iterList : ∀ ρ e xvs ido k, SG Q gd ρ → xExp gr gd e = true → (∀ p ∈ xvs, AllIn Q p.2) →
    ER eraseC (AllIn Q) (evalIterList n env ρ e xvs ido k)
      (evalIterList n env (eraseScope ρ) e (xvs.map eraseP) ido k)
  rounds : ∀ ρ e rs, SG Q gd ρ → xExp gr gd e = true → (∀ r ∈ rs, ∀ p ∈ r, AllIn Q p.2) →
    ER (List.map eraseC) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalRounds n env ρ e rs) (evalRounds n env (eraseScope ρ) e (rs.map (List.map eraseP)))
  pathGet : ∀ ρ v p, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    ER eraseC (AllIn Q) (pathGet n env ρ v p) (pathGet n env (eraseScope ρ) (eraseC v) p)
  pathSet : ∀ ρ v p w, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    pathSet n env (eraseScope ρ) (eraseC v) p (eraseC w) = eraseC <$> pathSet n env ρ v p w
  patLen : ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
    patLen n env (eraseScope ρ) e = patLen n env ρ e
  matchExp : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchExp n env ρ e v) (matchExp n env (eraseScope ρ) e (eraseC v))
  matchDefault : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchDefault n env ρ e v)
      (matchDefault n env (eraseScope ρ) e (eraseC v))
  matchExps : ∀ ρ es vs, SG Q gd ρ → xExps gr gd es = true → (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchExps n env ρ es vs)
      (matchExps n env (eraseScope ρ) es (vs.map eraseC))
  matchExpFields : ∀ ρ fs gs, SG Q gd ρ → xFields gr gd fs = true → (∀ p ∈ gs, AllIn Q p.2) →
    ER eraseScope (SG Q gd) (matchExpFields n env ρ fs gs)
      (matchExpFields n env (eraseScope ρ) fs (eraseCf gs))
  matchIterE : ∀ ρ e it ds v, SG Q gd ρ → xExp gr gd e = true → xIter gr gd it = true →
    xDoms gr gd ds = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchIterE n env ρ e it ds v)
      (matchIterE n env (eraseScope ρ) e it ds (eraseC v))
  matchIterList : ∀ ρ e ds ido vs, SG Q gd ρ → xExp gr gd e = true → xDoms gr gd ds = true →
    (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchIterList n env ρ e ds ido vs)
      (matchIterList n env (eraseScope ρ) e ds ido (vs.map eraseC))
  matchRounds : ∀ ρ e xs ido i vs, SG Q gd ρ → xExp gr gd e = true → (∀ v ∈ vs, AllIn Q v) →
    ER (List.map (List.map eraseC)) (fun rows => ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u)
      (matchRounds n env ρ e xs ido i vs)
      (matchRounds n env (eraseScope ρ) e xs ido i (vs.map eraseC))
  matchArg : ∀ ρ a w, SG Q gd ρ → xArg gr gd a = true → ArgIn Q gd w →
    ER eraseScope (SG Q gd) (matchArg n env ρ a w) (matchArg n env (eraseScope ρ) a (eraseA w))
  matchArgs : ∀ ρ l ws, SG Q gd ρ → xArgs gr gd l = true → (∀ w ∈ ws, ArgIn Q gd w) →
    ER eraseScope (SG Q gd) (matchArgs n env ρ l ws)
      (matchArgs n env (eraseScope ρ) l (ws.map eraseA))
  callDef : ∀ ρ x l, SG Q gd ρ → gd x = true → xArgs gr gd l = true →
    ER eraseC (AllIn Q) (callDef n env ρ x l) (callDef n env (eraseScope ρ) x l)
  tryClauses : ∀ cs ws, (∀ c ∈ cs, xClause gr gd c = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    ER eraseC (AllIn Q) (tryClauses n env cs ws) (tryClauses n env cs (ws.map eraseA))
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
    derives n env x op (ws.map eraseA) (eraseC v) = derives n env x op ws v
  anyRule : ∀ op ps ws v rs, (∀ r ∈ rs, xRule gr gd r = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    AllIn Q v → anyRule n env op ps (ws.map eraseA) (eraseC v) rs = anyRule n env op ps ws v rs

end



/-! ## The wasm-3.0 script -/

/-- The reachable names the evaluator-level erasure leaves out: `Step` (three of its rules read
`CODE`) and `$hostcall` (its primitive reads the whole store). -/
def excludedC : List (Nat × String) := [(1, "hostcall"), (0, "Step")]

/-- `Round7.Script.stepReach` without `excludedC`. -/
def stepReachC : List (Nat × String) :=
  Round7.Script.stepReach.filter fun p => !excludedC.contains p

/-- The definitions of `stepReachC`. -/
def gdC (x : String) : Bool := stepReachC.contains (1, x)

/-- The relations of `stepReachC`. -/
def grC (x : String) : Bool := stepReachC.contains (0, x)

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
      (if Round6.Reading.hasOptNil e then Round6.Reading.optAlts e else []).all (xExp gr gd)

/-- The definitions and relations bound by the top-level definition `d` pass the check, and so
do the conclusion alternatives of the relations' rules. -/
def xDefOk (gr gd : String → Bool) (d : Def) : Bool :=
  xDefsOk gr gd (defsOfDef d) && xRelsOk gr gd (relsOfDef d) && xAltsOk gr gd (relsOfDef d)

end Silmaril.Wasm.SpecTec.Sim.Round8.CodeErase.EraseAll
