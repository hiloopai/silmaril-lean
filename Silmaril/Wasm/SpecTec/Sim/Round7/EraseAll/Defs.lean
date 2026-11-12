module

public import Silmaril.Wasm.SpecTec.Sim.Round7.Erase.Thms
public import Silmaril.Wasm.SpecTec.Sim.Round7.Roots.Defs

/-!
# Round 7, the export swap: the whole evaluator commutes with erasure (round 3, pass 2)

Item 1 of the plan for `Round7.Swap.Task.stepErase`, for all 29 members of the evaluator's mutual
block (`Sem.evalExp` … `Sem.anyRule`), on syntax that a syntactic check accepts and under four
hypotheses on the environment. Definitions only; the proof is `Round7.EraseAll.eraseAt`
(`Round7/EraseAll/Thms.lean`).

**The syntactic check** `xExp gr gd e` (with siblings for every syntax class) accepts `e` when:

* every definition it calls, or passes as an argument, satisfies `gd`, and every relation of a
  premise satisfies `gr`;
* no `.EXPORTS` projection, record field or path step is named `EXPORTS`;
* every record composition `e₁ ++ e₂` has a record literal `e₁` whose fields are `[]`, `ε` or a
  list iteration (`nilLit`). This is the one composition `Step` reaches, in `Deftype_ok`;
* every update or extension path `p` ends, in its last field step, with an atom that is not a
  field of `moduleinst` (`updOk`). Of the paths `Step` reaches, `$with_tableinst`'s `.TABLES[i]`
  and `$with_meminst`'s `.MEMS[i]` fail this.

**The invariants.** A scope is `SG Q gd ρ` when its term bindings are in the swap set
(`Erase.ScopeIn Q`) and its definition variables satisfy `gd` (`DefsG`). An evaluated argument
is `ArgIn Q gd` when its value is in the swap set or its definition name satisfies `gd`.

**The hypotheses** (`Hyps Q gr gd env`): `QInj Q`; the clauses of every `gd` definition and the
rules of every `gr` relation pass the check; the builtins of `gd` names commute with erasure
(`BIErase`); and a path update along an `updOk` path keeps the swap set (`UpdSafe`).

**The statement** (`EraseAt`): each member, at fuel `n`, run on erased inputs (`eraseScope`,
`eraseV`, `Swap.eraseA`) gives the erased answer of the member run on the inputs, and that answer
satisfies the invariant (`ER`). Answers that are numbers (`patLen`) or booleans (`derives`,
`anyRule`) are equal.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap (eraseV eraseVf AllIn QInj eraseA)
open Silmaril.Wasm.SpecTec.Sim.Round7.Erase (eraseScope ScopeIn)

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
  | some a => !(Roots.modAtoms.contains a)

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

/-- `eraseV` on the value of a binding. -/
def eraseP (p : IL.Id × Value) : IL.Id × Value := (p.1, eraseV p.2)

/-! ## The hypotheses -/

/-- **The builtins of `gd` names commute with erasure**, and keep the swap set. -/
def BIErase (Q : Value → Prop) (gd : String → Bool) (env : Env) : Prop :=
  ∀ x ws, gd x = true → (∀ w ∈ ws, ArgIn Q gd w) →
    env.builtins.call x (ws.map eraseA) = (env.builtins.call x ws).map eraseV ∧
      ∀ u, env.builtins.call x ws = some u → AllIn Q u

/-- **Updates along `updOk` paths keep the swap set.** -/
def UpdSafe (Q : Value → Prop) (env : Env) : Prop :=
  ∀ m ρ v p w u, dotsOk p = true → updOk p = true → AllIn Q v → AllIn Q w →
    pathSet m env ρ v p w = .ok u → AllIn Q u

/-- A value that no path step can enter: not a record and not a list. -/
def Flat (u : Value) : Prop := (∀ gs, u ≠ .struct gs) ∧ ∀ l, u ≠ .list l

/-- **The records of `Q` look like module instances**: their fields are among those of
`moduleinst` (`Roots.modAtoms`), and every field other than `EXPORTS` is a list of `Flat` values.
Under it, `UpdSafe Q env` holds (`Round7.EraseAll.updSafe_of_shape`). -/
def QShape (Q : Value → Prop) : Prop :=
  ∀ r, Q r → ∃ gs, r = .struct gs ∧ ∀ p ∈ gs, p.1 ∈ Roots.modAtoms ∧
    (p.1 ≠ "EXPORTS" → ∃ us, p.2 = .list us ∧ ∀ u ∈ us, Flat u)

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
    ER eraseV (AllIn Q) (evalExp n env ρ e) (evalExp n env (eraseScope ρ) e)
  exps : ∀ ρ es, SG Q gd ρ → xExps gr gd es = true →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn Q v)
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
    ER eraseV (AllIn Q) (evalIterE n env ρ e it ds) (evalIterE n env (eraseScope ρ) e it ds)
  iterList : ∀ ρ e xvs ido k, SG Q gd ρ → xExp gr gd e = true → (∀ p ∈ xvs, AllIn Q p.2) →
    ER eraseV (AllIn Q) (evalIterList n env ρ e xvs ido k)
      (evalIterList n env (eraseScope ρ) e (xvs.map eraseP) ido k)
  rounds : ∀ ρ e rs, SG Q gd ρ → xExp gr gd e = true → (∀ r ∈ rs, ∀ p ∈ r, AllIn Q p.2) →
    ER (List.map eraseV) (fun vs => ∀ v ∈ vs, AllIn Q v)
      (evalRounds n env ρ e rs) (evalRounds n env (eraseScope ρ) e (rs.map (List.map eraseP)))
  pathGet : ∀ ρ v p, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    ER eraseV (AllIn Q) (pathGet n env ρ v p) (pathGet n env (eraseScope ρ) (eraseV v) p)
  pathSet : ∀ ρ v p w, SG Q gd ρ → xPath gr gd p = true → AllIn Q v →
    pathSet n env (eraseScope ρ) (eraseV v) p (eraseV w) = eraseV <$> pathSet n env ρ v p w
  patLen : ∀ ρ e, SG Q gd ρ → xExp gr gd e = true →
    patLen n env (eraseScope ρ) e = patLen n env ρ e
  matchExp : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchExp n env ρ e v) (matchExp n env (eraseScope ρ) e (eraseV v))
  matchDefault : ∀ ρ e v, SG Q gd ρ → xExp gr gd e = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchDefault n env ρ e v)
      (matchDefault n env (eraseScope ρ) e (eraseV v))
  matchExps : ∀ ρ es vs, SG Q gd ρ → xExps gr gd es = true → (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchExps n env ρ es vs)
      (matchExps n env (eraseScope ρ) es (vs.map eraseV))
  matchExpFields : ∀ ρ fs gs, SG Q gd ρ → xFields gr gd fs = true → (∀ p ∈ gs, AllIn Q p.2) →
    ER eraseScope (SG Q gd) (matchExpFields n env ρ fs gs)
      (matchExpFields n env (eraseScope ρ) fs (eraseVf gs))
  matchIterE : ∀ ρ e it ds v, SG Q gd ρ → xExp gr gd e = true → xIter gr gd it = true →
    xDoms gr gd ds = true → AllIn Q v →
    ER eraseScope (SG Q gd) (matchIterE n env ρ e it ds v)
      (matchIterE n env (eraseScope ρ) e it ds (eraseV v))
  matchIterList : ∀ ρ e ds ido vs, SG Q gd ρ → xExp gr gd e = true → xDoms gr gd ds = true →
    (∀ v ∈ vs, AllIn Q v) →
    ER eraseScope (SG Q gd) (matchIterList n env ρ e ds ido vs)
      (matchIterList n env (eraseScope ρ) e ds ido (vs.map eraseV))
  matchRounds : ∀ ρ e xs ido i vs, SG Q gd ρ → xExp gr gd e = true → (∀ v ∈ vs, AllIn Q v) →
    ER (List.map (List.map eraseV)) (fun rows => ∀ r ∈ rows, ∀ u ∈ r, AllIn Q u)
      (matchRounds n env ρ e xs ido i vs)
      (matchRounds n env (eraseScope ρ) e xs ido i (vs.map eraseV))
  matchArg : ∀ ρ a w, SG Q gd ρ → xArg gr gd a = true → ArgIn Q gd w →
    ER eraseScope (SG Q gd) (matchArg n env ρ a w) (matchArg n env (eraseScope ρ) a (eraseA w))
  matchArgs : ∀ ρ l ws, SG Q gd ρ → xArgs gr gd l = true → (∀ w ∈ ws, ArgIn Q gd w) →
    ER eraseScope (SG Q gd) (matchArgs n env ρ l ws)
      (matchArgs n env (eraseScope ρ) l (ws.map eraseA))
  callDef : ∀ ρ x l, SG Q gd ρ → gd x = true → xArgs gr gd l = true →
    ER eraseV (AllIn Q) (callDef n env ρ x l) (callDef n env (eraseScope ρ) x l)
  tryClauses : ∀ cs ws, (∀ c ∈ cs, xClause gr gd c = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    ER eraseV (AllIn Q) (tryClauses n env cs ws) (tryClauses n env cs (ws.map eraseA))
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
    derives n env x op (ws.map eraseA) (eraseV v) = derives n env x op ws v
  anyRule : ∀ op ps ws v rs, (∀ r ∈ rs, xRule gr gd r = true) → (∀ w ∈ ws, ArgIn Q gd w) →
    AllIn Q v → anyRule n env op ps (ws.map eraseA) (eraseV v) rs = anyRule n env op ps ws v rs

end

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
