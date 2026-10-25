module

public import Silmaril.Logic.Metamath.Verify.Compressed
public import Silmaril.Logic.Metamath.Verify.Database
public import Silmaril.Logic.Metamath.Text.Ast
public import Std.Data.HashMap
public import Std.Data.HashSet

@[expose] public section

/-!
# Checking a Metamath database

The checker reads a statement sequence (`Text.Source`) in order. It maintains
the declared constants and variables, the labels, and a stack of blocks with
the active variables, hypotheses and disjoint-variable pairs, and enforces the
well-formedness rules of the specification (Megill and Wheeler, *Metamath*,
§4.1): unique labels distinct from math symbols, constants declared once in
the outermost block, variables not redeclared while active, typecodes that are
constants, active symbols only, one active `$f` per variable with a single
global typecode, and balanced blocks.

For each `$a` and `$p` statement it computes the extended frame
(`Checker.addAssertion`): the mandatory variables are those of the conclusion and
of the active `$e` hypotheses, the mandatory hypotheses are the active `$f`
hypotheses of mandatory variables and all active `$e` hypotheses in database
order, and the mandatory `$d` pairs are the active pairs of mandatory
variables. Constants become `Sym.const` and variables `Sym.var`.

A proof (`proveTheorem`) may also use the active `$f` hypotheses of other
variables. Those it mentions, the first for each variable, become the dummy
floating hypotheses of a `Dummies` value, together with the active `$d` pairs
involving them, and the proof machine runs in the extended frame. Its disjointness test is exactly the
`$d` relation of that frame, which agrees with the active `$d` statements on
every variable a proof step can contain.

The checker produces the checked `Database`. Its correctness is proved in
`Silmaril.Logic.Metamath.Verify.Soundness`.
-/

namespace Silmaril.Logic.Metamath.Verify

open Std Text

/-- Why a database was rejected. -/
inductive Error where
  /-- The proof of the named theorem is wrong. -/
  | proof (label : String) (e : ProofError)
  /-- The proof of the named theorem contains `?`. -/
  | incomplete (label : String)
  /-- A statement violates the well-formedness rules of the language. -/
  | invalid (msg : String)
  deriving DecidableEq, Repr, Inhabited

instance : ToString Error where
  toString
    | .proof l e => s!"proof of {l} rejected: {e}"
    | .incomplete l => s!"proof of {l} is incomplete"
    | .invalid msg => msg

/-- Math strings, expressions, hypotheses and assertions of the text format. -/
abbrev MExpr := Expr String String
@[inherit_doc MExpr] abbrev MHyp := Hyp String String
@[inherit_doc MExpr] abbrev MAssertion := Assertion String String

/-! ## Helpers -/

/-- `true` when the list has no duplicates, using a hash set of seen elements. -/
def nodupAux {α : Type} [BEq α] [Hashable α] (seen : HashSet α) : List α → Bool
  | [] => true
  | a :: l => !seen.contains a && nodupAux (seen.insert a) l

/-- A hash-based decision procedure for the well-formedness of an assertion. -/
def wfCheck (A : MAssertion) : Bool :=
  let fv := A.floats.map Prod.snd
  let fs := HashSet.ofList fv
  A.vars.all fs.contains && nodupAux {} fv && A.dv.all fun p => p.1 != p.2

/-- Label tokens: letters, digits, `-`, `_` and `.`. -/
def isLabelChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- Math symbol tokens: printable ASCII other than space and `$`. -/
def isMathChar (c : Char) : Bool := 33 ≤ c.toNat && c.toNat ≤ 126 && c != '$'

/-- A valid label token. -/
def validLabel (l : String) : Bool := !l.isEmpty && l.all isLabelChar

/-- A valid math symbol token. -/
def validMath (s : String) : Bool := !s.isEmpty && s.all isMathChar

/-- All pairs `(xᵢ, xⱼ)` with `i < j`. -/
def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (x, ·) ++ pairs xs

/-! ## Scopes and environments -/

/-- The block-scoped part of the environment. -/
structure Scope where
  /-- Active variables. -/
  vars : HashSet String := {}
  /-- Active hypotheses in database order. -/
  hyps : Array (String × MHyp) := #[]
  /-- Active hypotheses by label. -/
  hypMap : HashMap String MHyp := {}
  /-- Active variables with an active `$f`. -/
  floated : HashSet String := {}
  /-- Active disjoint-variable pairs. -/
  dvPairs : Array (String × String) := #[]
  deriving Inhabited

/-- The checker's environment, apart from the checked assertions. -/
structure Env where
  consts : HashSet String := {}
  /-- Every symbol ever declared as a variable. -/
  declVars : HashSet String := {}
  /-- The typecode each variable was given by a `$f`. -/
  varType : HashMap String String := {}
  /-- Every label. -/
  labels : HashSet String := {}
  scope : Scope := {}
  /-- The enclosing blocks, innermost first. -/
  outer : List Scope := []
  deriving Inhabited

namespace Scope

/-- The mandatory variables of an assertion with conclusion `e`. -/
def mandVars (sc : Scope) (e : MExpr) : HashSet String :=
  sc.hyps.foldl (init := HashSet.ofList e.vars) fun m p =>
    match p.2 with
    | .ess e' => m.insertMany e'.vars
    | .float _ _ => m

/-- The mandatory hypotheses, labelled, for the mandatory variables `mv`. -/
def mandHyps (sc : Scope) (mv : HashSet String) : List (String × MHyp) :=
  sc.hyps.toList.filter fun p =>
    match p.2 with
    | .float _ v => mv.contains v
    | .ess _ => true

/-- The mandatory disjoint-variable pairs for the mandatory variables `mv`. -/
def mandDV (sc : Scope) (mv : HashSet String) : List (String × String) :=
  sc.dvPairs.toList.filter fun p => mv.contains p.1 && mv.contains p.2

end Scope

namespace Env

/-- Declare a label. -/
def newLabel (env : Env) (l : String) : Except Error Env :=
  if !validLabel l then .error (.invalid s!"invalid label {l}")
  else if env.labels.contains l then .error (.invalid s!"label {l} declared twice")
  else if env.consts.contains l || env.declVars.contains l then
    .error (.invalid s!"label {l} is also a math symbol")
  else .ok { env with labels := env.labels.insert l }

/-- Check a new math symbol token. -/
def checkSymbol (env : Env) (s : String) : Except Error Unit :=
  if !validMath s then .error (.invalid s!"invalid math symbol {s}")
  else if env.consts.contains s then .error (.invalid s!"{s} is already a constant")
  else if env.labels.contains s then .error (.invalid s!"math symbol {s} is also a label")
  else .ok ()

/-- A `$c` statement. -/
def addConsts (env : Env) (cs : List String) : Except Error Env := do
  unless env.outer.isEmpty do throw (.invalid "$c statement inside a block")
  if cs.isEmpty then throw (.invalid "empty $c statement")
  cs.foldlM (init := env) fun env c => do
    env.checkSymbol c
    if env.declVars.contains c then throw (.invalid s!"{c} is already a variable")
    pure { env with consts := env.consts.insert c }

/-- A `$v` statement. -/
def addVars (env : Env) (vs : List String) : Except Error Env := do
  if vs.isEmpty then throw (.invalid "empty $v statement")
  vs.foldlM (init := env) fun env v => do
    env.checkSymbol v
    if env.scope.vars.contains v then throw (.invalid s!"variable {v} is already active")
    pure { env with
      declVars := env.declVars.insert v
      scope := { env.scope with vars := env.scope.vars.insert v } }

/-- A `$d` statement. -/
def addDisjoint (env : Env) (vs : List String) : Except Error Env := do
  if vs.length < 2 then throw (.invalid "$d statement with fewer than two variables")
  for v in vs do
    unless env.scope.vars.contains v do throw (.invalid s!"$d on inactive variable {v}")
  let ps := pairs vs
  for p in ps do
    if p.1 == p.2 then throw (.invalid s!"variable {p.1} repeated in $d statement")
  pure { env with scope := { env.scope with dvPairs := env.scope.dvPairs ++ ps.toArray } }

/-- Add an active hypothesis. -/
def addHyp (env : Env) (l : String) (h : MHyp) : Env :=
  { env with scope := { env.scope with
      hyps := env.scope.hyps.push (l, h)
      hypMap := env.scope.hypMap.insert l h } }

/-- A `$f` statement. -/
def addFloat (env : Env) (l tc v : String) : Except Error Env := do
  let env ← env.newLabel l
  unless env.consts.contains tc do throw (.invalid s!"{l}: typecode {tc} is not a constant")
  unless env.scope.vars.contains v do throw (.invalid s!"{l}: {v} is not an active variable")
  if env.scope.floated.contains v then throw (.invalid s!"{l}: {v} already has an active $f")
  if let some tc' := env.varType[v]? then
    if tc' != tc then throw (.invalid s!"{l}: {v} already has typecode {tc'}")
  let env := { env with
    varType := env.varType.insert v tc
    scope := { env.scope with floated := env.scope.floated.insert v } }
  pure (env.addHyp l (.float tc v))

/-- Elaborate one math symbol of a `$e`, `$a` or `$p` statement. -/
def mkSym (env : Env) (l s : String) : Except Error (Sym String String) :=
  if env.consts.contains s then .ok (.const s)
  else if env.scope.vars.contains s then
    if env.scope.floated.contains s then .ok (.var s)
    else .error (.invalid s!"{l}: variable {s} has no active $f")
  else .error (.invalid s!"{l}: {s} is not an active math symbol")

/-- Elaborate a math string, accumulating the symbols in `out`. -/
def mkBody (env : Env) (l : String) :
    List String → Array (Sym String String) → Except Error (Array (Sym String String))
  | [], out => .ok out
  | s :: ss, out =>
    match env.mkSym l s with
    | .ok x => mkBody env l ss (out.push x)
    | .error e => .error e

/-- Elaborate the typecode and math string of a `$e`, `$a` or `$p` statement. -/
def mkExpr (env : Env) (l tc : String) (body : List String) : Except Error MExpr :=
  if env.consts.contains tc then
    match env.mkBody l body #[] with
    | .ok out => .ok ⟨tc, out.toList⟩
    | .error e => .error e
  else .error (.invalid s!"{l}: typecode {tc} is not a constant")

/-- A `$e` statement. -/
def addEssential (env : Env) (l tc : String) (body : List String) : Except Error Env := do
  let env ← env.newLabel l
  let e ← env.mkExpr l tc body
  pure (env.addHyp l (.ess e))

/-- Process a statement other than an assertion. -/
def step (env : Env) : Stmt → Except Error Env
  | .comment _ => .ok env
  | .constants cs => env.addConsts cs
  | .variables vs => env.addVars vs
  | .disjoint vs => env.addDisjoint vs
  | .floating l tc v => env.addFloat l tc v
  | .essential l tc body => env.addEssential l tc body
  | .openScope => .ok { env with outer := env.scope :: env.outer }
  | .closeScope =>
    match env.outer with
    | sc :: rest => .ok { env with scope := sc, outer := rest }
    | [] => .error (.invalid "$} without matching ${")
  | .include f => .error (.invalid s!"unresolved file inclusion {f}")
  | .axiom l _ _ | .provable l _ _ _ => .error (.invalid s!"{l}: unexpected assertion")

end Env

/-! ## Proofs -/

/-- The checked assertions so far, with a label index. -/
structure Core where
  db : Database String String := ⟨#[]⟩
  asserts : HashMap String MAssertion := {}
  deriving Inhabited

/-- Record a checked assertion. -/
def Core.add (c : Core) (l : String) (k : Kind) (A : MAssertion) : Core :=
  { db := c.db.push ⟨l, k, A⟩, asserts := c.asserts.insert l A }

/-- The distinct labels of a normal proof, in order of first occurrence. -/
def distinctLabels (steps : List String) : List String :=
  (steps.foldl (init := (({} : HashSet String), ([] : List String))) fun acc l =>
    if acc.1.contains l then acc else (acc.1.insert l, l :: acc.2)).2

/-- Keep the first labelled floating hypothesis of each variable not in `seen`. -/
def firstFloats (seen : HashSet String) :
    List (String × String × String) → List (String × String × String)
  | [] => []
  | p :: l => if seen.contains p.2.2 then firstFloats seen l
    else p :: firstFloats (seen.insert p.2.2) l

theorem firstFloats_spec : ∀ (seen : HashSet String) (l : List (String × String × String)),
    (∀ p ∈ firstFloats seen l, p ∈ l ∧ seen.contains p.2.2 = false) ∧
      ((firstFloats seen l).map fun p => p.2.2).Nodup
  | _, [] => by simp [firstFloats]
  | seen, p :: l => by
    unfold firstFloats
    split
    · obtain ⟨h₁, h₂⟩ := firstFloats_spec seen l
      exact ⟨fun q hq => ⟨List.mem_cons_of_mem _ (h₁ q hq).1, (h₁ q hq).2⟩, h₂⟩
    · rename_i hp
      obtain ⟨h₁, h₂⟩ := firstFloats_spec (seen.insert p.2.2) l
      have hmem : ∀ q ∈ firstFloats (seen.insert p.2.2) l,
          q ∈ l ∧ seen.contains q.2.2 = false ∧ p.2.2 ≠ q.2.2 := by
        intro q hq
        have hq' := (h₁ q hq).2
        simp only [HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hq'
        exact ⟨(h₁ q hq).1, hq'.2, hq'.1⟩
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨List.mem_cons_self .., by simpa using hp⟩
        · exact ⟨List.mem_cons_of_mem _ (hmem q hq).1, (hmem q hq).2.1⟩
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨?_, h₂⟩
        simp only [List.mem_map, not_exists, not_and]
        exact fun q hq h => (hmem q hq).2.2 h.symm

/-- The optional floating hypotheses a proof mentions, labelled, for a theorem
whose variables (with multiplicity) are listed in `allVars`: the first one of
each variable not in `allVars`. -/
def optionalFloats (sc : Scope) (allVars : List String) (labels : List String) :
    List (String × String × String) :=
  firstFloats (HashSet.ofList allVars) <| labels.filterMap fun l =>
    match (sc.hypMap[l]? : Option MHyp) with
    | some (Hyp.float tc v) => some (l, tc, v)
    | _ => none

theorem optionalFloats_fresh {sc : Scope} {allVars labels : List String}
    {p : String × String × String} (hp : p ∈ optionalFloats sc allVars labels) :
    p.2.2 ∉ allVars := by
  have h := ((firstFloats_spec _ _).1 p hp).2
  simp only [HashSet.contains_ofList] at h
  exact fun h' => Bool.noConfusion (h ▸ List.contains_iff_mem.2 h')

theorem optionalFloats_nodup (sc : Scope) (allVars labels : List String) :
    ((optionalFloats sc allVars labels).map fun p => p.2.2).Nodup :=
  (firstFloats_spec _ _).2

/-- The dummy variables of a proof: the optional floating hypotheses `opt` and
the active `$d` pairs that involve them. -/
def mkDummies (sc : Scope) (A : MAssertion) (opt : List (String × String × String))
    (hopt : ∀ p ∈ opt, p.2.2 ∉ A.allVars) (hnd : (opt.map fun p => p.2.2).Nodup) :
    Dummies A :=
  let ds := HashSet.ofList (opt.map fun p => p.2.2)
  { floats := opt.map Prod.snd
    dv := sc.dvPairs.toList.filter fun p => ds.contains p.1 || ds.contains p.2
    fresh := by
      intro p hp
      simp only [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact hopt q hq
    nodup := by simpa [List.map_map, Function.comp_def] using hnd
    dv_dummy := by
      intro p hp
      simp only [List.mem_filter, Bool.or_eq_true, ds, HashSet.contains_ofList,
        List.contains_iff_mem] at hp
      simpa [List.map_map, Function.comp_def] using hp.2 }

/-- The disjointness test of a frame. -/
def disjTest (F : MAssertion) : String → String → Bool :=
  let s := HashSet.ofList F.dv
  fun a b => s.contains (a, b) || s.contains (b, a)

/-- Resolve a proof label: an earlier assertion, a mandatory hypothesis, or an
optional floating hypothesis. -/
def resolve (asserts : HashMap String MAssertion) (mand : List (String × MHyp))
    (opt : List (String × String × String)) (l : String) :
    Except ProofError (Instr String String) :=
  match asserts[l]? with
  | some B => .ok (.app l B)
  | none =>
    match mand.lookup l with
    | some h => .ok (.hyp h.expr)
    | none =>
      match opt.lookup l with
      | some p => .ok (.hyp ⟨p.1, [.var p.2]⟩)
      | none => .error (.unknownLabel l)

/-- Resolve the steps of a normal proof. -/
def resolveSteps (r : String → Except ProofError (Instr String String)) :
    List String → Array (Instr String String) → Except ProofError (Array (Instr String String))
  | [], out => .ok out
  | l :: ls, out =>
    if l == "?" then .error .incomplete
    else
      match r l with
      | .ok i => resolveSteps r ls (out.push i)
      | .error e => .error e

/-- Resolve the label list of a compressed proof, which may not name mandatory
hypotheses. -/
def resolveList (r : String → Except ProofError (Instr String String))
    (mand : List (String × MHyp)) :
    List String → Array (Instr String String) → Except ProofError (Array (Instr String String))
  | [], out => .ok out
  | l :: ls, out =>
    if (mand.lookup l).isSome then .error (.mandatoryInList l)
    else
      match r l with
      | .ok i => resolveList r mand ls (out.push i)
      | .error e => .error e

/-- The instructions of a proof. -/
def instrs (r : String → Except ProofError (Instr String String)) (A : MAssertion)
    (mand : List (String × MHyp)) : ProofText → Except ProofError (List (Instr String String))
  | .normal steps =>
    match resolveSteps r steps #[] with
    | .ok out => .ok out.toList
    | .error e => .error e
  | .compressed labels letters =>
    match resolveList r mand labels #[] with
    | .ok list => decode A.hypExprs.toArray list letters
    | .error e => .error e

/-- The labels a proof mentions. -/
def proofLabels : ProofText → List String
  | .normal steps => distinctLabels steps
  | .compressed labels _ => labels

/-- Run the proof machine on the proof of `A`, whose mandatory hypotheses with
labels are `mand`, in the extended frame of the optional floating hypotheses
it mentions. -/
def runProof (asserts : HashMap String MAssertion) (sc : Scope) (A : MAssertion)
    (mand : List (String × MHyp)) (pf : ProofText) : Except ProofError Unit :=
  let opt := optionalFloats sc A.allVars (proofLabels pf)
  let D := mkDummies sc A opt (fun _ => optionalFloats_fresh) (optionalFloats_nodup ..)
  match instrs (resolve asserts mand opt) A mand pf with
  | .ok is => verify (disjTest (A.extend D)) is A.concl
  | .error e => .error e

/-- Check the proof of the theorem `label`. -/
def proveTheorem (asserts : HashMap String MAssertion) (sc : Scope) (label : String)
    (A : MAssertion) (mand : List (String × MHyp)) (pf : ProofText) : Except Error Unit :=
  match runProof asserts sc A mand pf with
  | .ok () => .ok ()
  | .error .incomplete => .error (.incomplete label)
  | .error e => .error (.proof label e)

/-! ## The checker -/

/-- The checker state. -/
structure Checker where
  core : Core := {}
  env : Env := {}
  deriving Inhabited

namespace Checker

/-- Check an assertion; `pf` is its proof if it is a `$p` statement. -/
def addAssertion (s : Checker) (l tc : String) (body : List String)
    (pf : Option ProofText) : Except Error Checker :=
  match s.env.newLabel l with
  | .error err => .error err
  | .ok env =>
    match env.mkExpr l tc body with
    | .error err => .error err
    | .ok e =>
      let mv := env.scope.mandVars e
      let mand := env.scope.mandHyps mv
      let A : MAssertion := ⟨env.scope.mandDV mv, mand.map Prod.snd, e⟩
      if wfCheck A then
        match pf with
        | none => .ok ⟨s.core.add l .axiom A, env⟩
        | some pf =>
          match proveTheorem s.core.asserts env.scope l A mand pf with
          | .ok () => .ok ⟨s.core.add l .theorem A, env⟩
          | .error err => .error err
      else .error (.invalid s!"{l}: ill-formed frame")

/-- Process one statement. -/
def step (s : Checker) (st : Stmt) : Except Error Checker :=
  match st with
  | .axiom l tc body => s.addAssertion l tc body none
  | .provable l tc body pf => s.addAssertion l tc body (some pf)
  | st =>
    match s.env.step st with
    | .ok env => .ok { s with env }
    | .error e => .error e

/-- Process a statement sequence. -/
def run : Checker → List Stmt → Except Error Checker
  | s, [] => .ok s
  | s, st :: sts =>
    match s.step st with
    | .ok s' => run s' sts
    | .error e => .error e

end Checker

/-- Check a database. On success, return its checked assertions. -/
def check (src : Source) : Except Error (Database String String) :=
  match Checker.run {} src with
  | .ok s => if s.env.outer.isEmpty then .ok s.core.db else .error (.invalid "unclosed ${")
  | .error e => .error e

end Silmaril.Logic.Metamath.Verify
