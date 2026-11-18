module

public import Silmaril.Project.Registry.Defs
public import Silmaril.Project.Registry.Language.Defs
public import Silmaril.Project.Registry.Predicate.Defs
public import Silmaril.Logic.Consequence.Soundness.Defs
public import Silmaril.Logic.Concrete.Codec.Defs
public import Silmaril.Logic.Consequence.Derivation.SExp.Defs

/-!
# Silmaril projects: formal rows, presentations, properties and problems

Four kinds that make a logic's interpretation, soundness and consistency explorable
(`docs/projects/formal-rows.md`). Each names Lean declarations, and Lean checks what the record
claims from their **types**. A theorem's name never stands in for its statement.

| kind | Lean checks | Lean fills |
|---|---|---|
| `presentation N := c` | `c : SExpCodec A` | `abstract` (`A`), `codec_name` and `codec_version` (read from `c`), `default` |
| `logic_property N := t (role := r) (system := S)` | the type of `t` (applied to `arg`, if given) has the shape of the role for the registered system `S` | `statement`, `interpretation` or `falsity` and `context`, `axioms` |
| `logic_problem N := φ (presentation := P)` | `φ`'s type is `P`'s abstract type; each claim's theorem states the claim *about `φ`* | `sexp` (`P` printing `φ`, by evaluation), `renderings` (every registered presentation of the same abstract syntax printing `φ`), claims with their statements and axioms |
| `logic_row N` | every referenced record exists, with its kind | — |

**Roles of `logic_property`:**
* `soundness`: `System.SoundFor S I`; Lean fills `interpretation` (`I`).
* `consistency`: `System.ConsistentWrt S ff Γ`; Lean fills `falsity` and `context`.
* `nontriviality`: `System.ContextConsistent S Γ`; Lean fills `context`.
* `satisfiability`: `Room.Satisfiable R Γ` or `Satisfaction.Satisfiable I Γ`, with no system.
* `inclusion`: `S ≤ T`, for the registered systems `S` (`system`) and `T` (`target`).

**Derivation systems and derivations:**
* `derivation_system N := D (arg := a)`: `D a : DerivationSystem J`. Optional claims, each a Lean
  term: `(locally_sound := t)`, checked as `D.LocallySound sat`; `(agrees := t) (system := S)`,
  checked as `X = S` for the registered system `S`. `(judgments := P)` must present `J`, and every
  presentation in `formats` must present proof trees or indexed lines over `J`.
* `derivation N := p (presentation := P) (system := D)`: `p` is of `P`'s abstract type. Lean prints `p`
  in every registered presentation of proof trees of that type and, flattened into indexed lines
  (`ProofTree.lines 0 p`), in every registered presentation of lines (`renderings`). Each theorem in
  `verdicts` must state `check e = r`, where `e` is one of those encodings of `p`; Lean records the
  checker, the result and whether it accepts (`Except.ok`). Lean also records the indexed `steps`
  (rule, judgment in the system's `judgments` presentation, cited lines) by evaluation. `(derives := t) (derives_system := S)`
  is checked as `S Γ φ`.

**Claims of `logic_problem`** (each optional):
* `(derived := t) (system := S)`: `t : S Γ φ` for some context `Γ`;
* `(entailed := t) (entailed_by := S)`: the same, for a semantic system;
* `(truth := t) (interpretation := I)`: `t : I.satC m φ` for some model `m`, or for every model;
  `I` is a Lean term (a string when it is an application).
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Term Command

/-- The roles a `logic_property` may have. -/
def propertyRoles : List String :=
  ["soundness", "consistency", "nontriviality", "satisfiability", "inclusion"]

/-- A registered consequence system's definition. -/
def systemDecl (kind name : String) : MetaM Name := do
  let some r := findRecord? (← getEnv) "consequence_system" name
    | throwError "silmaril {kind}: no `silmaril consequence_system {name}` is declared or imported"
  let some d := r.str? "decl" | throwError "silmaril {kind}: system {name} has no `decl`"
  return d.toName

/-- Elaborate `c args` (or `c` alone) as a closed term. -/
def elabApplied (kind : String) (c : Name) (args? : Option String) : TermElabM Expr := do
  match args? with
  | none => mkConstWithFreshMVarLevels c
  | some a =>
    let stx ← match Parser.runParserCategory (← getEnv) `term s!"{c} {a}" with
      | .ok stx => pure stx
      | .error err => throwError "silmaril {kind}: `arg`: {err}"
    elabClosed stx none

/-- `c : SExpCodec A`: the abstract type `A` and the codec's universe level. -/
def codecType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnf ty
  return if ty.isAppOfArity ``Silmaril.Logic.Concrete.SExpCodec 1 then some ty.appArg! else none

/-- Reduce a `String`-valued expression to its literal. -/
def stringLit (kind what : String) (e : Expr) : MetaM String := do
  match (← whnf e) with
  | .lit (.strVal s) => return s
  | e' => throwError "silmaril {kind}: {what} does not reduce to a string literal:{indentExpr e'}"

unsafe def evalStringUnsafe (e : Expr) : TermElabM String :=
  Meta.evalExpr String (mkConst ``String) e

/-- Evaluate a closed `String` expression (its constants must be compiled and imported as `meta`). -/
@[implemented_by evalStringUnsafe]
opaque evalString (e : Expr) : TermElabM String

@[silmaril_kind presentation] def presentationHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    let d ← fs.const kind "decl"
    let some A ← codecType? (← inferType (← mkConstWithFreshMVarLevels d))
      | throwError "silmaril {kind}: {d} is not an `SExpCodec`"
    let c ← mkConstWithFreshMVarLevels d
    let cname ← stringLit kind "the codec's name" (← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.name #[c])
    let cver ← stringLit kind "the codec's version" (← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.version #[c])
    let mut fs := fs
    fs ← fs.push kind "abstract" (.str (← ppOneLine (← whnfR A)))
    fs ← fs.push kind "codec_name" (.str cname)
    fs ← fs.push kind "codec_version" (.str cver)
    if (fs.get? "default").isNone then fs ← fs.push kind "default" (.bool false)
    return #[(name, fs)]

/-- A statement that does not have a role's shape. -/
def roleFail {α : Type} (kind : String) (ty : Expr) (shape : String) : TermElabM α :=
  throwError "silmaril {kind}: the statement{indentExpr ty}\nis not {shape}"

/-- The constant `n` applied to fresh metavariables for all its binders, with the binders at the
given positions unified with the given terms; also returns the arguments. -/
def roleTarget (kind : String) (n : Name) (fixed : List (Nat × Expr)) : MetaM (Expr × Array Expr) := do
  let c ← mkConstWithFreshMVarLevels n
  let (mvs, _, _) ← forallMetaTelescope (← inferType c)
  for (i, e) in fixed do
    unless ← isDefEq mvs[i]! e do
      throwError "silmaril {kind}: {e} does not fit argument {i} of {n}"
  return (mkAppN c mvs, mvs)

/-- The shape of a role, for the registered systems `S` (and `T`). Returns the extra fields. -/
def checkRole (kind role : String) (ty : Expr) (S? T? : Option Expr) : TermElabM (Array (String × Json)) := do
  let needS : TermElabM Expr := match S? with
    | some S => pure S
    | none => throwError "silmaril {kind}: role {role} names its system: `(system := …)`"
  let show₁ (e : Expr) : MetaM Json := return .str (← ppOneLine (← instantiateMVars e))
  match role with
  | "soundness" =>
    -- `System.SoundFor {Ax} {C} S I`
    let (target, xs) ← roleTarget kind ``Silmaril.Consequence.System.SoundFor [(2, ← needS)]
    unless ← isDefEq ty target do roleFail kind ty "`System.SoundFor S I` for the registered system"
    return #[("interpretation", ← show₁ xs[3]!)]
  | "consistency" =>
    -- `System.ConsistentWrt {Ax} {C} S ff a`
    let (target, xs) ← roleTarget kind ``Silmaril.Consequence.System.ConsistentWrt [(2, ← needS)]
    unless ← isDefEq ty target do roleFail kind ty "`System.ConsistentWrt S ff Γ` for the registered system"
    return #[("falsity", ← show₁ xs[3]!), ("context", ← show₁ xs[4]!)]
  | "nontriviality" =>
    let (target, xs) ← roleTarget kind ``Silmaril.Consequence.System.ContextConsistent [(2, ← needS)]
    unless ← isDefEq ty target do roleFail kind ty "`System.ContextConsistent S Γ` for the registered system"
    return #[("context", ← show₁ xs[3]!)]
  | "satisfiability" =>
    let ty ← whnfR ty
    if ty.isAppOf ``Silmaril.Consequence.Room.Satisfiable ||
        ty.isAppOf ``Silmaril.Consequence.Satisfaction.Satisfiable then
      return #[("context", ← show₁ ty.appArg!)]
    roleFail kind ty "`Room.Satisfiable R Γ` or `Satisfaction.Satisfiable I Γ`"
  | "inclusion" =>
    let S ← needS
    let some T := T? | throwError "silmaril {kind}: role inclusion names its target: `(target := …)`"
    unless ← isDefEq ty (← mkAppM ``LE.le #[S, T]) do roleFail kind ty "`S ≤ T` for the registered systems"
    return #[]
  | r => throwError "silmaril {kind}: unknown role {r.quote}; expected one of {propertyRoles}"

@[silmaril_kind logic_property] def logicPropertyHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    let t ← fs.const kind "decl"
    unless ← isProp (← getConstInfo t).type do throwError "silmaril {kind}: {t} is not a theorem"
    let role ← fs.str kind "role"
    let at? := match fs.get? "arg" with | some (.str a) => some a | _ => none
    let e ← elabApplied kind t at?
    let ty ← instantiateMVars (← inferType e)
    let S? ← match fs.get? "system" with
      | some (.str s) => pure (some (Lean.mkConst (← systemDecl kind s)))
      | _ => pure none
    let T? ← match fs.get? "target" with
      | some (.str s) => pure (some (Lean.mkConst (← systemDecl kind s)))
      | _ => pure none
    let extra ← checkRole kind role ty S? T?
    let mut fs := fs
    fs ← fs.push kind "statement" (.str (← ppOneLine ty))
    for (k, v) in extra do fs ← fs.push kind k v
    let axioms := ((← collectAxioms t).map toString).qsort (· < ·)
    fs ← fs.push kind "axioms" (toJson axioms)
    return #[(name, fs)]

/-- Check a claim theorem `t` about `φ`: `t : S Γ φ` (for some `Γ`). -/
def checkDerived (kind : String) (t : Name) (S φ : Expr) : TermElabM Json := do
  let ty ← inferType (← mkConstWithFreshMVarLevels t)
  let Γ ← mkFreshExprMVar none
  unless ← isDefEq ty (mkApp2 S Γ φ) do
    throwError "silmaril {kind}: {t} states{indentExpr ty}\nnot that the system derives the problem's sentence"
  let axioms := ((← collectAxioms t).map toString).qsort (· < ·)
  return Json.mkObj [("proof", .str t.toString), ("context", .str (← ppOneLine (← instantiateMVars Γ))),
    ("statement", .str (← ppOneLine ty)), ("axioms", toJson axioms)]

/-- Check a truth theorem: `t : I.satC m φ` for some `m`, or `∀ m, I.satC m φ`. -/
def checkTruth (kind : String) (t : Name) (I φ : Expr) : TermElabM Json := do
  let ty ← inferType (← mkConstWithFreshMVarLevels t)
  let ok ← forallTelescope ty fun xs body => do
    if xs.size > 1 then return false
    -- `Satisfaction.satC {Ax} {C} I m φ`
    let c ← mkConstWithFreshMVarLevels ``Silmaril.Consequence.Satisfaction.satC
    let (mvs, _, _) ← forallMetaTelescope (← inferType c)
    unless (← isDefEq mvs[2]! I) && (← isDefEq mvs[4]! φ) do return false
    isDefEq body (mkAppN c mvs)
  unless ok do
    throwError "silmaril {kind}: {t} states{indentExpr ty}\nnot that the problem's sentence holds in a model of the interpretation"
  let axioms := ((← collectAxioms t).map toString).qsort (· < ·)
  return Json.mkObj [("proof", .str t.toString), ("statement", .str (← ppOneLine ty)), ("axioms", toJson axioms)]

@[silmaril_kind logic_problem] def logicProblemHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    let φn ← fs.const kind "decl"
    let φ ← mkConstWithFreshMVarLevels φn
    let pname ← fs.str kind "presentation"
    let pr ← needRecord kind "presentation" pname
    let some pd := pr.str? "decl" | throwError "silmaril {kind}: presentation {pname} has no `decl`"
    let c ← mkConstWithFreshMVarLevels pd.toName
    let some A ← codecType? (← inferType c) | throwError "silmaril {kind}: bad presentation {pname}"
    unless ← isDefEq (← inferType φ) A do
      throwError "silmaril {kind}: {φn} is not of the presentation's abstract type{indentExpr A}"
    -- the canonical S-expression, by evaluating the printer
    let bytes ← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.print #[c, φ]
    let text ← evalString (← mkAppM ``String.fromUTF8! #[← mkAppM ``List.toByteArray #[bytes]])
    let trim (t : String) : String := String.ofList (t.toList.reverse.dropWhile Char.isWhitespace).reverse
    -- the sentence in every registered presentation of the same abstract syntax
    let mut renderings : Array (String × Json) := #[]
    for r in records (← getEnv) do
      if r.kind != "presentation" then continue
      let some rd := r.str? "decl" | continue
      let c' ← mkConstWithFreshMVarLevels rd.toName
      let some A' ← codecType? (← inferType c') | continue
      unless ← isDefEq A' A do continue
      let b' ← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.print #[c', φ]
      let t' ← evalString (← mkAppM ``String.fromUTF8! #[← mkAppM ``List.toByteArray #[b']])
      renderings := renderings.push (r.name, .str (trim t'))
    let mut fs := fs
    fs ← fs.push kind "sexp" (.str (trim text))
    fs ← fs.push kind "renderings" (Json.mkObj renderings.toList)
    fs ← fs.push kind "sentence" (.str (← ppOneLine φ))
    if let some (.str t) := fs.get? "derived" then
      let S := Lean.mkConst (← systemDecl kind (← fs.str kind "system"))
      fs := fs.set "derived" (← checkDerived kind t.toName S φ)
    if let some (.str t) := fs.get? "entailed" then
      let S := Lean.mkConst (← systemDecl kind (← fs.str kind "entailed_by"))
      fs := fs.set "entailed" (← checkDerived kind t.toName S φ)
    if let some (.str t) := fs.get? "truth" then
      let istr ← fs.str kind "interpretation"
      let I ← match Parser.runParserCategory (← getEnv) `term istr with
        | .ok stx => elabClosed stx none
        | .error err => throwError "silmaril {kind}: `interpretation`: {err}"
      fs := fs.set "truth" (← checkTruth kind t.toName I φ)
    return #[(name, fs)]

/-! ## Derivation systems and derivations -/

/-- Elaborate a field holding a Lean term (a name or a string). -/
def termField (kind key : String) (fs : Fields) : TermElabM (Option Expr) := do
  match fs.get? key with
  | some (.str s) =>
    match Parser.runParserCategory (← getEnv) `term s with
    | .ok stx => return some (← elabClosed stx none)
    | .error err => throwError "silmaril {kind}: `{key}`: {err}"
  | none => return none
  | some _ => throwError "silmaril {kind}: `{key}` is a Lean term"

/-- A proof's statement and axioms, as recorded JSON. -/
def proofJson (kind key : String) (e : Expr) (extra : List (String × Json) := []) : TermElabM Json := do
  let ty ← instantiateMVars (← inferType e)
  let some c := e.getAppFn.constName? | throwError "silmaril {kind}: `{key}` is not a theorem application"
  let axioms := ((← collectAxioms c).map toString).qsort (· < ·)
  return Json.mkObj ([("proof", .str (← ppOneLine e)), ("statement", .str (← ppOneLine ty)),
    ("axioms", toJson axioms)] ++ extra)

/-- A constant with fresh universe levels, applied to the given arguments (which may contain
metavariables). -/
def appFresh (n : Name) (args : Array Expr) : MetaM Expr :=
  return mkAppN (← mkConstWithFreshMVarLevels n) args

/-- `D : DerivationSystem J`: the judgment type `J`. -/
def derivationSystemType? (ty : Expr) : MetaM (Option Expr) := do
  let ty ← whnfR ty
  return if ty.isAppOfArity ``Silmaril.Consequence.DerivationSystem 1 then some ty.appArg! else none

/-- A registered presentation's codec and abstract type. -/
def presentationCodec (kind pname : String) : TermElabM (Expr × Expr) := do
  let pr ← needRecord kind "presentation" pname
  let some pd := pr.str? "decl" | throwError "silmaril {kind}: presentation {pname} has no `decl`"
  let c ← mkConstWithFreshMVarLevels pd.toName
  let some A ← codecType? (← inferType c) | throwError "silmaril {kind}: bad presentation {pname}"
  return (c, A)

@[silmaril_kind derivation_system] def derivationSystemHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    let d ← fs.const kind "decl"
    let at? := match fs.get? "arg" with | some (.str a) => some a | _ => none
    let D ← elabApplied kind d at?
    let some J ← derivationSystemType? (← inferType D)
      | throwError "silmaril {kind}: {d} is not a `DerivationSystem`"
    let mut fs := fs
    fs ← fs.push kind "judgment" (.str (← ppOneLine (← whnfR J)))
    if let some (.str p) := fs.get? "judgments" then
      let (_, A) ← presentationCodec kind p
      unless ← isDefEq A J do throwError "silmaril {kind}: presentation {p} does not present {J}"
    if let some (.arr ps) := fs.get? "formats" then
      for x in ps do
        let .str p := x | throwError "silmaril {kind}: `formats` is a list of presentations"
        let (_, A) ← presentationCodec kind p
        let R ← mkFreshTypeMVar
        let tree ← appFresh ``Silmaril.Consequence.ProofTree #[R, J]
        let lines ← appFresh ``List #[← appFresh ``Silmaril.Consequence.Line #[R, J]]
        unless (← isDefEq A tree) || (← isDefEq A lines) do
          throwError "silmaril {kind}: presentation {p} presents neither proof trees nor lines over {J}"
    let mut claims : Array Json := #[]
    if let some t ← termField kind "locally_sound" fs then
      -- `DerivationSystem.LocallySound {J} D {M} sat`
      let (target, xs) ← roleTarget kind ``Silmaril.Consequence.DerivationSystem.LocallySound [(1, D)]
      let sat := xs[3]!
      unless ← isDefEq (← inferType t) target do
        roleFail kind (← inferType t) "`D.LocallySound sat` for this derivation system"
      claims := claims.push (← proofJson kind "locally_sound" t
        [("role", .str "locally_sound"), ("interpretation", .str (← ppOneLine (← instantiateMVars sat)))])
    if let some t ← termField kind "agrees" fs then
      let S := Lean.mkConst (← systemDecl kind (← fs.str kind "system"))
      let X ← mkFreshExprMVar none
      unless ← isDefEq (← inferType t) (← mkEq X S) do
        roleFail kind (← inferType t) "`X = S` for the registered system `S`"
      claims := claims.push (← proofJson kind "agrees" t [("role", .str "agrees")])
    fs ← fs.push kind "claims" (toJson claims)
    return #[(name, fs)]

/-- Print a value with a codec, by evaluation. -/
def printWith (c v : Expr) : TermElabM String := do
  let bytes ← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.print #[c, v]
  let text ← evalString (← mkAppM ``String.fromUTF8! #[← mkAppM ``List.toByteArray #[bytes]])
  return String.ofList (text.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- A checker such as `checkTree Theory.pa`, with short names: the function's last name component
and, for constant arguments, their last two. -/
def shortApp (e : Expr) : MetaM String := do
  let short (n : Name) (k : Nat) : String :=
    ".".intercalate ((n.componentsRev.take k).reverse.map toString)
  let some f := e.getAppFn.constName? | ppOneLine e
  let args ← e.getAppArgs.toList.mapM fun a => do
    match a.constName? with
    | some c => pure (short c 2)
    | none => pure s!"({← ppOneLine a})"
  return " ".intercalate (short f 1 :: args)

@[silmaril_kind derivation] def derivationHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    let pn ← fs.const kind "decl"
    let p ← mkConstWithFreshMVarLevels pn
    let sysRec ← needRecord kind "derivation_system" (← fs.str kind "system")
    let fname ← fs.str kind "presentation"
    let (c, A) ← presentationCodec kind fname
    unless ← isDefEq (← inferType p) A do
      throwError "silmaril {kind}: {pn} is not of the format's abstract type{indentExpr A}"
    let R ← mkFreshTypeMVar
    let J ← mkFreshTypeMVar
    unless ← isDefEq A (← appFresh ``Silmaril.Consequence.ProofTree #[R, J]) do
      throwError "silmaril {kind}: presentation {fname} does not present proof trees"
    let flat ← mkAppM ``Silmaril.Consequence.ProofTree.lines #[mkNatLit 0, p]
    let linesTy ← instantiateMVars (← appFresh ``List #[← appFresh ``Silmaril.Consequence.Line #[R, J]])
    -- every registered rendering: trees of this type, and the flattened lines
    let mut renderings : Array (String × Json) := #[]
    let mut encodings : Array (String × Expr) := #[]
    for r in records (← getEnv) do
      if r.kind != "presentation" then continue
      let some rd := r.str? "decl" | continue
      let c' ← mkConstWithFreshMVarLevels rd.toName
      let some A' ← codecType? (← inferType c') | continue
      let v? ← if ← isDefEq A' A then pure (some p)
        else if ← isDefEq A' linesTy then pure (some flat) else pure none
      let some v := v? | continue
      renderings := renderings.push (r.name, .str (← printWith c' v))
      encodings := encodings.push (r.name, ← mkAppM ``Silmaril.Logic.Concrete.SExpCodec.encode #[c', v])
    let mut verdicts : Array Json := #[]
    if let some (.arr ts) := fs.get? "verdicts" then
      for x in ts do
        let .str t := x | throwError "silmaril {kind}: `verdicts` is a list of theorems"
        let e ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload (mkIdent t.toName))
        let ty ← whnfR (← inferType e)
        let some (_, lhs, rhs) := ty.eq?
          | throwError "silmaril {kind}: {t} is not an equation `check e = r`"
        let some arg := (if lhs.isApp then some lhs.appArg! else none)
          | throwError "silmaril {kind}: {t}: the left side is not a checker applied to a proof"
        let mut fmt? : Option String := none
        for (n, enc) in encodings do
          if fmt?.isNone then
            if ← withNewMCtxDepth (isDefEq arg enc) then fmt? := some n
        let some fmt := fmt?
          | throwError "silmaril {kind}: {t} does not check an encoding of {pn}"
        let rhs' ← whnfR rhs
        let accepted := rhs'.isAppOf ``Except.ok
        -- a rejection's stage: the last component of the error's constructor
        let stage := if accepted || !rhs'.isApp then "" else
          match rhs'.appArg!.getAppFn.constName? with
          | some n => n.componentsRev.head?.map toString |>.getD ""
          | none => ""
        verdicts := verdicts.push (← proofJson kind "verdicts" e
          [("checker", .str (← shortApp lhs.appFn!)), ("format", .str fmt),
           ("result", .str (← ppOneLine rhs)), ("accepted", .bool accepted), ("stage", .str stage)])
    -- the indexed steps, with judgments in the system's judgment presentation
    let mut steps : Array Json := #[]
    if let some jp := sysRec.str? "judgments" then
      let (cj, _) ← presentationCodec kind jp
      let txt ← evalString (← mkAppM ``Silmaril.Consequence.ProofSExp.stepsText #[cj, p])
      let mut i := 0
      for row in txt.splitOn "\n" do
        match row.splitOn "\t" with
        | [k, r, j, ps] =>
          let prems := (ps.splitOn ",").filterMap String.toNat?
          steps := steps.push (Json.mkObj [("index", toJson i), ("kind", .str k), ("rule", .str r),
            ("judgment", .str j), ("premises", toJson prems)])
        | _ => throwError "silmaril {kind}: malformed step row {row.quote}"
        i := i + 1
    let mut fs := fs
    fs ← fs.push kind "steps" (toJson steps)
    fs ← fs.push kind "sexp" (.str (← printWith c p))
    fs ← fs.push kind "renderings" (Json.mkObj renderings.toList)
    -- the conclusion: the last step's judgment, as printed; otherwise the Lean term
    let concl ← match steps.back? with
      | some st => pure (st.getObjValAs? String "judgment" |>.toOption.getD "")
      | none => ppOneLine (← whnfR (← mkAppM ``Silmaril.Consequence.ProofTree.concl #[p]))
    fs ← fs.push kind "conclusion" (.str concl)
    fs := fs.set "verdicts" (toJson verdicts)
    if let some (.str t) := fs.get? "derives" then
      let S := Lean.mkConst (← systemDecl kind (← fs.str kind "derives_system"))
      let e ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload (mkIdent t.toName))
      let Γ ← mkFreshExprMVar none
      let φ ← mkFreshExprMVar none
      unless ← isDefEq (← inferType e) (mkApp2 S Γ φ) do
        roleFail kind (← inferType e) "`S Γ φ` for the registered system"
      fs := fs.set "derives" (← proofJson kind "derives" e
        [("context", .str (← ppOneLine (← instantiateMVars Γ))),
         ("sentence", .str (← ppOneLine (← instantiateMVars φ)))])
    return #[(name, fs)]

/-- The record kind of each list field of a `logic_row`. -/
def rowRefs : List (String × String) :=
  [("systems", "consequence_system"), ("presentations", "presentation"),
   ("properties", "logic_property"), ("problems", "logic_problem"),
   ("derivation_systems", "derivation_system"), ("derivations", "derivation")]

@[silmaril_kind logic_row] def logicRowHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    liftTermElabM do
    for (key, ofKind) in rowRefs do
      match fs.get? key with
      | some (.arr xs) => for x in xs do
          let .str s := x | throwError "silmaril {kind}: `{key}` is a list of names"
          discard <| needRecord kind ofKind s
      | some _ => throwError "silmaril {kind}: `{key}` is a list of names"
      | none => pure ()
    if let some (.arr xs) := fs.get? "interpretations" then
      for x in xs do
        let .str s := x | throwError "silmaril {kind}: `interpretations` is a list of declarations"
        let c ← mkConstWithFreshMVarLevels (← realizeGlobalConstNoOverload (mkIdent s.toName))
        let ok ← forallTelescopeReducing (← inferType c) fun _ body =>
          return (← whnfR body).isAppOf ``Silmaril.Consequence.Satisfaction
        unless ok do
          throwError "silmaril {kind}: {s} is not an interpretation (a family of `Satisfaction`s)"
    return #[(name, fs)]

end Silmaril.Project
