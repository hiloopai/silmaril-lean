module

public meta import Lean
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Free
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.IL.Decode
public meta import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Parse

/-!
# Errata, as patches on an imported `IL.Script`

Phase 4 of `docs/projects/spectec-divergences.md`.  Thirty-three defects in the pinned
WebAssembly specifications have been verified and given local numbers;
this file turns one of them into a Lean value, so that "the corrected
specification" is an `IL.Script` in which every definition that differs from
the pinned one cites an erratum number.

## The shape of a patch

An `Erratum` is *one corrected top-level definition* plus its provenance.
`applyErratum` splices it into a script by name, and refuses to do anything
surprising:

* the name must be declared exactly once in the whole script — `countDefs`
  counts across all four of `free.ml`'s declaration namespaces and recurses
  into `recD` groups, because most definitions live inside one;
* the corrected definition must declare that same name;
* and it must actually differ from the one it replaces.

Replacement itself (`replaceDef`) is keyed not on the bare name but on
`declKind?`, the *namespace and* name a definition declares.  That is what
makes the metatheory below unconditional: a definition is only ever swapped
for one that declares exactly what it declared, so

* `boundDefs` — the identifiers the script declares, `spectec/src/il/free.ml`
  — is preserved (`boundDefs_replaceDefs`),
* the number of definitions is preserved (`length_replaceDefs`),
* `countDefs` of every name is preserved (`countDefs_replaceDefs`),
* and two errata with different targets commute (`replaceDefs_comm`,
  `applyErratum_comm`).

Nothing here says a patch is *right*; that is the job of the issue it cites
and of the elaborator below, which makes the edit auditable by forcing it to
be spelled out as a textual diff of the definition's own `--ast` rendering.

## The `spectec_erratum` command

```
spectec_erratum 655 in wasm30 on "cont"
  because "the continuation-byte range excludes 0x80"
  replacing "(cmp lt nat (num (nat 128))"
  with      "(cmp le nat (num (nat 128))"
```

The elaborator reads `wasm30` back out of the environment with `Import.lean`'s
`unqDef`, finds the single definition named `cont`, prints it with `IL.defS`
and `SExp.render` at `wideWidth` (so the fragment cannot straddle a line
break), checks the `replacing` string occurs **exactly once** — ambiguity is an
error, not a silent first match — substitutes, re-reads the result with
`SExp.parse`, decodes it with `IL.decodeDef?`, checks that it differs from the
original and declares the same thing, and emits

```lean
def wasm30.erratum655 : IL.Erratum := { issue := 655, …, corrected := … }
```

Three properties make that honest: the patch is a diff, so a reader sees
exactly what changed; the corrected definition comes out of the *same* decoder
as the original, so it cannot be ill-formed in a way the original was not; and
"occurs exactly once" and "actually changes something" are checked, so a patch
cannot silently stop applying if the pinned stream is ever rebumped.

`because`, `replacing` and `with` each take one or more string literals, which
are concatenated.  A long fragment is therefore written as several lines
rather than as one over-long literal.  The optional `as` clause names the
emitted constant; it is needed when one issue corrects more than one
definition, as `#654` does.
-/

@[expose] public section

namespace Silmaril.SpecTec.IL

/-! ## Equality of definitions

`IL.Def` sits in a nested, mutually recursive group, so Lean's `deriving`
handler cannot give it `DecidableEq`.  As in `Silmaril/SpecTec/Sem/Eval.lean`,
equality is decided *through the printer*: `defS` is injective
(`IL.defS_injective`) and `SExp` does have `DecidableEq`. -/

/-- Structural equality of top-level definitions, decided through `IL.defS`. -/
def defEq (d₁ d₂ : Def) : Bool := defS d₁ == defS d₂

/-- `defEq` decides equality of definitions: `decodeDef?` is a left inverse of
`defS` (`IL.decodeDef?_defS`), so `defS` is injective. -/
@[simp] theorem defEq_iff {d₁ d₂ : Def} : defEq d₁ d₂ = true ↔ d₁ = d₂ := by
  constructor
  · intro h
    have h' : defS d₁ = defS d₂ := by simpa [defEq] using h
    exact defS_injective h'
  · rintro rfl; simp [defEq]

/-! ## What a top-level definition declares -/

/-- Which of `spectec/src/il/free.ml`'s declaration namespaces a top-level
definition declares into.  `varid` is missing because no `Def` binds a term
variable at top level (`free.ml:205-212`). -/
inductive DeclKind where
  /-- `typD`: a `syntax` definition; `bound_def` puts it in `typid`. -/
  | typ
  /-- `relD`: a relation declaration; `relid`. -/
  | rel
  /-- `decD`: a function definition; `defid`. -/
  | dec
  /-- `gramD`: a grammar definition; `gramid`. -/
  | gram
  deriving DecidableEq, Repr, Inhabited

/-- The namespace and name a top-level definition declares.  A `recD` is a
recursion group rather than a declaration and has no single name, so it is
`none` (`spectec/src/il/free.ml:211`). -/
def declKind? : Def → Option (DeclKind × Id)
  | .typD x _ _ => some (.typ, x)
  | .relD x _ _ _ _ => some (.rel, x)
  | .decD x _ _ _ => some (.dec, x)
  | .gramD x _ _ _ => some (.gram, x)
  | .recD _ => none

/-- The name a top-level definition declares, forgetting the namespace. -/
def declName? (d : Def) : Option Id := (declKind? d).map Prod.snd

/-- `true` exactly on `Def.recD`, the one constructor whose children are
themselves top-level definitions. -/
def isRecD : Def → Bool
  | .recD _ => true
  | _ => false

/-- The identifier set `bound_def` (`spectec/src/il/free.ml:205-212`) assigns
to a declaration, as a function of its namespace and name. -/
def boundDecl : DeclKind × Id → Sets
  | (.typ, x) => boundTypid x
  | (.rel, x) => boundRelid x
  | (.dec, x) => boundDefid x
  | (.gram, x) => boundGramid x

/-- `boundDef` factors through `declKind?` on every non-`recD` definition. -/
theorem boundDef_eq_boundDecl {d : Def} {kx : DeclKind × Id} (h : declKind? d = some kx) :
    boundDef d = boundDecl kx := by
  cases d <;> simp only [declKind?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-- A definition that declares something is not a recursion group. -/
theorem isRecD_eq_false_of_declKind? {d : Def} {kx : DeclKind × Id}
    (h : declKind? d = some kx) : isRecD d = false := by
  cases d <;> simp_all [declKind?, isRecD]

/-- `declName?` factors through `declKind?`. -/
theorem declName?_eq_of_declKind? {d₁ d₂ : Def} (h : declKind? d₁ = declKind? d₂) :
    declName? d₁ = declName? d₂ := by
  simp [declName?, h]

/-! ## Counting declarations

`countDef` counts by *name* across all four namespaces at once.  That is
deliberately coarse: an erratum whose target name is reused in a second
namespace is rejected rather than resolved silently. -/

mutual

/-- How many definitions inside `d` declare the name `x`, in any namespace,
counting into `recD` groups. -/
def countDef (x : Id) : Def → Nat
  | .recD ds => countDefs x ds
  | d => if declName? d == some x then 1 else 0

/-- `countDef` summed over a list of definitions; `IL.Script` is one. -/
def countDefs (x : Id) : List Def → Nat
  | [] => 0
  | d :: ds => countDef x d + countDefs x ds

end

/-- The uniform equation for `countDef` away from `recD`. -/
theorem countDef_of_not_isRecD {x : Id} {d : Def} (h : isRecD d = false) :
    countDef x d = if declName? d == some x then 1 else 0 := by
  cases d <;> first | rfl | simp [isRecD] at h

@[simp] theorem countDef_recD (x : Id) (ds : List Def) :
    countDef x (.recD ds) = countDefs x ds := rfl

@[simp] theorem countDefs_nil (x : Id) : countDefs x [] = 0 := rfl

@[simp] theorem countDefs_cons (x : Id) (d : Def) (ds : List Def) :
    countDefs x (d :: ds) = countDef x d + countDefs x ds := rfl

/-! ## Finding and replacing a declaration -/

/-- `true` when `d` declares exactly what `new` declares — same namespace,
same name — and so is the definition `new` is meant to replace. -/
def matchesDecl (new d : Def) : Bool :=
  match declKind? d with
  | some kx => declKind? new == some kx
  | none => false

/-- A match forces both sides to declare the same thing. -/
theorem declKind?_of_matchesDecl {new d : Def} (h : matchesDecl new d = true) :
    ∃ kx, declKind? d = some kx ∧ declKind? new = some kx := by
  cases d <;> simp_all [matchesDecl, declKind?]

/-- Nothing matches a definition that declares something else. -/
theorem matchesDecl_eq_false {n m : Def} {kx : DeclKind × Id}
    (hm : declKind? m = some kx) (h : declKind? n ≠ some kx) : matchesDecl n m = false := by
  simp [matchesDecl, hm, h]

/-- A recursion group matches nothing: it declares no single name. -/
@[simp] theorem matchesDecl_recD (new : Def) (ds : List Def) :
    matchesDecl new (.recD ds) = false := rfl

mutual

/-- The definition inside `d` that declares what `new` declares, if any; the
first in printing order. -/
def findDef? (new : Def) : Def → Option Def
  | .recD ds => findDefs? new ds
  | d => if matchesDecl new d then some d else none

/-- `findDef?` over a list, left to right. -/
def findDefs? (new : Def) : List Def → Option Def
  | [] => none
  | d :: ds => (findDef? new d).or (findDefs? new ds)

end

mutual

/-- Replace every definition declaring what `new` declares by `new`,
recursing into `recD` groups. -/
def replaceDef (new : Def) : Def → Def
  | .recD ds => .recD (replaceDefs new ds)
  | d => if matchesDecl new d then new else d

/-- `replaceDef` over a list; `IL.Script` is one. -/
def replaceDefs (new : Def) : List Def → List Def
  | [] => []
  | d :: ds => replaceDef new d :: replaceDefs new ds

end

/-- The uniform equation for `findDef?` away from `recD`. -/
theorem findDef?_of_not_isRecD {new d : Def} (h : isRecD d = false) :
    findDef? new d = if matchesDecl new d then some d else none := by
  cases d <;> first | rfl | simp [isRecD] at h

/-- The uniform equation for `replaceDef` away from `recD`. -/
theorem replaceDef_of_not_isRecD {new d : Def} (h : isRecD d = false) :
    replaceDef new d = if matchesDecl new d then new else d := by
  cases d <;> first | rfl | simp [isRecD] at h

@[simp] theorem findDefs?_nil (new : Def) : findDefs? new [] = none := rfl

@[simp] theorem findDefs?_cons (new d : Def) (ds : List Def) :
    findDefs? new (d :: ds) = (findDef? new d).or (findDefs? new ds) := rfl

@[simp] theorem replaceDefs_nil (new : Def) : replaceDefs new [] = [] := rfl

@[simp] theorem replaceDefs_cons (new d : Def) (ds : List Def) :
    replaceDefs new (d :: ds) = replaceDef new d :: replaceDefs new ds := rfl

/-! ## Flattening, and the definitions a script declares -/

mutual

/-- The declarations inside a definition, with `recD` groups flattened away. -/
def flattenDef : Def → List Def
  | .recD ds => flattenDefs ds
  | d => [d]

/-- `flattenDef` over a list; `IL.Script` is one. -/
def flattenDefs : List Def → List Def
  | [] => []
  | d :: ds => flattenDef d ++ flattenDefs ds

end

/-- The uniform equation for `flattenDef` away from `recD`. -/
theorem flattenDef_of_not_isRecD {d : Def} (h : isRecD d = false) : flattenDef d = [d] := by
  cases d <;> first | rfl | simp [isRecD] at h

/-- The declarations of a script that declare the name `x`.  This is what the
`spectec_erratum` elaborator searches with. -/
def namedDefs (x : Id) (s : List Def) : List Def :=
  (flattenDefs s).filter (fun d => declName? d == some x)

/-- The non-`recD` half of `countDef_eq_length_filter`. -/
theorem countDef_eq_length_filter_aux {x : Id} {d : Def} (h : isRecD d = false) :
    countDef x d = ((flattenDef d).filter (fun e => declName? e == some x)).length := by
  rw [countDef_of_not_isRecD h, flattenDef_of_not_isRecD h]
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp_all

mutual

/-- `countDef` counts exactly the declarations `namedDefs` finds. -/
theorem countDef_eq_length_filter (x : Id) : ∀ d : Def,
    countDef x d = ((flattenDef d).filter (fun e => declName? e == some x)).length
  | .recD ds => countDefs_eq_length_filter x ds
  | .typD .. => countDef_eq_length_filter_aux rfl
  | .relD .. => countDef_eq_length_filter_aux rfl
  | .decD .. => countDef_eq_length_filter_aux rfl
  | .gramD .. => countDef_eq_length_filter_aux rfl

/-- `countDefs` counts exactly the declarations `namedDefs` finds. -/
theorem countDefs_eq_length_filter (x : Id) : ∀ ds : List Def,
    countDefs x ds = ((flattenDefs ds).filter (fun e => declName? e == some x)).length
  | [] => rfl
  | d :: ds => by
      show countDef x d + countDefs x ds = _
      rw [countDef_eq_length_filter x d, countDefs_eq_length_filter x ds]
      show _ = (List.filter _ (flattenDef d ++ flattenDefs ds)).length
      rw [List.filter_append, List.length_append]

end

/-- `countDefs x s` is the number of definitions `namedDefs x s` returns, so
the elaborator's "exactly one definition named `x`" and `applyErratum`'s
`countDefs x s = 1` are the same condition. -/
theorem countDefs_eq_length_namedDefs (x : Id) (s : List Def) :
    countDefs x s = (namedDefs x s).length :=
  countDefs_eq_length_filter x s

/-! ## The metatheory of replacement -/

/-- `replaceDefs` is a `map`, so a script's definitions are patched
independently and in place. -/
theorem replaceDefs_eq_map (new : Def) : ∀ ds : List Def,
    replaceDefs new ds = ds.map (replaceDef new)
  | [] => rfl
  | d :: ds => by simp [replaceDefs_eq_map new ds]

/-- A patch preserves the number of top-level definitions. -/
@[simp] theorem length_replaceDefs (new : Def) (ds : List Def) :
    (replaceDefs new ds).length = ds.length := by
  simp [replaceDefs_eq_map]

/-- The non-`recD` half of `declKind?_replaceDef`. -/
theorem declKind?_replaceDef_aux (new : Def) {d : Def} (h : isRecD d = false) :
    declKind? (replaceDef new d) = declKind? d := by
  rw [replaceDef_of_not_isRecD h]
  by_cases hm : matchesDecl new d
  · obtain ⟨kx, hd, hn⟩ := declKind?_of_matchesDecl hm
    simp [hm, hd, hn]
  · simp [hm]

mutual

/-- A patch preserves what each definition declares. -/
theorem declKind?_replaceDef (new : Def) : ∀ d : Def,
    declKind? (replaceDef new d) = declKind? d
  | .recD _ => rfl
  | .typD .. => declKind?_replaceDef_aux new rfl
  | .relD .. => declKind?_replaceDef_aux new rfl
  | .decD .. => declKind?_replaceDef_aux new rfl
  | .gramD .. => declKind?_replaceDef_aux new rfl

end

/-- The non-`recD` half of `countDef_replaceDef`. -/
theorem countDef_replaceDef_aux (new : Def) (x : Id) {d : Def} (h : isRecD d = false) :
    countDef x (replaceDef new d) = countDef x d := by
  rw [replaceDef_of_not_isRecD h]
  by_cases hm : matchesDecl new d
  · obtain ⟨kx, hd, hn⟩ := declKind?_of_matchesDecl hm
    have hite : (if matchesDecl new d = true then new else d) = new := by simp [hm]
    rw [hite, countDef_of_not_isRecD (isRecD_eq_false_of_declKind? hn),
      countDef_of_not_isRecD h, declName?_eq_of_declKind? (hn.trans hd.symm)]
  · simp [hm]

mutual

/-- A patch preserves `countDef`. -/
theorem countDef_replaceDef (new : Def) (x : Id) : ∀ d : Def,
    countDef x (replaceDef new d) = countDef x d
  | .recD ds => countDefs_replaceDefs new x ds
  | .typD .. => countDef_replaceDef_aux new x rfl
  | .relD .. => countDef_replaceDef_aux new x rfl
  | .decD .. => countDef_replaceDef_aux new x rfl
  | .gramD .. => countDef_replaceDef_aux new x rfl

/-- A patch preserves `countDefs`: the names a script declares, with
multiplicity, do not move. -/
theorem countDefs_replaceDefs (new : Def) (x : Id) : ∀ ds : List Def,
    countDefs x (replaceDefs new ds) = countDefs x ds
  | [] => rfl
  | d :: ds => by
      show countDef x (replaceDef new d) + countDefs x (replaceDefs new ds) = _
      rw [countDef_replaceDef new x d, countDefs_replaceDefs new x ds]
      rfl

end

/-- The non-`recD` half of `boundDef_replaceDef`. -/
theorem boundDef_replaceDef_aux (new : Def) {d : Def} (h : isRecD d = false) :
    boundDef (replaceDef new d) = boundDef d := by
  rw [replaceDef_of_not_isRecD h]
  by_cases hm : matchesDecl new d
  · obtain ⟨kx, hd, hn⟩ := declKind?_of_matchesDecl hm
    have hite : (if matchesDecl new d = true then new else d) = new := by simp [hm]
    rw [hite, boundDef_eq_boundDecl hn, boundDef_eq_boundDecl hd]
  · simp [hm]

mutual

/-- A patch preserves the identifiers a definition binds
(`spectec/src/il/free.ml:205-212`). -/
theorem boundDef_replaceDef (new : Def) : ∀ d : Def,
    boundDef (replaceDef new d) = boundDef d
  | .recD ds => boundDefs_replaceDefs new ds
  | .typD .. => boundDef_replaceDef_aux new rfl
  | .relD .. => boundDef_replaceDef_aux new rfl
  | .decD .. => boundDef_replaceDef_aux new rfl
  | .gramD .. => boundDef_replaceDef_aux new rfl

/-- A patch preserves the identifiers a script declares.  This is the sense in
which a corrected specification declares the same things as the pinned one. -/
theorem boundDefs_replaceDefs (new : Def) : ∀ ds : List Def,
    boundDefs (replaceDefs new ds) = boundDefs ds
  | [] => rfl
  | d :: ds => by
      show (boundDef (replaceDef new d)).union (boundDefs (replaceDefs new ds)) = _
      rw [boundDef_replaceDef new d, boundDefs_replaceDefs new ds]
      rfl

end

/-- The non-`recD` half of `replaceDef_of_countDef_eq_zero`. -/
theorem replaceDef_of_countDef_eq_zero_aux {new d : Def} {x : Id}
    (hname : declName? new = some x) (hr : isRecD d = false) (h : countDef x d = 0) :
    replaceDef new d = d := by
  rw [replaceDef_of_not_isRecD hr]
  have hm : matchesDecl new d = false := by
    by_contra hc
    obtain ⟨kx, hk, hn⟩ := declKind?_of_matchesDecl (by simpa using hc)
    have hx : declName? d = some x := by
      rw [declName?_eq_of_declKind? (hk.trans hn.symm), hname]
    rw [countDef_of_not_isRecD hr, hx] at h
    simp at h
  simp [hm]

mutual

/-- A definition that does not declare the patch's name is left alone. -/
theorem replaceDef_of_countDef_eq_zero {new : Def} {x : Id}
    (hname : declName? new = some x) : ∀ d : Def, countDef x d = 0 → replaceDef new d = d
  | .recD ds, h => congrArg Def.recD (replaceDefs_of_countDefs_eq_zero hname ds h)
  | .typD .., h => replaceDef_of_countDef_eq_zero_aux hname rfl h
  | .relD .., h => replaceDef_of_countDef_eq_zero_aux hname rfl h
  | .decD .., h => replaceDef_of_countDef_eq_zero_aux hname rfl h
  | .gramD .., h => replaceDef_of_countDef_eq_zero_aux hname rfl h

/-- A list of definitions none of which declares the patch's name is left
alone.  With `replaceDefs_eq_map`, this is "definitions other than the target
are unchanged". -/
theorem replaceDefs_of_countDefs_eq_zero {new : Def} {x : Id}
    (hname : declName? new = some x) : ∀ ds : List Def, countDefs x ds = 0 →
      replaceDefs new ds = ds
  | [], _ => rfl
  | d :: ds, h => by
      have h' : countDef x d = 0 ∧ countDefs x ds = 0 := by
        have : countDef x d + countDefs x ds = 0 := h
        omega
      show replaceDef new d :: replaceDefs new ds = d :: ds
      rw [replaceDef_of_countDef_eq_zero hname d h'.1,
        replaceDefs_of_countDefs_eq_zero hname ds h'.2]

end

/-! ## Disjoint patches commute -/

/-- The non-`recD` half of `findDef?_replaceDef`. -/
theorem findDef?_replaceDef_aux {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂)
    {d : Def} (hd : isRecD d = false) :
    findDef? n₂ (replaceDef n₁ d) = findDef? n₂ d := by
  rw [replaceDef_of_not_isRecD hd]
  by_cases hm : matchesDecl n₁ d
  · obtain ⟨kx, hk, hn⟩ := declKind?_of_matchesDecl hm
    have hne : declKind? n₂ ≠ some kx := fun hc => h (hn.trans hc.symm)
    simp [hm, findDef?_of_not_isRecD (isRecD_eq_false_of_declKind? hn),
      findDef?_of_not_isRecD hd, matchesDecl_eq_false hn hne, matchesDecl_eq_false hk hne]
  · simp [hm]

mutual

/-- Looking for one patch's target is unaffected by applying a patch with a
different target. -/
theorem findDef?_replaceDef {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂) : ∀ d : Def,
    findDef? n₂ (replaceDef n₁ d) = findDef? n₂ d
  | .recD ds => findDefs?_replaceDefs h ds
  | .typD .. => findDef?_replaceDef_aux h rfl
  | .relD .. => findDef?_replaceDef_aux h rfl
  | .decD .. => findDef?_replaceDef_aux h rfl
  | .gramD .. => findDef?_replaceDef_aux h rfl

/-- `findDef?_replaceDef`, over a list. -/
theorem findDefs?_replaceDefs {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂) :
    ∀ ds : List Def, findDefs? n₂ (replaceDefs n₁ ds) = findDefs? n₂ ds
  | [] => rfl
  | d :: ds => by
      show (findDef? n₂ (replaceDef n₁ d)).or (findDefs? n₂ (replaceDefs n₁ ds)) = _
      rw [findDef?_replaceDef h d, findDefs?_replaceDefs h ds]
      rfl

end

/-- The non-`recD` half of `replaceDef_comm`. -/
theorem replaceDef_comm_aux {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂)
    {d : Def} (hd : isRecD d = false) :
    replaceDef n₂ (replaceDef n₁ d) = replaceDef n₁ (replaceDef n₂ d) := by
  rw [replaceDef_of_not_isRecD hd, replaceDef_of_not_isRecD hd]
  by_cases hm₁ : matchesDecl n₁ d
  · obtain ⟨kx, hk, hn⟩ := declKind?_of_matchesDecl hm₁
    have hne : declKind? n₂ ≠ some kx := fun hc => h (hn.trans hc.symm)
    simp [hm₁, matchesDecl_eq_false hk hne, matchesDecl_eq_false hn hne,
      replaceDef_of_not_isRecD hd, replaceDef_of_not_isRecD (isRecD_eq_false_of_declKind? hn)]
  · by_cases hm₂ : matchesDecl n₂ d
    · obtain ⟨kx, hk, hn⟩ := declKind?_of_matchesDecl hm₂
      have hne : declKind? n₁ ≠ some kx := fun hc => h (hc.trans hn.symm)
      simp [hm₁, hm₂, matchesDecl_eq_false hn hne,
        replaceDef_of_not_isRecD hd, replaceDef_of_not_isRecD (isRecD_eq_false_of_declKind? hn)]
    · simp [hm₁, hm₂, replaceDef_of_not_isRecD hd]

mutual

/-- Two patches with different targets commute. -/
theorem replaceDef_comm {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂) : ∀ d : Def,
    replaceDef n₂ (replaceDef n₁ d) = replaceDef n₁ (replaceDef n₂ d)
  | .recD ds => congrArg Def.recD (replaceDefs_comm h ds)
  | .typD .. => replaceDef_comm_aux h rfl
  | .relD .. => replaceDef_comm_aux h rfl
  | .decD .. => replaceDef_comm_aux h rfl
  | .gramD .. => replaceDef_comm_aux h rfl

/-- Two patches with different targets commute, on a whole script. -/
theorem replaceDefs_comm {n₁ n₂ : Def} (h : declKind? n₁ ≠ declKind? n₂) :
    ∀ ds : List Def, replaceDefs n₂ (replaceDefs n₁ ds) = replaceDefs n₁ (replaceDefs n₂ ds)
  | [] => rfl
  | d :: ds => by
      show replaceDef n₂ (replaceDef n₁ d) :: replaceDefs n₂ (replaceDefs n₁ ds) = _
      rw [replaceDef_comm h d, replaceDefs_comm h ds]
      rfl

end

/-! ## Errata -/

/-- One verified erratum: a local erratum number, the single top-level
definition it changes, and the corrected definition.  `corrected` is always
produced by `IL.decodeDef?` from an edit of the original's own `--ast`
rendering, so it is a definition the printer could have printed. -/
structure Erratum where
  /-- The local erratum number the patch cites. -/
  issue : Nat
  /-- A one-line statement of the defect, for the audit trail. -/
  summary : String
  /-- The name of the one top-level definition the erratum changes. -/
  target : Id
  /-- The corrected definition. -/
  corrected : Def
  deriving Repr, Inhabited

/-- The `--ast` width an erratum's fragments are quoted at.  No `IL.Def` in the
pinned streams renders anywhere near this wide, so `SExp.render wideWidth`
always lays a definition out flat on one line and a textual fragment never
straddles a line break that `Util.Sexpr.pp` would have inserted. -/
def wideWidth : Nat := 1000000000

/-- The conditions under which an erratum applies to a script: the target is
declared exactly once, the corrected definition declares it, and the patch is
not a no-op. -/
def Erratum.applies (e : Erratum) (s : Script) : Bool :=
  declName? e.corrected == some e.target && countDefs e.target s == 1 &&
    (match findDefs? e.corrected s with
      | some d => !defEq d e.corrected
      | none => false)

/-- The corrected definition of an applicable erratum declares its target. -/
theorem declName?_of_applies {e : Erratum} {s : Script} (h : e.applies s = true) :
    declName? e.corrected = some e.target := by
  unfold Erratum.applies at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

/-- Splice an erratum's corrected definition into a script, replacing the one
definition that declares the same thing.  `none` when `Erratum.applies` fails:
when the target is missing or ambiguous, when the corrected definition
declares something else, or when the patch would change nothing. -/
def applyErratum (e : Erratum) (s : Script) : Option Script :=
  if e.applies s then some (replaceDefs e.corrected s) else none

/-- Apply a list of errata left to right, failing if any of them fails. -/
def applyErrata : List Erratum → Script → Option Script
  | [], s => some s
  | e :: es, s => (applyErratum e s).bind (applyErrata es)

@[simp] theorem applyErrata_nil (s : Script) : applyErrata [] s = some s := rfl

@[simp] theorem applyErrata_cons (e : Erratum) (es : List Erratum) (s : Script) :
    applyErrata (e :: es) s = (applyErratum e s).bind (applyErrata es) := rfl

/-- An applicable erratum's result is the replacement, and nothing else. -/
theorem applyErratum_eq_some {e : Erratum} {s s' : Script}
    (h : applyErratum e s = some s') : e.applies s = true ∧ s' = replaceDefs e.corrected s := by
  by_cases hc : e.applies s
  · have hs : applyErratum e s = some (replaceDefs e.corrected s) := by simp [applyErratum, hc]
    rw [hs] at h
    exact ⟨hc, (Option.some.inj h).symm⟩
  · simp [applyErratum, hc] at h

/-- An erratum preserves the number of top-level definitions. -/
theorem length_of_applyErratum {e : Erratum} {s s' : Script}
    (h : applyErratum e s = some s') : s'.length = s.length := by
  rw [(applyErratum_eq_some h).2]; simp

/-- An erratum preserves the identifiers the script declares. -/
theorem boundDefs_of_applyErratum {e : Erratum} {s s' : Script}
    (h : applyErratum e s = some s') : boundDefs s' = boundDefs s := by
  rw [(applyErratum_eq_some h).2]; exact boundDefs_replaceDefs _ _

/-- An erratum leaves every definition that does not declare its target
alone.  Together with `replaceDefs_eq_map` and `(applyErratum_eq_some h).2`
this is "definitions other than the target are unchanged". -/
theorem applyErratum_other {e : Erratum} {s s' : Script} {d : Def}
    (h : applyErratum e s = some s') (hd : countDef e.target d = 0) :
    replaceDef e.corrected d = d :=
  replaceDef_of_countDef_eq_zero (declName?_of_applies (applyErratum_eq_some h).1) d hd

/-- A list of errata preserves the number of top-level definitions. -/
theorem length_of_applyErrata : ∀ (es : List Erratum) (s s' : Script),
    applyErrata es s = some s' → s'.length = s.length
  | [], s, s', h => by simp only [applyErrata_nil, Option.some.injEq] at h; rw [h]
  | e :: es, s, s', h => by
      simp only [applyErrata_cons, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ht'⟩ := h
      exact (length_of_applyErrata es t s' ht').trans (length_of_applyErratum ht)

/-- A list of errata preserves the identifiers the script declares. -/
theorem boundDefs_of_applyErrata : ∀ (es : List Erratum) (s s' : Script),
    applyErrata es s = some s' → boundDefs s' = boundDefs s
  | [], s, s', h => by simp only [applyErrata_nil, Option.some.injEq] at h; rw [h]
  | e :: es, s, s', h => by
      simp only [applyErrata_cons, Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, ht'⟩ := h
      exact (boundDefs_of_applyErrata es t s' ht').trans (boundDefs_of_applyErratum ht)

/-- Two errata with different targets have the same effect in either order.
`declKind?` rather than `target` is the hypothesis because that is what
`replaceDef` keys on: two errata in *different namespaces* with the same name
commute too. -/
theorem applyErratum_comm {e₁ e₂ : Erratum}
    (h : declKind? e₁.corrected ≠ declKind? e₂.corrected) (s : Script) :
    (applyErratum e₁ s).bind (applyErratum e₂) =
      (applyErratum e₂ s).bind (applyErratum e₁) := by
  have ha₂ : e₂.applies (replaceDefs e₁.corrected s) = e₂.applies s := by
    simp [Erratum.applies, countDefs_replaceDefs, findDefs?_replaceDefs h]
  have ha₁ : e₁.applies (replaceDefs e₂.corrected s) = e₁.applies s := by
    simp [Erratum.applies, countDefs_replaceDefs, findDefs?_replaceDefs (Ne.symm h)]
  by_cases h₁ : e₁.applies s <;> by_cases h₂ : e₂.applies s <;>
    simp [applyErratum, h₁, h₂, ha₁, ha₂, replaceDefs_comm h]

/-- Two errata with different targets commute, as a two-element list. -/
theorem applyErrata_pair_comm {e₁ e₂ : Erratum}
    (h : declKind? e₁.corrected ≠ declKind? e₂.corrected) (s : Script) :
    applyErrata [e₁, e₂] s = applyErrata [e₂, e₁] s := by
  have he : ∀ e : Erratum, applyErrata [e] = applyErratum e := by
    intro e
    funext t
    cases ht : applyErratum e t <;> simp [applyErrata, ht]
  show (applyErratum e₁ s).bind (applyErrata [e₂]) = (applyErratum e₂ s).bind (applyErrata [e₁])
  rw [he, he]
  exact applyErratum_comm h s

end Silmaril.SpecTec.IL

end

/-! ## The elaborator -/

public meta section

namespace Silmaril.SpecTec.IL

open Lean Elab Command Term Meta Silmaril.SpecTec

/- The elaborator below is compile-time code that calls the run-time
declarations above — `namedDefs`, `wideWidth`, `applyErratum` — in the *same*
module, which the module system's phase check rejects by default.  This is the
option Lean core itself uses for the same situation
(`Lean/Parser/Term/Basic.lean:189`); it relaxes the check for same-module
references only, and references to imports are unaffected. -/
set_option compiler.relaxedMetaCheck true

/-- Read the `IL.Script` a constant denotes, at elaboration time.

`spectec_import` emits a script as a list of *constants*, one per definition,
so each element is unfolded once before `Import.lean`'s `unqDef` reads it back.
A script written out as a literal list of reflected definitions is accepted
too. -/
def erratumScript (n : Name) : CommandElabM Script := do
  let value ← constValue n
  let some elems := unqList (fun e => some e) value
    | throwError "spectec_erratum: the term for {n} is not a list of `IL.Def`"
  elems.mapM fun e => do
    match unqDef e with
    | some d => pure d
    | none =>
      let some c := e.constName?
        | throwError "spectec_erratum: {n} has an element that is neither a reflected \
            `IL.Def` nor a constant"
      let some d := unqDef (← constValue c)
        | throwError "spectec_erratum: {c} is not a reflected `IL.Def`"
      pure d

/-- Concatenate the string literals of a `str+` position.  A long fragment is
written as several literals, one per source line, rather than as one literal
too wide for the line-length limit. -/
def joinStrs (ss : Array (TSyntax `str)) : String :=
  String.join (ss.toList.map (·.getString))

/-- `spectec_erratum N in script on "target" because … replacing … with … [as x]`
— see the module documentation. -/
syntax (name := spectecErratum)
  "spectec_erratum " num " in " ident " on " str
  " because " str+
  " replacing " str+
  " with " str+
  (" as " ident)? : command

/-- Elaborate `spectec_erratum`. -/
@[command_elab spectecErratum]
def elabSpectecErratum : CommandElab := fun stx => do
  let `(command| spectec_erratum $issueStx:num in $scriptStx:ident on $targetStx:str
      because $becauseStx:str* replacing $oldStx:str* with $newStx:str*
      $[as $asStx:ident]?) := stx
    | throwUnsupportedSyntax
  let issue := issueStx.getNat
  let target := targetStx.getString
  let summary := joinStrs becauseStx
  let oldFrag := joinStrs oldStx
  let newFrag := joinStrs newStx
  if oldFrag.isEmpty then
    throwError "spectec_erratum: the `replacing` fragment is empty"
  let scriptName ← liftCoreM <| realizeGlobalConstNoOverload scriptStx
  let script ← erratumScript scriptName
  let hits := namedDefs target script
  let [orig] := hits
    | throwError "spectec_erratum: {scriptName} declares {hits.length} definitions named \
        {target}; an erratum must name exactly one"
  let printed := SExp.render wideWidth (defS orig)
  let occurrences := (printed.splitOn oldFrag).length - 1
  unless occurrences == 1 do
    throwError "spectec_erratum: the `replacing` fragment occurs {occurrences} times in the \
      printed form of {target}; it must occur exactly once.  The definition reads:\n{printed}"
  let edited := printed.replace oldFrag newFrag
  let form ← match SExp.parse edited with
    | .error message =>
        throwError "spectec_erratum: the edited {target} is not an S-expression: {message}"
    | .ok form => pure form
  let some corrected := decodeDef? form
    | throwError "spectec_erratum: the edited {target} is not a printed SpecTec IL definition"
  if defS corrected == defS orig then
    throwError "spectec_erratum: the edit leaves {target} unchanged; a no-op erratum is an error"
  unless declKind? corrected == declKind? orig do
    throwError "spectec_erratum: the edit changes what {target} declares"
  let erratum : Erratum :=
    { issue := issue, summary := summary, target := target, corrected := corrected }
  unless (applyErratum erratum script).isSome do
    throwError "spectec_erratum: the erratum does not apply to {scriptName}"
  let suffix := match asStx with
    | some x => x.getId
    | none => Name.mkSimple s!"erratum{issue}"
  let declName := (← getCurrNamespace) ++ Name.mkSimple scriptName.getString! ++ suffix
  let value := mkAppN (mkConst ``Erratum.mk)
    #[mkNatLit issue, mkStrLit summary, mkStrLit target, qDef corrected]
  liftCoreM <| addDefn declName (mkConst ``Erratum) value
  checkErratum declName corrected
  logInfo m!"spectec_erratum {issue}: {declName} corrects {target} in {scriptName} \
    ({oldFrag.length} characters replaced by {newFrag.length} in a \
    {printed.length}-character definition)"
where
  /-- Re-read the term the kernel accepted and check it denotes `corrected`,
  exactly as `spectec_import`'s `checkDefn` does for an imported definition. -/
  checkErratum (declName : Name) (corrected : Def) : CommandElabM Unit := do
    let value ← constValue declName
    let some field := (match value.getAppFnArgs with
      | (``Erratum.mk, #[_, _, _, c]) => some c
      | _ => none)
      | throwError "spectec_erratum: the term emitted for {declName} is not an `IL.Erratum`"
    let some d := unqDef field
      | throwError "spectec_erratum: the `corrected` field of {declName} is not a reflected \
          `IL.Def`"
    unless defS d == defS corrected do
      throwError "spectec_erratum: the term emitted for {declName} does not denote the \
        definition it was decoded from; `qDef` and `unqDef` disagree"

end Silmaril.SpecTec.IL
