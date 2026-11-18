module

public import Silmaril.Logic.Consequence.Derivation.Defs
public import Silmaril.Logic.Concrete.Codec.Defs
public import Silmaril.Logic.Concrete.SExp.Defs

/-!
# Derivations as S-expressions (presentations `silmaril.derivation.tree` and `….lines`, v1)

Two concrete proof formats, generic in the presentation `cj` of the judgments. Rule labels are
**raw**: any S-expression, by convention a rule name or `(name arg*)`. A logic's elaborator turns
raw labels into its checked rule labels (`ProofTree.elaborate`), so these formats never trust a
label.

```
tree  ::= (assume J) | (infer RULE J tree*)
lines ::= (proof line*)
line  ::= (assume J) | (infer RULE J (i*))
```

`J` is a judgment in the presentation `cj`; `i` is the canonical decimal position of an earlier
line (from `0`). The tree format nests subproofs; the lines format is indexed, the shape shared
with Alethe (`assume`, `step … :premises`) and with index-based NDJSON formats.

`treeCodec cj` and `linesCodec cj` are presentations (`SExpCodec`): each decoder accepts exactly
the canonical forms (`Thms`).
-/

@[expose] public section

namespace Silmaril.Consequence.ProofSExp

open Silmaril.Logic.Smt (SE)
open Silmaril.Logic.Concrete (SExpCodec)
open Silmaril.Logic.Concrete.SExp (num num?)

universe u

variable {J : Type u} (cj : SExpCodec J)

mutual

/-- The concrete form of a proof tree. -/
def encodeTree : ProofTree SE J → SE
  | .assume j => .list [.atom "assume", cj.encode j]
  | .infer r c ts => .list (.atom "infer" :: r :: cj.encode c :: encodeTrees ts)

/-- The concrete forms of subproofs. -/
def encodeTrees : List (ProofTree SE J) → List SE
  | [] => []
  | t :: ts => encodeTree t :: encodeTrees ts

end

mutual

/-- Read the tree grammar. -/
def readTree : SE → Option (ProofTree SE J)
  | .list [.atom "assume", j] => (cj.decode j).map .assume
  | .list (.atom "infer" :: r :: c :: ts) =>
    match cj.decode c, readTrees ts with
    | some c, some ts => some (.infer r c ts)
    | _, _ => none
  | _ => none

/-- Read subproofs. -/
def readTrees : List SE → Option (List (ProofTree SE J))
  | [] => some []
  | e :: es =>
    match readTree e, readTrees es with
    | some t, some ts => some (t :: ts)
    | _, _ => none

end

/-- The concrete form of a line. -/
def encodeLine : Line SE J → SE
  | .assume j => .list [.atom "assume", cj.encode j]
  | .infer r c ixs => .list [.atom "infer", r, cj.encode c, .list (ixs.map num)]

/-- The concrete form of indexed lines. -/
def encodeLines (ls : List (Line SE J)) : SE := .list (.atom "proof" :: ls.map (encodeLine cj))

/-- Read canonical decimals. -/
def readNums : List SE → Option (List ℕ)
  | [] => some []
  | e :: es =>
    match num? e, readNums es with
    | some i, some is => some (i :: is)
    | _, _ => none

/-- Read a line. -/
def readLine : SE → Option (Line SE J)
  | .list [.atom "assume", j] => (cj.decode j).map .assume
  | .list [.atom "infer", r, c, .list is] =>
    match cj.decode c, readNums is with
    | some c, some is => some (.infer r c is)
    | _, _ => none
  | _ => none

/-- Read lines. -/
def readLineList : List SE → Option (List (Line SE J))
  | [] => some []
  | e :: es =>
    match readLine cj e, readLineList es with
    | some l, some ls => some (l :: ls)
    | _, _ => none

/-- Read the lines grammar. -/
def readLines : SE → Option (List (Line SE J))
  | .list (.atom "proof" :: es) => readLineList cj es
  | _ => none

end Silmaril.Consequence.ProofSExp
