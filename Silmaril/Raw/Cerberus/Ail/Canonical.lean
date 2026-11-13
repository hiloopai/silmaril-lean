module

public import Silmaril.Cerberus.Ail.Codec.Defs
public import Std.Data.HashMap
public import Std.Data.HashSet

/-! # Canonical fresh numbers

Cerberus draws symbol numbers, loop ids and CN marker ids from one process-wide counter,
`Cerb_fresh.int`, which the `std.core` parse and the Core evaluation of integer constant
expressions also advance. The oracle (`cerb-export2`, `export2/main.ml` `renumber`)
therefore prints each such value as its **rank** among the distinct values of its digest
group in the document: symbols are grouped by their own digest, loop and marker ids by the
input file's digest. Ranking keeps `Symbol.symbol_compare`, so maps keyed by symbols stay
strictly increasing.

`renumber` does the same to a printed document, so the frontend can allocate from any
increasing counter: only the relative order of the values that reach the output matters.
It reads the document back into an `Sx`, ranks, and renders. The fresh positions are those
of `wire.ml`'s `fresh_nat` (`Wire.sym`, `LAloop*`, `Amarker*`, `loop_attribute.marker_id`)
and of the generated printers (`AilSwhile`/`AilSdo` loop ids, `AilSmarker`, the marker of
`sigma_function_definition`, the keys of `sigma.loop_attributes`).

`renumber` is idempotent on canonical documents: the golden check runs every oracle Ail and
typed-Ail document through it.
-/

@[expose] public section

namespace Silmaril.Cerberus.Ail.Canonical

open Silmaril.Cerberus Cabs.Wire

/-! ## Rendering -/

/-- The canonical text of a tree: `(tag c₁ … cₙ)` with single spaces, atoms verbatim and
quoted atoms with the five escapes, as the emitters of `Cabs.Wire` print them. -/
def render : Sx → Out → Out
  | .atom s, o => o ++ s
  | .str s, o => quoted s o
  | .node t cs, o => close (cs.attach.foldl (fun o ⟨c, _⟩ => render c (o.push ' ')) (open_ t o))

/-! ## Fresh positions -/

/-- The child that holds a fresh number in a node of this tag, if any (besides `Symbol`). -/
def freshChild : String → Option Nat
  | "LAloop" | "LAloop_continue" | "LAloop_break" | "Amarker" | "Amarker_object_types"
  | "loop_attribute" | "AilSmarker" => some 0
  | "AilSwhile" | "AilSdo" => some 2
  | _ => none

section Walk

variable {m : Type → Type} [Monad m] (fileDigest : String) (f : String → Nat → m Nat)

/-- Apply `f group n` to a fresh atom. -/
def freshAtom (group : String) : Sx → m Sx
  | .atom s => match s.toNat? with
    | some n => return .atom (toString (← f group n))
    | none => return .atom s
  | x => return x

/-- The marker of a `sigma_function_definition`: `($tuple sym ($tuple loc n …))`. -/
def functionMarker : Sx → m Sx
  | .node "$tuple" #[s, .node "$tuple" #[l, n, as, ps, b]] => do
    return .node "$tuple" #[s, .node "$tuple" #[l, ← freshAtom f fileDigest n, as, ps, b]]
  | x => return x

/-- A key of `sigma.loop_attributes`: `($tuple n attr)`. -/
def loopKey : Sx → m Sx
  | .node "$tuple" #[k, v] => do return .node "$tuple" #[← freshAtom f fileDigest k, v]
  | x => return x

/-- The fixed positions of one node, after its children are walked. -/
def fixNode (tag : String) (cs : Array Sx) : m (Array Sx) := do
  if tag == "Symbol" then
    match cs with
    | #[.node "$str" #[.str d], n, desc] => return #[.node "$str" #[.str d], ← freshAtom f d n, desc]
    | _ => return cs
  if tag == "sigma" && cs.size == 14 then
    let fds ← match cs[2]! with
      | .node "$list" xs => Sx.node "$list" <$> xs.mapM (functionMarker fileDigest f)
      | x => pure x
    let las ← match cs[7]! with
      | .node "$map" xs => Sx.node "$map" <$> xs.mapM (loopKey fileDigest f)
      | x => pure x
    return (cs.set! 2 fds).set! 7 las
  match freshChild tag with
  | some i => if h : i < cs.size then return cs.set i (← freshAtom f fileDigest cs[i]) else return cs
  | none => return cs

/-- Rewrite every fresh number of a document with `f group n`. -/
def walk : Sx → m Sx
  | .node t cs => do
    let cs ← cs.attach.mapM fun ⟨c, _⟩ => walk c
    return .node t (← fixNode fileDigest f t cs)
  | x => return x

end Walk

/-! ## Ranking -/

/-- The fresh values of a document, as `(group, number)` pairs. -/
def collect (fileDigest : String) (t : Sx) : Std.HashSet (String × Nat) :=
  let go : StateM (Std.HashSet (String × Nat)) Sx :=
    walk fileDigest (fun g n => do modify (·.insert (g, n)); return n) t
  (go.run {}).2

/-- Rank every value within its group: 0, 1, … in increasing order. -/
def ranks (keys : Std.HashSet (String × Nat)) : Std.HashMap (String × Nat) Nat :=
  let groups : Std.HashMap String (Array Nat) :=
    keys.fold (fun g (d, n) => g.insert d ((g.getD d #[]).push n)) {}
  groups.fold (fun r d ns =>
    (ns.qsort (· < ·)).zipIdx.foldl (fun r (n, i) => r.insert (d, n) i) r) {}

/-- Replace every fresh value by its rank in its group. -/
def renumberSx (fileDigest : String) (t : Sx) : Sx :=
  let r := ranks (collect fileDigest t)
  Id.run (walk fileDigest (fun g n => pure (r.getD (g, n) n)) t)

/-- The digest of the children of a `Symbol` node, unless it is `""`. -/
def symbolDigest : Array Sx → Option String
  | #[.node "$str" #[.str d], _, _] => if d.isEmpty then none else some d
  | _ => none

/-- The digest of the first symbol whose digest is not `""` (a document comes from one
translation unit), or `""`. Used to renumber an oracle document, whose input file is not
at hand. -/
def firstDigest : Sx → Option String
  | .node t cs => if t == "Symbol" then symbolDigest cs else cs.attach.findSome? fun ⟨c, _⟩ => firstDigest c
  | _ => none

/-- Renumber a printed document (with its final newline) under the file digest `fileDigest`
(lowercase hex; `none`: take it from the document). A document that does not read back is
returned unchanged. -/
def renumber (fileDigest : Option String) (text : String) : String :=
  match read text.toByteArray with
  | .error _ => text
  | .ok t =>
    let d := fileDigest.getD ((firstDigest t).getD "")
    (render (renumberSx d t) "").push '\n'

end Silmaril.Cerberus.Ail.Canonical
