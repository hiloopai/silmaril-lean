module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.SExp.Basic

/-!
# The `--ast` pretty printer

`spectec/src/util/sexpr.ml:15` lays out an S-expression against a target line
`width`: a node is printed on one line when it fits, and otherwise one child
per line, each indented two columns past its parent.  The transcription below
is literal.

## The length `pp` returns is exact

`len` (`spectec/src/util/sexpr.ml:19`) is not an estimate: it is exactly the
byte width of the one-line rendering of its argument.  That rendering is an
open parenthesis, the tag, a space and a child for each child, and a close
parenthesis, so it is `1 + |s| + Σᵢ (1 + lenᵢ) + 1` bytes; `sexpr.ml:19`
groups the same sum as `|s| + n + (2 + Σᵢ lenᵢ)`.  `flatWidth` below is that
number and `pp_fst` identifies it with `(pp off width e).1`, which — as in
OCaml — depends on neither `off` nor `width`.

Two consequences:

* A node that fits never has a child that breaks.  The node fits exactly when
  `off + len ≤ width`, and its children are laid out at `off + 2`; whenever
  there is an `i`-th child, `len = |s| + n + 2 + Σⱼ lenⱼ ≥ 3 + lenᵢ`, so
  `off + 2 + lenᵢ < off + len ≤ width`.  The whole subtree is therefore flat,
  and the rendering really is `flatWidth` bytes wide.
* `pp` lays the children out at `off + 2` (`sexpr.ml:18`) *before* testing
  whether the parent fits, and keeps that layout either way.  By the previous
  point that is harmless rather than a quirk: if the parent fits, every child
  was laid out flat and its offset never entered the result; if the parent
  breaks, `off + 2` is the column the child is actually printed at.

The corresponding Lean statement, `flatWidth e = (render w e).utf8ByteSize`
for `w` at least `flatWidth e`, is true by the argument above but is *not*
proved in this file; only `pp_fst` is.

## Byte lengths

Lengths are byte lengths, as in OCaml.  Every atom and tag that `--ast` emits
is ASCII — texts and identifiers go through `String.escaped`
(`spectec/src/backend-ast/print.ml:12`), and every other atom is a fixed
keyword or a numeral — so `String.utf8ByteSize` and `String.length` agree on
them, but the byte length is what the OCaml code uses and what is transcribed
here.
-/

@[expose] public section

namespace Silmaril.SpecTec

/-- `rope` (`spectec/src/util/sexpr.ml:3`). -/
inductive Rope where
  /-- `Leaf of string`. -/
  | leaf (value : String)
  /-- `Concat of rope list`. -/
  | concat (parts : List Rope)
  deriving Repr, Inhabited

namespace Rope

mutual

/-- `concat` (`spectec/src/util/sexpr.ml:11-12`). -/
def flatten : Rope → String
  | .leaf s => s
  | .concat rs => flattens rs

/-- `String.concat "" (List.map concat rs)` (`spectec/src/util/sexpr.ml:13`). -/
def flattens : List Rope → String
  | [] => ""
  | r :: rs => flatten r ++ flattens rs

end

@[simp] theorem flatten_leaf (s : String) : flatten (.leaf s) = s := rfl
@[simp] theorem flatten_concat (rs : List Rope) : flatten (.concat rs) = flattens rs := rfl
@[simp] theorem flattens_nil : flattens [] = "" := rfl
@[simp] theorem flattens_cons (r : Rope) (rs : List Rope) :
    flattens (r :: rs) = flatten r ++ flattens rs := rfl

end Rope

namespace SExp

/-- `String.make off ' '` (`spectec/src/util/sexpr.ml:22`). -/
def indent (off : Nat) : String := String.ofList (List.replicate off ' ')

@[simp] theorem indent_zero : indent 0 = "" := rfl

mutual

/-- `pp` (`spectec/src/util/sexpr.ml:15-23`), returning the flat width of the
argument and the layout rope. -/
def pp (off width : Nat) : SExp → Nat × Rope
  | .atom s => (s.utf8ByteSize, .leaf s)
  | .node s xs =>
      let lrs := ppList (off + 2) width xs
      let len := s.utf8ByteSize + lrs.length + (2 + (lrs.map Prod.fst).sum)
      let sepFin : String × String :=
        if off + len ≤ width then (" ", "")
        else ("\n  " ++ indent off, "\n" ++ indent off)
      (len,
        .concat
          (.leaf "(" :: .leaf s ::
            (lrs.map fun lr => Rope.concat [.leaf sepFin.1, lr.2]) ++
              [.leaf sepFin.2, .leaf ")"]))

/-- `List.map (pp (off + 2) width) xs` (`spectec/src/util/sexpr.ml:18`). -/
def ppList (off width : Nat) : List SExp → List (Nat × Rope)
  | [] => []
  | x :: xs => pp off width x :: ppList off width xs

end

theorem ppList_eq_map (off width : Nat) :
    ∀ xs : List SExp, ppList off width xs = xs.map (pp off width)
  | [] => rfl
  | x :: xs => by simp [ppList, ppList_eq_map off width xs]

/-- The flat width that `pp` assigns to an S-expression.  This is `fst (pp …)`
and, as in OCaml, does not depend on the offset or the target width. -/
def flatWidth : SExp → Nat
  | .atom s => s.utf8ByteSize
  | .node s xs => s.utf8ByteSize + xs.length + (2 + (xs.map flatWidth).sum)

mutual

theorem pp_fst (off width : Nat) : ∀ e : SExp, (pp off width e).1 = flatWidth e
  | .atom _ => by simp [pp, flatWidth]
  | .node s xs => by
      simp only [pp, flatWidth, ppList_eq_map, List.length_map, List.map_map]
      exact congrArg (fun l => s.utf8ByteSize + xs.length + (2 + l.sum))
        (ppList_fst (off + 2) width xs)

theorem ppList_fst (off width : Nat) :
    ∀ xs : List SExp, xs.map (fun e => (pp off width e).1) = xs.map flatWidth
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, pp_fst off width x, ppList_fst off width xs]

end

/-- The layout of a single S-expression at a given offset and target width. -/
def render (width : Nat) (e : SExp) : String := (pp 0 width e).2.flatten

/-- `Sexpr.output` (`spectec/src/util/sexpr.ml:25-28`) appends a newline
(`sexpr.ml:27`). -/
def output (width : Nat) (e : SExp) : String := render width e ++ "\n"

/-- `List.iter (Sexpr.output oc cfg.width)`, the body of
`Backend_ast.Print.output_script` (`spectec/src/backend-ast/print.ml:235`).

The OCaml applies that iteration not to the script but to `script s`
(`print.ml:224-225`), which is `List.map def` followed by
`List.filter ((<>) (Atom ""))`.  The only definition `def` can send to
`Atom ""` is a `HintD` (`print.ml:218-219`), so the filter is exactly the
erasure that `Silmaril/SpecTec/IL/Ast.lean` builds into `IL.Def`; `es` here is
already the filtered list. -/
def outputScript (width : Nat) (es : List SExp) : String :=
  String.join (es.map (output width))

/-- The exact contents of a `spectec --ast -o FILE` file: `output_script`
followed by one more newline (`spectec/src/exe-spectec/main.ml:256-257`). -/
def astFile (width : Nat) (es : List SExp) : String := outputScript width es ++ "\n"

/-- The default `--ast-width` (`spectec/src/backend-ast/config.ml:9`). -/
def defaultWidth : Nat := 80

end SExp

end Silmaril.SpecTec
