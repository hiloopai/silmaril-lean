module

public import Silmaril.Compiler.Core.Verified.Fold.Defs

/-! # `main` returning a closed integer expression

Cerberus elaborates `return e;` in `main` to `run ret_N(conv_loaded_int(int, x))` inside the
sequencing glue of the body (`sseq`, `wseq`, `bound`, `pure`), followed by the saved return
label `save ret_N(y := Specified 0) in pure y`. `recognize doc = some n` when `main`'s body has
exactly that shape and the glue before the label folds (`evalE`) to a transfer to the return
label with the integer `n`: every expression on the way is a closed pure integer expression
(`Fold.eval`), so this is constant folding, not an execution of the program. Memory actions,
calls, branches, loops and unsequenced expressions are outside the fragment.
-/

@[expose] public section
namespace Silmaril.Compile.Core.Verified.Return

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Fold

abbrev EExp := Expr Codec.wireModel Unit Unit Sym

/-- What the glue folds to: a value, or a transfer to a saved label with its arguments. -/
inductive Res where
  | val : WVal → Res
  | jump : Sym → List WVal → Res

/-- The sequencing glue whose transfers and values fold. -/
def simple : EExp → Bool
  | .mk _ (.pure _) | .mk _ (.bound _) | .mk _ (.run _ _ _) => true
  | .mk _ (.sseq _ a b) | .mk _ (.wseq _ a b) => simple a && simple b
  | _ => false

/-- Fold the glue. A transfer ends the evaluation of the enclosing sequence. -/
def evalE (doc : Doc) (fuel : Nat) : WEnv → EExp → Option Res
  | env, .mk _ (.pure p) => (eval doc fuel env p).map .val
  | env, .mk _ (.bound e) => evalE doc fuel env e
  | env, .mk _ (.sseq pat a b) | env, .mk _ (.wseq pat a b) =>
      match evalE doc fuel env a with
      | some (.val v) => match matchP pat v with
        | some xs => evalE doc fuel (extend xs env) b
        | none => none
      | some (.jump l vs) => some (.jump l vs)
      | none => none
  | env, .mk _ (.run _ l (p :: ps)) => ((p :: ps).mapM (eval doc fuel env)).map (.jump l)
  | _, _ => none

/-- The fuel of the folder: the nesting depth of std.core's conversions is below 10. -/
def fuel : Nat := 256

/-- `main`'s body: glue that transfers an integer to the return label, then that label. -/
def recognizeBody (doc : Doc) : EExp → Option Int
  | .mk _ (.sseq _ a (.mk _ (.save (ret, _) [(x, _)] (.mk _ (.pure (.mk _ _ (.sym y))))))) =>
      if MapKey.key x = MapKey.key y ∧ simple a = true then
        match evalE doc fuel ∅ a with
        | some (.jump l [.loaded (.specified (.integer n))]) =>
            if MapKey.key l = MapKey.key ret then some n else none
        | _ => none
      else none
  | _ => none

/-- No global definitions, `main` a procedure without parameters whose body is recognised. -/
def recognize (doc : Codec.Document) : Option Int := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

end Silmaril.Compile.Core.Verified.Return
