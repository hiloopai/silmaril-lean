module

public import Silmaril.Wasm.Wat
public meta import Silmaril.Wasm.Wat.CoreModules
public meta import Silmaril.Wasm.Wat.CoreInstructions

/-!
# `wat3b!`: Binaryen's WAT printing as Core 3 module terms

`wat3!` (silmaril-lean, `Silmaril.Wasm.Wat`) reads standard WAT. Binaryen prints multi-value
code with its own tuple instructions, which are not WAT: a function returning two values ends in
`(tuple.make 2 (a) (b))`, and a multi-value result is discarded by `(tuple.drop 2 (e))`. The
certificates of `wasm-check pass --wat` state their modules as `wat3!` terms (so that the
kernel checks the decoded module directly instead of decoding a binary), and could not use
Binaryen's printing of the `opt-in` corpus, which has such a function.

`wat3b! "…"` is `wat3!` after a rewrite of the instruction nodes (every function body, global
initialiser and segment offset, at every nesting depth):

* `(tuple.make n e₁ … eₙ)` becomes the folded operands `e₁ … eₙ`, spliced into the enclosing
  instruction sequence (a tuple of `n` values is `n` values on the stack);
* `(tuple.drop n e)` becomes `e drop … drop` (`n` drops).

These are the stack readings of Binaryen's tuple instructions. Before that, each function is
rewritten at the module level (`lowerFunc`) to remove **tuple-typed
locals**, which Binaryen introduces for the results of multi-value calls:

* `(local $t (tuple t₀ … tₙ₋₁))` becomes the `n` locals `(local $t.0 t₀) … (local $t.n-1 tₙ₋₁)`;
* `(local.get $t)` becomes `(local.get $t.0) … (local.get $t.n-1)`;
* `(local.set $t e)` becomes `e (local.set $t.n-1) … (local.set $t.0)` (the top of the stack is
  the last component), and `(local.tee $t e)` is that followed by the `local.get`s;
* `(tuple.extract n k (local.get $t))` becomes `(local.get $t.k)`, and
  `(tuple.extract n k (local.tee $t e))` the `local.set`s of `e` followed by `(local.get $t.k)`;
* `(tuple.extract n k e)` of any other operand `e` with `n` results whose types the text
  gives (a direct or indirect call, a `block`, `loop` or `if` with a result or type annotation)
  becomes `e`, `n - 1 - k` drops and, for `k > 0`, `(local.set $__tx.t)`, `k` drops and
  `(local.get $__tx.t)`, where `$__tx.t` is a scratch local of the component's type `t`, one per
  type and function, declared after the function's other locals.

The rewritten module is printed back to text (`render`) and read by `wat3!`'s module parser with
the instruction rewrite above. A `tuple.extract` of an operand whose result types the text does
not give, a tuple-typed local without a name, and a `tuple.make` whose operand count is not `n`
are rejected (an elaboration error). Like `wat3!`, this is an elaboration-time front end, not a
validator: the generated term contains only constructors and is checked by the kernel, and
which binary it is the module of is not checked (see `docs/projects/wasm-binaryen-tooling.md`).

A Silmaril addition.
-/

public meta section

namespace Silmaril.Wasm.Auto2.Wat

open Lean Silmaril.Wasm.Wat

/-- Rewrite Binaryen's tuple instructions in a list of instruction nodes (at every depth). -/
partial def untuple : List Node → Except String (List Node)
  | [] => pure []
  | n :: rest => do
    let rest ← untuple rest
    match n with
    | .list p (.atom _ "tuple.make" :: .atom _ k :: args) =>
      let args ← untuple args
      if k.toNat? != some args.length then
        throw s!"wat3b!: tuple.make {k} with {args.length} operands at {p}"
      pure (args ++ rest)
    | .list p (.atom _ "tuple.drop" :: .atom _ k :: args) =>
      let args ← untuple args
      match k.toNat? with
      | some c => pure (args ++ List.replicate c (Node.atom p "drop") ++ rest)
      | none => throw s!"wat3b!: tuple.drop {k} at {p}"
    | .list p (.atom _ "tuple.extract" :: _) =>
      throw s!"wat3b!: tuple.extract is not supported (at {p})"
    | .list p (.atom _ "tuple" :: _) =>
      throw s!"wat3b!: tuple-typed values are not supported (at {p})"
    | .list p cs => pure (.list p (← untuple cs) :: rest)
    | n => pure (n :: rest)

/-- The Core 3 instruction parser after `untuple`. -/
def instructionsB : Core.InstructionParser := fun scope nodes => do
  match untuple nodes with
  | .ok ns => Core.instructions scope ns
  | .error e => Macro.throwError e

/-! ## Tuple-typed locals -/

/-- The name of component `k` of tuple local `t`. -/
def compName (t : String) (k : Nat) : String := t ++ "." ++ toString k

/-- `(local.get $t.0) … (local.get $t.n-1)`. -/
def getsOf (p : Nat) (t : String) (n : Nat) : List Node :=
  (List.range n).map fun k => .list p [.atom p "local.get", .atom p (compName t k)]

/-- `(local.set $t.n-1) … (local.set $t.0)`. -/
def setsOf (p : Nat) (t : String) (n : Nat) : List Node :=
  ((List.range n).reverse).map fun k => .list p [.atom p "local.set", .atom p (compName t k)]

/-- What the lowering of a function knows about its module: the
result types of each function (by name and by index, imports first) and of each type. -/
structure Env where
  funcs : List (String × List Node) := []
  funcsByIdx : List (List Node) := []
  types : List (String × List Node) := []
  typesByIdx : List (List Node) := []

/-- The result types of a type use `(type $T)` or of explicit `(result …)` children. -/
def sigResults (env : Env) (cs : List Node) : List Node :=
  let rs := (cs.filterMap fun
    | .list _ (.atom _ "result" :: ts) => some ts
    | _ => none).flatten
  if !rs.isEmpty then rs else
  match cs.findSome? (fun | .list _ [.atom _ "type", .atom _ t] => some t | _ => none) with
  | some t =>
    match env.types.lookup t, t.toNat? with
    | some r, _ => r
    | none, some k => env.typesByIdx.getD k []
    | none, none => []
  | none => []

/-- The result types of an instruction node producing a tuple: a call (direct or indirect), a
block, a loop or an `if` (from its `(result …)` or its type). -/
def resultsOf (env : Env) : Node → Except String (List Node)
  | .list _ [.atom _ "call", .atom _ f] => fn f
  | .list _ (.atom _ "call" :: .atom _ f :: _) => fn f
  | .list _ (.atom _ "call_indirect" :: cs) => pure (sigResults env cs)
  | .list _ (.atom _ "block" :: cs) => pure (sigResults env cs)
  | .list _ (.atom _ "loop" :: cs) => pure (sigResults env cs)
  | .list _ (.atom _ "if" :: cs) => pure (sigResults env cs)
  | .list p _ => throw s!"wat3b!: the result types of a tuple.extract operand at {p}"
  | n => throw s!"wat3b!: a tuple.extract operand at {n.pos}"
where
  fn (f : String) : Except String (List Node) :=
    match env.funcs.lookup f, f.toNat? with
    | some r, _ => pure r
    | none, some k => pure (env.funcsByIdx.getD k [])
    | none, none => throw s!"wat3b!: unknown function {f}"

/-- The scratch local of `tuple.extract` for a number or vector type (one per type and
function). -/
def scratchName : Node → Option String
  | .atom _ t => some ("$__tx." ++ t)
  | _ => none

/-- Rewrite the uses of the tuple locals `tl` (name, arity) in a list of instruction nodes, at
every depth. A `tuple.extract n k e` of another operand `e` becomes `e`, `n - 1 - k` drops, and,
for `k > 0`, a `local.set` of the scratch local of the component's type, `k` drops and its
`local.get` (Binaryen's own lowering of such extracts when it writes a binary). -/
partial def lowerUses (env : Env) (tl : List (String × Nat)) :
    List Node → Except String (List Node)
  | [] => pure []
  | n :: rest => do
    match n with
    | .list p (.atom _ "tuple.extract" :: .atom _ ns :: .atom _ ks :: args) =>
      let some n' := ns.toNat? | throw s!"wat3b!: tuple.extract {ns} at {p}"
      let some k := ks.toNat? | throw s!"wat3b!: tuple.extract {ns} {ks} at {p}"
      if k ≥ n' then throw s!"wat3b!: tuple.extract {n'} {k} at {p}"
      match args with
      | [.list _ [.atom _ "local.get", .atom _ t]] =>
        match tl.lookup t with
        | some _ => pure (.list p [.atom p "local.get", .atom p (compName t k)] ::
            (← lowerUses env tl rest))
        | none => throw s!"wat3b!: tuple.extract of {t}, not a tuple local, at {p}"
      | [.list _ (.atom _ "local.tee" :: .atom _ t :: e)] =>
        match tl.lookup t with
        | some m => pure ((← lowerUses env tl e) ++ setsOf p t m ++
            [.list p [.atom p "local.get", .atom p (compName t k)]] ++ (← lowerUses env tl rest))
        | none => throw s!"wat3b!: tuple.extract of {t}, not a tuple local, at {p}"
      | [e] =>
        let ts ← resultsOf env e
        if ts.length != n' then
          throw s!"wat3b!: tuple.extract {n'} of an operand with {ts.length} results at {p}"
        let e' ← lowerUses env tl [e]
        let drops (c : Nat) : List Node := List.replicate c (.list p [.atom p "drop"])
        let rest' ← lowerUses env tl rest
        if k == 0 then pure (e' ++ drops (n' - 1 - k) ++ rest')
        else
          let some x := scratchName ts[k]!
            | throw s!"wat3b!: tuple.extract of a component of reference type at {p}"
          pure (e' ++ drops (n' - 1 - k) ++ [.list p [.atom p "local.set", .atom p x]] ++
            drops k ++ [.list p [.atom p "local.get", .atom p x]] ++ rest')
      | _ => throw s!"wat3b!: tuple.extract with {args.length} operands at {p}"
    | .list p [.atom _ "local.get", .atom _ t] =>
      match tl.lookup t with
      | some m => pure (getsOf p t m ++ (← lowerUses env tl rest))
      | none => pure (n :: (← lowerUses env tl rest))
    | .list p (.atom q "local.set" :: .atom r t :: e) =>
      match tl.lookup t with
      | some m => pure ((← lowerUses env tl e) ++ setsOf p t m ++ (← lowerUses env tl rest))
      | none => pure (.list p (.atom q "local.set" :: .atom r t :: (← lowerUses env tl e)) ::
          (← lowerUses env tl rest))
    | .list p (.atom q "local.tee" :: .atom r t :: e) =>
      match tl.lookup t with
      | some m => pure ((← lowerUses env tl e) ++ setsOf p t m ++ getsOf p t m ++
          (← lowerUses env tl rest))
      | none => pure (.list p (.atom q "local.tee" :: .atom r t :: (← lowerUses env tl e)) ::
          (← lowerUses env tl rest))
    | .atom p op =>
      -- Plain (unfolded) `local.get $t`, `local.set $t`, `local.tee $t`.
      match rest with
      | .atom _ t :: rest' =>
        match op, tl.lookup t with
        | "local.get", some m => pure (getsOf p t m ++ (← lowerUses env tl rest'))
        | "local.set", some m => pure (setsOf p t m ++ (← lowerUses env tl rest'))
        | "local.tee", some m =>
          pure (setsOf p t m ++ getsOf p t m ++ (← lowerUses env tl rest'))
        | _, _ => pure (n :: (← lowerUses env tl rest))
      | _ => pure (n :: (← lowerUses env tl rest))
    | .list p cs => pure (.list p (← lowerUses env tl cs) :: (← lowerUses env tl rest))
    | n => pure (n :: (← lowerUses env tl rest))

/-- The node contains a `tuple.extract`. -/
partial def hasExtract : Node → Bool
  | .list _ (.atom _ "tuple.extract" :: _) => true
  | .list _ cs => cs.any hasExtract
  | _ => false

/-- The scratch locals a lowered body uses (`local.set $__tx.…`), with their types, in order of
first use. -/
partial def scratchUses : List Node → List String
  | [] => []
  | .list _ [.atom _ "local.set", .atom _ x] :: rest =>
    if x.startsWith "$__tx." then x :: scratchUses rest else scratchUses rest
  | .list _ cs :: rest => scratchUses cs ++ scratchUses rest
  | _ :: rest => scratchUses rest

/-- A tuple local declaration `(local $t (tuple t₀ … tₙ₋₁))`: its name and component types. -/
def tupleLocal? : Node → Option (Nat × String × List Node)
  | .list p [.atom _ "local", .atom _ t, .list _ (.atom _ "tuple" :: ts)] => some (p, t, ts)
  | _ => none

/-- Rewrite one module field: a `func` loses its tuple-typed locals and its `tuple.extract`s
(scratch locals, one per type, are declared after the other locals). -/
def lowerFunc (env : Env) : Node → Except String Node
  | .list p (.atom q "func" :: cs) => do
    let tl := cs.filterMap fun c => (tupleLocal? c).map fun (_, t, ts) => (t, ts.length)
    if tl.isEmpty && !cs.any hasExtract then return .list p (.atom q "func" :: cs)
    for c in cs do
      if let .list r (.atom _ "local" :: .list _ (.atom _ "tuple" :: _) :: _) := c then
        throw s!"wat3b!: a tuple-typed local without a name at {r}"
    -- `head`: the name, type use, parameters, results and locals (in order); `body`: the rest.
    let mut head : List Node := []
    let mut body : List Node := []
    for c in cs do
      match tupleLocal? c with
      | some (r, t, ts) =>
        head := head ++ ((List.range ts.length).zip ts).map fun (k, ty) =>
          .list r [.atom r "local", .atom r (compName t k), ty]
      | none =>
        match c with
        | .list _ (.atom _ "local" :: _) | .list _ (.atom _ "param" :: _)
        | .list _ (.atom _ "result" :: _) | .list _ (.atom _ "type" :: _)
        | .list _ (.atom _ "export" :: _) | .list _ (.atom _ "import" :: _) =>
          head := head ++ [c]
        | .atom _ t =>
          if body.isEmpty && t.startsWith "$" then head := head ++ [c]
          else body := body ++ (← lowerUses env tl [c])
        | _ => body := body ++ (← lowerUses env tl [c])
    let xs := (scratchUses body).foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
    let scratch := xs.map fun x =>
      Node.list p [.atom p "local", .atom p x, .atom p (x.drop "$__tx.".length).toString]
    return .list p (.atom q "func" :: (head ++ scratch ++ body))
  | n => pure n

/-- The function and type signatures of a module's fields (`Env`). -/
def envOf (fields : List Node) : Env :=
  let typeOf : Node → Option (Option String × List Node)
    | .list _ (.atom _ "type" :: rest) =>
      let name := match rest with
        | .atom _ t :: _ => if t.startsWith "$" then some t else none
        | _ => none
      let body := rest.findSome? fun
        | .list _ (.atom _ "func" :: fs) => some fs
        | _ => none
      body.map fun fs =>
        (name, (fs.filterMap fun
          | .list _ (.atom _ "result" :: ts) => some ts
          | _ => none).flatten)
    | _ => none
  let tys := fields.filterMap typeOf
  let env0 : Env :=
    { types := tys.filterMap fun (n, r) => n.map (·, r), typesByIdx := tys.map (·.2) }
  let fnOf : Node → Option (Option String × List Node)
    | .list _ (.atom _ "import" :: rest) =>
      rest.findSome? fun
        | .list _ (.atom _ "func" :: fs) =>
          let name := match fs with
            | .atom _ t :: _ => if t.startsWith "$" then some t else none
            | _ => none
          some (name, sigResults env0 fs)
        | _ => none
    | .list _ (.atom _ "func" :: fs) =>
      let name := match fs with
        | .atom _ t :: _ => if t.startsWith "$" then some t else none
        | _ => none
      some (name, sigResults env0 fs)
    | _ => none
  let imps := fields.filter fun | .list _ (.atom _ "import" :: _) => true | _ => false
  let defs := fields.filter fun | .list _ (.atom _ "func" :: _) => true | _ => false
  let fns := (imps ++ defs).filterMap fnOf
  { env0 with funcs := fns.filterMap fun (n, r) => n.map (·, r), funcsByIdx := fns.map (·.2) }

/-- Hexadecimal escapes of a byte string (for string literals and quoted identifiers). -/
def escapeBytes (bs : ByteArray) : String :=
  String.join (bs.toList.map fun b =>
    let h := "0123456789abcdef".toList
    String.ofList ['\\', h[b.toNat / 16]!, h[b.toNat % 16]!])

/-- Print nodes back to WAT text. -/
partial def render : Node → String
  | .atom _ t => t
  | .string _ bs => "\"" ++ escapeBytes bs ++ "\""
  | .quotedIdentifier _ bs => "$\"" ++ escapeBytes bs ++ "\""
  | .list _ cs => "(" ++ " ".intercalate (cs.map render) ++ ")"

/-- The module text with tuple-typed locals removed (`lowerFunc` on every field). -/
def lowerText (text : String) : Except String String := do
  let nodes ← parse text
  let nodes ← match nodes with
    | [.list p (.atom q "module" :: args)] =>
      pure [Node.list p (.atom q "module" :: (← args.mapM (lowerFunc (envOf args))))]
    | ns => ns.mapM (lowerFunc (envOf ns))
  return "\n".intercalate (nodes.map render)

/-- A Core 3 module from Binaryen's WAT printing (`wat3!` after `lowerText` and `untuple`). -/
macro "wat3b! " text:str : term => do
  match lowerText text.getString with
  | .ok t => Core.moduleTerm instructionsB t
  | .error e => Macro.throwError e

end Silmaril.Wasm.Auto2.Wat
