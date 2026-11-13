module

public import Silmaril.Compiler.Core.Verified.Cfg.Defs
public import Silmaril.Compiler.Core.Verified.ArgvTest.Defs
/-! # `main(argc, argv)` as a control-flow graph: recogniser and code

The machine of `Cfg` for `main(argc, argv)`, with tests on characters of the arguments. The
slots are `argc` (the parameter object, defined at entry with the argument count) and the `int`
locals of `main`'s block; `argv` stays the parameter object, read through `ArgvTest`. Its nodes are
`int` statements, Cerberus's statement test (`LoopCondition`), the test of a character
`argv[i][x]` (`ArgvTest`, `i ≤ 1` so that `argv[i]` is a string or, for `i = argc = 1`, the null
slot), jumps between labels and `return e;`.

A character `argv[i][x]` is read only within its string (its terminator included): past it
Cerberus's load is not undefined behaviour but an unsupported access. The recogniser makes this an
invariant of the slots `bnd` that index the arguments (each with its argument `i`, `bounds`):
such a slot is written only by `x = 0;` (or `int x = 0;`), and by `x++;` on a path where the
test `argv[i][x]` (in the form `while (argv[i][x])`, `zeroTest`) found a character that is not
the terminator (`sb`, the slots known to be below their string's length on the current path). So
`0 ≤ x ≤ strlen(argv[i])` holds wherever `x` is defined.

The code (`Plan.blocks`) is `Cfg`'s, with the slot registers `0 … n - 1`, the base of the argument
block kept in register `n` (`R`) and temporaries from `n + 1`; block 0 copies `argc` and the base
from the registers `__ccomp_start` receives them in. Nothing of the program is evaluated by the
compiler.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgArgv

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE PE)
open Silmaril.Machine
open StateExpr (Key Term)
open StateStmt (assignStmt initStmt uninitStmt isLocal isFresh)
open LoopMain (covered regOf)
open Cfg (labelTable find selfParams symArgs Atom labelDefs pos jump)

/-! ## Code -/

/-- The loop-free code from a cut point: each node is one Lir block. -/
inductive Code where
  | atom (a : Atom) (next : Code)
  /-- Cerberus's statement test of `t`. -/
  | test (t : Term) (yes no : Code)
  /-- The statement test of `t` over the character `argv[i][q]`. -/
  | atest (i : Nat) (q : Key) (t : IntExpr.Term) (yes no : Code)
  | goto (l : Key)
  | ret (t : Term)

/-- The number of blocks of a tree. -/
def Code.size : Code → Nat
  | .atom _ c => c.size + 1
  | .test _ y n => y.size + n.size + 1
  | .atest _ _ _ y n => y.size + n.size + 1
  | .goto _ => 1
  | .ret _ => 1

/-- The slots that index the arguments, each with its argument. -/
abbrev Bnd := List (Key × Nat)

def inBnd (bnd : Bnd) (q : Key) : Bool := bnd.any (·.1 == q)

/-- `0`. -/
def isZero : Term → Bool
  | .lit 0 => true
  | _ => false

/-- `+ 1`. -/
def isAdd : IntOp → Bool
  | .add => true
  | _ => false

/-- The condition of `while (c)` for a character `c`: `c == 0`, whose statement test enters the
body exactly when `c` is not `0`. -/
def zeroTest : IntExpr.Term → Bool
  | .cmp .eq 1 0 .var (.lit 0) => true
  | _ => false

/-- An `int` statement with the bound discipline: the register operation, the defined locals and
the slots below their string's length after it. -/
def atom (file : File Codec.wireModel Unit Unit) (xs : List Sym) (bnd : Bnd) (sb dk : List Key)
    (e : EE) : Option (Atom × List Key × List Key) :=
  match assignStmt file e with
  | some (x, t) =>
    if isLocal xs x = true ∧ covered dk t = true ∧ (inBnd bnd x.key = false ∨ isZero t = true) then
      some (.set x.key t, x.key :: dk, sb.filter (· != x.key))
    else none
  | none => match initStmt file e with
    | some (x, t) =>
      if isLocal xs x = true ∧ covered dk t = true ∧ (inBnd bnd x.key = false ∨ isZero t = true) then
        some (.set x.key t, x.key :: dk, sb.filter (· != x.key))
      else none
    | none => match uninitStmt e with
      | some x => if isLocal xs x = true then
          some (.clear x.key, dk.filter (· != x.key), sb.filter (· != x.key)) else none
      | none => match Rmw.rmwStmt file e with
        | some (x, op) =>
          if isLocal xs x = true ∧ covered dk (.bin op (.var x.key) (.lit 1)) = true ∧
              (inBnd bnd x.key = false ∨ (isAdd op = true ∧ x.key ∈ sb)) then
            some (.set x.key (.bin op (.var x.key) (.lit 1)), x.key :: dk, sb.filter (· != x.key))
          else none
        | none => none

/-- The two binders of a statement test. -/
def ifBinders : EE → Option (Sym × Sym)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) _ (.mk _ (.sseq (.mk _ (.base (some b, _))) _ _))) =>
    some (c, b)
  | _ => none

/-- The binders of a statement test are not `argv`. -/
def bindersOk (argv : Sym) (e : EE) : Bool :=
  match ifBinders e with
  | some (c, b) => c.key != argv.key && b.key != argv.key
  | none => false

/-- The code from `e` with the pending statements `P`, the defined locals `dk`, the slots `sb`
below their string's length, the remaining fuel and the labels met. -/
def walk (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    (fuel : Nat) → List Key → List Key → EE → List EE → List (Key × List Key) →
      Option (Code × Nat × List (Key × List Key))
  | 0, _, _, _, _, _ => none
  | fuel + 1, dk, sb, e, P, seen =>
    match Cfg.retStmt file ret xs e with
    | some t => if covered dk t = true then some (.ret t, fuel, seen) else none
    | none => match atom file xs bnd sb dk e with
    | some (a, dk', sb') => match P with
      | b :: P' => (walk file ret argv xs bnd tbl D T fuel dk' sb' b P' seen).map fun (c, r) => (.atom a c, r)
      | [] => none
    | none => match LoopCondition.recognize file xs e with
    | some (t, yes, no) =>
      if covered dk t = true ∧ bindersOk argv e = true then
        match walk file ret argv xs bnd tbl D T fuel dk sb yes P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret argv xs bnd tbl D T f dk sb no P s).map fun (cn, r) => (.test t cy cn, r)
          else none
        | none => none
      else none
    | none => match ArgvTest.recognize file xs argv e with
    | some (i, x, t, yes, no) =>
      if i ≤ 1 ∧ isLocal xs x = true ∧ x.key ∈ dk ∧ (x.key, i) ∈ bnd then
        match walk file ret argv xs bnd tbl D T fuel dk (if zeroTest t then x.key :: sb else sb) yes P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret argv xs bnd tbl D T f dk sb no P s).map fun (cn, r) => (.atest i x.key t cy cn, r)
          else none
        | none => none
      else none
    | none => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => walk file ret argv xs bnd tbl D T fuel dk sb a (b :: P) seen
    | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
      | b :: P' => walk file ret argv xs bnd tbl D T fuel dk sb b P' seen
      | [] => none
    | .mk _ (.save (l, _) ps body) =>
      if selfParams xs ps = true then walk file ret argv xs bnd tbl D T fuel dk sb body P (seen ++ [(l.key, dk)])
      else none
    | .mk _ (.run () l args) =>
      if jump ret xs tbl D T dk l args = true then some (.goto l.key, fuel, seen ++ [(l.key, dk)])
      else none
    | _ => none
termination_by fuel _ _ _ _ _ => fuel
decreasing_by all_goals omega

/-- The blocks of a tree whose root is block `i`: slot registers `regs`, the argument block's base
in `R`, temporaries from `d`. -/
def Code.emit (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (idx : Key → Nat) :
    Code → Nat → List (Lir.Block Mir.Reg)
  | .atom (.set q t) c, i => ⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩ ::
      c.emit regs d R argv idx (i + 1)
  | .atom (.clear _) c, i => ⟨[], .jump (i + 1)⟩ :: c.emit regs d R argv idx (i + 1)
  | .test t y n, i =>
    LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) (i + 1) (i + 1 + y.size) ::
      (y.emit regs d R argv idx (i + 1) ++ n.emit regs d R argv idx (i + 1 + y.size))
  | .atest a q t y n, i =>
    ArgvTest.block regs d R argv a q t (i + 1) (i + 1 + y.size) ::
      (y.emit regs d R argv idx (i + 1) ++ n.emit regs d R argv idx (i + 1 + y.size))
  | .goto l, _ => [⟨[], .jump (idx l)⟩]
  | .ret t, _ => [⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩]

/-- The first block of the tree of label `l`, the trees placed one after another from `i`. -/
def posA : Nat → List (Key × Code) → Key → Nat
  | _, [], _ => 0
  | i, (l', c) :: cs, l => if l' = l then i else posA (i + c.size) cs l

/-- The labels met by the trees of the labels met so far (`Cfg.grow`). -/
def grow (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (T : List Key) (g : List Key) :
    Nat → List (Key × List Key) → List (Key × List Key)
  | 0, seen => seen
  | n + 1, seen =>
    let D := labelDefs seen g
    let met := fun l => seen.any (·.1 == l)
    let new := tbl.flatMap fun z =>
      if met z.1.key then
        match walk file ret argv xs bnd tbl D T Cfg.fuel (D z.1.key) [] z.2.2 [] [] with
        | some (_, _, s) => s.filter fun q => !met q.1
        | none => []
      else []
    if new.isEmpty then seen else grow file ret argv xs bnd tbl T g n (seen ++ new)

/-- The blocks of the labels' trees, placed from `i`. -/
def emitAll (regs : Key → Mir.Reg) (d R : Nat) (argv : Key) (idx : Key → Nat) :
    Nat → List (Key × Code) → List (Lir.Block Mir.Reg)
  | _, [] => []
  | i, (_, c) :: cs => c.emit regs d R argv idx i ++ emitAll regs d R argv idx (i + c.size) cs

/-- A recognised `main(argc, argv)`. -/
structure Plan where
  argc : Sym
  argv : Sym
  xs : List Sym
  entry : Code
  codes : List (Key × Code)
  D : Key → List Key
  bnd : Bnd

/-- The first block of the label `l`. -/
def Plan.idx (P : Plan) (l : Key) : Nat := posA (P.entry.size + 1) P.codes l

/-- Block 0 copies `argc` (register 1) to its slot register and the base of the argument block
(register 2) to `R`, then `main`'s tree and the labels' trees. -/
def Plan.blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  let regs := regOf (P.xs.map (·.key))
  let R := P.xs.length
  let d := P.xs.length + 1
  ⟨([.move (d + 3) 1, .move (d + 4) 2, .move (regs P.argc.key) (d + 3), .move R (d + 4)] :
      List (Lir.Op Mir.Reg)).map .op, .jump 1⟩ ::
    (P.entry.emit regs d R P.argv.key P.idx 1 ++
      emitAll regs d R P.argv.key P.idx (P.entry.size + 1) P.codes)

/-- The trees of the labels of `zs` with a key in `T` (`Cfg.labelCodes`). -/
def labelCodes (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    List (Sym × (List Sym × EE)) → List (Key × Code)
  | [] => []
  | z :: zs =>
    if z.1.key ∈ T then
      match walk file ret argv xs bnd tbl D T Cfg.fuel (D z.1.key) [] z.2.2 [] [] with
      | some (c, _) => (z.1.key, c) :: labelCodes file ret argv xs bnd tbl D T zs
      | none => labelCodes file ret argv xs bnd tbl D T zs
    else labelCodes file ret argv xs bnd tbl D T zs

/-- The labels whose trees succeed with jumps to these labels only (`Cfg.stable`). -/
def stable (file : File Codec.wireModel Unit Unit) (ret argv : Sym) (xs : List Sym) (bnd : Bnd)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) :
    Nat → List Key → Option (List Key × List (Key × Code))
  | 0, _ => none
  | n + 1, T =>
    let cs := labelCodes file ret argv xs bnd tbl D T tbl
    if cs.map (·.1) = T then some (T, cs) else stable file ret argv xs bnd tbl D n (cs.map (·.1))

/-! ## The slots that index the arguments -/

mutual
/-- The characters `argv[i][x]` of an expression: `x`'s key with `i`. -/
def charVars (argv : Sym) : EE → Bnd
  | e => (match ArgvVar.charVarOf argv e with
      | some (i, x) => [(x.key, i)]
      | none => []) ++ charVarsIn argv e

def charVarsIn (argv : Sym) : EE → Bnd
  | .mk _ (.sseq _ a b) => charVars argv a ++ charVars argv b
  | .mk _ (.wseq _ a b) => charVars argv a ++ charVars argv b
  | .mk _ (.save _ _ body) => charVars argv body
  | .mk _ (.let_ _ _ body) => charVars argv body
  | .mk _ (.if_ _ a b) => charVars argv a ++ charVars argv b
  | .mk _ (.case_ _ bs) => charVarsCases argv bs
  | .mk _ (.unseq es) => charVarsList argv es
  | .mk _ (.bound e) => charVars argv e
  | _ => []

def charVarsList (argv : Sym) : List EE → Bnd
  | [] => []
  | e :: es => charVars argv e ++ charVarsList argv es

def charVarsCases (argv : Sym) : List (Pattern Sym × EE) → Bnd
  | [] => []
  | (_, e) :: es => charVars argv e ++ charVarsCases argv es
end

/-! ## The recogniser -/

/-- The body of `main(argc, argv)`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (argc argv : Sym) (body : EE) : Option Plan :=
  match body with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
    if r'.key = r.key ∧ (LoopMain.labelKeys body).Nodup ∧ argc.key ≠ argv.key then
      match LoopMain.creates [argc] a with
      | some (xs, e) =>
        let bnd := (charVars argv body).eraseDups
        if (xs.map (·.key)).Nodup ∧ isFresh xs argv = true ∧ xs.length < 1024 ∧
            (bnd.map (·.1)).Nodup ∧ inBnd bnd argc.key = false then
          let tbl := labelTable body
          let T₀ := (tbl.filter fun z => z.1.key != ret.key).map (·.1.key)
          match walk file ret argv xs bnd tbl (fun _ => []) T₀ Cfg.fuel [argc.key] [] e [] [] with
          | some (_, _, seen) =>
            let D := labelDefs (grow file ret argv xs bnd tbl T₀ [argc.key] tbl.length seen) [argc.key]
            match stable file ret argv xs bnd tbl D (tbl.length + 1) T₀ with
            | some (T, codes) => match walk file ret argv xs bnd tbl D T Cfg.fuel [argc.key] [] e [] [] with
              | some (entry, _) => some ⟨argc, argv, xs, entry, codes, D, bnd⟩
              | none => none
            | none => none
          | none => none
        else none
      | none => none
    else none
  | _ => none

/-- `main(argc, argv)` of a file without global definitions. -/
def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    if doc.file.callingConvention = .normal then do
      let s ← doc.file.main
      let .procedure _ _ _ [(argc, _), (argv, _)] body ← doc.file.funs.lookup s | none
      recognizeBody doc.file argc argv body
    else none

end Silmaril.Compile.Core.Verified.CfgArgv
