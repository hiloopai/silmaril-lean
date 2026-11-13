module

public import Silmaril.Compiler.Core.Verified.LoopMain.Defs
public import Silmaril.Compiler.Core.Verified.CfgPrintStmt.Defs
public import Silmaril.Compiler.Core.Verified.CfgGlobals.Defs
public import Silmaril.Compiler.Core.Verified.Rmw.Defs
public import Silmaril.Compiler.Core.Verified.DoCondition.Defs
public import Silmaril.Compiler.Core.Verified.Switch.Defs
public import Silmaril.Compiler.Core.Verified.VoidCall.Defs
public import Silmaril.Compiler.Core.Verified.StateGlobals.Defs
public import Silmaril.Compiler.Core.Verified.StateExitLink.Defs

/-! # `main` as a control-flow graph of its saved labels: recogniser and code

Cerberus elaborates every C jump (the back edge of `while`, `for` and `do`, `break`,
`continue`) to `run l(x₁, …, xₙ)` of a label `save l(x₁ := x₁, …, xₙ := xₙ) in body`, whose
parameters rebind the pointers of the locals in scope. A `run` discards the continuation and
evaluates the label's body with its right continuations attached (`Dynamics.saves`), under the
procedure's base frames. So every label is a cut point with a fixed Core form, and the code
between two cut points is loop free.

`walk` translates the Core statements from one cut point on, with a stack of pending right
sides of strong sequences (the Core frames), into a `Code` tree:

* `int` statements `x = e;`, `int x = e;`, `int x;` (`StateStmt`), `x++;` and `x--;` (`Rmw`)
  become register operations;
* Cerberus's statement test (`LoopCondition`) and the test of a `do` loop (`DoCondition`) become a
  branch whose arms both continue with the same pending statements;
* a `switch` (`Switch`) becomes a chain of tests of its controlling expression against the case
  constants, each jumping to its case label, then a jump to `default` (or `break`);
* a `save` met by falling through is entered in place;
* `run l(…)` becomes a jump to the block of `l`; `return e;` returns;
* `exit(n)` of an `int` literal returns `n` (Cerberus's `exit` ends like a return from `main`), and
  `abort()` stores the abort control word and traps.

The code of `main` (`compile`) is the tree of the block after the creations of its `int`
locals, then one tree per label, from the label's body with its right continuations. Each
tree node is one Lir block (`Code.emit`); reads are of the current registers. The defined locals
at a label are those defined wherever `main`'s tree enters its `save` or jumps to it (`walk`'s
`seen`; the globals at a label it never meets), and every jump checks that they are defined. Jumps go only to the labels of a stable set whose trees
succeed (`stable`): labels in dead code after a `break` or `return` (a `continue` label never
entered) are left out. The work of `walk` is bounded by a fuel threaded through the branches.
Nothing of the program is evaluated by the compiler.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.Cfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE PE)
open Silmaril.Machine
open StateExpr (Key Term)
open StateStmt (assignStmt initStmt uninitStmt isLocal)
open LoopMain (covered regOf)

/-! ## Labels -/

mutual
/-- The labels of an expression with their bodies, each with the right sides of the sequences
around it attached: a copy of `Dynamics.saves` (`labelTable_eq`). -/
def labelTable : EE → List (Sym × (List Sym × EE))
  | .mk ann (.sseq p a b) =>
      (labelTable a).map (fun z => (z.1, z.2.1, .mk ann (.sseq p z.2.2 b))) ++ labelTable b
  | .mk ann (.wseq p a b) =>
      (labelTable a).map (fun z => (z.1, z.2.1, .mk ann (.wseq p z.2.2 b))) ++ labelTable b
  | .mk _ (.save (s, _) ps body) =>
      (s, ps.map Prod.fst, body) :: labelTable body
  | .mk _ (.let_ _ _ body) => labelTable body
  | .mk _ (.if_ _ a b) => labelTable a ++ labelTable b
  | .mk _ (.case_ _ bs) => labelTableCases bs
  | .mk _ (.unseq es) => labelTableList es
  | _ => []

def labelTableList : List EE → List (Sym × (List Sym × EE))
  | [] => []
  | e :: es => labelTable e ++ labelTableList es

def labelTableCases : List (Pattern Sym × EE) → List (Sym × (List Sym × EE))
  | [] => []
  | (_, e) :: es => labelTable e ++ labelTableCases es
end

/-- The parameters and body of the label with the key of `l`. -/
def find (tbl : List (Sym × (List Sym × EE))) (l : Sym) : Option (List Sym × EE) :=
  (tbl.find? fun z => z.1.key == l.key).map (·.2)

/-- The parameters of a `save` rebind locals to themselves: `x := x`. -/
def selfParams (xs : List Sym) :
    List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE)) → Bool
  | [] => true
  | (x, (_, .mk _ () (.sym x'))) :: ps => x'.key == x.key && isLocal xs x && selfParams xs ps
  | _ => false

/-- The arguments of a `run`, when they are symbols. -/
def symArgs : List PE → Option (List Sym)
  | [] => some []
  | .mk _ () (.sym y) :: ps => (symArgs ps).map (y :: ·)
  | _ => none

/-! ## Code -/

/-- A register operation: assign a local, or forget its value (`int x;`). -/
inductive Atom where
  | set (q : Key) (t : Term)
  | clear (q : Key)

/-- The loop-free code from a cut point: each node is one Lir block. -/
inductive Code where
  | atom (a : Atom) (next : Code)
  /-- One open signed-int conversion; the operand is computed from the current slots. -/
  | print (pre suf : List Char) (t : Term) (next : Code)
  /-- A statement test: Cerberus's `z ≠ 1` conversion of `t` (`LoopBlocks.coreTest`), or, for
  the condition of a `do` loop (`direct`), `t ≠ 0` itself. -/
  | test (direct : Bool) (t : Term) (yes no : Code)
  | goto (l : Key)
  | ret (t : Term)
  /-- `abort()`: the control word records the abort, then the run traps. -/
  | abort

/-- The number of blocks of a tree. -/
def Code.size : Code → Nat
  | .atom _ c => c.size + 1
  | .print _ _ _ c => c.size + 1
  | .test _ _ y n => y.size + n.size + 1
  | .goto _ => 1
  | .ret _ => 1
  | .abort => 1

/-- The defined locals of a label met by a walk: those defined wherever it was met (entered or
jumped to). -/
def defsAt (seen : List (Key × List Key)) (l : Key) : List Key :=
  match (seen.filter fun z => z.1 == l).map (·.2) with
  | [] => []
  | d :: ds => ds.foldl (fun acc d' => acc.filter (· ∈ d')) d

/-- The defined locals of the labels: those of `defsAt` at the labels the walk met, the
globals `g` at the others (each jump checks them). -/
def labelDefs (seen : List (Key × List Key)) (g : List Key) (l : Key) : List Key :=
  if seen.any (·.1 == l) then defsAt seen l else g

/-- The dispatch of a `switch` on `t`: `t = k` jumps to the label of `k`, for each case in
order, then the jump to `d`. -/
def dispatch (t : Term) : List (Int × Switch.Jump) → Switch.Jump → Code
  | [], d => .goto d.1.key
  | (k, l, _) :: cs, d => .test true (.cmp .eq 1 0 t (.lit k)) (.goto l.key) (dispatch t cs d)

/-- `int` statements (`x = e;`, `int x = e;`, `int x;`, `x++;`, `x--;`): the register operation
and the defined locals after it. -/
def atom (file : File Codec.wireModel Unit Unit) (xs : List Sym) (dk : List Key) (e : EE) :
    Option (Atom × List Key) :=
  match assignStmt file e with
  | some (x, t) => if isLocal xs x = true ∧ covered dk t = true then some (.set x.key t, x.key :: dk) else none
  | none => match initStmt file e with
    | some (x, t) => if isLocal xs x = true ∧ covered dk t = true then some (.set x.key t, x.key :: dk) else none
    | none => match uninitStmt e with
      | some x => if isLocal xs x = true then some (.clear x.key, dk.filter (· != x.key)) else none
      | none => match Rmw.rmwStmt file e with
        | some (x, op) =>
          if isLocal xs x = true ∧ covered dk (.bin op (.var x.key) (.lit 1)) = true then
            some (.set x.key (.bin op (.var x.key) (.lit 1)), x.key :: dk)
          else none
        | none => none

/-- The jump `run l(y₁, …, yₙ)` to a label of `tbl` with a tree (its key in `T`) other than `ret`,
whose parameters are the locals `yᵢ`, with its defined locals `D l` defined. -/
def jump (ret : Sym) (xs : List Sym) (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key)
    (T : List Key) (dk : List Key) (l : Sym) (args : List PE) : Bool :=
  match symArgs args, find tbl l with
  | some ys, some (qs, _) =>
      decide (l.key ≠ ret.key ∧ l.key ∈ T ∧ qs.map (·.key) = ys.map (·.key) ∧
        ys.all (isLocal xs) = true ∧ ∀ q ∈ D l.key, q ∈ dk)
  | _, _ => false

/-- Returns share the State machine's value interface; only slots named by cleanup are killed. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) (e : EE) :
    Option Term :=
  let killed := CfgGlobals.returnKeys e
  StateGlobals.retStmt file ret xs (xs.filter fun x => killed.contains x.key) e

/-- A print-enabled walk takes the format literals explicitly. The ordinary CFG fragment
uses `none` until its startup and resource certificate establish the print preconditions. -/
def printStmt (file : File Codec.wireModel Unit Unit) (lits : Option (List (Sym × List Int))) :
    EE → Option (List Char × List Char × Term)
  | .mk _ (.bound e) => match lits with
    | some ls => PrintfIntStmt.printfTerm file ls ∅ e
    | none => none
  | _ => none

theorem printStmt_some {file : File Codec.wireModel Unit Unit} {lits : Option (List (Sym × List Int))}
    {e : EE} {r : List Char × List Char × Term} (h : printStmt file lits e = some r) :
    ∃ ann e0 ls, e = .mk ann (.bound e0) ∧ lits = some ls ∧
      PrintfIntStmt.printfTerm file ls ∅ e0 = some r := by
  unfold printStmt at h
  split at h
  · rename_i ann e0
    split at h
    · rename_i ls
      exact ⟨ann, e0, ls, rfl, rfl, h⟩
    · cases h
  · cases h

theorem printStmt_disabled (file : File Codec.wireModel Unit Unit) (e : EE) :
    printStmt file none e = none := by
  cases e with
  | mk ann node => cases node <;> rfl

/-- With literals, the temporaries `ys` a test binds differ from every literal symbol, so the
literals' bindings survive the test. -/
def litFresh (lits : Option (List (Sym × List Int))) (ys : List Sym) : Bool :=
  match lits with
  | none => true
  | some ls => ys.all fun y => ls.all fun z => z.1.key != y.key

/-- The code from `e` with the pending statements `P` and the defined locals `dk`, the remaining
fuel and the labels met (with their defined locals). -/
def walk (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (lits : Option (List (Sym × List Int))) :
    (fuel : Nat) → List Key → EE → List EE → List (Key × List Key) →
      Option (Code × Nat × List (Key × List Key))
  | 0, _, _, _, _ => none
  | fuel + 1, dk, e, P, seen =>
    if AbortCall.abortStmt file e = true then some (.abort, fuel, seen) else
    match ExitCall.recognizeBody file e with
    | some v => if -2147483648 ≤ v ∧ v ≤ 2147483647 then some (.ret (.lit v), fuel, seen) else none
    | none =>
    match retStmt file ret xs e with
    | some t => if covered dk t = true then some (.ret t, fuel, seen) else none
    | none => match printStmt file lits e with
    | some (pre, suf, t) =>
      if covered dk t = true ∧ xs.length < 10 then match P with
        | b :: P' => (walk file ret xs tbl D T lits fuel dk b P' seen).map
            fun (c, r) => (.print pre suf t c, r)
        | [] => none
      else none
    | none => match atom file xs dk e with
    | some (a, dk') => match P with
      | b :: P' => (walk file ret xs tbl D T lits fuel dk' b P' seen).map fun (c, r) => (.atom a c, r)
      | [] => none
    | none => if VoidCall.recognize file e then
      match P with
      | b :: P' => walk file ret xs tbl D T lits fuel dk b P' seen
      | [] => none
    else match LoopCondition.recognize file xs e with
    | some (t, yes, no) =>
      if covered dk t = true ∧ litFresh lits (LoopCondition.binders e) = true then
        match walk file ret xs tbl D T lits fuel dk yes P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret xs tbl D T lits f dk no P s).map fun (cn, r) => (.test false t cy cn, r)
          else none
        | none => none
      else none
    | none => match DoCondition.recognize file xs e with
    | some (t, yes, no) =>
      if covered dk t = true ∧ litFresh lits (DoCondition.binders e) = true then
        match walk file ret xs tbl D T lits fuel dk yes P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret xs tbl D T lits f dk no P s).map fun (cn, r) => (.test true t cy cn, r)
          else none
        | none => none
      else none
    | none => match Switch.recognize file xs e with
    | some (t, cs, d) =>
      if covered dk t = true ∧ litFresh lits (Switch.binders e) = true ∧
          (d :: cs.map (·.2)).all (fun j => jump ret xs tbl D T dk j.1 j.2) = true then
        some (dispatch t cs d, fuel, seen ++ (d :: cs.map (·.2)).map fun j => (j.1.key, dk))
      else none
    | none => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => walk file ret xs tbl D T lits fuel dk a (b :: P) seen
    | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
      | b :: P' => walk file ret xs tbl D T lits fuel dk b P' seen
      | [] => none
    | .mk _ (.save (l, _) ps body) =>
      if selfParams xs ps = true then walk file ret xs tbl D T lits fuel dk body P (seen ++ [(l.key, dk)])
      else none
    | .mk _ (.run () l args) =>
      if jump ret xs tbl D T dk l args = true then some (.goto l.key, fuel, seen ++ [(l.key, dk)])
      else none
    | _ => none
termination_by fuel _ _ _ _ => fuel
decreasing_by all_goals omega

/-- An enabled walk emits the print node and continues with the same defined slots.
The surrounding recognizers retain their existing priority. -/
theorem walk_print {file : File Codec.wireModel Unit Unit} {ret : Sym} {xs : List Sym}
    {tbl : List (Sym × (List Sym × EE))} {D : Key → List Key} {T : List Key}
    {lits : Option (List (Sym × List Int))} {dk : List Key} {e b : EE} {P : List EE}
    {seen : List (Key × List Key)} {pre suf : List Char} {t : Term} {c : Code}
    {fuel remaining : Nat} {seen' : List (Key × List Key)}
    (habort : AbortCall.abortStmt file e = false) (hexit : ExitCall.recognizeBody file e = none)
    (hret : retStmt file ret xs e = none) (hp : printStmt file lits e = some (pre, suf, t))
    (hc : covered dk t = true) (hd : xs.length < 10)
    (next : walk file ret xs tbl D T lits fuel dk b P seen = some (c, remaining, seen')) :
    walk file ret xs tbl D T lits (fuel + 1) dk e (b :: P) seen =
      some (.print pre suf t c, remaining, seen') := by
  unfold walk
  simp only [habort, Bool.false_eq_true, ↓reduceIte, hexit, hret, hp, hc,
    hd, and_self, next, Option.map_some]

/-- The work bound of one tree. -/
def fuel : Nat := 65536

/-- The blocks of a tree whose root is block `i`, jumps to label `l` going to `idx l`. -/
def Code.emit (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) : Code → Nat → List (Lir.Block Mir.Reg)
  | .atom (.set q t) c, i => ⟨(StateExprLir.assignOps regs d q t).map .op, .jump (i + 1)⟩ ::
      c.emit regs d idx (i + 1)
  | .atom (.clear _) c, i => ⟨[], .jump (i + 1)⟩ :: c.emit regs d idx (i + 1)
  | .print pre suf t c, i =>
    ⟨(CfgPrintStmt.ops regs d pre suf t).map .op, .jump (i + 1)⟩ ::
      c.emit regs d idx (i + 1)
  | .test direct t y n, i =>
    LoopBlocks.testBlock regs d (if direct then t else LoopBlocks.coreTest t) (i + 1) (i + 1 + y.size) ::
      (y.emit regs d idx (i + 1) ++ n.emit regs d idx (i + 1 + y.size))
  | .goto l, _ => [⟨[], .jump (idx l)⟩]
  | .ret t, _ => [⟨(StateExprLir.ops regs d t).map .op, .ret [.reg d]⟩]
  | .abort, _ => [⟨StateExitLink.abortOps.map .op, .trap⟩]

/-- The first block of the tree of label `l`, the trees placed one after another from `i`. -/
def pos : Nat → List (Key × Code) → Key → Nat
  | _, [], _ => 0
  | i, (l', c) :: cs, l => if l' = l then i else pos (i + c.size) cs l

/-- The labels met by the trees of the labels met so far: each round walks the tree of every
label met (with its defined locals) and adds the labels it meets that were not met yet, with
the locals defined there. A heuristic: every jump checks the defined locals of its label. -/
def grow (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (T : List Key) (g : List Key)
    (lits : Option (List (Sym × List Int))) :
    Nat → List (Key × List Key) → List (Key × List Key)
  | 0, seen => seen
  | n + 1, seen =>
    let D := labelDefs seen g
    let met := fun l => seen.any (·.1 == l)
    let new := tbl.flatMap fun z =>
      if met z.1.key then
        match walk file ret xs tbl D T lits fuel (D z.1.key) z.2.2 [] [] with
        | some (_, _, s) => s.filter fun q => !met q.1
        | none => []
      else []
    if new.isEmpty then seen else grow file ret xs tbl T g lits n (seen ++ new)

/-- The blocks of the labels' trees, placed from `i`. -/
def emitAll (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) : Nat → List (Key × Code) →
    List (Lir.Block Mir.Reg)
  | _, [] => []
  | i, (_, c) :: cs => c.emit regs d idx i ++ emitAll regs d idx (i + c.size) cs

/-- A recognised `main`: globals and locals, the statement trees and label definitions. -/
structure Plan where
  xs : List Sym
  entry : Code
  codes : List (Key × Code)
  D : Key → List Key
  globals : List (Sym × Int)

/-- The first block of the label `l`. -/
def Plan.idx (P : Plan) (l : Key) : Nat := pos (P.entry.size + 1) P.codes l

/-- Block 0 initializes globals, then `main`'s tree and the labels' trees. -/
def Plan.blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  let regs := regOf (P.xs.map (·.key))
  ⟨(CfgGlobals.seedOps regs P.globals).map .op, .jump 1⟩ ::
    (P.entry.emit regs P.xs.length P.idx 1 ++ emitAll regs P.xs.length P.idx (P.entry.size + 1) P.codes)

/-- The trees of the labels of `zs` with a key in `T`, each from its body with its defined locals,
jumps going to labels of `T`; a label whose tree fails is left out. -/
def labelCodes (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key)
    (lits : Option (List (Sym × List Int))) :
    List (Sym × (List Sym × EE)) → List (Key × Code)
  | [] => []
  | z :: zs =>
    if z.1.key ∈ T then
      match walk file ret xs tbl D T lits fuel (D z.1.key) z.2.2 [] [] with
      | some (c, _) => (z.1.key, c) :: labelCodes file ret xs tbl D T lits zs
      | none => labelCodes file ret xs tbl D T lits zs
    else labelCodes file ret xs tbl D T lits zs

/-- The labels whose trees succeed with jumps to these labels only: dropping the failing labels
until none fails (a label whose code jumps to a dropped label is dropped in the next round). -/
def stable (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (lits : Option (List (Sym × List Int))) :
    Nat → List Key → Option (List Key × List (Key × Code))
  | 0, _ => none
  | n + 1, T =>
    let cs := labelCodes file ret xs tbl D T lits tbl
    if cs.map (·.1) = T then some (T, cs) else stable file ret xs tbl D lits n (cs.map (·.1))

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (body : EE) (gs : List (Sym × Int) := [])
    (lits : Option (List (Sym × List Int)) := none) : Option Plan :=
  match body with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
    if r'.key = r.key ∧ (LoopMain.labelKeys body).Nodup then
      match LoopMain.creates (gs.map (·.1)) a with
      | some (xs, e) =>
        if (xs.map (·.key)).Nodup then
          let tbl := labelTable body
          let T₀ := (tbl.filter fun z => z.1.key != ret.key).map (·.1.key)
          match walk file ret xs tbl (fun _ => []) T₀ lits fuel (gs.map (·.1.key)) e [] [] with
          | some (_, _, seen) =>
            let D := labelDefs (grow file ret xs tbl T₀ (gs.map (·.1.key)) lits tbl.length seen)
              (gs.map (·.1.key))
            match stable file ret xs tbl D lits (tbl.length + 1) T₀ with
            | some (T, codes) => match walk file ret xs tbl D T lits fuel (gs.map (·.1.key)) e [] [] with
              | some (entry, _) => some ⟨xs, entry, codes, D, gs⟩
              | none => none
            | none => none
          | none => none
        else none
      | none => none
    else none
  | _ => none

/-- Literal-initialized `int` globals and a block of locals with a control-flow graph of labels. -/
def recognize (doc : Codec.Document) : Option Plan := do
  let ds := Globals.definitions doc.file
  let gs ← Globals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ ds.length < 1024 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body gs none
  else none

end Silmaril.Compile.Core.Verified.Cfg
