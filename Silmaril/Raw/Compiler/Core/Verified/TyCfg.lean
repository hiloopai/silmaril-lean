module

public import Silmaril.Compiler.Core.Verified.Cfg.Defs
public import Silmaril.Compiler.Core.Verified.TyLoopCondition.Defs
public import Silmaril.Compiler.Core.Verified.TyGlobals.Defs
public import Silmaril.Compiler.Core.Verified.TyDoCondition.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # `main` as a control-flow graph over typed integer slots: recogniser and code

`Cfg` with the slots of `TyRun`: globals and locals of every supported integer type
(`TyMem`), statements and tests over typed terms (`TyExpr`). The labels, their table, the jumps
and the placement of the trees are `Cfg`'s; only the nodes change:

* `T x = e;`, `x = e;` (`TyStmt.initStmt`, `TyStmt.assignStmt`) store `e` converted to the type
  of `x` (`TyStmt.convT`): the Lir code computes the converted value in the register of `x`
  (`TyInput.assign`); `T x;` forgets the value of `x`;
* the statement test of `while`/`for`/`if` (`TyRun.ifParts`) and the test of a `do` loop
  (`TyDoCondition`) branch on a comparison computed from the current registers
  (`TyLoopCondition.testBlock`);
* `return e;` (`TyRun.retStmt`), `exit(n)`, `abort()`, effect-free void calls, `save` and `run`
  as in `Cfg`.

Reads are of the current registers (`TyInput.ops`). Nothing of the program is evaluated by the
compiler.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyCfg

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE PE)
open Silmaril.Machine
open TyExpr (Key Term)
open TyStmt (Vars isLocal isFresh typedIn)
open Cfg (find symArgs labelDefs)
open LoopMain (regOf)

/-- `x` is a slot of `xs` (any type). -/
def isSlot (xs : Vars) (x : Sym) : Bool := xs.any fun y => y.1.key == x.key

/-- The parameters of a `save` rebind slots to themselves: `x := x`. -/
def selfParams (xs : Vars) :
    List (Sym × ((BaseType × Option (Ctype × PassBy)) × PE)) → Bool
  | [] => true
  | (x, (_, .mk _ () (.sym x'))) :: ps => x'.key == x.key && isSlot xs x && selfParams xs ps
  | _ => false

/-- The keys a term reads are defined. -/
def covered (dk : List Key) (t : Term) : Bool := t.vars.all fun q => dk.contains q.1

/-- A term the Lir code computes: it reads slots at their types, with the recogniser's guards. -/
def usable (xs : Vars) (dk : List Key) (t : Term) : Bool :=
  covered dk t && typedIn xs t && TyState.Term.wf t

/-! ## Code -/

/-- A register operation: store a converted value into a slot, or forget its value (`T x;`). -/
inductive Atom where
  | set (q : Key) (ity : IntegerType) (t : Term)
  | clear (q : Key)

/-- The loop-free code from a cut point: each node is one Lir block. -/
inductive Code where
  | atom (a : Atom) (next : Code)
  /-- A test of a comparison `t`: the statement test (`yes` when `t ≠ 1`), or, for the condition
  of a `do` loop (`direct`), `yes` when `t ≠ 0`. -/
  | test (direct : Bool) (t : Term) (yes no : Code)
  | goto (l : Key)
  | ret (t : Term)
  /-- `abort()`: the control word records the abort, then the run traps. -/
  | abort

/-- The number of blocks of a tree. -/
def Code.size : Code → Nat
  | .atom _ c => c.size + 1
  | .test _ _ y n => y.size + n.size + 1
  | .goto _ => 1
  | .ret _ => 1
  | .abort => 1

/-- Typed statements (`x = e;`, `T x = e;`, `T x;`): the register operation and the defined
slots after it. -/
def atom (file : File Codec.wireModel Unit Unit) (xs : Vars) (dk : List Key) (e : EE) :
    Option (Atom × List Key) :=
  match TyStmt.assignStmt file e with
  | some (x, ity, t) =>
    if isLocal xs x ity = true ∧ usable xs dk t = true then some (.set x.key ity t, x.key :: dk)
    else none
  | none => match TyStmt.initStmt file e with
    | some (x, ity, t) =>
      if isLocal xs x ity = true ∧ usable xs dk t = true then some (.set x.key ity t, x.key :: dk)
      else none
    | none => match TyStmt.uninitStmt e with
      | some (x, ity) =>
        if isLocal xs x ity = true then some (.clear x.key, dk.filter (· != x.key)) else none
      | none => none

/-- The jump `run l(y₁, …, yₙ)` to a label of `tbl` with a tree (its key in `T`) other than `ret`,
whose parameters are the slots `yᵢ`, with its defined slots `D l` defined. -/
def jump (ret : Sym) (xs : Vars) (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key)
    (T : List Key) (dk : List Key) (l : Sym) (args : List PE) : Bool :=
  match symArgs args, find tbl l with
  | some ys, some (qs, _) =>
      decide (l.key ≠ ret.key ∧ l.key ∈ T ∧ qs.map (·.key) = ys.map (·.key) ∧
        ys.all (isSlot xs) = true ∧ ∀ q ∈ D l.key, q ∈ dk)
  | _, _ => false

/-- `return e;`: the slots named by its cleanup are killed. -/
def retStmt (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars) (e : EE) :
    Option Term :=
  let killed := CfgGlobals.returnKeys e
  TyRun.retStmt file ret xs (xs.filter fun x => killed.contains x.1.key) e

/-- The code from `e` with the pending statements `P` and the defined slots `dk`, the remaining
fuel and the labels met (with their defined slots). -/
def walk (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    (fuel : Nat) → List Key → EE → List EE → List (Key × List Key) →
      Option (Code × Nat × List (Key × List Key))
  | 0, _, _, _, _ => none
  | fuel + 1, dk, e, P, seen =>
    if AbortCall.abortStmt file e = true then some (.abort, fuel, seen) else
    match ExitCall.recognizeBody file e with
    | some v => if -2147483648 ≤ v ∧ v ≤ 2147483647 then some (.ret (.lit v), fuel, seen) else none
    | none =>
    match retStmt file ret xs e with
    | some t => if usable xs dk t = true then some (.ret t, fuel, seen) else none
    | none => match atom file xs dk e with
    | some (a, dk') => match P with
      | b :: P' => (walk file ret xs tbl D T fuel dk' b P' seen).map fun (c, r) => (.atom a c, r)
      | [] => none
    | none => if VoidCall.recognize file e then
      match P with
      | b :: P' => walk file ret xs tbl D T fuel dk b P' seen
      | [] => none
    else match TyRun.ifParts file xs e with
    | some (t, yes, no) =>
      if usable xs dk t = true ∧ TyState.Term.bool01 t = true then
        match walk file ret xs tbl D T fuel dk no P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret xs tbl D T f dk yes P s).map fun (cn, r) => (.test false t cy cn, r)
          else none
        | none => none
      else none
    | none => match TyDoCondition.recognize file xs e with
    | some (t, yes, no) =>
      if usable xs dk t = true ∧ TyState.Term.bool01 t = true then
        match walk file ret xs tbl D T fuel dk yes P seen with
        | some (cy, f, s) =>
          if _h : f < fuel + 1 then
            (walk file ret xs tbl D T f dk no P s).map fun (cn, r) => (.test true t cy cn, r)
          else none
        | none => none
      else none
    | none => match e with
    | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => walk file ret xs tbl D T fuel dk a (b :: P) seen
    | .mk _ (.pure (.mk _ () (.val .unit))) => match P with
      | b :: P' => walk file ret xs tbl D T fuel dk b P' seen
      | [] => none
    | .mk _ (.save (l, _) ps body) =>
      if selfParams xs ps = true then walk file ret xs tbl D T fuel dk body P (seen ++ [(l.key, dk)])
      else none
    | .mk _ (.run () l args) =>
      if jump ret xs tbl D T dk l args = true then some (.goto l.key, fuel, seen ++ [(l.key, dk)])
      else none
    | _ => none
termination_by fuel _ _ _ _ => fuel
decreasing_by all_goals omega

/-- The blocks of a tree whose root is block `i`, jumps to label `l` going to `idx l`. A test
branches to its first tree when the comparison is `1` (`TyLoopCondition.testBlock`). -/
def Code.emit (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) : Code → Nat → List (Lir.Block Mir.Reg)
  | .atom (.set q ity t) c, i => ⟨(TyInput.assign regs q d (TyStmt.convT ity t)).map .op, .jump (i + 1)⟩ ::
      c.emit regs d idx (i + 1)
  | .atom (.clear _) c, i => ⟨[], .jump (i + 1)⟩ :: c.emit regs d idx (i + 1)
  | .test _ t y n, i =>
    TyLoopCondition.testBlock regs d t (i + 1 + y.size) (i + 1) ::
      (y.emit regs d idx (i + 1) ++ n.emit regs d idx (i + 1 + y.size))
  | .goto l, _ => [⟨[], .jump (idx l)⟩]
  | .ret t, _ => [⟨(TyInput.ops regs d t).map .op, .ret [.reg d]⟩]
  | .abort, _ => [⟨StateExitLink.abortOps.map .op, .trap⟩]

/-- The labels met by the trees of the labels met so far (`Cfg.grow`). -/
def grow (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (T : List Key) (g : List Key) :
    Nat → List (Key × List Key) → List (Key × List Key)
  | 0, seen => seen
  | n + 1, seen =>
    let D := labelDefs seen g
    let met := fun l => seen.any (·.1 == l)
    let new := tbl.flatMap fun z =>
      if met z.1.key then
        match walk file ret xs tbl D T Cfg.fuel (D z.1.key) z.2.2 [] [] with
        | some (_, _, s) => s.filter fun q => !met q.1
        | none => []
      else []
    if new.isEmpty then seen else grow file ret xs tbl T g n (seen ++ new)

/-- The blocks of the labels' trees, placed from `i`. -/
def emitAll (regs : Key → Mir.Reg) (d : Nat) (idx : Key → Nat) : Nat → List (Key × Code) →
    List (Lir.Block Mir.Reg)
  | _, [] => []
  | i, (_, c) :: cs => c.emit regs d idx i ++ emitAll regs d idx (i + c.size) cs

/-- The first block of the tree of label `l`, the trees placed one after another from `i`. -/
def pos : Nat → List (Key × Code) → Key → Nat
  | _, [], _ => 0
  | i, (l', c) :: cs, l => if l' = l then i else pos (i + c.size) cs l

/-- Set the globals' registers to their initial values, computed at run time; the first
definition of a key is set last. -/
def seedOps (regs : Key → Mir.Reg) (d : Nat) : List (Sym × IntegerType × Term) → List (Lir.Op Mir.Reg)
  | [] => []
  | (x, _, t) :: gs => seedOps regs d gs ++ TyInput.assign regs x.key d t

/-- A recognised `main`: slots (globals, then locals), the statement trees and label
definitions. -/
structure Plan where
  xs : Vars
  entry : Code
  codes : List (Key × Code)
  D : Key → List Key
  globals : List (Sym × IntegerType × Term)

/-- The first block of the label `l`. -/
def Plan.idx (P : Plan) (l : Key) : Nat := pos (P.entry.size + 1) P.codes l

/-- Block 0 initializes the globals, then `main`'s tree and the labels' trees. -/
def Plan.blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  let regs := regOf (P.xs.map (·.1.key))
  ⟨(seedOps regs P.xs.length P.globals).map .op, .jump 1⟩ ::
    (P.entry.emit regs P.xs.length P.idx 1 ++ emitAll regs P.xs.length P.idx (P.entry.size + 1) P.codes)

/-- The trees of the labels of `zs` with a key in `T` (`Cfg.labelCodes`). -/
def labelCodes (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) (T : List Key) :
    List (Sym × (List Sym × EE)) → List (Key × Code)
  | [] => []
  | z :: zs =>
    if z.1.key ∈ T then
      match walk file ret xs tbl D T Cfg.fuel (D z.1.key) z.2.2 [] [] with
      | some (c, _) => (z.1.key, c) :: labelCodes file ret xs tbl D T zs
      | none => labelCodes file ret xs tbl D T zs
    else labelCodes file ret xs tbl D T zs

/-- The labels whose trees succeed with jumps to these labels only (`Cfg.stable`). -/
def stable (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : Vars)
    (tbl : List (Sym × (List Sym × EE))) (D : Key → List Key) :
    Nat → List Key → Option (List Key × List (Key × Code))
  | 0, _ => none
  | n + 1, T =>
    let cs := labelCodes file ret xs tbl D T tbl
    if cs.map (·.1) = T then some (T, cs) else stable file ret xs tbl D n (cs.map (·.1))

/-- The creations of typed locals at the start of `main`'s block (`TyRun.block`). -/
def creates : Vars → EE → Option (Vars × EE)
  | xs, .mk _ (.sseq (.mk _ (.base (some x, _))) cr rest) =>
    match TyState.createTy cr with
    | some ity =>
      if isFresh xs x = true ∧ xs.length < 1024 then creates (xs ++ [(x, ity)]) rest else none
    | none => none
  | xs, e => some (xs, e)
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The body of `main` over the globals `gs`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (body : EE)
    (gs : List (Sym × IntegerType × Term)) : Option Plan :=
  match body with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
    if r'.key = r.key ∧ (LoopMain.labelKeys body).Nodup ∧
        gs.all (fun g => TyState.Term.wf g.2.2 && g.2.2.vars.isEmpty) = true then
      match creates (gs.map fun g => (g.1, g.2.1)) a with
      | some (xs, e) =>
        if (xs.map (·.1.key)).Nodup then
          let tbl := Cfg.labelTable body
          let g := gs.map (·.1.key)
          let T₀ := (tbl.filter fun z => z.1.key != ret.key).map (·.1.key)
          match walk file ret xs tbl (fun _ => []) T₀ Cfg.fuel g e [] [] with
          | some (_, _, seen) =>
            let D := labelDefs (grow file ret xs tbl T₀ g tbl.length seen) g
            match stable file ret xs tbl D (tbl.length + 1) T₀ with
            | some (T, codes) => match walk file ret xs tbl D T Cfg.fuel g e [] [] with
              | some (entry, _) => some ⟨xs, entry, codes, D, gs⟩
              | none => none
            | none => none
          | none => none
        else none
      | none => none
    else none
  | _ => none

/-- Typed globals initialised by literals and a block of typed locals with a control-flow graph
of labels. -/
def recognize (doc : Codec.Document) : Option Plan := do
  let ds := Globals.definitions doc.file
  let gs ← TyGlobals.inits doc.file ds
  if (ds.map fun d => d.1.key).Nodup ∧ ds.length < 1024 then do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body gs
  else none

end Silmaril.Compile.Core.Verified.TyCfg
