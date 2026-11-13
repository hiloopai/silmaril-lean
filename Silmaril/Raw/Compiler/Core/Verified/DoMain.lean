module

public import Silmaril.Compiler.Core.Verified.LoopMain.Defs
public import Silmaril.Compiler.Core.Verified.DoCondition.Defs

-- The unused-tactic linter flags tactics that other runs of the same tactic block need;
-- it is off in this Raw module until a cleanup pass checks each site.
set_option linter.unusedTactic false
/-! # `main` with one body-first `do` loop

The saved label enters the body before testing the current integer value.
A nonzero test runs that label again; zero falls through to the return.
All assignments and tests are emitted as runtime register code.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.DoMain

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics (EE)
open Silmaril.Machine
open StateExpr (Key Term term)
open StateStmt (assignStmt initStmt uninitStmt retStmt isLocal isFresh)
open ReturnLit (Eff)
open LoopMain (Pre classifyPre covered stmtAfter isUnit Plan creates labelKeys regOf)

/-- Body-first save, direct test and pointer back edge. -/
def loopStmt (file : File Codec.wireModel Unit Unit) (xs : List Sym) :
    Eff → Option (Term × LoopFallthrough.Stmt × LoopFallthrough.Stmt)
  | .mk _ (.sseq (.mk _ (.base (none, _)))
      (.mk _ (.save (label, _) [(x, (_, .mk _ () (.sym x')))]
        (.mk _ (.sseq (.mk _ (.base (none, _))) body cond)))) brk) =>
    if x' = x ∧ isLocal xs x = true then
      match DoCondition.recognize file xs cond with
      | some (t, .mk _ (.run () label' [.mk _ () (.sym x'')]), no) =>
        if label' = label ∧ x'' = x ∧ isUnit no = true then
          match LoopFallthrough.recognize file body, LoopFallthrough.recognize file brk with
          | some sb, some sk => some (t, sb, sk)
          | _, _ => none
        else none
      | _ => none
    else none
  | _ => none

/-- The statements of the block with the locals `xs`, `dk` defined: straight statements, the
loop, the return. -/
def stmts (file : File Codec.wireModel Unit Unit) (ret : Sym) (xs : List Sym) :
    List Key → Eff →
      Option (List Pre × Term × LoopFallthrough.Stmt × LoopFallthrough.Stmt × Term)
  | dk, .mk _ (.sseq (.mk _ (.base (none, _))) s rest) =>
    match classifyPre file s with
    | some st => match st.after xs dk with
      | some dk' => (stmts file ret xs dk' rest).map fun (ps, r) => (st :: ps, r)
      | none => none
    | none => match loopStmt file xs s, rest with
      | some (t, sb, sk), .mk _ (.sseq (.mk _ (.base (none, _))) r _) =>
        match stmtAfter xs dk sb with
        | some dB => match stmtAfter xs dB sk, retStmt file ret xs r with
          | some dk', some tr =>
            if covered dB t = true ∧ covered dk' tr = true then some ([], t, sb, sk, tr) else none
          | _, _ => none
        | none => none
      | _, _ => none
  | _, _ => none
termination_by _ e => sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- The body of `main`: the block, then the return label. -/
def recognizeBody (file : File Codec.wireModel Unit Unit) (body : Eff) : Option Plan :=
  match body with
  | .mk _ (.sseq (.mk _ (.base (none, _))) a
      (.mk _ (.save (ret, _) [(r, _)] (.mk _ (.pure (.mk _ () (.sym r'))))))) =>
    if r'.key = r.key ∧ (labelKeys body).Nodup then
      match creates [] a with
      | some (xs, e) =>
        if (xs.map (·.key)).Nodup then
          (stmts file ret xs [] e).map fun (ps, t, sb, sk, tr) => ⟨xs, ps, t, sb, sk, tr⟩
        else none
      | none => none
    else none
  | _ => none

/-- `main` is a block of `int` locals with one loop. -/
def recognize (doc : Codec.Document) : Option Plan := do
  if doc.file.globs.any (fun (_, g) => match g with
      | .definition _ _ => true | .declaration _ => false) then none else do
    let s ← doc.file.main
    let .procedure _ _ _ [] body ← doc.file.funs.lookup s | none
    recognizeBody doc.file body

/-- The body executes before the first test and every subsequent test. -/
def blocks (P : Plan) : List (Lir.Block Mir.Reg) :=
  let regs := regOf (P.xs.map (·.key))
  let d := P.xs.length
  [⟨(P.pre.flatMap (Pre.ops regs d)).map .op, .jump 1⟩,
   LoopIteration.bodyBlock regs d P.body 2,
   LoopBlocks.testBlock regs d P.test 1 3,
   ⟨(P.brk.ops regs d ++ StateExprLir.ops regs d P.ret).map .op, .ret [.reg d]⟩]

end Silmaril.Compile.Core.Verified.DoMain
