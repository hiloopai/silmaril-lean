module

public import Silmaril.Wasm.FX.Asyncify.Tool.Core.Defs

/-!
# The bounded frame machine against Core 3.0 `Step`: the simulation relation

`Silmaril.Wasm.FX.Asyncify.Tool.Core` proves the straight-line instructions of the frame machine
against silmaril-lean's Core 3.0 `Step`. This module states what is needed for the control
instructions and whole runs.

**A checker for machine code** (`InsOk`, `Ck`). The frame machine splices an `if` arm into the
code of its frame and keeps one operand stack per frame, while Core opens a label whose operand
stack starts empty; the machine's word memory agrees with Core's bytes only at aligned words.
`Ck X Q code a` says that `code` runs from an abstract operand stack `a` (one flag per operand:
`true` when the operand is known to be a multiple of 4) without underflow, with in-range locals and
globals `0, 1`, aligned word accesses (address flagged, offset a multiple of 4), calls of defined
functions only, `if` arms that are balanced (from and to an empty stack, or ending in `return`),
and ends in a stack satisfying `Q` or at a `return` with at least the result count on the stack.
`EnvOk E`: every body of `E` checks from the empty stack to its result count.

**The relation** (`CRel`). A machine frame is cut into *levels* (`Lvl`): level 0 is the code of the
innermost open `if` arm with its operands, each further level an enclosing arm, the last one the
function body. In Core a frame is `frame n {locals} [label n [] Z]` with the levels nested as
`label 0 [] …` inside `Z` (`wrapL`), and the frame of the callee (if any) sits between level 0's
operands and its code (`stackC`). Frames below the top wait on the callee's results (`Waits`).
`CRel` also asks that the store holds the program, the globals (two, the second a multiple of 4:
`GInv`) and the memory.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.FX.Asyncify.Tool

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-- What the checker needs to know of the function: the program, the number of locals and the
result count. -/
structure CkCtx where
  E : Env
  L : Nat
  nres : Nat

/-- The alignment flag of the result of a binary operator: sums and differences of multiples of
4 are multiples of 4 (modulo `2 ^ 32`). -/
def binAl : IntBinOp → Bool → Bool → Bool
  | .add, x, y => x && y
  | .sub, x, y => x && y
  | _, _, _ => false

/-- A non-branching instruction from abstract stack `a` (top first) to `a'`. -/
inductive InsOk (X : CkCtx) : Instr → List Bool → List Bool → Prop where
  | nop {a : List Bool} : InsOk X .nop a a
  | drop {b : Bool} {a : List Bool} : InsOk X .drop (b :: a) a
  | get {i : LocalIdx} {a : List Bool} : i.value.val < X.L → InsOk X (.localGet i) a (false :: a)
  | set {i : LocalIdx} {b : Bool} {a : List Bool} : i.value.val < X.L →
      InsOk X (.localSet i) (b :: a) a
  | tee {i : LocalIdx} {b : Bool} {a : List Bool} : i.value.val < X.L →
      InsOk X (.localTee i) (b :: a) (false :: a)
  | const {c : W} {a : List Bool} : InsOk X (.intConst .i32 c) a (decide (c.toNat % 4 = 0) :: a)
  | un {op : IntUnOp} {b : Bool} {a : List Bool} : InsOk X (.intUnOp .i32 op) (b :: a) (false :: a)
  | bin {op : IntBinOp} {y x : Bool} {a : List Bool} :
      InsOk X (.intBinOp .i32 op) (y :: x :: a) (binAl op x y :: a)
  | test {op : IntTestOp} {b : Bool} {a : List Bool} :
      InsOk X (.intTestOp .i32 op) (b :: a) (false :: a)
  | rel {op : IntRelOp} {y x : Bool} {a : List Bool} :
      InsOk X (.intRelOp .i32 op) (y :: x :: a) (false :: a)
  | gget {g : GlobalIdx} {a : List Bool} : g.value.val < 2 →
      InsOk X (.globalGet g) a (decide (g.value.val = 1) :: a)
  | gset {g : GlobalIdx} {b : Bool} {a : List Bool} : g.value.val < 2 →
      (g.value.val = 1 → b = true) → InsOk X (.globalSet g) (b :: a) a
  | load {arg : MemArg} {a : List Bool} : arg.offset.val % 4 = 0 →
      InsOk X (.intLoad .i32 none ⟨0⟩ arg) (true :: a) (false :: a)
  | store {arg : MemArg} {b : Bool} {a : List Bool} : arg.offset.val % 4 = 0 →
      InsOk X (.intStore .i32 none ⟨0⟩ arg) (b :: true :: a) a
  | call {f : FuncIdx} {fn : FnDef} {a : List Bool} : X.E.imps.length ≤ f.value.val →
      X.E.fns[f.value.val - X.E.imps.length]? = some fn → fn.nparams ≤ a.length →
      InsOk X (.call f) a (List.replicate fn.nres false ++ a.drop fn.nparams)

/-- Code checked from abstract stack `a`, ending in a stack satisfying `Q` or at a `return`. -/
inductive Ck (X : CkCtx) : (List Bool → Prop) → List Instr → List Bool → Prop where
  | nil {Q : List Bool → Prop} {a : List Bool} : Q a → Ck X Q [] a
  | ret {Q : List Bool → Prop} {a : List Bool} {rest : List Instr} : X.nres ≤ a.length →
      Ck X Q (.return_ :: rest) a
  | ins {Q : List Bool → Prop} {i : Instr} {a a' : List Bool} {rest : List Instr} :
      InsOk X i a a' → Ck X Q rest a' → Ck X Q (i :: rest) a
  | ifE {Q : List Bool → Prop} {t e rest : List Instr} {b : Bool} {a : List Bool} :
      Ck X (· = []) t [] → Ck X (· = []) e [] → Ck X Q rest a →
      Ck X Q (.if_ .empty t e :: rest) (b :: a)

/-- Every function body of `E` checks from the empty stack to its result count. -/
def EnvOk (E : Env) : Prop :=
  ∀ (j : Nat) (fn : FnDef), E.fns[j]? = some fn →
    Ck ⟨E, fn.nparams + fn.nlocals, fn.nres⟩ (fun a => a.length = fn.nres) fn.body []

/-- The operands `ops` agree with the abstract stack `a`: flagged operands are multiples of 4. -/
def AbsOk (a : List Bool) (ops : List W) : Prop :=
  List.Forall₂ (fun b w => b = true → w.toNat % 4 = 0) a ops

/-- The globals of the asyncified program: `state` and `sp`, the second a multiple of 4. -/
def GInv (gs : List W) : Prop := gs.length = 2 ∧ ∀ v, gs[1]? = some v → v.toNat % 4 = 0

/-- A level of a frame: the operands of an open arm (or of the body), their flags, the rest of
its code. -/
structure Lvl where
  ops : List W
  abs : List Bool
  code : List Instr

/-- How a level must end: the body (no level above) with the result count, an arm empty. -/
def qOf (n : Nat) : List Lvl → List Bool → Prop
  | [] => fun a => a.length = n
  | _ :: _ => fun a => a = []

/-- The enclosing levels are checked. -/
def LvlsOk (X : CkCtx) : List Lvl → Prop
  | [] => True
  | l :: ls => AbsOk l.abs l.ops ∧ Ck X (qOf X.nres ls) l.code l.abs ∧ LvlsOk X ls

/-- The shape of a machine frame: locals, result count, the innermost level and the enclosing
ones (innermost first). -/
structure CFr where
  locals : List W
  nres : Nat
  l0 : Lvl
  ls : List Lvl

/-- The checker context of a frame. -/
def CFr.ctx (E : Env) (fs : CFr) : CkCtx := ⟨E, fs.locals.length, fs.nres⟩

/-- A frame is checked, with abstract values `pre` to be pushed on level 0 first (the results
of the callee a frame waits on). -/
def CFr.Ok (E : Env) (pre : List Bool) (fs : CFr) : Prop :=
  AbsOk fs.l0.abs fs.l0.ops ∧ Ck (fs.ctx E) (qOf fs.nres fs.ls) fs.l0.code (pre ++ fs.l0.abs) ∧
    LvlsOk (fs.ctx E) fs.ls

/-- The machine operands of a frame shape. -/
def CFr.ops (fs : CFr) : List W := fs.l0.ops ++ fs.ls.flatMap Lvl.ops

/-- The machine code of a frame shape. -/
def CFr.code (fs : CFr) : List Instr := fs.l0.code ++ fs.ls.flatMap Lvl.code

/-- A machine frame has a shape. -/
def FrRel (fr : Frame) (fs : CFr) : Prop :=
  fr.locals = fs.locals ∧ fr.nres = fs.nres ∧ fr.ops = fs.ops ∧ fr.code = fs.code

/-- The frames below the top wait on the results of the frame above. -/
def Waits (E : Env) : Nat → List CFr → Prop
  | _, [] => True
  | k, fs :: rest => fs.Ok E (List.replicate k false) ∧ Waits E fs.nres rest

/-- A stack of frame shapes (top first) is checked. -/
def StackOk (E : Env) : List CFr → Prop
  | [] => False
  | fs :: rest => fs.Ok E [] ∧ Waits E fs.nres rest

/-- The Core frame of a function with `n` results, locals `ls` and label contents `Z`. -/
def frameA (mi : ModuleInst) (n : Nat) (ls : List W) (Z : List Admin) : Admin :=
  .frame n (localsF ⟨[], mi⟩ ls) [.label n [] Z]

/-- Nest code `Z` of the innermost level into the enclosing levels. -/
def wrapL : List Admin → List Lvl → List Admin
  | Z, [] => Z
  | Z, l :: ls => wrapL (stackA l.ops ++ .label 0 [] Z :: expression l.code) ls

/-- The Core frame of a frame shape, with `inner` (the callee's frame, if any) between level 0's
operands and its code. -/
def CFr.admin (mi : ModuleInst) (fs : CFr) (inner : List Admin) : Admin :=
  frameA mi fs.nres fs.locals (wrapL (stackA fs.l0.ops ++ inner ++ expression fs.l0.code) fs.ls)

/-- Put `X` inside the frames `fss` (innermost first). -/
def stackC (mi : ModuleInst) : List CFr → List Admin → List Admin
  | [], X => X
  | fs :: rest, X => stackC mi rest [fs.admin mi X]

/-- **The simulation relation**: machine configuration `c` and the Core configuration with store
`s`, frame `⟨[], mi⟩` and code `Z`. -/
def CRel {H : Type} (cap : Nat) (E : Env) (mi : ModuleInst) (c : Cfg) (s : Store H)
    (Z : List Admin) : Prop :=
  ∃ fss, List.Forall₂ FrRel c.frames fss ∧ StackOk E fss ∧ Z = stackC mi fss [] ∧
    HoldsProg s mi E ∧ GlobalsAre s ⟨[], mi⟩ c.globals ∧ MemAre s ⟨[], mi⟩ c.mem cap ∧
    GInv c.globals ∧ EnvOk E

/-- What a machine step result needs of the related Core configuration (store `s`, frame
`⟨[], mi⟩`, code `Z`): a next configuration is reached by Core steps into the relation again; a
return of the bottom frame by Core steps to the same values, with a store holding the program,
the final globals (still with `GInv`) and memory; a trap by Core steps to a trap. An import call never happens. -/
def CMatch {H : Type} (Pf : Numerics.Profile) (host : HostSemantics H) (cap : Nat) (E : Env)
    (mi : ModuleInst) (s : Store H) (Z : List Admin) : Res → Prop
  | .next c' => ∃ s' Z', Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, Z⟩ ⟨s', ⟨[], mi⟩, Z'⟩ ∧
      CRel cap E mi c' s' Z'
  | .done vs c' => ∃ s', Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, Z⟩ ⟨s', ⟨[], mi⟩, stackA vs⟩ ∧
      HoldsProg s' mi E ∧ GlobalsAre s' ⟨[], mi⟩ c'.globals ∧ MemAre s' ⟨[], mi⟩ c'.mem cap ∧
      GInv c'.globals
  | .trap => ∃ C', Execution.Core.Steps Pf host ⟨s, ⟨[], mi⟩, Z⟩ C' ∧ C'.code = [.trap]
  | .ask _ _ _ => False

end Silmaril.Wasm.FX.Asyncify.Tool
