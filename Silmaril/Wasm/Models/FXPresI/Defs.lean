module

public import Silmaril.Wasm.Models.FXPres.Defs

/-!
# An instance of `FXPres.CoreHyp`: a Core typing of integer code and exceptions

`FXPres.preservation` is conditional on `CoreHyp E P host fx`, a list of properties of the
Core typing `E.ct`. This module gives a concrete typing environment `envI` whose Core part
`CtI` is a **principal** typing of a Core fragment:

* integer constants, unary, binary, test and comparison operators (`i32` and `i64`);
* `nop`, `drop` (one operand of any FX type);
* `unreachable` and `trap` (any type);
* `ref.exn a` for an allocated exception `a`, and `throw_ref` (stack-polymorphic, on an
  `exnref` operand).

Store extension `ExtI` keeps the tags and extends the exceptions. `cont.new` and calls are not
typed by `CtI` (no function references), so the FX function table plays no part. Everything
else of `TL` (labels, frames, handler frames, blocks, `loop`, `if`, `br`, `return`,
continuation references, `cont.bind`, `resume`, `resume_throw`, `suspend`) is `TL`'s.

Why not Silmaril's `AdminsOk` directly: see `Silmaril.Wasm.Models.FXPresI.Thms`
(`naive_val_fails`): `AdminsOk` has stack weakening (`frame`) and subsumption (`sub`), so it is
not principal, while `CoreHyp.val`/`CoreHyp.drop` ask for principal value and `drop` types and
`TL` types sequences by exact matching. And `CoreHyp.core` gives the Core step's frame only
through its module, so a frame-dependent typing (locals) cannot be used.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics

variable {H : Type}

/-- The FX type of an integer type. -/
def intTy (t : IntType) : FTy := .val (.num (.int t))

/-- `exnref` as an FX type. -/
def exnTy : FTy := .val (.refT true (.abs .exn))

/-- **The Core fragment typing** (principal: no stack weakening, no subsumption). -/
inductive CtI (s : Store H) : Admin → List FTy → List FTy → Prop where
  | intConst {t : IntType} {x : BitVec t.width} : CtI s (.plain (.intConst t x)) [] [intTy t]
  | intUnOp {t : IntType} {op : IntUnOp} :
      CtI s (.plain (.intUnOp t op)) [intTy t] [intTy t]
  | intBinOp {t : IntType} {op : IntBinOp} :
      CtI s (.plain (.intBinOp t op)) [intTy t, intTy t] [intTy t]
  | intTestOp {t : IntType} {op : IntTestOp} :
      CtI s (.plain (.intTestOp t op)) [intTy t] [intTy .i32]
  | intRelOp {t : IntType} {op : IntRelOp} :
      CtI s (.plain (.intRelOp t op)) [intTy t, intTy t] [intTy .i32]
  | nop : CtI s (.plain .nop) [] []
  | drop {x : FTy} : CtI s (.plain .drop) [x] []
  | unreachable {i o : List FTy} : CtI s (.plain .unreachable) i o
  | trap {i o : List FTy} : CtI s .trap i o
  | refExn {a : Nat} (ha : a < s.exns.length) : CtI s (.ref (.exn a)) [] [exnTy]
  | throwRef {i o : List FTy} : CtI s (.plain .throwRef) (i ++ [exnTy]) o

/-- Store extension: the same tags, more exceptions. -/
def ExtI (s s' : Store H) : Prop := s.tags = s'.tags ∧ s.exns <+: s'.exns

/-- **The typing environment.** Any module instance `m₀`, any reading `ι` of declared value
types, any operand type `newTy` of `cont.new` (no Core code has it, so `cont.new` is never
typed). -/
def envI (m₀ : ModuleInst) (ι : CValType → FTy) (newTy : TypeIdx → FTy) : TyEnv H where
  m₀ := m₀
  ι := ι
  ct := CtI
  ext := ExtI
  newTy := newTy

/-! ## Progress -/

/-- The operand type of `cont.new` in `envP`: `funcref`, which no `CtI` value has. -/
def ntP (_ : TypeIdx) : FTy := .val (.refT true (.abs .func))

/-- **The environment of the progress theorem**: declared value types read as themselves. -/
def envP (m₀ : ModuleInst) : TyEnv H := envI m₀ FTy.val ntP

open Silmaril.Wasm.Models.FXV in
/-- **Code that does not step on its own** (in store `s`, continuation store `K`, frame `f`):
values, `trap`, a thrown exception, a `br` or `return` with values before it, an unhandled
`suspend` with the tag's operands, or `resume_throw` of a consumed continuation (which has no
rule in `StepFXS`). -/
inductive Halt (s : Store H) (K : List (Option ContFX)) (f : Frame) : List AdminFX → Prop where
  | vals (vs : List FVal) : Halt s K f (fvals vs)
  | trap : Halt s K f [.core .trap]
  | throw (a : Nat) : Halt s K f (cthrowing a)
  | br (vs : List FVal) (l : LabelIdx) (rest : List AdminFX) :
      Halt s K f (fvals vs ++ [.core (.plain (.br l))] ++ rest)
  | ret (vs : List FVal) (rest : List AdminFX) :
      Halt s K f (fvals vs ++ [.core (.plain .return_)] ++ rest)
  | suspend {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (ha : TagArity ti vs.length) : Halt s K f (E.plug (fvals vs ++ [.fx (.suspend x)]))
  | usedThrow {E : CtxV} {ws : List Val} {k : Nat} {ct : TypeIdx} {x : TagIdx}
      {hs : List OnClause} (hk : K[k]? = some none) :
      Halt s K f (E.plug (cvals ws ++ [.contRef k, .fx (.resumeThrow ct x hs)]))

open Silmaril.Wasm.Models.FXV in
/-- **A final configuration's code** (top level: no labels, no return): values, `trap`, a thrown
exception, an unhandled `suspend`, or `resume_throw` of a consumed continuation. -/
inductive Final (s : Store H) (K : List (Option ContFX)) (f : Frame) : List AdminFX → Prop where
  | vals (vs : List FVal) : Final s K f (fvals vs)
  | trap : Final s K f [.core .trap]
  | throw (a : Nat) : Final s K f (cthrowing a)
  | suspend {E : CtxV} {vs : List FVal} {x : TagIdx} {ta : Nat} {ti : TagInst}
      (ht : s.tag? (E.frameAt f) x = some (ta, ti)) (hE : ¬ E.Handles ta)
      (ha : TagArity ti vs.length) : Final s K f (E.plug (fvals vs ++ [.fx (.suspend x)]))
  | usedThrow {E : CtxV} {ws : List Val} {k : Nat} {ct : TypeIdx} {x : TagIdx}
      {hs : List OnClause} (hk : K[k]? = some none) :
      Final s K f (E.plug (cvals ws ++ [.contRef k, .fx (.resumeThrow ct x hs)]))

end Silmaril.Wasm.Models.FXPresI
