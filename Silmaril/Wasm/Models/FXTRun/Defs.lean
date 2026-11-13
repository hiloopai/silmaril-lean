module

public import Silmaril.Wasm.Models.FXT.Defs

/-!
# An interpreter for a fragment of `StepFXT`

`StepFXT` (`Silmaril.Wasm.Models.FXT`) is a relation: a `StepFX'` step, or a call of an intrinsic
(continuation cells, the queue, the log). This module gives a **step function** `tstep` that
computes one step for a fragment of FX code, so that runs of whole programs can be computed by
evaluation; `Silmaril.Wasm.Models.FXTRun.Thms` proves that every step it computes is a `StepFXT`
step (`tstep_sound`), so a computed run is a run of the relation.

The fragment (enough for the explainer's schedulers once compiled, `Silmaril.Wasm.Models.FXLComp`):

* structured control: `block` and `loop` without parameters, `if` on an `i32`, values out of a
  label, `br` out of and through labels and handlers, `return` out of labels, handlers and
  frames, values out of frames and handlers;
* Core code: `ref.func x` only (constants are values);
* calls `ref.func a; call_ref` of an **intrinsic** (its arguments are the last `arity`
  values) or of an **FX function** (its parameters are the last `nparams` values, which must be
  Core values);
* `cont.new`, `resume` (with no arguments: the explainer's threads have type `(cont (func))`),
  `drop` of a continuation reference, and `suspend` under a handler with an `(on $t $l)`
  clause, the payload being the last `tar ta` values (`tar`: the payload arity of each tag
  address; `StepFX'` itself is untyped and allows every split).

`tstep d` has a fuel `d` bounding the nesting depth it looks into; it returns `none` when no
rule of the fragment applies (a finished or stuck configuration, or unsupported code). `runT`
iterates it, and `checkT` tests that a run ends with empty code and a given log.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXTRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Wasm.Models.FXT

/-! ## Pieces -/

/-- An FX value instruction. -/
def valOf : AdminFX → Option FVal
  | .core a => a.val?.map .val
  | .contRef k => some (.cont k)
  | _ => none

/-- Split code at its first non-value: the leading values and the rest. -/
def splitV : List AdminFX → List FVal × List AdminFX
  | [] => ([], [])
  | a :: as =>
    match valOf a with
    | some v => (v :: (splitV as).1, (splitV as).2)
    | none => ([], a :: as)

/-- The last `n` values: the values before them and them. -/
def splitEnd (n : Nat) (vs : List FVal) : Option (List FVal × List FVal) :=
  if n ≤ vs.length then some (vs.take (vs.length - n), vs.drop (vs.length - n)) else none

/-- A function reference. -/
def asFunc : FVal → Option Nat
  | .val (.ref (.func a)) => some a
  | _ => none

/-- A continuation reference. -/
def asCont : FVal → Option Nat
  | .cont k => some k
  | _ => none

/-- An `i32`. -/
def asI32 : FVal → Option (BitVec 32)
  | .val (.num ⟨.int .i32, c⟩) => some c
  | _ => none

/-- Core values among FX values. -/
def coreVals : List FVal → Option (List Val)
  | [] => some []
  | .val v :: r => (coreVals r).map (v :: ·)
  | .cont _ :: _ => none

/-- How many arguments an intrinsic takes. -/
def arity : Intr → Nat
  | .log | .enq | .cset _ | .isNull => 1
  | _ => 0

/-- Does a handler frame of the context have a clause for tag address `ta`? -/
def handlesB (ta : Nat) : CtxV → Bool
  | .hole => false
  | .seq _ E _ => handlesB ta E
  | .label _ _ E => handlesB ta E
  | .frame _ _ E => handlesB ta E
  | .handler hs E => hs.any (fun c => c.tag == ta) || handlesB ta E

/-- The continuation `cont.new` makes of function address `a`. -/
def newC {H : Type} (a : Nat) (fi : FuncInst H) : ContFX :=
  ⟨fun c => c ++ [.core (.ref (.func a)), .core (.callRefType fi.type)]⟩

/-- A step result: continuation store, table, the values kept below the redex, and its
replacement. -/
abbrev HRes := List (Option ContFX) × Tbl × List FVal × List AdminFX

/-- A step result without kept values: continuation store, table, new code. -/
abbrev ERes := List (Option ContFX) × Tbl × List AdminFX

/-- A one-step function on code at a frame. -/
abbrev Stepper := Frame → List (Option ContFX) → Tbl → List AdminFX → Option ERes

variable {H : Type} (tar : Nat → Nat) (s : Store H) (fx : H → Option FuncFX)
  (intr : H → Option Intr)

/-! ## Finding a `suspend` -/

/-- The context of the first `suspend` of the code (through labels, frames and handlers), its
payload (the last `tar ta` values before it) and its tag; `f` is the frame in effect. -/
def findSus : Nat → Frame → List AdminFX → Option (CtxV × List FVal × TagIdx)
  | 0, _, _ => none
  | d + 1, f, code =>
    match splitV code with
    | (vs, .fx (.suspend x) :: rest) =>
      match s.tag? f x with
      | some (ta, _) =>
        match splitEnd (tar ta) vs with
        | some (u, w) => some (.seq u .hole rest, w, x)
        | none => none
      | none => none
    | (vs, .label n k body :: rest) =>
      (findSus d f body).map fun r => (.seq vs (.label n k r.1) rest, r.2)
    | (vs, .frame n fi body :: rest) =>
      (findSus d fi body).map fun r => (.seq vs (.frame n fi r.1) rest, r.2)
    | (vs, .handler hs body :: rest) =>
      (findSus d f body).map fun r => (.seq vs (.handler hs r.1) rest, r.2)
    | _ => none

/-! ## One step at the head of the code -/

/-- The last value is a function reference `ref.func a`: the values before it and `a`. -/
def lastFunc (vs : List FVal) : Option (List FVal × Nat) :=
  match splitEnd 1 vs with
  | some (u, [v]) => (asFunc v).map (u, ·)
  | _ => none

/-- The last value is a continuation reference. -/
def lastCont (vs : List FVal) : Option (List FVal × Nat) :=
  match splitEnd 1 vs with
  | some (u, [v]) => (asCont v).map (u, ·)
  | _ => none

/-- The last value is an `i32`. -/
def lastI32 (vs : List FVal) : Option (List FVal × BitVec 32) :=
  match splitEnd 1 vs with
  | some (u, [v]) => (asI32 v).map (u, ·)
  | _ => none

/-- A call of the intrinsic `op` on the last `arity op` values of `u`. -/
def callIntr (op : Intr) (K : List (Option ContFX)) (t : Tbl) (u : List FVal) : Option HRes :=
  match splitEnd (arity op) u with
  | some (u₁, args) =>
    match op.run args t with
    | some (res, t') => some (K, t', u₁, fvals res)
    | none => none
  | none => none

/-- A call of the FX function `F` on the last `F.nparams` values of `u` (Core values). -/
def callFx (F : FuncFX) (K : List (Option ContFX)) (t : Tbl) (u : List FVal) : Option HRes :=
  match splitEnd F.nparams u with
  | some (u₁, args) =>
    match coreVals args with
    | some cs =>
      some (K, t, u₁, [.frame F.nresults (Frame.forCall F.module cs F.locals)
        [.label F.nresults [] (F.body.map InstrFX.toAdmin)]])
    | none => none
  | none => none

/-- A call of the function at address `a`: an intrinsic or an FX function. -/
def callTo (K : List (Option ContFX)) (t : Tbl) (u : List FVal) (a : Nat) : Option HRes :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .host h =>
      match intr h with
      | some op => callIntr op K t u
      | none =>
        match fx h with
        | some F => callFx F K t u
        | none => none
    | .wasm _ => none
  | none => none

/-- A call `ref.func a; call_ref` (the reference is the last value). -/
def callHead (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) : Option HRes :=
  match lastFunc vs with
  | some (u, a) => callTo s fx intr K t u a
  | none => none

/-- `ref.func x`. -/
def refFuncHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal)
    (x : FuncIdx) : Option HRes :=
  match f.module.funcs[x.toNat]? with
  | some a => some (K, t, vs, [.core (.ref (.func a))])
  | none => none

/-- `drop` of a continuation reference. -/
def dropHead (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) : Option HRes :=
  match lastCont vs with
  | some (u, _) => some (K, t, u, [])
  | none => none

/-- Core instructions at the head. -/
def coreHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) :
    Admin → Option HRes
  | .plain (.refFunc x) => refFuncHead f K t vs x
  | .plain .drop => dropHead K t vs
  | .plain (.callRef _) => callHead s fx intr K t vs
  | .callRefType _ => callHead s fx intr K t vs
  | _ => none

/-- `br l` with values `ws` out of a label of arity `n` and continuation `k`. -/
def brOut (K : List (Option ContFX)) (t : Tbl) (n : Nat) (k : List InstrFX) (ws : List FVal)
    (l : LabelIdx) : Option ERes :=
  if l.toNat = 0 then
    match splitEnd n ws with
    | some (_, w) => some (K, t, fvals w ++ k.map InstrFX.toAdmin)
    | none => none
  else some (K, t, fvals ws ++ [.core (.plain (.br (labelPred l)))])

/-- A label at the head. -/
def labelHead (rec : Stepper) (f : Frame) (K : List (Option ContFX)) (t : Tbl) (n : Nat)
    (k : List InstrFX) (body : List AdminFX) : Option ERes :=
  match splitV body with
  | (ws, []) => some (K, t, fvals ws)
  | (ws, .core (.plain (.br l)) :: _) => brOut K t n k ws l
  | (ws, .core (.plain .return_) :: _) => some (K, t, fvals ws ++ [.core (.plain .return_)])
  | _ => (rec f K t body).map fun r => (r.1, r.2.1, [.label n k r.2.2])

/-- A function frame at the head. -/
def frameHead (rec : Stepper) (K : List (Option ContFX)) (t : Tbl) (n : Nat) (fi : Frame)
    (body : List AdminFX) : Option ERes :=
  match splitV body with
  | (ws, []) => if ws.length = n then some (K, t, fvals ws) else none
  | (ws, .core (.plain .return_) :: _) =>
    match splitEnd n ws with
    | some (_, w) => some (K, t, fvals w)
    | none => none
  | _ => (rec fi K t body).map fun r => (r.1, r.2.1, [.frame n fi r.2.2])

/-- The clause of `hs` for tag address `ta` catches the `suspend` in context `E` with payload
`w`. -/
def catchAt (K : List (Option ContFX)) (t : Tbl) (hs : List HClause) (E : CtxV) (w : List FVal)
    (ta : Nat) : Option ERes :=
  match hs.find? (fun c => c.tag == ta) with
  | some (.onLabel _ l) =>
    some (K ++ [some ⟨E.plug⟩], t, fvals w ++ [.contRef K.length, .core (.plain (.br l))])
  | _ => none

/-- A `suspend` caught by the handler frame `hs` around `body`. -/
def susHead (d : Nat) (f : Frame) (K : List (Option ContFX)) (t : Tbl) (hs : List HClause)
    (body : List AdminFX) : Option ERes :=
  match findSus tar s d f body with
  | some (E, w, x) =>
    match s.tag? (E.frameAt f) x with
    | some (ta, _) => if handlesB ta E then none else catchAt K t hs E w ta
    | none => none
  | none => none

/-- A handler frame at the head. -/
def handlerHead (rec : Stepper) (d : Nat) (f : Frame) (K : List (Option ContFX)) (t : Tbl)
    (hs : List HClause) (body : List AdminFX) : Option ERes :=
  match splitV body with
  | (ws, []) => some (K, t, fvals ws)
  | (ws, .core (.plain (.br l)) :: _) => some (K, t, fvals ws ++ [.core (.plain (.br l))])
  | (ws, .core (.plain .return_) :: _) => some (K, t, fvals ws ++ [.core (.plain .return_)])
  | _ =>
    match rec f K t body with
    | some r => some (r.1, r.2.1, [.handler hs r.2.2])
    | none => susHead tar s d f K t hs body

/-- `block` without parameters. -/
def blockHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) (bt : BlockType)
    (body : List InstrFX) : Option HRes :=
  match f.module.blockType? bt with
  | some ([], t₂) => some (K, t, vs, [.label t₂.length [] (fvals [] ++ body.map InstrFX.toAdmin)])
  | _ => none

/-- `loop` without parameters. -/
def loopHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) (bt : BlockType)
    (body : List InstrFX) : Option HRes :=
  match f.module.blockType? bt with
  | some ([], _) =>
    some (K, t, vs, [.label 0 [.loop bt body] (fvals [] ++ body.map InstrFX.toAdmin)])
  | _ => none

/-- `if` on the last value. -/
def ifHead (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) (bt : BlockType)
    (b₁ b₂ : List InstrFX) : Option HRes :=
  match lastI32 vs with
  | some (u, c) => some (K, t, u, [.block bt (if c = 0 then b₂ else b₁)])
  | none => none

/-- `cont.new` of the last value. -/
def contNewHead (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) : Option HRes :=
  match lastFunc vs with
  | some (u, a) =>
    match s.funcs[a]? with
    | some fi => some (K ++ [some (newC a fi)], t, u, [.contRef K.length])
    | none => none
  | none => none

/-- `resume` of the last value, with no arguments. -/
def resumeHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal)
    (hs : List OnClause) : Option HRes :=
  match lastCont vs with
  | some (u, k) =>
    match K[k]? with
    | some (some C) =>
      match hs.mapM (resolve s f) with
      | some hs' => some (K.set k none, t, u, [.handler hs' (C.plug (fvals []))])
      | none => none
    | _ => none
  | none => none

/-- FX instructions at the head. -/
def fxHead (f : Frame) (K : List (Option ContFX)) (t : Tbl) (vs : List FVal) :
    FXInstr → Option HRes
  | .contNew _ => contNewHead s K t vs
  | .resume _ hs => resumeHead s f K t vs hs
  | _ => none

/-- **One step at the head** `vs; e` (values `vs` before the first non-value `e`). -/
def head (rec : Stepper) (d : Nat) (f : Frame) (K : List (Option ContFX)) (t : Tbl)
    (vs : List FVal) : AdminFX → Option HRes
  | .block bt body => blockHead f K t vs bt body
  | .loop bt body => loopHead f K t vs bt body
  | .if_ bt b₁ b₂ => ifHead K t vs bt b₁ b₂
  | .label n k body => (labelHead rec f K t n k body).map fun r => (r.1, r.2.1, vs, r.2.2)
  | .frame n fi body => (frameHead rec K t n fi body).map fun r => (r.1, r.2.1, vs, r.2.2)
  | .handler hs body =>
    (handlerHead tar s rec d f K t hs body).map fun r => (r.1, r.2.1, vs, r.2.2)
  | .fx i => fxHead s f K t vs i
  | .core a => coreHead s fx intr f K t vs a
  | _ => none

/-- **One step**, looking at most `d` levels deep. -/
def tstep : Nat → Stepper
  | 0, _, _, _, _ => none
  | d + 1, f, K, t, code =>
    match splitV code with
    | (_, []) => none
    | (vs, e :: rest) =>
      (head tar s fx intr (fun g K' t' c => tstep d g K' t' c) d f K t vs e).map
        fun r => (r.1, r.2.1, fvals r.2.2.1 ++ r.2.2.2 ++ rest)

/-- One step of a configuration (store and frame unchanged). -/
def stepC (d : Nat) (c : ConfigT H) : Option (ConfigT H) :=
  (tstep tar c.cfg.store fx intr d c.cfg.frame c.cfg.conts c.tbl c.cfg.code).map
    fun r => ⟨⟨c.cfg.store, r.1, c.cfg.frame, r.2.2⟩, r.2.1⟩

/-- Run at most `n` steps (stopping when no step applies). -/
def runT (d : Nat) : Nat → ConfigT H → ConfigT H
  | 0, c => c
  | n + 1, c =>
    match stepC tar fx intr d c with
    | some c' => runT d n c'
    | none => c

/-- The run of `n` steps ends with empty code and the log `log`. -/
def checkT (d n : Nat) (c : ConfigT H) (log : List Val) : Bool :=
  let e := runT tar fx intr d n c
  e.cfg.code.isEmpty && decide (e.tbl.log = log)

/-! ## Comparing configurations

To split a long run into segments checked separately, a segment ends at a configuration given
explicitly. `sameCfg` compares configurations on a fragment without closures: no live
continuations (every entry of the continuation store used), and code that is one function
frame around one label around flat code (Core `i32.const`, `ref.func`, `call_ref`, and
`cont.new`). The store and frame are not compared (the interpreter does not change them). -/

/-- Equality of the Core instructions of flat code. -/
def beqInstr : Instr → Instr → Bool
  | .intConst .i32 a, .intConst .i32 b => decide (a = b)
  | .refFunc x, .refFunc y => decide (x = y)
  | .callRef x, .callRef y => decide (x = y)
  | _, _ => false

/-- Equality of flat FX instructions. -/
def beqFlat : AdminFX → AdminFX → Bool
  | .core (.plain i), .core (.plain j) => beqInstr i j
  | .fx (.contNew c), .fx (.contNew c') => decide (c = c')
  | _, _ => false

/-- Equality of flat code. -/
def beqFlats : List AdminFX → List AdminFX → Bool
  | [], [] => true
  | a :: as, b :: bs => beqFlat a b && beqFlats as bs
  | _, _ => false

/-- Equality of code that is a frame around a label around flat code. -/
def beqCode : List AdminFX → List AdminFX → Bool
  | [.frame n f [.label m [] b]], [.frame n' f' [.label m' [] b']] =>
    decide (n = n') && decide (f = f') && decide (m = m') && beqFlats b b'
  | _, _ => false

/-- Equality of FX values. -/
def beqFV : FVal → FVal → Bool
  | .val v, .val w => decide (v = w)
  | .cont k, .cont k' => decide (k = k')
  | _, _ => false

/-- Equality of lists of FX values. -/
def beqFVs : List FVal → List FVal → Bool
  | [], [] => true
  | a :: as, b :: bs => beqFV a b && beqFVs as bs
  | _, _ => false

/-- **The two configurations agree** (store and frame aside): same number of continuations, all
used, the same code (`beqCode`) and the same table. -/
def sameCfg (c m : ConfigT H) : Bool :=
  decide (c.cfg.conts.length = m.cfg.conts.length) && c.cfg.conts.all Option.isNone &&
    m.cfg.conts.all Option.isNone && beqCode c.cfg.code m.cfg.code &&
    beqFVs c.tbl.cells m.tbl.cells && beqFVs c.tbl.queue m.tbl.queue &&
    decide (c.tbl.log = m.tbl.log)

/-- A segment: the run of `n` steps from `c` ends at `m`. -/
def segT (d n : Nat) (c m : ConfigT H) : Bool := sameCfg (runT tar fx intr d n c) m

end Silmaril.Wasm.Models.FXTRun
