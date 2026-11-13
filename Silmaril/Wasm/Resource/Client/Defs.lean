module

public import Silmaril.Wasm.Resource.Handle.Defs
public import Silmaril.Wasm.Verify.Check.Defs

@[expose] public section

/-!
# A typestate verifier for clients of the handle protocol

`checkClient m ia iu if_ ps` decides, conservatively, that the Core 3.0 module `m` is a safe
client of the handle protocol `clientSpec ia iu if_` (imports `ia : [] → [h]` allocate,
`iu : [h] → …` uses, `if_ : [h] → …` frees). It is a Flow-style abstract interpretation
(`Silmaril.Wasm.Verify.Flow` is the template), with handles kept in **globals**.

## Handles in globals

`ps` lists pairs `(gf, gh)` of store global addresses: a flag global and a handle global. The
store invariant `Sigma ps L s` (`L` the live handles of the protocol state) says that a pair
whose flag is set (`On`: anything but `i32 0`) holds a live handle.

## The abstract state

* Facts (`Fact`): `on k`, `off k` (the flag of pair `k` is set, resp. `i32 0`), `live k` (the
  handle global of pair `k` holds a live handle that no *other* flagged pair holds), `loc i`
  (local `i` of the current frame holds a live handle held by no flagged pair). Local facts are
  frame-local: `FactSem`/`SoundF` read them against the locals `lc` of the frame whose code is
  checked (`okA … gs lc`; a nested `frame` is checked against its own locals), so they die with
  the frame. `local.get i` gives `fr` under `loc i`; `local.set i`/`local.tee i` of a value of top
  `fr` give `loc i` (`locF`); `loc` facts are killed like `live` facts (`isLive`: frees, writes of
  handle globals, setting a flag).
* Tops (`CTop`): `zero`, `nz` (the `i32` `0`, a nonzero `i32`), `flag k` (the current value of the
  flag of pair `k`), `gg` (a live handle), `fr` (a live handle held by no flagged pair), `other`,
  `ex` (dead code).
* `pre`: still in the value prefix of the sequence. Values of the prefix are runtime values,
  abstracted **semantically** (`Ab`, depending on the protocol state and the store); values
  after the first non-value are source constants, abstracted syntactically (`topOfConst`). After
  the first non-value only source instructions, references and `trap` are accepted, so nested
  bodies form a chain ending at the redex.

## The checks

`okI`/`okL` (Bool, mutual, structural) check source code: `call iu` needs `fr` or `gg`,
`call if_` needs `fr` (and drops the `live` facts), `call ia` gives `fr`; `global.set gh` needs
`fr` (and gives `live k`); `global.set gf` needs `zero` or `live k` (clearing the flag gives
`off k`, and `live k` when `on k` was known and every other pair is known `off`:
`liveAfterClear`); `global.get gf` gives
`flag k` (an `if` on it adds `on k`/`off k` to its branches); `global.get gh` gives `gg` under
`on k` or `live k`, and `fr` under `live k` and `off k`. Calls of other functions, `block`,
`loop`, `if`, `try_table` end with no facts (their code may write globals); bodies of `block`,
`if` and `try_table` start with the current facts, `loop` bodies with none.

`okA` (Prop) checks administrative code; nested `label`/`handler`/`frame` bodies are checked
(from some sound facts) inside `okX`.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Resource.Client

open Silmaril.Wasm Silmaril.Wasm.Execution.Core

/-! ## The abstract domain -/

/-- The abstraction of the value on top of the stack. -/
inductive CTop where
  | other
  | zero
  | nz
  | flag (k : Nat)
  | gg
  | fr
  | ex
  deriving DecidableEq, Repr

/-- Facts about the handle pairs. -/
inductive Fact where
  | on (k : Nat)
  | off (k : Nat)
  | live (k : Nat)
  | loc (i : Nat)
  deriving DecidableEq, Repr

/-- The abstract state of administrative code. -/
structure CSt where
  F : List Fact
  top : CTop
  pre : Bool

/-- The static parameters: handle pairs (store global addresses), the function list of the
module and the host functions of the three imports. -/
structure Cfg where
  ps : List (Nat × Nat)
  fs : List Nat
  isA : Nat → Bool
  isU : Nat → Bool
  isF : Nat → Bool
  /-- Uses are neutral: a call of the use import has no requirement (it still keeps the facts).
  Used by the owned-handle instance of `Silmaril.Wasm.Resource.OBClient`. -/
  nU : Bool := false
  /-- Internal functions taking a handle argument (`Silmaril.Wasm.Resource.ClientArg`): a call
  needs a live handle held by no flagged pair. -/
  isH : Nat → Bool := fun _ => false

/-- The pair of an address and whether it is its flag (`true`) or its handle (`false`). -/
def pairOf : List (Nat × Nat) → Nat → Option (Nat × Bool)
  | [], _ => none
  | p :: ps, a =>
    if p.1 == a then some (0, true) else if p.2 == a then some (0, false)
    else (pairOf ps a).map fun r => (r.1 + 1, r.2)

/-- A live fact: killed by a free and by writes making a handle flagged. -/
def isLive : Fact → Bool
  | .live _ => true
  | .loc _ => true
  | _ => false

/-- The facts after writing local `i` with a value of top `t`: `loc i` when the value is a live
handle held by no flagged pair. -/
def locF (F : List Fact) (t : CTop) (i : Nat) : List Fact :=
  (if t == .fr then [.loc i] else []) ++ F.filter fun f => f != .loc i

/-- The top after a constant. -/
def topOfConst : Instr → CTop
  | .intConst .i32 c => if c == 0 then .zero else .nz
  | _ => .other

section
variable (C : Cfg) (gs : List Nat)

/-- The top after reading the handle global of pair `k`. -/
def handTop (F : List Fact) (k : Nat) : CTop :=
  if F.contains (.live k) && F.contains (.off k) then .fr
  else if F.contains (.on k) || F.contains (.live k) then .gg
  else .other

/-- The top after `global.get` of address `a`. -/
def getTop (F : List Fact) (a : Nat) : CTop :=
  match pairOf C.ps a with
  | some (k, true) => .flag k
  | some (k, false) => handTop F k
  | none => .other

/-- The requirement of `global.set` of address `a`. -/
def setReq (F : List Fact) (t : CTop) (a : Nat) : Bool :=
  match pairOf C.ps a with
  | some (k, true) => t == .zero || F.contains (.live k)
  | some (_, false) => t == .fr
  | none => true

/-- Clearing the flag of pair `k` makes its handle `live` when the flag was set and every other
pair is known to be unflagged. -/
def liveAfterClear (F : List Fact) (k : Nat) : Bool :=
  F.contains (.on k) && (List.range C.ps.length).all fun j => j == k || F.contains (.off j)

/-- The facts after `global.set` of address `a`. -/
def setF (F : List Fact) (t : CTop) (a : Nat) : List Fact :=
  match pairOf C.ps a with
  | some (k, true) =>
    (if t == .zero then .off k :: (if liveAfterClear C F k then [.live k] else [])
      else if t == .nz then [.on k] else []) ++
      F.filter fun f => f != .on k && f != .off k && (t == .zero || !isLive f || f == .live k)
  | some (k, false) => .live k :: F.filter fun f => !isLive f
  | none => F

/-- The requirement of a `call`: a use needs a live handle (unless uses are neutral, `nU`), a free
and a call of a handle-taking function (`isH`) one held by no flagged pair. -/
def callReq (t : CTop) (x : FuncIdx) : Bool :=
  match C.fs[x.toNat]? with
  | some a =>
    if C.isU a then C.nU || t == .fr || t == .gg else if C.isF a then t == .fr
    else if C.isH a then t == .fr else true
  | none => true

/-- The state after a `call`. -/
def callNext (F : List Fact) (x : FuncIdx) : List Fact × CTop :=
  match C.fs[x.toNat]? with
  | some a =>
    if C.isU a then (F, .other) else if C.isF a then (F.filter fun f => !isLive f, .other)
    else if C.isA a then (F, .fr) else ([], .other)
  | none => ([], .other)

/-- The facts at the start of the `then` branch. -/
def thenF (F : List Fact) : CTop → List Fact
  | .flag k => .on k :: F
  | _ => F

/-- The facts at the start of the `else` branch. -/
def elseF (F : List Fact) : CTop → List Fact
  | .flag k => .off k :: F
  | _ => F

/-- The state after a source instruction. -/
def nextI (F : List Fact) (t : CTop) : Instr → List Fact × CTop
  | .intConst t' c => (F, topOfConst (.intConst t' c))
  | .localGet x => (F, if F.contains (.loc x.toNat) then .fr else .other)
  | .localSet x => (locF F t x.toNat, .other)
  | .localTee x => (locF F t x.toNat, .other)
  | .globalGet x => (F, match gs[x.toNat]? with
      | some a => getTop C F a
      | none => .other)
  | .globalSet x => (match gs[x.toNat]? with
      | some a => setF C F t a
      | none => F, .other)
  | .call x => callNext C F x
  | .callRef _ => ([], .other)
  | .callIndirect _ _ => ([], .other)
  | .returnCall _ => ([], .other)
  | .returnCallRef _ => ([], .other)
  | .returnCallIndirect _ _ => ([], .other)
  | .block _ _ => ([], .other)
  | .loop _ _ => ([], .other)
  | .if_ _ _ _ => ([], .other)
  | .tryTable _ _ _ => ([], .other)
  | .throwRef => (F, .ex)
  | _ => (F, .other)

mutual

/-- **The check of a source instruction**, bodies included. -/
def okI (F : List Fact) (t : CTop) : Instr → Bool
  | .block _ b => okL F .other b
  | .loop _ b => okL [] .other b
  | .tryTable _ _ b => okL F .other b
  | .if_ _ b₁ b₂ =>
    (t == .zero || okL (thenF F t) .other b₁) && (t == .nz || okL (elseF F t) .other b₂)
  | .globalSet x => match gs[x.toNat]? with
    | some a => setReq C F t a
    | none => true
  | .call x => callReq C t x
  | _ => true

/-- **The check of a source sequence.** -/
def okL : List Fact → CTop → List Instr → Bool
  | _, _, [] => true
  | F, t, i :: is => t == .ex || (okI F t i && okL (nextI C gs F t i).1 (nextI C gs F t i).2 is)

end

end

/-! ## Semantics -/

section

/-- The value of the global at address `a` (in the globals `gl` of a store). -/
def gval (gl : List GlobalInst) (a : Nat) : Option Val := (gl[a]?).map (·.value)

/-- The flag of the pair is set. -/
def On (gl : List GlobalInst) (p : Nat × Nat) : Prop := ∃ v, gval gl p.1 = some v ∧ v ≠ Val.i32 0

/-- **The store invariant**: a pair whose flag is set holds a live handle. -/
def Sigma (ps : List (Nat × Nat)) (L : List Val) (gl : List GlobalInst) : Prop :=
  ∀ p ∈ ps, On gl p → ∃ v, gval gl p.2 = some v ∧ v ∈ L

/-- The meaning of a fact (`lc`: the locals of the current frame). -/
def FactSem (ps : List (Nat × Nat)) (L : List Val) (gl : List GlobalInst) (lc : List (Option Val)) :
    Fact → Prop
  | .on k => ∃ p, ps[k]? = some p ∧ On gl p
  | .off k => ∃ p, ps[k]? = some p ∧ gval gl p.1 = some (Val.i32 0)
  | .live k => ∃ p, ps[k]? = some p ∧ ∃ v, gval gl p.2 = some v ∧ v ∈ L ∧
      ∀ j q, j ≠ k → ps[j]? = some q → On gl q → gval gl q.2 ≠ some v
  | .loc i => ∃ v, lc[i]? = some (some v) ∧ v ∈ L ∧ ∀ p ∈ ps, On gl p → gval gl p.2 ≠ some v

/-- The facts are sound. -/
def SoundF (ps : List (Nat × Nat)) (L : List Val) (gl : List GlobalInst) (lc : List (Option Val))
    (F : List Fact) : Prop :=
  ∀ f ∈ F, FactSem ps L gl lc f

/-- The meaning of a top: the abstraction of a runtime value. -/
def Ab (ps : List (Nat × Nat)) (L : List Val) (gl : List GlobalInst) : CTop → Val → Prop
  | .other, _ => True
  | .zero, v => v = Val.i32 0
  | .nz, v => ∃ c : BitVec 32, v = Val.i32 c ∧ c ≠ 0
  | .flag k, v => ∃ p, ps[k]? = some p ∧ gval gl p.1 = some v
  | .gg, v => v ∈ L
  | .fr, v => v ∈ L ∧ ∀ p ∈ ps, On gl p → gval gl p.2 ≠ some v
  | .ex, _ => False

/-- The pair addresses are pairwise distinct. -/
def PairsOK (ps : List (Nat × Nat)) : Prop :=
  ∀ k j : Fin ps.length, ((ps[k]).1 = (ps[j]).1 → k = j) ∧ ((ps[k]).2 = (ps[j]).2 → k = j) ∧
    (ps[k]).1 ≠ (ps[j]).2

instance (ps : List (Nat × Nat)) : Decidable (PairsOK ps) := by
  unfold PairsOK; infer_instance

/-- The administrative instructions with a nested body or a call: the first non-value of a
sequence only. -/
def NestA : Admin → Prop
  | .label _ _ _ => True
  | .handler _ _ _ => True
  | .frame _ _ _ => True
  | .callRefType _ => True
  | .returnCallRefType _ => True
  | _ => False

variable (C : Cfg) (L : List Val) (gl : List GlobalInst)

mutual

/-- The check of a nested administrative instruction (pre-mode, first non-value); `lc` are the
locals of the current frame. -/
def okX (gs : List Nat) (lc : List (Option Val)) : Admin → Prop
  | .label _ cont b => okL C gs [] .other cont = true ∧
      ∃ F, SoundF C.ps L gl lc F ∧ okA gs lc ⟨F, .other, true⟩ b
  | .handler _ _ b => ∃ F, SoundF C.ps L gl lc F ∧ okA gs lc ⟨F, .other, true⟩ b
  | .frame _ fr b => ∃ F, SoundF C.ps L gl fr.locals F ∧
      okA fr.module.globals fr.locals ⟨F, .other, true⟩ b
  | _ => True

/-- **The check of administrative code.** -/
def okA (gs : List Nat) (lc : List (Option Val)) : CSt → List Admin → Prop
  | _, [] => True
  | st, x :: l => st.top = .ex ∨
    (∃ v, x.val? = some v ∧ st.pre = true ∧ ∃ t, Ab C.ps L gl t v ∧ okA gs lc ⟨st.F, t, true⟩ l) ∨
    ((x.val? = none ∨ st.pre = false) ∧
      ((∃ i, x = .plain i ∧ okI C gs st.F st.top i = true ∧
          okA gs lc ⟨(nextI C gs st.F st.top i).1, (nextI C gs st.F st.top i).2, false⟩ l) ∨
        (∃ r, x = .ref r ∧ okA gs lc ⟨st.F, .other, false⟩ l) ∨ x = .trap ∨
        (NestA x ∧ st.pre = true ∧ okX gs lc x ∧ okA gs lc ⟨[], .other, false⟩ l)))

end

/-- The code of a frame is checked from sound facts. -/
def CodeOK (f : Frame) (code : List Admin) : Prop :=
  ∃ F, SoundF C.ps L gl f.locals F ∧ okA C L gl f.module.globals f.locals ⟨F, .other, true⟩ code

end

/-- Every Wasm function in `G` has a body checked from no facts, against its module's
globals. -/
def BodiesC {H : Type} (G : Nat → Prop) (C : Cfg) (funcs : List (FuncInst H)) : Prop :=
  ∀ a fi code, G a → funcs[a]? = some fi → fi.code = .wasm code →
    okL C fi.module.globals [] .other code.body = true

/-! ## The checker on modules -/

open Silmaril.Wasm.Verify (isHost closure rootsOf rootsB avoidsB instrRF instrCalls exprRF exprCalls
  instOf)

/-- The configuration of the analysis for an instantiated store. -/
def cfgOf (s : Store Nat) (fs : List Nat) (ia iu if_ : Nat) (ps : List (Nat × Nat)) : Cfg :=
  ⟨ps, fs, isHost s ia, isHost s iu, isHost s if_, false, fun _ => false⟩

/-- A host function of one of the three imports. -/
def isBadC (s : Store Nat) (ia iu if_ a : Nat) : Bool :=
  isHost s ia a || isHost s iu a || isHost s if_ a

/-- The function at address `a` passes the client check. -/
def funcOkC (s : Store Nat) (fs G : List Nat) (ia iu if_ : Nat) (ps : List (Nat × Nat))
    (a : Nat) : Bool :=
  match s.funcs[a]? with
  | some fi =>
    match fi.code with
    | .wasm code => fi.module.funcs == fs &&
        (exprRF code.body).all (fun x => match fs[x]? with
          | some b => G.contains b
          | none => true) &&
        (exprCalls code.body).all (fun x => match fs[x]? with
          | some b => G.contains b || isBadC s ia iu if_ b
          | none => true) &&
        okL (cfgOf s fs ia iu if_ ps) fi.module.globals [] .other code.body
    | .host _ => true
  | none => true

/-- The parameter and result counts of import `i` of an instance. -/
def importArity (I : Silmaril.Wasm.Game.ScalarInstance) (i : Nat) : Option (Nat × Nat) :=
  (I.imports[i]?).map fun ft => (ft.params.length, ft.results.length)

/-- The function list of the module of the first export (any choice is sound: `funcOkC` checks
it). -/
def fsOf (I : Silmaril.Wasm.Game.ScalarInstance) : List Nat :=
  match I.addrs.head? with
  | some a => match I.store.funcs[a]? with
    | some fi => fi.module.funcs
    | none => []
  | none => []

/-- The reachable non-bad functions of an instance. -/
def reachC (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat) : List Nat :=
  (closure I.store (fsOf I) (rootsOf I.store I.addrs)).filter
    fun a => !isBadC I.store ia iu if_ a

/-- **The client check on an instance**: the three imports are distinct, of arities
`[] → [h]`, `[h] → …`, `[h] → …`; the pairs are distinct, their flags start at `i32 0`; the
reachable functions (closed, containing the roots, avoiding the three imports) pass the
check. -/
def checkInst (I : Silmaril.Wasm.Game.ScalarInstance) (ia iu if_ : Nat)
    (ps : List (Nat × Nat)) : Bool :=
  let s := I.store
  let fs := fsOf I
  let G := reachC I ia iu if_
  ia != iu && ia != if_ && iu != if_ &&
    (importArity I ia).map (·.1) == some 0 && (importArity I ia).map (·.2) == some 1 &&
    (importArity I iu).map (·.1) == some 1 && (importArity I if_).map (·.1) == some 1 &&
    decide (PairsOK ps) && ps.all (fun p => gval s.globals p.1 == some (Val.i32 0)) &&
    G.all (funcOkC s fs G ia iu if_ ps) && rootsB G (rootsOf s I.addrs) &&
    avoidsB s G ia && avoidsB s G iu && avoidsB s G if_

/-- **The client check on a module** (its instance `instOf m`, `Silmaril.Wasm.Verify.Check`). -/
def checkClient (m : Module) (ia iu if_ : Nat) (ps : List (Nat × Nat)) : Bool :=
  (Silmaril.Wasm.Verify.instance? m).isSome && checkInst (instOf m) ia iu if_ ps

end Silmaril.Wasm.Resource.Client
