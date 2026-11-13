module

public import Silmaril.Wasm.Models.FXAsync.Defs
public import Silmaril.Wasm.Models.FXV.Defs

/-!
# The asyncify handler kernel as a fragment of `StepFX'`

`Silmaril.Wasm.Models.FXAsync` lowers an abstract one-shot handler kernel `sstep` to an asyncify
machine `tstep` (`lower_correct`). This module ties the **source** side of that lowering to
WasmFX: a kernel program over Core values (`V := Val`) is related to an actual `StepFX'`
configuration, with its functions given as FX functions of a store, and its code as `InstrFX`
source code. The results (`Thms`) show that every behaviour of the kernel run (hence of the
asyncify target, by `lower_correct`) is a `StepFX'` behaviour of the WasmFX program, on the
fragment below.

**The setting** (`Setup`): a profile, host and FX function table, a Core store `s` and module
instance `M` shared by all frames, the root frame `f0`, and for kernel function `f` its function
index `xf f` and address `fa f`, for kernel tag `t` its tag index `xt t`, address `ta t` and
payload arity `ar t`, and the (unchecked) continuation type immediate `ct`.

**The code relation** `EncI S W c Y`: kernel code `c` (of program `W`) is encoded as FX source
code `Y`, instruction by instruction:

* `push v` as `v; nop` (the `nop` keeps one `StepFX'` step per kernel step), for a numeric or
  vector `v`;
* `prim n op` as a Core instruction `i` that computes `op` on `i32` arguments (`PrimOk`);
* `drop` as `drop`; `call f` as `call (xf f)`;
* `cond f g` as `if bt (call f) (call g)` (`bt` takes the arguments as block parameters);
* `contNew f` as `ref.func (xf f); cont.new ct`, for a function without parameters;
* `resume 0 [(on t h)]` (no arguments, one clause) as the usual WasmFX shape
  ```
  block btD                ;; [cont] -> [r]
    block btH              ;; [cont] -> [payload, cont]
      resume ct (on (xt t) 0)
      br 1
    end
    <h's body, inlined>
  end
  ```
  so a handler is inlined code reached by a branch, as in WasmFX, not a call (an FX function's
  arguments are Core values in `StepFX'`, so a continuation cannot be passed to one). The
  inlining is a finite derivation, so handlers whose code resumes under themselves are not in
  the fragment;
* `suspend t (ar t)` as `suspend (xt t)`.

Each FX function of the store (`FuncOk`) has body `local.get 0 … local.get (np-1)` followed by
the encoding of the kernel body, one result, no further locals.

**Configurations** (`Rel`). A kernel stack is annotated (`Ann`) by how each frame is wrapped
(`Kind`: an FX function frame `frame 1 fi (label 1 …)`, the `block btD` label of an inlined
handler, or the root), what a waiting frame waits under (`WA`: a call, possibly inside the label
of an `if`, or a `resume` with its inlined handler code), and its FX code. `stkCtx` builds the
`CtxV` context of a stack, with the hole at the top frame's next instruction; a continuation is
either fresh (`ref.func … ; call_ref`) or a captured stack (`KRel`).

**The fragment checked along a run** (`fine`, `Supported`): the kernel does not trap, a returning
frame returns exactly one value (the root returns Core values), and `prim`, `call` and `cond` get
`i32`/Core-value operands. `i32Test` is the branch test of `if`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXAsyncFX

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (CValType)
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXAsync

/-! ## The setting -/

/-- An index of any kind (modulo `2 ^ 32`). -/
def ix {k : IndexKind} (j : Nat) : Idx k := ⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩

/-- The FX side of the encoding: Core semantics, store, module instance, root frame, and the
indices and addresses of kernel functions and tags. -/
structure Setup (H : Type) where
  P : Profile
  host : HostSemantics H
  fx : H → Option FuncFX
  s : Store H
  M : ModuleInst
  f0 : Frame
  xf : Nat → FuncIdx
  fa : Nat → Nat
  xt : Nat → TagIdx
  ta : Nat → Nat
  ar : Nat → Nat
  ct : TypeIdx

variable {H : Type}

/-- The prologue of an FX function: push its `np` parameters. -/
def localGets (np : Nat) : List InstrFX := (List.range np).map fun i => .core (.localGet (ix i))

/-- The test of `if`: an `i32` other than `0`. -/
def i32Test (v : Val) : Bool := v != Val.i32 0

/-- An `i32` value. -/
def isI32 : SV Val → Bool
  | .val (.num ⟨.int .i32, _⟩) => true
  | _ => false

/-- `i` computes `op` on `n` `i32` operands (top first) in one Core step, at every frame of `M`. -/
def PrimOk (S : Setup H) (n : Nat) (op : List Val → List Val) (i : Instr) : Prop :=
  ∀ (bs : List (BitVec 32)) (f : Frame), bs.length = n → f.module = S.M →
    Step S.P (blockFX S.host S.fx) ⟨S.s, f, vals (bs.map Val.i32).reverse ++ [.plain i]⟩
      ⟨S.s, f, vals (op (bs.map Val.i32)).reverse⟩

/-- Kernel tag `t` is tag `xt t` of `M`, at address `ta t`. -/
def TagOk (S : Setup H) (t : Nat) : Prop :=
  ∃ ti, S.M.tags[(S.xt t).toNat]? = some (S.ta t) ∧ S.s.tags[S.ta t]? = some ti

/-- **The code relation**: kernel code and its WasmFX source code. -/
inductive EncI (S : Setup H) (W : Prog (Ins Val)) : List (Ins Val) → List InstrFX → Prop where
  | nil : EncI S W [] []
  | push {c : List (Ins Val)} {Y : List InstrFX} {v : Val} {i : Instr}
      (hv : Admin.plain i = v.toAdmin) (h : EncI S W c Y) :
      EncI S W (.push v :: c) (.core i :: .core .nop :: Y)
  | prim {c : List (Ins Val)} {Y : List InstrFX} {n : Nat} {op : List Val → List Val}
      {i : Instr} (hi : PrimOk S n op i) (h : EncI S W c Y) :
      EncI S W (.prim n op :: c) (.core i :: Y)
  | drop {c : List (Ins Val)} {Y : List InstrFX} (h : EncI S W c Y) :
      EncI S W (.drop :: c) (.core .drop :: Y)
  | call {c : List (Ins Val)} {Y : List InstrFX} {f : Nat} (h : EncI S W c Y) :
      EncI S W (.call f :: c) (.core (.call (S.xf f)) :: Y)
  | cond {c : List (Ins Val)} {Y : List InstrFX} {f g np : Nat} {bf bg : List (Ins Val)}
      {bt : BlockType} {t₁ t₂ : List CValType} (hf : W f = some (np, bf))
      (hg : W g = some (np, bg)) (hbt : S.M.blockType? bt = some (t₁, t₂))
      (ht : t₁.length = np) (h : EncI S W c Y) :
      EncI S W (.cond f g :: c)
        (.if_ bt [.core (.call (S.xf f))] [.core (.call (S.xf g))] :: Y)
  | contNew {c : List (Ins Val)} {Y : List InstrFX} {f : Nat} {bf : List (Ins Val)}
      (hf : W f = some (0, bf)) (h : EncI S W c Y) :
      EncI S W (.contNew f :: c) (.core (.refFunc (S.xf f)) :: .fx (.contNew S.ct) :: Y)
  | resume {c : List (Ins Val)} {Y Z : List InstrFX} {t hf np : Nat} {bh : List (Ins Val)}
      {btD btH : BlockType} {d₁ d₂ e₁ e₂ : List CValType} (htag : TagOk S t)
      (hh : W hf = some (np, bh)) (hZ : EncI S W bh Z)
      (hD : S.M.blockType? btD = some (d₁, d₂)) (hD₁ : d₁.length = 1) (hD₂ : d₂.length = 1)
      (hH : S.M.blockType? btH = some (e₁, e₂)) (hH₁ : e₁.length = 1)
      (hH₂ : e₂.length = S.ar t + 1) (h : EncI S W c Y) :
      EncI S W (.resume 0 [⟨t, hf⟩] :: c)
        (.block btD (.block btH [.fx (.resume S.ct [.onLabel (S.xt t) (ix 0)]),
          .core (.br (ix 1))] :: Z) :: Y)
  | suspend {c : List (Ins Val)} {Y : List InstrFX} {t : Nat} (htag : TagOk S t)
      (h : EncI S W c Y) :
      EncI S W (.suspend t (S.ar t) :: c) (.fx (.suspend (S.xt t)) :: Y)

/-- The FX functions of the store: kernel function `f` is FX function `xf f` at address `fa f`,
with the prologue and the encoded body. -/
def FuncOk (S : Setup H) (W : Prog (Ins Val)) : Prop :=
  ∀ f np body, W f = some (np, body) → np < 2 ^ 32 ∧
    ∃ (fi : FuncInst H) (h : H) (Y : List InstrFX),
      S.M.funcs[(S.xf f).toNat]? = some (S.fa f) ∧ S.s.funcs[S.fa f]? = some fi ∧
      fi.code = .host h ∧ S.fx h = some ⟨S.M, np, 1, [], localGets np ++ Y⟩ ∧ EncI S W body Y

/-- **The global hypotheses** of the setting: the FX functions, the module of the root frame,
and distinct tag addresses. -/
structure Ok (S : Setup H) (W : Prog (Ins Val)) : Prop where
  funcs : FuncOk S W
  root : S.f0.module = S.M
  tags : Function.Injective S.ta

/-! ## Annotated stacks and their contexts -/

/-- How a kernel frame is wrapped in the FX code. -/
inductive Kind where
  /-- An FX function frame: `frame 1 fi (label 1 …)`. -/
  | fn (fi : Frame)
  /-- The `block btD` label of an inlined handler. -/
  | blk
  /-- The root code. -/
  | root

/-- What a waiting frame waits under. -/
inductive WA where
  /-- A call, inside the label of an `if` when `jk = some n`. -/
  | call (jk : Option Nat)
  /-- A `resume`, with the inlined handler code `Z` after its `block btH`. -/
  | res (Z : List InstrFX)

/-- The annotation of a kernel frame. -/
structure Ann where
  kind : Kind
  wa : WA
  code : List InstrFX

/-- FX values of a kernel operand. -/
def toF : SV Val → FVal
  | .val v => .val v
  | .cont k => .cont k

/-- A kernel operand stack (top first) as FX values (bottom first). -/
def opsF (o : List (SV Val)) : List FVal := (o.map toF).reverse

/-- FX source code as administrative code. -/
def adm (Y : List InstrFX) : List AdminFX := Y.map InstrFX.toAdmin

/-- Compose contexts: fill the hole of the first with the second. -/
def comp : CtxV → CtxV → CtxV
  | .hole, E => E
  | .seq vs E rest, E' => .seq vs (comp E E') rest
  | .label n k E, E' => .label n k (comp E E')
  | .frame n f E, E' => .frame n f (comp E E')
  | .handler hs E, E' => .handler hs (comp E E')

/-- The wrapper of a frame. -/
def kindCtx : Kind → CtxV → CtxV
  | .fn fi, E => .frame 1 fi (.label 1 [] E)
  | .blk, E => .label 1 [] E
  | .root, E => E

/-- `br 1`. -/
def br1 : AdminFX := .core (.plain (.br (ix 1)))

/-- The context of a waiting frame around the frame above it. -/
def waitCtx (S : Setup H) : Option (List Clause) → WA → CtxV
  | none, .call none => .hole
  | none, .call (some n) => .label n [] .hole
  | some [⟨t, _⟩], .res Z =>
    .label 1 [] (.seq [] (.label (S.ar t + 1) []
      (.seq [] (.handler [.onLabel (S.ta t) (ix 0)] .hole) [br1])) (adm Z))
  | _, _ => .hole

/-- The context of the top frame: its operands, then the hole, then its code. -/
def topCtx (p : SFrame Val × Ann) : CtxV :=
  kindCtx p.2.kind (.seq (opsF p.1.ops) .hole (adm p.2.code))

/-- The context of a waiting frame. -/
def lowCtx (S : Setup H) (p : SFrame Val × Ann) : CtxV :=
  kindCtx p.2.kind (.seq (opsF p.1.ops) (waitCtx S p.1.wait p.2.wa) (adm p.2.code))

/-- The context of the waiting frames (top first; the bottom frame is outermost). -/
def lowsCtx (S : Setup H) : List (SFrame Val × Ann) → CtxV
  | [] => .hole
  | p :: ps => comp (lowsCtx S ps) (lowCtx S p)

/-- **The context of an annotated stack**, with the hole at the top frame's next instruction. -/
def stkCtx (S : Setup H) : List (SFrame Val × Ann) → CtxV
  | [] => .hole
  | p :: ps => comp (lowsCtx S ps) (topCtx p)

/-! ## Well-formed annotations -/

/-- A root annotation. -/
def Kind.isRoot : Kind → Bool
  | .root => true
  | _ => false

/-- A frame and its annotation: encoded code, and function frames of `M`. -/
def FrOk (S : Setup H) (W : Prog (Ins Val)) (p : SFrame Val × Ann) : Prop :=
  EncI S W p.1.code p.2.code ∧ ∀ fi, p.2.kind = .fn fi → fi.module = S.M

/-- A waiting frame: waiting on a call, or on a one-clause `resume` with its inlined handler. -/
def WaitOk (S : Setup H) (W : Prog (Ins Val)) (p : SFrame Val × Ann) : Prop :=
  (p.1.wait = none ∧ ∃ jk, p.2.wa = .call jk) ∨
    ∃ (t hf np : Nat) (bh : List (Ins Val)) (Z : List InstrFX), p.1.wait = some [⟨t, hf⟩] ∧ p.2.wa = .res Z ∧ W hf = some (np, bh) ∧
      EncI S W bh Z

/-- A captured or fresh stack segment: no root frame. -/
def SegOk (S : Setup H) (W : Prog (Ins Val)) (st : List (SFrame Val × Ann)) : Prop :=
  st ≠ [] ∧ (∀ p ∈ st, FrOk S W p ∧ p.2.kind.isRoot = false) ∧ ∀ p ∈ st.tail, WaitOk S W p

/-- The main stack: a segment on top of the root frame. -/
def MainOk (S : Setup H) (W : Prog (Ins Val)) (st : List (SFrame Val × Ann)) : Prop :=
  (∀ p ∈ st, FrOk S W p) ∧ (∀ p ∈ st.tail, WaitOk S W p) ∧
    ∃ init last, st = init ++ [last] ∧ last.2.kind = .root ∧ ∀ p ∈ init, p.2.kind.isRoot = false

/-- **Continuations**: consumed on both sides, fresh (a function without parameters, as
`cont.new` makes it), or a captured stack segment. -/
def KRel (S : Setup H) (W : Prog (Ins Val)) : Option (List (SFrame Val)) → Option ContFX → Prop
  | none, none => True
  | some seg, some C =>
    (∃ (f : Nat) (body : List (Ins Val)) (fi : FuncInst H), W f = some (0, body) ∧ S.s.funcs[S.fa f]? = some fi ∧
      seg = [⟨body, [], none⟩] ∧
      C = ⟨fun c => c ++ [.core (.ref (.func (S.fa f))), .core (.callRefType fi.type)]⟩) ∨
    ∃ st, seg = st.map Prod.fst ∧ SegOk S W st ∧ C = ⟨(stkCtx S st).plug⟩
  | _, _ => False

/-- **Kernel and `StepFX'` configurations.** -/
def Rel (S : Setup H) (W : Prog (Ins Val)) (x : SCfg Val) (c : ConfigFX H) : Prop :=
  c.store = S.s ∧ c.frame = S.f0 ∧ List.Forall₂ (KRel S W) x.conts c.conts ∧
    ∃ st, x.stack = st.map Prod.fst ∧ MainOk S W st ∧ c.code = (stkCtx S st).plug []

/-! ## The fragment along a run -/

/-- The checks on the top frame. -/
def fineTop (W : Prog (Ins Val)) (fr : SFrame Val) (rest : List (SFrame Val)) : Bool :=
  match fr.code with
  | [] =>
    match rest with
    | [] => (allVals fr.ops).isSome
    | _ :: _ => fr.ops.length == 1
  | .prim n _ :: _ => (fr.ops.take n).all isI32
  | .call f :: _ =>
    match W f with
    | some (np, _) => (allVals (fr.ops.take np)).isSome
    | none => false
  | .cond f g :: _ =>
    match fr.ops with
    | .val v :: o =>
      isI32 (.val v) &&
        match W (if i32Test v then f else g) with
        | some (np, _) => (allVals (o.take np)).isSome
        | none => false
    | _ => false
  | _ => true

/-- **The fragment at a configuration**: no trap next, and the operand checks of `fineTop`. -/
def fine (W : Prog (Ins Val)) (x : SCfg Val) : Bool :=
  (match sstep W i32Test x with
    | .stop .trap => false
    | _ => true) &&
  match x.stack with
  | [] => false
  | fr :: rest => fineTop W fr rest

/-- Every configuration of the kernel run from `x` is in the fragment. -/
def Supported (W : Prog (Ins Val)) (x : SCfg Val) : Prop :=
  ∀ n y, runN (sstep W i32Test) n x = .next y → fine W y = true

/-- A kernel outcome as a Core behaviour (returned operands are listed bottom first). -/
def obsB : Obs Val → Behaviour Val
  | .done vs =>
    match allVals vs with
    | some ws => .returns ws.reverse
    | none => .traps
  | .trap => .traps
  | .diverges => .diverges

/-- The root FX configuration that calls kernel function `f` with Core arguments `args`. -/
def fxInit (S : Setup H) (f : Nat) (args : List Val) : ConfigFX H :=
  ⟨S.s, [], S.f0, cvals args.reverse ++ [.core (.plain (.call (S.xf f)))]⟩

end Silmaril.Wasm.Models.FXAsyncFX
