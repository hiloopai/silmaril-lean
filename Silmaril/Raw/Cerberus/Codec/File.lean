module

public import Silmaril.Cerberus.Codec.Core.Defs
public import Silmaril.Semantics.CPort.Formats.SExp.EncodingTagged.Defs

/-! # Wire codecs for Core actions, effectful expressions and files

The rest of the `Core.file` closure, and the version 1/2 document envelopes. Effectful
expressions are the remaining recursive family. Their encoders use
well-founded recursion through nested lists. As in `Core.lean`, the local
`SizeOf Int` instance matches the abstract memory-value size used by the syntax.

A document retains ordered `FileBindings` for exact re-encoding, and decodes
all eight maps with `Map.ofList` into `Document.file`. `Document.file_eq` proves
that the semantic file is exactly the interpretation of the retained bindings.
This is necessary because semantic map equality ignores diagnostic key fields.
The map-order and digest-length restrictions belong to `WellFormed`; the syntax
codec's laws cover arbitrary representable bindings.
-/

@[expose] public section

namespace Silmaril.Cerberus.Codec

open Silmaril.TaggedCodec Codec
open Core

/-! ## Memory orders, operations and actions -/

def encodeMemoryOrder : MemoryOrder → Tree
  | .na => node (tag% MemoryOrder.na) []
  | .seqCst => node (tag% MemoryOrder.seqCst) []
  | .relaxed => node (tag% MemoryOrder.relaxed) []
  | .release => node (tag% MemoryOrder.release) []
  | .acquire => node (tag% MemoryOrder.acquire) []
  | .consume => node (tag% MemoryOrder.consume) []
  | .acqRel => node (tag% MemoryOrder.acqRel) []

def memoryOrder : Codec MemoryOrder := ofLeaves encodeMemoryOrder
  [leafPair% MemoryOrder.na, leafPair% MemoryOrder.seqCst, leafPair% MemoryOrder.relaxed, leafPair% MemoryOrder.release,
   leafPair% MemoryOrder.acquire, leafPair% MemoryOrder.consume, leafPair% MemoryOrder.acqRel] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeLinuxMemoryOrder : LinuxMemoryOrder → Tree
  | .once => node (tag% LinuxMemoryOrder.once) []
  | .acquire => node (tag% LinuxMemoryOrder.acquire) []
  | .release => node (tag% LinuxMemoryOrder.release) []
  | .rmb => node (tag% LinuxMemoryOrder.rmb) []
  | .wmb => node (tag% LinuxMemoryOrder.wmb) []
  | .mb => node (tag% LinuxMemoryOrder.mb) []
  | .rbDep => node (tag% LinuxMemoryOrder.rbDep) []
  | .rcuLock => node (tag% LinuxMemoryOrder.rcuLock) []
  | .rcuUnlock => node (tag% LinuxMemoryOrder.rcuUnlock) []
  | .syncRcu => node (tag% LinuxMemoryOrder.syncRcu) []

def linuxMemoryOrder : Codec LinuxMemoryOrder := ofLeaves encodeLinuxMemoryOrder
  [leafPair% LinuxMemoryOrder.once, leafPair% LinuxMemoryOrder.acquire, leafPair% LinuxMemoryOrder.release, leafPair% LinuxMemoryOrder.rmb,
   leafPair% LinuxMemoryOrder.wmb, leafPair% LinuxMemoryOrder.mb, leafPair% LinuxMemoryOrder.rbDep, leafPair% LinuxMemoryOrder.rcuLock,
   leafPair% LinuxMemoryOrder.rcuUnlock, leafPair% LinuxMemoryOrder.syncRcu] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeGenericMemop : MemOp Sym → Tree
  | .ptrEq => node (tag% MemOp.ptrEq) []
  | .ptrNe => node (tag% MemOp.ptrNe) []
  | .ptrLt => node (tag% MemOp.ptrLt) []
  | .ptrGt => node (tag% MemOp.ptrGt) []
  | .ptrLe => node (tag% MemOp.ptrLe) []
  | .ptrGe => node (tag% MemOp.ptrGe) []
  | .ptrdiff => node (tag% MemOp.ptrdiff) []
  | .intFromPtr => node (tag% MemOp.intFromPtr) []
  | .ptrFromInt => node (tag% MemOp.ptrFromInt) []
  | .ptrValidForDeref => node (tag% MemOp.ptrValidForDeref) []
  | .ptrWellAligned => node (tag% MemOp.ptrWellAligned) []
  | .ptrArrayShift => node (tag% MemOp.ptrArrayShift) []
  | .ptrMemberShift s i => node (tag% MemOp.ptrMemberShift) [sym.enc s, identifier.enc i]
  | .memcpy => node (tag% MemOp.memcpy) []
  | .memcmp => node (tag% MemOp.memcmp) []
  | .realloc => node (tag% MemOp.realloc) []
  | .vaStart => node (tag% MemOp.vaStart) []
  | .vaCopy => node (tag% MemOp.vaCopy) []
  | .vaArg => node (tag% MemOp.vaArg) []
  | .vaEnd => node (tag% MemOp.vaEnd) []
  | .copyAllocId => node (tag% MemOp.copyAllocId) []
  | .cheriIntrinsic s (t, ts) =>
    node (tag% MemOp.cheriIntrinsic) [str.enc s, node "$tuple" [ctype.enc t, (list ctype).enc ts]]

def memOp : Codec (MemOp Sym) := ofAlts encodeGenericMemop
  [leaf% MemOp.ptrEq, leaf% MemOp.ptrNe, leaf% MemOp.ptrLt, leaf% MemOp.ptrGt,
   leaf% MemOp.ptrLe, leaf% MemOp.ptrGe, leaf% MemOp.ptrdiff,
   leaf% MemOp.intFromPtr, leaf% MemOp.ptrFromInt,
   leaf% MemOp.ptrValidForDeref, leaf% MemOp.ptrWellAligned,
   leaf% MemOp.ptrArrayShift,
   alt% MemOp.ptrMemberShift (sym ⊗ identifier),
   leaf% MemOp.memcpy, leaf% MemOp.memcmp, leaf% MemOp.realloc,
   leaf% MemOp.vaStart, leaf% MemOp.vaCopy, leaf% MemOp.vaArg,
   leaf% MemOp.vaEnd, leaf% MemOp.copyAllocId,
   alt% MemOp.cheriIntrinsic (str ⊗ tuple (ctype ⊗ list ctype))]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodePolarity : Polarity → Tree
  | .pos => node (tag% Core.Polarity.pos) []
  | .neg => node (tag% Core.Polarity.neg) []

def polarity : Codec Polarity := ofLeaves encodePolarity [leafPair% Core.Polarity.pos, leafPair% Core.Polarity.neg] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

def encodeKillKind : KillKind → Tree
  | .dynamic => node (tag% Core.KillKind.dynamic) []
  | .static t => node (tag% Core.KillKind.static) [ctype.enc t]

def killKind : Codec KillKind := ofAlts encodeKillKind
  [leaf% Core.KillKind.dynamic, alt% Core.KillKind.static ctype]
  (by codec_nodup) (by codec_enc) (by codec_cover)

abbrev ActionNode := Core.ActionNode M Unit Sym
abbrev Action := Core.Action M Unit Unit Sym

def encodeActionNode : ActionNode → Tree
  | .create e e' p => node (tag% Core.ActionNode.create) [pexpr.enc e, pexpr.enc e', prefix_.enc p]
  | .createReadOnly e e' e'' p =>
    node (tag% Core.ActionNode.createReadOnly) [pexpr.enc e, pexpr.enc e', pexpr.enc e'', prefix_.enc p]
  | .alloc e e' p => node (tag% Core.ActionNode.alloc) [pexpr.enc e, pexpr.enc e', prefix_.enc p]
  | .kill k e => node (tag% Core.ActionNode.kill) [killKind.enc k, pexpr.enc e]
  | .store b e e' e'' o =>
    node (tag% Core.ActionNode.store) [boolean.enc b, pexpr.enc e, pexpr.enc e', pexpr.enc e'', memoryOrder.enc o]
  | .load e e' o => node (tag% Core.ActionNode.load) [pexpr.enc e, pexpr.enc e', memoryOrder.enc o]
  | .seqRmw b e e' s e'' =>
    node (tag% Core.ActionNode.seqRmw) [boolean.enc b, pexpr.enc e, pexpr.enc e', sym.enc s, pexpr.enc e'']
  | .rmw e e' e'' e''' o o' => node (tag% Core.ActionNode.rmw) [pexpr.enc e, pexpr.enc e', pexpr.enc e'',
      pexpr.enc e''', memoryOrder.enc o, memoryOrder.enc o']
  | .fence o => node (tag% Core.ActionNode.fence) [memoryOrder.enc o]
  | .compareExchangeStrong e e' e'' e''' o o' => node (tag% Core.ActionNode.compareExchangeStrong) [pexpr.enc e,
      pexpr.enc e', pexpr.enc e'', pexpr.enc e''', memoryOrder.enc o, memoryOrder.enc o']
  | .compareExchangeWeak e e' e'' e''' o o' => node (tag% Core.ActionNode.compareExchangeWeak) [pexpr.enc e,
      pexpr.enc e', pexpr.enc e'', pexpr.enc e''', memoryOrder.enc o, memoryOrder.enc o']
  | .linuxFence o => node (tag% Core.ActionNode.linuxFence) [linuxMemoryOrder.enc o]
  | .linuxLoad e e' o => node (tag% Core.ActionNode.linuxLoad) [pexpr.enc e, pexpr.enc e', linuxMemoryOrder.enc o]
  | .linuxStore e e' e'' o =>
    node (tag% Core.ActionNode.linuxStore) [pexpr.enc e, pexpr.enc e', pexpr.enc e'', linuxMemoryOrder.enc o]
  | .linuxRmw e e' e'' o =>
    node (tag% Core.ActionNode.linuxRmw) [pexpr.enc e, pexpr.enc e', pexpr.enc e'', linuxMemoryOrder.enc o]

def actionNode : Codec ActionNode := ofAlts encodeActionNode
  [alt% Core.ActionNode.create (pexpr ⊗ pexpr ⊗ prefix_),
   alt% Core.ActionNode.createReadOnly (pexpr ⊗ pexpr ⊗ pexpr ⊗ prefix_),
   alt% Core.ActionNode.alloc (pexpr ⊗ pexpr ⊗ prefix_),
   alt% Core.ActionNode.kill (killKind ⊗ pexpr),
   alt% Core.ActionNode.store (boolean ⊗ pexpr ⊗ pexpr ⊗ pexpr ⊗ memoryOrder),
   alt% Core.ActionNode.load (pexpr ⊗ pexpr ⊗ memoryOrder),
   alt% Core.ActionNode.seqRmw (boolean ⊗ pexpr ⊗ pexpr ⊗ sym ⊗ pexpr),
   alt% Core.ActionNode.rmw (pexpr ⊗ pexpr ⊗ pexpr ⊗ pexpr ⊗ memoryOrder ⊗ memoryOrder),
   alt% Core.ActionNode.fence memoryOrder,
   alt% Core.ActionNode.compareExchangeStrong (pexpr ⊗ pexpr ⊗ pexpr ⊗ pexpr ⊗ memoryOrder ⊗ memoryOrder),
   alt% Core.ActionNode.compareExchangeWeak (pexpr ⊗ pexpr ⊗ pexpr ⊗ pexpr ⊗ memoryOrder ⊗ memoryOrder),
   alt% Core.ActionNode.linuxFence linuxMemoryOrder,
   alt% Core.ActionNode.linuxLoad (pexpr ⊗ pexpr ⊗ linuxMemoryOrder),
   alt% Core.ActionNode.linuxStore (pexpr ⊗ pexpr ⊗ pexpr ⊗ linuxMemoryOrder),
   alt% Core.ActionNode.linuxRmw (pexpr ⊗ pexpr ⊗ pexpr ⊗ linuxMemoryOrder)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeAction : Action → Tree
  | .mk l u a => node (tag% Core.Action.mk) [loc.enc l, unit.enc u, actionNode.enc a]

def action : Codec Action := ofAlts encodeAction
  [alt% Core.Action.mk (loc ⊗ unit ⊗ actionNode)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodePaction : Core.PolarizedAction M Unit Unit Sym → Tree
  | .mk p a => node (tag% Core.PolarizedAction.mk) [polarity.enc p, action.enc a]

def paction : Codec (Core.PolarizedAction M Unit Unit Sym) := ofAlts encodePaction
  [alt% Core.PolarizedAction.mk (polarity ⊗ action)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeDynAnnotation : DynAnnotation M → Tree
  | .neg n ns f => node (tag% Core.DynAnnotation.neg) [nat.enc n, (list nat).enc ns, empty.enc f]
  | .pos ns f => node (tag% Core.DynAnnotation.pos) [(list nat).enc ns, empty.enc f]

def dynAnnotation : Codec (DynAnnotation M) := ofAlts encodeDynAnnotation
  [alt% Core.DynAnnotation.neg (nat ⊗ list nat ⊗ empty),
   alt% Core.DynAnnotation.pos (list nat ⊗ empty)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodePassByValueOrPointer : PassBy → Tree
  | .pointer => node (tag% Core.PassBy.pointer) []
  | .value => node (tag% Core.PassBy.value) []

def passByValueOrPointer : Codec PassBy := ofLeaves encodePassByValueOrPointer
  [leafPair% Core.PassBy.pointer, leafPair% Core.PassBy.value] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

@[simp] theorem memOp_budget : memOp.budget = none := rfl
@[simp] theorem paction_budget : paction.budget = none := rfl
@[simp] theorem action_budget : action.budget = none := rfl
@[simp] theorem dynAnnotation_budget : dynAnnotation.budget = none := rfl
@[simp] theorem passByValueOrPointer_budget : passByValueOrPointer.budget = none := by
  simp [passByValueOrPointer]

/-! ## Effectful expressions -/

abbrev Expr := Core.Expr M Unit Unit Sym
abbrev ExprNode := Core.ExprNode M Unit Unit Sym

/-- The `Esave` parameters, `list ('sym * ((core_base_type * maybe (ctype *
pass_by_value_or_pointer)) * generic_pexpr))`. -/
def saveParams : Codec (List (Sym ×
    ((BaseType × Option (Ctype × PassBy)) × Pexpr))) :=
  list (tuple (sym ⊗ tuple (tuple (baseType ⊗ option (tuple (ctype ⊗ passByValueOrPointer)))
    ⊗ pexpr)))

@[simp] theorem saveParams_budget : saveParams.budget = none := by simp [saveParams]

/-- See the same instance for `Pexpr`. -/
local instance : SizeOf Int := instSizeOfDefault Int

mutual

def encodeExpr : Expr → Tree
  | .mk as e => node (tag% Core.Expr.mk) [(list annot).enc as, encodeExprNode e]

def encodeExprNode : ExprNode → Tree
  | .pure e => node (tag% Core.ExprNode.pure) [pexpr.enc e]
  | .memop o es => node (tag% Core.ExprNode.memop) [memOp.enc o, (list pexpr).enc es]
  | .action a => node (tag% Core.ExprNode.action) [paction.enc a]
  | .case_ e cs => node (tag% Core.ExprNode.case_) [pexpr.enc e, node "$list" (cs.map fun p =>
      node "$tuple" [pattern.enc p.1, encodeExpr p.2])]
  | .let_ p e x => node (tag% Core.ExprNode.let_) [pattern.enc p, pexpr.enc e, encodeExpr x]
  | .if_ e x y => node (tag% Core.ExprNode.if_) [pexpr.enc e, encodeExpr x, encodeExpr y]
  | .ccall u e e' es => node (tag% Core.ExprNode.ccall) [unit.enc u, pexpr.enc e, pexpr.enc e', (list pexpr).enc es]
  | .proc u n es => node (tag% Core.ExprNode.proc) [unit.enc u, name.enc n, (list pexpr).enc es]
  | .unseq xs => node (tag% Core.ExprNode.unseq) [node "$list" (xs.map encodeExpr)]
  | .wseq p x y => node (tag% Core.ExprNode.wseq) [pattern.enc p, encodeExpr x, encodeExpr y]
  | .sseq p x y => node (tag% Core.ExprNode.sseq) [pattern.enc p, encodeExpr x, encodeExpr y]
  | .bound x => node (tag% Core.ExprNode.bound) [encodeExpr x]
  | .nd xs => node (tag% Core.ExprNode.nd) [node "$list" (xs.map encodeExpr)]
  | .save (s, t) ps x =>
    node (tag% Core.ExprNode.save) [node "$tuple" [sym.enc s, baseType.enc t], saveParams.enc ps, encodeExpr x]
  | .run u s es => node (tag% Core.ExprNode.run) [unit.enc u, sym.enc s, (list pexpr).enc es]
  | .par xs => node (tag% Core.ExprNode.par) [node "$list" (xs.map encodeExpr)]
  | .wait t => node (tag% Core.ExprNode.wait) [nat.enc t]
  | .annot ds x => node (tag% Core.ExprNode.annot) [(list dynAnnotation).enc ds, encodeExpr x]
  | .excluded n a => node (tag% Core.ExprNode.excluded) [nat.enc n, action.enc a]
decreasing_by codec_decreasing

end

def exprNode (c : Codec Expr) (h : c.enc = encodeExpr) : Codec ExprNode :=
  let x := slot c encodeExpr h
  ofAlts encodeExprNode
  [alt% Core.ExprNode.pure pexpr,
   alt% Core.ExprNode.memop (memOp ⊗ list pexpr),
   alt% Core.ExprNode.action paction,
   alt% Core.ExprNode.case_ (pexpr ⊗ list (tuple (pattern ⊗ x))),
   alt% Core.ExprNode.let_ (pattern ⊗ pexpr ⊗ x),
   alt% Core.ExprNode.if_ (pexpr ⊗ x ⊗ x),
   alt% Core.ExprNode.ccall (unit ⊗ pexpr ⊗ pexpr ⊗ list pexpr),
   alt% Core.ExprNode.proc (unit ⊗ name ⊗ list pexpr),
   alt% Core.ExprNode.unseq (list x),
   alt% Core.ExprNode.wseq (pattern ⊗ x ⊗ x),
   alt% Core.ExprNode.sseq (pattern ⊗ x ⊗ x),
   alt% Core.ExprNode.bound x,
   alt% Core.ExprNode.nd (list x),
   alt% Core.ExprNode.save (tuple (sym ⊗ baseType) ⊗ saveParams ⊗ x),
   alt% Core.ExprNode.run (unit ⊗ sym ⊗ list pexpr),
   alt% Core.ExprNode.par (list x),
   alt% Core.ExprNode.wait nat,
   alt% Core.ExprNode.annot (list dynAnnotation ⊗ x),
   alt% Core.ExprNode.excluded (nat ⊗ action)]
  (by codec_nodup) (by codec_enc [encodeExprNode]) (by codec_cover)

def exprLayer : Layer Expr encodeExpr where
  build c h := ofAlts encodeExpr
    [alt% Core.Expr.mk (list annot ⊗ exprNode c h)]
    (by codec_nodup) (by codec_enc [encodeExpr]) (by codec_cover)
  build_enc _ _ := rfl
  guard c h k hk d hd := by simp [exprNode, hk]; omega

def expr : Codec Expr := fix encodeExpr exprLayer

@[simp] theorem expr_budget : expr.budget = none := rfl

/-! ## Files -/

/-- `list (Symbol.sym * core_base_type)`. -/
def params : Codec (List (Sym × BaseType)) := list (tuple (sym ⊗ baseType))

def encodeImplDecl : ImplDecl M Unit → Tree
  | .constant t e => node (tag% Core.ImplDecl.constant) [baseType.enc t, pexpr.enc e]
  | .function t ps e => node (tag% Core.ImplDecl.function) [baseType.enc t, params.enc ps, pexpr.enc e]

def implDecl : Codec (ImplDecl M Unit) := ofAlts encodeImplDecl
  [alt% Core.ImplDecl.constant (baseType ⊗ pexpr),
   alt% Core.ImplDecl.function (baseType ⊗ params ⊗ pexpr)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeFunMapDecl : FunDecl M Unit Unit → Tree
  | .function t ps e => node (tag% Core.FunDecl.function) [baseType.enc t, params.enc ps, pexpr.enc e]
  | .procedure l m t ps x => node (tag% Core.FunDecl.procedure) [loc.enc l, (option nat).enc m, baseType.enc t,
      params.enc ps, expr.enc x]
  | .procedureDecl l t ts => node (tag% Core.FunDecl.procedureDecl) [loc.enc l, baseType.enc t, (list baseType).enc ts]
  | .builtinDecl l t ts =>
    node (tag% Core.FunDecl.builtinDecl) [loc.enc l, baseType.enc t, (list baseType).enc ts]

def funDecl : Codec (FunDecl M Unit Unit) := ofAlts encodeFunMapDecl
  [alt% Core.FunDecl.function (baseType ⊗ params ⊗ pexpr),
   alt% Core.FunDecl.procedure (loc ⊗ option nat ⊗ baseType ⊗ params ⊗ expr),
   alt% Core.FunDecl.procedureDecl (loc ⊗ baseType ⊗ list baseType),
   alt% Core.FunDecl.builtinDecl (loc ⊗ baseType ⊗ list baseType)]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeLinkingKind : LinkingKind → Tree
  | .none => node (tag% Core.LinkingKind.none) []
  | .tentative s => node (tag% Core.LinkingKind.tentative) [sym.enc s]
  | .normal s => node (tag% Core.LinkingKind.normal) [sym.enc s]

def linkingKind : Codec LinkingKind := ofAlts encodeLinkingKind
  [leaf% Core.LinkingKind.none, alt% Core.LinkingKind.tentative sym, alt% Core.LinkingKind.normal sym]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeGlobs : Global M Unit Unit → Tree
  | .definition (b, t) x => node (tag% Core.Global.definition) [node "$tuple" [baseType.enc b, ctype.enc t], expr.enc x]
  | .declaration (b, t) => node (tag% Core.Global.declaration) [node "$tuple" [baseType.enc b, ctype.enc t]]

def global : Codec (Global M Unit Unit) := ofAlts encodeGlobs
  [alt% Core.Global.definition (tuple (baseType ⊗ ctype) ⊗ expr),
   alt% Core.Global.declaration (tuple (baseType ⊗ ctype))]
  (by codec_nodup) (by codec_enc) (by codec_cover)

def encodeCallingConvention : CallingConvention → Tree
  | .normal => node (tag% Core.CallingConvention.normal) []
  | .innerArg => node (tag% Core.CallingConvention.innerArg) []

def callingConvention : Codec CallingConvention := ofLeaves encodeCallingConvention
  [leafPair% Core.CallingConvention.normal, leafPair% Core.CallingConvention.innerArg] []
  (by decide +kernel) (by decide +kernel) (by codec_enc) (by codec_leaf_cover)

/-- Ordered bindings retain the wire keys' descriptions and locations. Semantic
`Map` equality discards those representatives, so a codec of `Core.File` alone
cannot satisfy the tree canonicity law. Only this file boundary stores bindings;
all payloads are the ordinary Core syntax. -/
structure FileBindings where
  main : Option Sym
  callingConvention : CallingConvention
  tagDefs : List (Sym × (Loc × TagDefinition))
  stdlib : List (Sym × FunDecl M Unit Unit)
  impl : List (ImplementationConstant × ImplDecl M Unit)
  globs : List (Sym × Global M Unit Unit)
  funs : List (Sym × FunDecl M Unit Unit)
  extern : List (Identifier × (List Sym × LinkingKind))
  funInfo : List (Sym × (Loc × Attributes × Ctype × List (Option Sym × Ctype) × Bool × Bool))
  loopAttributes : List (Nat × LoopAttribute)
  visibleObjects : List (Nat × List (Sym × Ctype))

/-- Interpret every wire map with Lem's key equality and last-binding-wins
`ofList`. The document parser checks strict ordering before exposing a file. -/
def FileBindings.toFile (f : FileBindings) : Core.File M Unit Unit :=
  ⟨f.main, f.callingConvention, Map.ofList f.tagDefs, Map.ofList f.stdlib,
    Map.ofList f.impl, f.globs, Map.ofList f.funs, Map.ofList f.extern,
    Map.ofList f.funInfo, Map.ofList f.loopAttributes, Map.ofList f.visibleObjects⟩


/-- `map Symbol.sym (Loc.t * attributes * ctype * list (maybe sym * ctype) * bool * bool)`. -/
def funInfo : Codec (List (Sym × (Loc × Attributes × Ctype ×
    List (Option Sym × Ctype) × Bool × Bool))) :=
  map sym (tuple (loc ⊗ attributes ⊗ ctype ⊗ list (tuple (option sym ⊗ ctype)) ⊗ boolean ⊗ boolean))

def encodeFileBindings : FileBindings → Tree
  | ⟨m, cc, td, sl, im, gl, fs, ex, fi, la, vo⟩ => node (recordTag% Core.File) [(option sym).enc m,
      callingConvention.enc cc, (map sym (tuple (loc ⊗ tagDefinition))).enc td,
      (map sym funDecl).enc sl, (map implementationConstant implDecl).enc im,
      (list (tuple (sym ⊗ global))).enc gl, (map sym funDecl).enc fs,
      (map identifier (tuple (list sym ⊗ linkingKind))).enc ex, funInfo.enc fi,
      (map nat loopAttribute).enc la, (map nat (list (tuple (sym ⊗ ctype)))).enc vo]

-- The wire tag names `Core.File`, but the retained lists construct `FileBindings`.
-- This boundary representation has no entry of its own in `Names`.
def fileBindings : Codec FileBindings := ofAlts encodeFileBindings
  [ctorAlt% FileBindings.mk (recordTag% Core.File) (option sym ⊗ callingConvention ⊗ map sym (tuple (loc ⊗ tagDefinition)) ⊗
      map sym funDecl ⊗ map implementationConstant implDecl ⊗ list (tuple (sym ⊗ global)) ⊗
      map sym funDecl ⊗ map identifier (tuple (list sym ⊗ linkingKind)) ⊗ funInfo ⊗
      map nat loopAttribute ⊗ map nat (list (tuple (sym ⊗ ctype))))]
  (by codec_nodup) (by codec_enc) (by codec_cover)

/-! ## Documents -/

/-- A version 1 document: the Cerberus commit, the implementation file, and the
linked Core file. -/
structure Document where
  commit : String
  implementation : String
  bindings : FileBindings
  file : Core.File M Unit Unit
  /-- The semantic maps come from the retained wire bindings. -/
  file_eq : file = bindings.toFile
  /-- Version 2 transports the frontend's enum registration results. Version 1
  has no registry, retaining its exact canonical bytes. -/
  enumBindings : Option (List (Sym × IntegerType)) := none

def encodeDocument : Document → Tree
  | ⟨c, i, f, _, _, none⟩ => node "$document" [.atom "1", str.enc c, str.enc i, fileBindings.enc f]
  | ⟨c, i, f, _, _, some enums⟩ => node "$document_enums"
      [.atom "2", str.enc c, str.enc i, fileBindings.enc f, (list (tuple (sym ⊗ integerType))).enc enums]

-- These document envelopes are wire-only forms. Decoding reconstructs both
-- the semantic maps and their dependent equality proof. The enum payload uses
-- the maintained symbol and integer-type codecs, without a second tag table.
def document : Codec Document := ofAlts encodeDocument
  [alt "$document" (lit (.atom "1") ⊗ str ⊗ str ⊗ fileBindings)
    (fun (_, c, i, f) => ⟨c, i, f, f.toFile, rfl, none⟩),
   alt "$document_enums" (lit (.atom "2") ⊗ str ⊗ str ⊗ fileBindings ⊗ list (tuple (sym ⊗ integerType)))
    (fun (_, c, i, f, enums) => ⟨c, i, f, f.toFile, rfl, some enums⟩)]
  (by codec_nodup) (by codec_enc)
  (by
    rintro ⟨c, i, f, semantic, h, enums⟩
    cases h
    cases enums with
    | none => exact Alt.exists_head ((), c, i, f) rfl
    | some enums => exact Alt.exists_tail (Alt.exists_head ((), c, i, f, enums) rfl))

example : polarity.dec (node "Pos" []) = some Core.Polarity.pos := rfl
example : polarity.dec (node "Neg" []) = some Core.Polarity.neg := rfl
example : memoryOrder.dec (node "Acquire" []) = some MemoryOrder.acquire := rfl
example : memoryOrder.dec (node "Release" []) = some MemoryOrder.release := rfl
example : linuxMemoryOrder.dec (node "LAcquire" []) = some LinuxMemoryOrder.acquire := rfl
example : linuxMemoryOrder.dec (node "LRelease" []) = some LinuxMemoryOrder.release := rfl

end Silmaril.Cerberus.Codec
