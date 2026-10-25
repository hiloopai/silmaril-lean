module

public import Silmaril.Wasm.Binaryen.InstrUtil
public import Silmaril.Wasm.Validation.Modules
public import Silmaril.Wasm.Binaryen.TypingInv

@[expose] public section

/-! # Typing by lowering (layer D)

A sequence of trees is well typed exactly when its lowering is, under Core 3.0's
own judgement (`Validation.InstrsOk`), and a module is valid exactly when its
lowering is (`Validation.ModuleOk`). There is no second typing system to keep in
sync: refined `br_if` typing and every subtyping rule come from Core 3.0.

`infer` is the algorithmic part the passes need: the result types of a closed
tree, or `bot` when the tree never falls through (Binaryen's `unreachable`
type). `BExpr.isBot` is the syntactic bottom check DCE uses
(`Binaryen/Pass/DCE.lean`); `isBot_sound` (`Binaryen/Effects.lean`) says it is
semantically right, and `infer_bot` that it is typable at any result type.
-/

namespace Silmaril.Wasm.Binaryen

open Validation

/-- `es` has instruction type `it` in context `C`: its lowering does. -/
def SeqOk (C : Context) (es : List BExpr) (it : InstrType) : Prop :=
  InstrsOk C (BExpr.lowerList es) it

/-- A layer-D module is valid when its lowering is. -/
def BModule.Ok (m : BModule) : Prop := ∃ t, ModuleOk m.lower t

/-- Inference result: the values a closed tree leaves, or bottom. -/
inductive Out where
  | vals (ts : List CValType)
  | bot

/-- Flat instructions that never fall through (Binaryen type `unreachable`). -/
def botInstr : Instr → Bool
  | .unreachable | .br _ | .brTable _ _ | .return_ | .throw _ | .throwRef
  | .returnCall _ | .returnCallRef _ | .returnCallIndirect _ _ => true
  | _ => false

/-- Result types of a flat instruction whose operands are supplied (profile
fragment); `none` when not inferable from the context alone. -/
def flatResults (C : Context) : Instr → Option (List CValType)
  | .intConst t _ | .intUnOp t _ | .intBinOp t _ => some [.num (.int t)]
  | .intTestOp _ _ | .intRelOp _ _ => some [.num (.int .i32)]
  | .localGet x | .localTee x => (C.locals[x.toNat]?).map fun lt => [lt.type]
  | .globalGet g => (C.globals[g.toNat]?).map fun gt => [gt.type]
  | .localSet _ | .globalSet _ | .drop | .nop => some []
  | .brIf l => C.labels[l.toNat]?
  | .call f => (C.funcs[f.toNat]? >>= DefType.funcType?).map Prod.snd
  | _ => none

/-- The results of a block type in context `C`. -/
def blockResults (C : Context) : BlockType → Option (List CValType)
  | .empty => some []
  | .value t => some [C.closeVal t]
  | .typeIdx x => (C.type? x >>= DefType.funcType?).map Prod.snd

mutual
/-- Infer the results of one tree whose operands are all children. -/
def infer (C : Context) : BExpr → Option Out
  | .op i args => do
      match ← inferList C args with
      | .bot => some .bot
      | .vals _ => if botInstr i then some .bot else (flatResults C i).map Out.vals
  | .block bt _ => (blockResults C bt).map Out.vals
  | .loop bt _ => (blockResults C bt).map Out.vals
  | .if_ bt c _ _ => do
      match ← inferList C c with
      | .bot => some .bot
      | .vals _ => (blockResults C bt).map Out.vals
  | .tryTable bt _ _ => (blockResults C bt).map Out.vals
/-- Infer a sequence: bottom as soon as an element is bottom; otherwise the
concatenation of results (operands of later elements are their own children). -/
def inferList (C : Context) : List BExpr → Option Out
  | [] => some (.vals [])
  | e :: es => do
      match ← infer C e with
      | .bot => some .bot
      | .vals ts =>
        match ← inferList C es with
        | .bot => some .bot
        | .vals us => some (.vals (ts ++ us))
end

mutual
/-- **Syntactic bottom.** The tree never falls through: it traps, branches,
returns, or diverges on every path (Binaryen's `unreachable` type, as computed
by `ReFinalize`, `src/ir/ReFinalize.cpp`). A block is bottom when its body is and
nothing targets its label. -/
def BExpr.isBot : BExpr → Bool
  | .op i args => BExpr.listBot args || botInstr i
  | .block _ body => BExpr.listBot body && !(BExpr.labelsList body).contains 0
  | .loop _ body => BExpr.listBot body
  | .if_ _ c t e => BExpr.listBot c || (BExpr.listBot t && BExpr.listBot e &&
      !(BExpr.labelsList t).contains 0 && !(BExpr.labelsList e).contains 0)
  | .tryTable .. => false
/-- Some element of the list is bottom. -/
def BExpr.listBot : List BExpr → Bool
  | [] => false
  | e :: es => BExpr.isBot e || BExpr.listBot es
end

/-! ## Saturation and stack-polymorphic bottom

`infer` reads the results of an `op` node off its operator alone, so it is only
meaningful when every node's children supply exactly the operator's operands
(and blocks take no parameters from earlier siblings). `saturated` is that
side condition; without it `infer_sound` fails (`infer_sound_unsaturated`). -/

/-- Operand count of the flat instructions `flatResults` covers. -/
def flatArity (C : Context) : Instr → Option Nat
  | .intConst _ _ | .localGet _ | .globalGet _ | .nop => some 0
  | .intUnOp _ _ | .intTestOp _ _ | .localSet _ | .localTee _ | .globalSet _ | .drop => some 1
  | .intBinOp _ _ | .intRelOp _ _ => some 2
  | .brIf l => (C.labels[l.toNat]?).map (·.length + 1)
  | .call f => (C.funcs[f.toNat]? >>= DefType.funcType?).map (·.1.length)
  | _ => none

/-- The parameter count of a block type in context `C`. -/
def blockParams (C : Context) : BlockType → Option Nat
  | .empty | .value _ => some 0
  | .typeIdx x => (C.type? x >>= DefType.funcType?).map (·.1.length)

mutual
/-- Every node whose results `infer` computes from its operator gets exactly that
operator's operands from its children; structured nodes take no parameters. -/
def BExpr.saturated (C : Context) : BExpr → Bool
  | .op i args => BExpr.saturatedList C args && (botInstr i ||
      match inferList C args with
      | some (.vals vs) => flatArity C i == some vs.length
      | _ => true)
  | .block bt _ => blockParams C bt == some 0
  | .loop bt _ => blockParams C bt == some 0
  | .if_ bt c _ _ => BExpr.saturatedList C c &&
      match inferList C c with
      | some (.vals vs) => (blockParams C bt).map (· + 1) == some vs.length
      | _ => true
  | .tryTable bt _ _ => blockParams C bt == some 0
/-- `saturated` on every element of a list. -/
def BExpr.saturatedList (C : Context) : List BExpr → Bool
  | [] => true
  | e :: es => BExpr.saturated C e && BExpr.saturatedList C es
end

/-- **Stack-polymorphic bottom.** The tree's own operator never falls through, so
its lowering ends in an instruction of arbitrary result type. Core 3.0's block
types are fixed, so a `block`/`loop`/`if` whose body is bottom is *not* typable at
every result type (`infer_bot_block`), and neither is an operator applied to a
bottom operand; `infer_bot` needs this stronger condition. -/
def BExpr.polyBot : BExpr → Bool
  | .op i _ => botInstr i
  | _ => false

/-! ## Inversion of `infer` -/

theorem infer_op_vals {C : Context} {i : Instr} {args : List BExpr} {ts : List CValType}
    (h : infer C (.op i args) = some (.vals ts)) :
    ∃ vs, inferList C args = some (.vals vs) ∧ botInstr i = false ∧
      flatResults C i = some ts := by
  simp only [infer] at h
  cases hl : inferList C args with
  | none => simp [hl] at h
  | some o =>
    cases o with
    | bot => simp [hl] at h
    | vals vs =>
      cases hb : botInstr i with
      | true => simp [hl, hb] at h
      | false =>
        simp only [hl, hb] at h
        simp at h
        exact ⟨vs, rfl, rfl, h⟩

theorem infer_if_vals {C : Context} {bt : BlockType} {c t e : List BExpr} {ts : List CValType}
    (h : infer C (.if_ bt c t e) = some (.vals ts)) :
    ∃ vs, inferList C c = some (.vals vs) ∧ blockResults C bt = some ts := by
  simp only [infer] at h
  cases hl : inferList C c with
  | none => simp [hl] at h
  | some o =>
    cases o with
    | bot => simp [hl] at h
    | vals vs =>
      simp only [hl] at h
      simp at h
      exact ⟨vs, rfl, h⟩

theorem inferList_cons_vals {C : Context} {e : BExpr} {es : List BExpr} {ts : List CValType}
    (h : inferList C (e :: es) = some (.vals ts)) :
    ∃ a b, infer C e = some (.vals a) ∧ inferList C es = some (.vals b) ∧ ts = a ++ b := by
  simp only [inferList] at h
  cases he : infer C e with
  | none => simp [he] at h
  | some o =>
    cases o with
    | bot => simp [he] at h
    | vals a =>
      cases hl : inferList C es with
      | none => simp [he, hl] at h
      | some o' =>
        cases o' with
        | bot => simp [he, hl] at h
        | vals b =>
          simp only [he, hl] at h
          simp at h
          exact ⟨a, b, rfl, rfl, h.symm⟩

/-! ## Typing inversion for the inferable instructions -/

theorem blockType_inv {C D : Context} (hT : D.toTypeCtx = C.toTypeCtx) {bt : BlockType}
    {t₁ t₂ : List CValType} (h : BlockTypeOk D bt t₁ t₂) :
    blockResults C bt = some t₂ ∧ blockParams C bt = some t₁.length := by
  have hty : D.types = C.types := congrArg TypeCtx.types hT
  cases h with
  | empty => simp [blockResults, blockParams]
  | @value t _ =>
    have : D.closeVal t = C.closeVal t := by unfold Context.closeVal; rw [hty]
    simp [blockResults, blockParams, this]
  | @typeIdx x d ps rs hd he =>
    have hd' : C.type? x = some d := by rw [← hd]; unfold Context.type?; rw [hty]
    have hf : d.funcType? = some (ps.toList, rs.toList) := by
      simp [DefType.funcType?, Expand.iff.mp he]
    simp [blockResults, blockParams, hd', hf]

theorem local_type_eq {C D : Context}
    (hloc : ∀ y : Nat, (D.locals[y]?).map LocalType.type = (C.locals[y]?).map LocalType.type)
    {x : Nat} {lt : LocalType} (h : D.locals[x]? = some lt) :
    (C.locals[x]?).map (fun l => [l.type]) = some [lt.type] := by
  have := hloc x
  rw [h] at this
  cases hc : C.locals[x]? with
  | none => rw [hc] at this; simp at this
  | some c => rw [hc] at this; simp_all

theorem flat_inv {C D : Context}
    (hloc : ∀ y : Nat, (D.locals[y]?).map LocalType.type = (C.locals[y]?).map LocalType.type)
    (hglob : D.globals = C.globals) (hlab : D.labels = C.labels) (hfun : D.funcs = C.funcs)
    {i : Instr} {it₀ : InstrType} {r : List CValType} {n : Nat}
    (hi : InstrOk D i it₀) (hr : flatResults C i = some r) (hn : flatArity C i = some n) :
    it₀.params.length = n ∧ it₀.results = r := by
  cases hi with
  | parametric h => cases h <;> simp_all [flatResults, flatArity]
  | numeric h => cases h <;> simp_all [flatResults, flatArity, Ty.i32] <;> (subst_vars; simp)
  | «variable» h =>
    cases h with
    | localGet h =>
      have hl := local_type_eq hloc h
      simp only [flatResults, flatArity] at hr hn
      rw [hl] at hr
      simp only [Option.some.injEq] at hr hn
      subst hr hn
      simp
    | localSet => simp_all [flatResults, flatArity]
    | localTee h =>
      have hl := local_type_eq hloc h
      simp only [flatResults, flatArity] at hr hn
      rw [hl] at hr
      simp only [Option.some.injEq] at hr hn
      subst hr hn
      simp
    | globalGet h =>
      rw [hglob] at h
      simp_all [flatResults, flatArity]
    | globalSet => simp_all [flatResults, flatArity]
  | brIf hl =>
    rw [hlab] at hl
    simp_all [flatResults, flatArity]
  | call hf he =>
    rw [hfun] at hf
    have hft := Expand.iff.mp he
    simp_all [flatResults, flatArity, DefType.funcType?]
  | vector h => cases h <;> simp [flatResults] at hr
  | memory h => cases h <;> simp [flatResults] at hr
  | table h => cases h <;> simp [flatResults] at hr
  | reference h => cases h <;> simp [flatResults] at hr
  | block | loop | if_ | br | brTable | brOnNull | brOnNonNull | brOnCast | brOnCastFail
  | callRef | callIndirect | return_ | returnCall | returnCallRef | returnCallIndirect | throw
  | throwRef | tryTable => simp [flatResults] at hr

/-! ## Principality of inference -/

mutual
theorem principal_tree {C : Context} (hC : C.Wf) :
    ∀ (e : BExpr) (ys : List Nat) (ts : List CValType), e.saturated C = true →
      infer C e = some (.vals ts) → Principal (C.initLocals ys) e.lower ts
  | .op i args, ys, ts, hs, hi => by
    obtain ⟨vs, hl, hb, hr⟩ := infer_op_vals hi
    simp only [BExpr.saturated, hl, hb, Bool.and_eq_true, Bool.false_or, beq_iff_eq] at hs
    rw [BExpr.lower_op]
    refine Principal.snoc (hC.initLocals ys) (principal_list hC args ys vs hs.1 hl) ?_
    intro ya it₀ hit
    rw [← Context.initLocals_append] at hit
    exact flat_inv (initLocals_localType C _) (initLocals_globals C _)
      (Context.initLocals_labels C _) (initLocals_funcs C _) hit hr hs.2
  | .block bt body, ys, ts, hs, hi => by
    simp only [infer, Option.map_eq_some_iff, Out.vals.injEq] at hi
    obtain ⟨_, hr, rfl⟩ := hi
    simp only [BExpr.saturated, beq_iff_eq] at hs
    show Principal _ ([] ++ [_]) _
    refine Principal.snoc (hC.initLocals ys) (Principal.nil (hC.initLocals ys)) ?_
    intro ya it₀ hit
    obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_block_inv hit
    obtain ⟨h1, h2⟩ := blockType_inv (C := C) (by simp) hbt
    rw [hr] at h1; rw [hs] at h2
    simp_all
  | .loop bt body, ys, ts, hs, hi => by
    simp only [infer, Option.map_eq_some_iff, Out.vals.injEq] at hi
    obtain ⟨_, hr, rfl⟩ := hi
    simp only [BExpr.saturated, beq_iff_eq] at hs
    show Principal _ ([] ++ [_]) _
    refine Principal.snoc (hC.initLocals ys) (Principal.nil (hC.initLocals ys)) ?_
    intro ya it₀ hit
    obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_loop_inv hit
    obtain ⟨h1, h2⟩ := blockType_inv (C := C) (by simp) hbt
    rw [hr] at h1; rw [hs] at h2
    simp_all
  | .tryTable bt cs body, ys, ts, hs, hi => by
    simp only [infer, Option.map_eq_some_iff, Out.vals.injEq] at hi
    obtain ⟨_, hr, rfl⟩ := hi
    simp only [BExpr.saturated, beq_iff_eq] at hs
    show Principal _ ([] ++ [_]) _
    refine Principal.snoc (hC.initLocals ys) (Principal.nil (hC.initLocals ys)) ?_
    intro ya it₀ hit
    obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_tryTable_inv hit
    obtain ⟨h1, h2⟩ := blockType_inv (C := C) (by simp) hbt
    rw [hr] at h1; rw [hs] at h2
    simp_all
  | .if_ bt c t e, ys, ts, hs, hi => by
    obtain ⟨vs, hl, hr⟩ := infer_if_vals hi
    simp only [BExpr.saturated, hl, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [BExpr.lower]
    refine Principal.snoc (hC.initLocals ys) (principal_list hC c ys vs hs.1 hl) ?_
    intro ya it₀ hit
    obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_if_inv hit
    obtain ⟨h1, h2⟩ := blockType_inv (C := C) (by simp) hbt
    rw [hr] at h1
    have h3 := hs.2
    rw [h2] at h3
    simp only [Option.map_some, Option.some.injEq] at h3
    simp only [Option.some.injEq] at h1
    simp [h1, ← h3]
theorem principal_list {C : Context} (hC : C.Wf) :
    ∀ (es : List BExpr) (ys : List Nat) (ts : List CValType), BExpr.saturatedList C es = true →
      inferList C es = some (.vals ts) → Principal (C.initLocals ys) (BExpr.lowerList es) ts
  | [], ys, ts, _, hi => by
    simp only [inferList, Option.some.injEq, Out.vals.injEq] at hi
    subst hi
    exact Principal.nil (hC.initLocals ys)
  | e :: es, ys, ts, hs, hi => by
    obtain ⟨a, b, ha, hb, rfl⟩ := inferList_cons_vals hi
    simp only [BExpr.saturatedList, Bool.and_eq_true] at hs
    rw [BExpr.lowerList_cons]
    refine Principal.append (hC.initLocals ys) (principal_tree hC e ys a hs.1 ha) ?_
    intro ya
    rw [← Context.initLocals_append]
    exact principal_list hC es (ys ++ ya) b hs.2 hb
end

/-! ## Inference theorems -/

/-- **Soundness of inference.** A closed tree typed at some result type is typed at
the inferred one. -/
-- FLAG(statement-change): added `hC : C.Wf` (typing inversion needs a well-formed
-- context) and `hs : e.saturated C = true` (`infer` ignores surplus operands, so the
-- original statement is false: `infer_sound_unsaturated`).
theorem infer_sound {C : Context} {e : BExpr} {xs : List Nat} {rs ts : List CValType}
    (h : SeqOk C [e] ⟨[], xs, rs⟩) (hi : infer C e = some (.vals ts))
    (hC : C.Wf) (hs : e.saturated C = true) :
    ∃ xs', SeqOk C [e] ⟨[], xs', ts⟩ := by
  have hg := principal_tree hC e [] ts hs hi
  rw [Context.initLocals_nil] at hg
  unfold SeqOk at h ⊢
  rw [BExpr.lowerList_singleton] at h ⊢
  obtain ⟨-, xs', h', -⟩ := hg [] xs rs h
  exact ⟨xs', h'⟩

/-- **Principality.** The inferred type is a subtype of every result type. -/
-- FLAG(statement-change): added `hC : C.Wf` and `hs : e.saturated C = true`; the
-- original statement is false (`infer_principal_unsaturated`).
theorem infer_principal {C : Context} {e : BExpr} {xs : List Nat} {rs ts : List CValType}
    (h : SeqOk C [e] ⟨[], xs, rs⟩) (hi : infer C e = some (.vals ts))
    (hC : C.Wf) (hs : e.saturated C = true) :
    ∃ xs', InstrTypeSub C ⟨[], xs', ts⟩ ⟨[], xs, rs⟩ := by
  have hg := principal_tree hC e [] ts hs hi
  rw [Context.initLocals_nil] at hg
  unfold SeqOk at h
  rw [BExpr.lowerList_singleton] at h
  obtain ⟨hsub, -⟩ := hg [] xs rs h
  exact ⟨xs, List.Forall₂.nil, by simpa using hsub, fun _ hx hn => absurd hx hn⟩

theorem botInstr_retype {D : Context} {i : Instr} (hb : botInstr i = true)
    {it₀ : InstrType} (hi : InstrOk D i it₀) {fr rs' : List CValType}
    (hfr : ResultOk D.toTypeCtx fr) (hrs : ResultOk D.toTypeCtx rs') :
    it₀.inits = [] ∧ InstrOk D i (.plain (fr ++ it₀.params) rs') := by
  cases hi with
  | parametric h =>
    cases h with
    | unreachable hok =>
      exact ⟨rfl, .parametric (.unreachable ⟨ResultOk.append hfr hok.1, hrs, by simp⟩)⟩
    | nop | drop | selectExpl | selectImpl => simp [botInstr] at hb
  | br hl hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.br (t₁ := fr ++ _) (t₂ := rs') hl
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | brTable hls hl' hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.brTable (t₁ := fr ++ _) (t₂ := rs') hls hl'
      ⟨by simpa [List.append_assoc] using ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | return_ hr hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.return_ (t₁ := fr ++ _) (t₂ := rs') hr
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | throw hx he hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.throw (t₁ := fr ++ _) (t₂ := rs') hx he
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | throwRef hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.throwRef (C := D) (t₁ := fr ++ _) (t₂ := rs')
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | returnCall hf he hr hs hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.returnCall (t₃ := fr ++ _) (t₄ := rs') hf he hr hs
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | returnCallRef hd he hr hs hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.returnCallRef (t₃ := fr ++ _) (t₄ := rs') hd he hr hs
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | returnCallIndirect ht hs hd he hr hrs' hok =>
    refine ⟨rfl, ?_⟩
    have := InstrOk.returnCallIndirect (t₃ := fr ++ _) (t₄ := rs') ht hs hd he hr hrs'
      ⟨ResultOk.append hfr hok.1, hrs, by simp⟩
    simpa [List.append_assoc] using this
  | numeric h => cases h <;> simp [botInstr] at hb
  | vector h => cases h <;> simp [botInstr] at hb
  | «variable» h => cases h <;> simp [botInstr] at hb
  | memory h => cases h <;> simp [botInstr] at hb
  | table h => cases h <;> simp [botInstr] at hb
  | reference h => cases h <;> simp [botInstr] at hb
  | block | loop | if_ | brIf | brOnNull | brOnNonNull | brOnCast | brOnCastFail | call
  | callRef | callIndirect | tryTable => simp [botInstr] at hb

/-- A bottom tree is typable at every well-formed result type (Core's stack
polymorphism after `unreachable`/`br`/`return`). This keeps DCE type-preserving. -/
-- FLAG(statement-change): added `hC : C.Wf` and `hp : e.polyBot = true`. With only
-- `isBot`, the statement is false: a `block` with a bottom body keeps its declared
-- block type in Core 3.0 (`infer_bot_block`).
theorem infer_bot {C : Context} {e : BExpr} {ps rs rs' : List CValType} {xs : List Nat}
    (_hb : e.isBot = true) (h : SeqOk C [e] ⟨ps, xs, rs⟩) (hok : InstrTypeOk C ⟨ps, xs, rs'⟩)
    (hC : C.Wf) (hp : e.polyBot = true) :
    SeqOk C [e] ⟨ps, xs, rs'⟩ := by
  cases e with
  | op i args =>
    simp only [BExpr.polyBot] at hp
    unfold SeqOk at h ⊢
    rw [BExpr.lowerList_singleton, BExpr.lower_op] at h ⊢
    obtain ⟨m, ya, yb, ha, hb', hL⟩ := InstrsOk.split hC h rfl
    have hDa := hC.initLocals ya
    obtain ⟨fr, it₀, hfr, hi, hsub⟩ := single_inv_ok hDa hb'
    have rm : ResultOk C.toTypeCtx m := (InstrsOk.regular hC ha).2.1
    have rr : ResultOk C.toTypeCtx rs' := hok.2.1
    obtain ⟨hinit, hi'⟩ := botInstr_retype hp hi (fr := fr) (rs' := rs') (by simpa using hfr)
      (by simpa using rr)
    have hj : InstrsOk (C.initLocals ya) [i] ⟨m, [], rs'⟩ :=
      .sub (.instr hi') ⟨by simpa using hsub.1, ResultSub.refl _ _, fun _ h _ => by simp at h⟩
        ⟨by simpa using rm, by simpa using rr, by simp⟩
    have hall := InstrsOk.append ha (InstrsOk.regular hC ha).2.2 hj
    refine .sub hall ⟨ResultSub.refl _ _, ResultSub.refl _ _, ?_⟩ hok
    intro x hx hn
    simp only [List.append_nil] at hn
    obtain ⟨lt, hlt⟩ := hok.2.2 x hx
    have h1 : (C.initLocals xs).locals[x]? = some ⟨.set, lt.type⟩ :=
      Context.initLocals_set_of_mem hx hlt
    have h2 := LocalsLe.set hL h1
    rw [Context.initLocals_append] at h2
    have hyb : (C.initLocals ya).initLocals yb = C.initLocals ya := by
      apply Context.initLocals_of_set
      intro y hy
      exact hsub.2.2 y hy (by simp [hinit])
    rw [hyb] at h2
    rcases Context.initLocals_set h2 with h3 | h3
    · exact absurd h3 hn
    · exact ⟨_, h3⟩
  | block => simp [BExpr.polyBot] at hp
  | loop => simp [BExpr.polyBot] at hp
  | if_ => simp [BExpr.polyBot] at hp
  | tryTable => simp [BExpr.polyBot] at hp

/-! ## The unrestricted statements are false

Witnesses in the empty context: `i32.const 0; nop` folded as `nop (i32.const 0)`
leaves an `i32` that `infer` (reading `nop`'s results) does not report, and
`block (unreachable)` is bottom but has the fixed type `[] → []`. -/

private def cexOp : BExpr := .op .nop [.op (.intConst .i32 0) []]

private def cexBlock : BExpr := .block .empty [.op .unreachable []]

private theorem tyOk_i32 : ResultOk ({} : Context).toTypeCtx [.num (.int .i32)] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  exact TyOk.num _

private theorem cexOp_typed : SeqOk {} [cexOp] ⟨[], [], [.num (.int .i32)]⟩ := by
  unfold SeqOk cexOp
  simp only [BExpr.lower_op, BExpr.lowerList_nil, List.nil_append,
    BExpr.lowerList_cons, List.append_nil, List.singleton_append]
  have hn : InstrsOk (({} : Context).initLocals []) [.nop]
      ⟨[.num (.int .i32)], [], [.num (.int .i32)]⟩ := by
    simpa using InstrsOk.frame (ts := [.num (.int .i32)])
      (InstrsOk.instr (C := {}) (InstrOk.parametric .nop)) tyOk_i32
  exact InstrsOk.cons (InstrOk.numeric (.intConst .i32 0)) (by simp) hn

private theorem cexOp_infer : infer {} cexOp = some (.vals []) := by
  simp [cexOp, infer, inferList, flatResults, botInstr]

private theorem cexOp_untyped (xs : List Nat) :
    ¬ InstrsOk {} [.intConst .i32 0, .nop] ⟨[], xs, []⟩ := by
  intro h
  obtain ⟨t₂, xs₁, xs₂, h₁, h₂⟩ :=
    InstrsOk.append_inv (is₁ := [.intConst .i32 0]) (is₂ := [.nop]) wf_emptyContext h
  obtain ⟨k, it₀, hi, e1, e2⟩ := single_len wf_emptyContext h₁
  obtain ⟨k', it₁, hi', e1', e2'⟩ := single_len (wf_emptyContext.initLocals xs₁) h₂
  rw [instrOk_intConst_inv hi] at e1 e2
  rw [instrOk_nop_inv hi'] at e1' e2'
  simp at e1 e2 e1' e2'
  omega

theorem infer_sound_unsaturated : ¬ ∀ (C : Context) (e : BExpr) (xs : List Nat)
    (rs ts : List CValType), SeqOk C [e] ⟨[], xs, rs⟩ → infer C e = some (.vals ts) →
      ∃ xs', SeqOk C [e] ⟨[], xs', ts⟩ := by
  intro H
  obtain ⟨xs', h⟩ := H {} cexOp [] _ _ cexOp_typed cexOp_infer
  apply cexOp_untyped xs'
  simpa [SeqOk, cexOp] using h

theorem infer_principal_unsaturated : ¬ ∀ (C : Context) (e : BExpr) (xs : List Nat)
    (rs ts : List CValType), SeqOk C [e] ⟨[], xs, rs⟩ → infer C e = some (.vals ts) →
      ∃ xs', InstrTypeSub C ⟨[], xs', ts⟩ ⟨[], xs, rs⟩ := by
  intro H
  obtain ⟨xs', h⟩ := H {} cexOp [] _ _ cexOp_typed cexOp_infer
  have := List.Forall₂.length_eq h.2.1
  simp at this

private theorem cexBlock_isBot : cexBlock.isBot = true := by
  have : instrLabels .unreachable = [] := by rw [instrLabels.eq_def]
  simp [cexBlock, BExpr.isBot, BExpr.listBot, botInstr, BExpr.labelsList, instrsLabels, this]

theorem infer_bot_block : ¬ ∀ (C : Context) (e : BExpr) (ps rs rs' : List CValType)
    (xs : List Nat), e.isBot = true → SeqOk C [e] ⟨ps, xs, rs⟩ →
      InstrTypeOk C ⟨ps, xs, rs'⟩ → SeqOk C [e] ⟨ps, xs, rs'⟩ := by
  intro H
  have h : SeqOk {} [cexBlock] ⟨[], [], []⟩ := by
    unfold SeqOk cexBlock
    simp only [BExpr.lower, BExpr.lowerList, List.nil_append, List.append_nil]
    exact InstrsOk.instr (InstrOk.block .empty
      (InstrsOk.instr (InstrOk.parametric (.unreachable ⟨by simp [ResultOk], by simp [ResultOk],
        by simp⟩))))
  have hok : InstrTypeOk ({} : Context) ⟨[], [], [.num (.int .i32)]⟩ :=
    ⟨by simp [ResultOk], tyOk_i32, by simp⟩
  have h' := H {} cexBlock [] [] _ [] cexBlock_isBot h hok
  unfold SeqOk cexBlock at h'
  simp only [BExpr.lower, BExpr.lowerList, List.nil_append, List.append_nil] at h'
  obtain ⟨k, it₀, hi, e1, e2⟩ := single_len wf_emptyContext h'
  obtain ⟨t₁, t₂, hbt, rfl⟩ := instrOk_block_inv hi
  cases hbt
  simp at e1 e2
  omega

end Silmaril.Wasm.Binaryen
