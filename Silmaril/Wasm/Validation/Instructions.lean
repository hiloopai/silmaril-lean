module

public import Silmaril.Wasm.Validation.Instr.Parametric
public import Silmaril.Wasm.Validation.Instr.Numeric
public import Silmaril.Wasm.Validation.Instr.Vector
public import Silmaril.Wasm.Validation.Instr.Variable
public import Silmaril.Wasm.Validation.Instr.Memory
public import Silmaril.Wasm.Validation.Instr.Table
public import Silmaril.Wasm.Validation.Instr.Ref

@[expose] public section

/-! # Instruction typing (§2.3): `Instr_ok`, `Instrs_ok`, `Expr_ok`

`InstrOk`/`InstrsOk` are one mutual inductive. It contains every rule whose
premises mention instruction typing (block, loop, if, try_table) and every
control-transfer rule (branches, calls, tail calls, return, exceptions), fully
written out. Every *non-recursive* family is one delegating constructor to a
relation in its own file:

| constructor | relation | file |
|---|---|---|
| `parametric` | `ParametricInstrOk` | `Instr/Parametric.lean` |
| `numeric` | `NumericInstrOk` | `Instr/Numeric.lean` |
| `vector` | `VectorInstrOk` | `Instr/Vector.lean` |
| `variable` | `VariableInstrOk` | `Instr/Variable.lean` |
| `memory` | `MemoryInstrOk` | `Instr/Memory.lean` |
| `table` | `TableInstrOk` | `Instr/Table.lean` |
| `reference` | `RefInstrOk` | `Instr/Ref.lean` |

**`Instrs_ok` shape.** The spec's five rules `empty`, `instr`, `seq`, `sub`,
`frame` are the constructors `nil`, `instr`, `seq`, `sub`, `frame`. The extra
constructor `cons` (one instruction, then the rest under the context whose locals
the instruction initialised) is `seq ∘ instr`, kept for convenience.

A `nil`/`cons`-only presentation (without `instr`/`seq`) is *incomplete*: `cons`
types its head by `Instr_ok` with no frame, so e.g. `local.get 0; local.get 1;
i32.add` (whose second instruction must run under a frame) has no derivation.
Inversion through arbitrary splits is `InstrsOk.append_inv`/`InstrsOk.single_inv`
in `Instructions/Properties.lean`.

All types are closed (see `Validation/Context.lean`).
-/

namespace Silmaril.Wasm.Validation

/-- `$diffrt(rt_1, rt_2)`: the reference type left after a failed cast. -/
def Ty.diffrt : CRefType → CRefType → CRefType
  | .ref _ h₁, .ref true _ => .ref false h₁
  | r₁, .ref false _ => r₁

/-- `Blocktype_ok: C ⊢ blocktype : t_1* -> t_2*`. The spec's `_RESULT valtype?`
is the source `empty`/`value t`. -/
inductive BlockTypeOk (C : Context) : BlockType → List CValType → List CValType → Prop where
  /-- `Blocktype_ok/valtype` with no result. -/
  | empty : BlockTypeOk C .empty [] []
  /-- `Blocktype_ok/valtype` with one result. -/
  | value {t : ValType} (h : TyOk C.toTypeCtx (C.closeVal t)) :
      BlockTypeOk C (.value t) [] [C.closeVal t]
  /-- `Blocktype_ok/typeidx`. -/
  | typeIdx {x : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
      (hd : C.type? x = some d) (he : Expand d (.func ps rs)) :
      BlockTypeOk C (.typeIdx x) ps.toList rs.toList

/-- `Catch_ok`. -/
inductive CatchOk (C : Context) : Catch → Prop where
  /-- `Catch_ok/catch`. -/
  | catch_ {x : TagIdx} {l : LabelIdx} {d : DefType} {ts : Ty (.list .val)}
      {lt : List CValType}
      (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil))
      (hl : C.labels[l.toNat]? = some lt) (hs : ResultSub C.toTypeCtx ts.toList lt) :
      CatchOk C (.catch_ x l)
  /-- `Catch_ok/catch_ref`. -/
  | catchRef {x : TagIdx} {l : LabelIdx} {d : DefType} {ts : Ty (.list .val)}
      {lt : List CValType}
      (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil))
      (hl : C.labels[l.toNat]? = some lt)
      (hs : ResultSub C.toTypeCtx (ts.toList ++ [.refT false (.abs .exn)]) lt) :
      CatchOk C (.catchRef x l)
  /-- `Catch_ok/catch_all`. -/
  | catchAll {l : LabelIdx} {lt : List CValType}
      (hl : C.labels[l.toNat]? = some lt) (hs : ResultSub C.toTypeCtx [] lt) :
      CatchOk C (.catchAll l)
  /-- `Catch_ok/catch_all_ref`. -/
  | catchAllRef {l : LabelIdx} {lt : List CValType}
      (hl : C.labels[l.toNat]? = some lt)
      (hs : ResultSub C.toTypeCtx [.refT false (.abs .exn)] lt) :
      CatchOk C (.catchAllRef l)

mutual

/-- `Instr_ok: C ⊢ instr : instrtype`. -/
inductive InstrOk : Context → Instr → InstrType → Prop where
  /-- Parametric family (`nop`, `unreachable`, `drop`, `select`). -/
  | parametric {C : Context} {i : Instr} {it : InstrType} (h : ParametricInstrOk C i it) :
      InstrOk C i it
  /-- Numeric family. -/
  | numeric {C : Context} {i : Instr} {it : InstrType} (h : NumericInstrOk C i it) :
      InstrOk C i it
  /-- Vector family (including relaxed SIMD). -/
  | vector {C : Context} {i : Instr} {it : InstrType} (h : VectorInstrOk C i it) :
      InstrOk C i it
  /-- Local and global family. -/
  | variable {C : Context} {i : Instr} {it : InstrType} (h : VariableInstrOk C i it) :
      InstrOk C i it
  /-- Memory family. -/
  | memory {C : Context} {i : Instr} {it : InstrType} (h : MemoryInstrOk C i it) :
      InstrOk C i it
  /-- Table family. -/
  | table {C : Context} {i : Instr} {it : InstrType} (h : TableInstrOk C i it) :
      InstrOk C i it
  /-- Reference, i31, struct, array and extern family. -/
  | reference {C : Context} {i : Instr} {it : InstrType} (h : RefInstrOk C i it) :
      InstrOk C i it
  /-- `Instr_ok/block`. -/
  | block {C : Context} {bt : BlockType} {body : List Instr} {t₁ t₂ : List CValType}
      {xs : List Nat}
      (hbt : BlockTypeOk C bt t₁ t₂) (hb : InstrsOk (C.withLabel t₂) body ⟨t₁, xs, t₂⟩) :
      InstrOk C (.block bt body) (.plain t₁ t₂)
  /-- `Instr_ok/loop`. -/
  | loop {C : Context} {bt : BlockType} {body : List Instr} {t₁ t₂ : List CValType}
      {xs : List Nat}
      (hbt : BlockTypeOk C bt t₁ t₂) (hb : InstrsOk (C.withLabel t₁) body ⟨t₁, xs, t₂⟩) :
      InstrOk C (.loop bt body) (.plain t₁ t₂)
  /-- `Instr_ok/if`. -/
  | if_ {C : Context} {bt : BlockType} {b₁ b₂ : List Instr} {t₁ t₂ : List CValType}
      {xs₁ xs₂ : List Nat}
      (hbt : BlockTypeOk C bt t₁ t₂)
      (h₁ : InstrsOk (C.withLabel t₂) b₁ ⟨t₁, xs₁, t₂⟩)
      (h₂ : InstrsOk (C.withLabel t₂) b₂ ⟨t₁, xs₂, t₂⟩) :
      InstrOk C (.if_ bt b₁ b₂) (.plain (t₁ ++ [.i32]) t₂)
  /-- `Instr_ok/br`. -/
  | br {C : Context} {l : LabelIdx} {ts t₁ t₂ : List CValType}
      (hl : C.labels[l.toNat]? = some ts) (hok : InstrTypeOk C (.plain t₁ t₂)) :
      InstrOk C (.br l) (.plain (t₁ ++ ts) t₂)
  /-- `Instr_ok/br_if`. -/
  | brIf {C : Context} {l : LabelIdx} {ts : List CValType}
      (hl : C.labels[l.toNat]? = some ts) :
      InstrOk C (.brIf l) (.plain (ts ++ [.i32]) ts)
  /-- `Instr_ok/br_table`. -/
  | brTable {C : Context} {ls : List LabelIdx} {l' : LabelIdx} {ts t₁ t₂ : List CValType}
      (hls : ∀ l ∈ ls, ∃ lt, C.labels[l.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt)
      (hl' : ∃ lt, C.labels[l'.toNat]? = some lt ∧ ResultSub C.toTypeCtx ts lt)
      (hok : InstrTypeOk C (.plain (t₁ ++ ts ++ [.i32]) t₂)) :
      InstrOk C (.brTable ls l') (.plain (t₁ ++ ts ++ [.i32]) t₂)
  /-- `Instr_ok/br_on_null`. -/
  | brOnNull {C : Context} {l : LabelIdx} {ts : List CValType} {ht : CHeapType}
      (hl : C.labels[l.toNat]? = some ts) (hh : TyOk C.toTypeCtx ht) :
      InstrOk C (.brOnNull l) (.plain (ts ++ [.refT true ht]) (ts ++ [.refT false ht]))
  /-- `Instr_ok/br_on_non_null`. -/
  | brOnNonNull {C : Context} {l : LabelIdx} {ts : List CValType} {n : Bool} {ht : CHeapType}
      (hl : C.labels[l.toNat]? = some (ts ++ [.refT n ht])) :
      InstrOk C (.brOnNonNull l) (.plain (ts ++ [.refT true ht]) ts)
  /-- `Instr_ok/br_on_cast`. -/
  | brOnCast {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} {ts : List CValType}
      {rt : CRefType}
      (hl : C.labels[l.toNat]? = some (ts ++ [.refv rt]))
      (h₁ : TyOk C.toTypeCtx (C.closeRef rt₁)) (h₂ : TyOk C.toTypeCtx (C.closeRef rt₂))
      (h₂₁ : Sub C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁))
      (h₂l : Sub C.toTypeCtx (C.closeRef rt₂) rt) :
      InstrOk C (.brOnCast l rt₁ rt₂)
        (.plain (ts ++ [.refv (C.closeRef rt₁)])
          (ts ++ [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))]))
  /-- `Instr_ok/br_on_cast_fail`. -/
  | brOnCastFail {C : Context} {l : LabelIdx} {rt₁ rt₂ : RefType} {ts : List CValType}
      {rt : CRefType}
      (hl : C.labels[l.toNat]? = some (ts ++ [.refv rt]))
      (h₁ : TyOk C.toTypeCtx (C.closeRef rt₁)) (h₂ : TyOk C.toTypeCtx (C.closeRef rt₂))
      (h₂₁ : Sub C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁))
      (hdl : Sub C.toTypeCtx (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) rt) :
      InstrOk C (.brOnCastFail l rt₁ rt₂)
        (.plain (ts ++ [.refv (C.closeRef rt₁)]) (ts ++ [.refv (C.closeRef rt₂)]))
  /-- `Instr_ok/call`. -/
  | call {C : Context} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
      (hf : C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs)) :
      InstrOk C (.call x) (.plain ps.toList rs.toList)
  /-- `Instr_ok/call_ref`. -/
  | callRef {C : Context} {x : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
      (hd : C.type? x = some d) (he : Expand d (.func ps rs)) :
      InstrOk C (.callRef x) (.plain (ps.toList ++ [.refT true (.defHeap d)]) rs.toList)
  /-- `Instr_ok/call_indirect`. -/
  | callIndirect {C : Context} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
      {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)}
      (ht : C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub C.toTypeCtx rt Ty.funcref)
      (hd : C.type? y = some d) (he : Expand d (.func ps rs)) :
      InstrOk C (.callIndirect x y) (.plain (ps.toList ++ [a.valType]) rs.toList)
  /-- `Instr_ok/return`. -/
  | return_ {C : Context} {ts t₁ t₂ : List CValType}
      (hr : C.return_ = some ts) (hok : InstrTypeOk C (.plain t₁ t₂)) :
      InstrOk C .return_ (.plain (t₁ ++ ts) t₂)
  /-- `Instr_ok/return_call`. -/
  | returnCall {C : Context} {x : FuncIdx} {d : DefType} {ps rs : Ty (.list .val)}
      {rs' t₃ t₄ : List CValType}
      (hf : C.funcs[x.toNat]? = some d) (he : Expand d (.func ps rs))
      (hr : C.return_ = some rs') (hs : ResultSub C.toTypeCtx rs.toList rs')
      (hok : InstrTypeOk C (.plain t₃ t₄)) :
      InstrOk C (.returnCall x) (.plain (t₃ ++ ps.toList) t₄)
  /-- `Instr_ok/return_call_ref`. -/
  | returnCallRef {C : Context} {x : TypeIdx} {d : DefType} {ps rs : Ty (.list .val)}
      {rs' t₃ t₄ : List CValType}
      (hd : C.type? x = some d) (he : Expand d (.func ps rs))
      (hr : C.return_ = some rs') (hs : ResultSub C.toTypeCtx rs.toList rs')
      (hok : InstrTypeOk C (.plain t₃ t₄)) :
      InstrOk C (.returnCallRef x) (.plain (t₃ ++ ps.toList ++ [.refT true (.defHeap d)]) t₄)
  /-- `Instr_ok/return_call_indirect`. -/
  | returnCallIndirect {C : Context} {x : TableIdx} {y : TypeIdx} {a : AddrType} {l : Limits}
      {rt : CRefType} {d : DefType} {ps rs : Ty (.list .val)} {rs' t₃ t₄ : List CValType}
      (ht : C.tables[x.toNat]? = some ⟨a, l, rt⟩) (hs : Sub C.toTypeCtx rt Ty.funcref)
      (hd : C.type? y = some d) (he : Expand d (.func ps rs))
      (hr : C.return_ = some rs') (hrs : ResultSub C.toTypeCtx rs.toList rs')
      (hok : InstrTypeOk C (.plain t₃ t₄)) :
      InstrOk C (.returnCallIndirect x y) (.plain (t₃ ++ ps.toList ++ [a.valType]) t₄)
  /-- `Instr_ok/throw`. -/
  | throw {C : Context} {x : TagIdx} {d : DefType} {ts : Ty (.list .val)} {t₁ t₂ : List CValType}
      (hx : C.tags[x.toNat]? = some d) (he : Expand d (.func ts .nil))
      (hok : InstrTypeOk C (.plain t₁ t₂)) :
      InstrOk C (.throw x) (.plain (t₁ ++ ts.toList) t₂)
  /-- `Instr_ok/throw_ref`. -/
  | throwRef {C : Context} {t₁ t₂ : List CValType} (hok : InstrTypeOk C (.plain t₁ t₂)) :
      InstrOk C .throwRef (.plain (t₁ ++ [.refT true (.abs .exn)]) t₂)
  /-- `Instr_ok/try_table`. -/
  | tryTable {C : Context} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {t₁ t₂ : List CValType} {xs : List Nat}
      (hbt : BlockTypeOk C bt t₁ t₂) (hb : InstrsOk (C.withLabel t₂) body ⟨t₁, xs, t₂⟩)
      (hc : ∀ c ∈ cs, CatchOk C c) :
      InstrOk C (.tryTable bt cs body) (.plain t₁ t₂)

/-- `Instrs_ok: C ⊢ instr* : instrtype`. -/
inductive InstrsOk : Context → List Instr → InstrType → Prop where
  /-- `Instrs_ok/empty`. -/
  | nil {C : Context} : InstrsOk C [] (.plain [] [])
  /-- `Instrs_ok/instr`. -/
  | instr {C : Context} {i : Instr} {it : InstrType} (h : InstrOk C i it) : InstrsOk C [i] it
  /-- `Instrs_ok/seq`. -/
  | seq {C : Context} {is₁ is₂ : List Instr} {t₁ t₂ t₃ : List CValType} {xs₁ xs₂ : List Nat}
      (h₁ : InstrsOk C is₁ ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (h₂ : InstrsOk (C.initLocals xs₁) is₂ ⟨t₂, xs₂, t₃⟩) :
      InstrsOk C (is₁ ++ is₂) ⟨t₁, xs₁ ++ xs₂, t₃⟩
  /-- Derived: `Instrs_ok/seq` with an `Instrs_ok/instr` left part (kept as a
  convenience constructor; see the module doc). -/
  | cons {C : Context} {i : Instr} {is : List Instr} {t₁ t₂ t₃ : List CValType}
      {xs₁ xs₂ : List Nat}
      (hi : InstrOk C i ⟨t₁, xs₁, t₂⟩) (hx : ∀ x ∈ xs₁, ∃ lt, C.locals[x]? = some lt)
      (hs : InstrsOk (C.initLocals xs₁) is ⟨t₂, xs₂, t₃⟩) :
      InstrsOk C (i :: is) ⟨t₁, xs₁ ++ xs₂, t₃⟩
  /-- `Instrs_ok/sub`. -/
  | sub {C : Context} {is : List Instr} {it it' : InstrType}
      (h : InstrsOk C is it) (hs : InstrTypeSub C it it') (hok : InstrTypeOk C it') :
      InstrsOk C is it'
  /-- `Instrs_ok/frame`. -/
  | frame {C : Context} {is : List Instr} {ts t₁ t₂ : List CValType} {xs : List Nat}
      (h : InstrsOk C is ⟨t₁, xs, t₂⟩) (hok : ResultOk C.toTypeCtx ts) :
      InstrsOk C is ⟨ts ++ t₁, xs, ts ++ t₂⟩

end

/-- `Expr_ok: C ⊢ expr : t*`. -/
def ExprOk (C : Context) (e : Expr) (ts : List CValType) : Prop := InstrsOk C e (.plain [] ts)

end Silmaril.Wasm.Validation
