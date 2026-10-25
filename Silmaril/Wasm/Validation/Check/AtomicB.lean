module

public import Silmaril.Wasm.Validation.Instructions
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # Executable checkers for the table, memory and reference typing families

For each family a *signature* function computes, from the context and the type
on top of the operand stack, a candidate instruction type (sound w.r.t. the
family relation). The family checker then verifies that the top `n` stack
entries are subtypes of the candidate parameters (`popsOk`).

Stacks are bottom-first. Completeness is not claimed.
-/

namespace Silmaril.Wasm.Validation

/-! ## Stack matching -/

/-- Pointwise `Sub.check` on lists. -/
def listSubCheck (Δ : TypeCtx) : List CValType → List CValType → Bool
  | [], [] => true
  | a :: l, b :: l' => Sub.check Δ a b && listSubCheck Δ l l'
  | _, _ => false

theorem listSubCheck_sound {Δ : TypeCtx} :
    ∀ {l l' : List CValType}, listSubCheck Δ l l' = true → ResultSub Δ l l'
  | [], [], _ => .nil
  | a :: l, b :: l', h => by
    simp only [listSubCheck, Bool.and_eq_true] at h
    exact .cons (Sub.check_sound h.1) (listSubCheck_sound h.2)
  | [], _ :: _, h => by simp [listSubCheck] at h
  | _ :: _, [], h => by simp [listSubCheck] at h

/-- The top `ts.length` entries of `stk` are subtypes of `ts`. -/
def popsOk (Δ : TypeCtx) (stk ts : List CValType) : Bool :=
  decide (ts.length ≤ stk.length) && listSubCheck Δ (stk.drop (stk.length - ts.length)) ts

theorem popsOk_sound {Δ : TypeCtx} {stk ts : List CValType} (h : popsOk Δ stk ts = true) :
    ts.length ≤ stk.length ∧ ResultSub Δ (stk.drop (stk.length - ts.length)) ts := by
  simp only [popsOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, listSubCheck_sound h.2⟩

/-- Generic family checker from a signature function. -/
def checkBySig (Δ : TypeCtx) (sig : Option InstrType) (stk : List CValType) :
    Option (Nat × List Nat × List CValType) :=
  match sig with
  | some it => if popsOk Δ stk it.params then some (it.params.length, it.inits, it.results)
      else none
  | none => none

theorem checkBySig_sound {Δ : TypeCtx} {sig : Option InstrType} {stk : List CValType}
    {n : Nat} {xs : List Nat} {out : List CValType}
    (h : checkBySig Δ sig stk = some (n, xs, out)) :
    ∃ it, sig = some it ∧ n ≤ stk.length ∧ it.params.length = n ∧ it.inits = xs ∧
      it.results = out ∧ ResultSub Δ (stk.drop (stk.length - n)) it.params := by
  unfold checkBySig at h
  split at h
  · rename_i it
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      have := popsOk_sound hp
      exact ⟨it, rfl, this.1, rfl, rfl, rfl, this.2⟩
    · cases h
  · cases h

/-! ## Table instructions -/

/-- Candidate signature of a table instruction. -/
def tableSig? (C : Context) : Instr → Option InstrType
  | .tableGet x => match C.tables[x.toNat]? with
    | some ⟨a, _, rt⟩ => some (.plain [a.valType] [.refv rt])
    | none => none
  | .tableSet x => match C.tables[x.toNat]? with
    | some ⟨a, _, rt⟩ => some (.plain [a.valType, .refv rt] [])
    | none => none
  | .tableSize x => match C.tables[x.toNat]? with
    | some ⟨a, _, _⟩ => some (.plain [] [a.valType])
    | none => none
  | .tableGrow x => match C.tables[x.toNat]? with
    | some ⟨a, _, rt⟩ => some (.plain [.refv rt, a.valType] [a.valType])
    | none => none
  | .tableFill x => match C.tables[x.toNat]? with
    | some ⟨a, _, rt⟩ => some (.plain [a.valType, .refv rt, a.valType] [])
    | none => none
  | .tableCopy x₁ x₂ => match C.tables[x₁.toNat]?, C.tables[x₂.toNat]? with
    | some ⟨a₁, _, rt₁⟩, some ⟨a₂, _, rt₂⟩ =>
      if Sub.check C.toTypeCtx rt₂ rt₁ then
        some (.plain [a₁.valType, a₂.valType, (AddrType.min a₁ a₂).valType] [])
      else none
    | _, _ => none
  | .tableInit x y => match C.tables[x.toNat]?, C.elems[y.toNat]? with
    | some ⟨a, _, rt₁⟩, some rt₂ =>
      if Sub.check C.toTypeCtx rt₂ rt₁ then some (.plain [a.valType, .i32, .i32] [])
      else none
    | _, _ => none
  | .elemDrop y => match C.elems[y.toNat]? with
    | some _ => some (.plain [] [])
    | none => none
  | _ => none

theorem tableSig?_sound {C : Context} {i : Instr} {it : InstrType}
    (h : tableSig? C i = some it) : TableInstrOk C i it := by
  cases i <;> simp only [tableSig?] at h <;> (try cases h)
  all_goals
    repeat' (split at h <;> (try cases h))
  all_goals first
    | exact .tableGet (by assumption)
    | exact .tableSet (by assumption)
    | exact .tableSize (by assumption)
    | exact .tableGrow (by assumption)
    | exact .tableFill (by assumption)
    | exact .tableCopy (by assumption) (by assumption) (Sub.check_sound (by assumption))
    | exact .tableInit (by assumption) (by assumption) (Sub.check_sound (by assumption))
    | exact .elemDrop (by assumption)

/-- The table-family checker. -/
def tableCheck? (C : Context) (stk : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  checkBySig C.toTypeCtx (tableSig? C i) stk

theorem tableCheck?_sound {C : Context} {stk : List CValType} {i : Instr}
    {n : Nat} {xs : List Nat} {out : List CValType}
    (h : tableCheck? C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ TableInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  obtain ⟨it, hs, hn, hl, hx, hr, hsub⟩ := checkBySig_sound h
  refine ⟨hn, it.params, hl, ?_, hsub⟩
  subst hx hr
  exact tableSig?_sound hs

/-! ## Memory instructions -/

/-- Candidate signature of a memory instruction. -/
def memorySig? (C : Context) : Instr → Option InstrType
  | .memorySize x => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ => some (.plain [] [a.valType])
    | none => none
  | .memoryGrow x => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ => some (.plain [a.valType] [a.valType])
    | none => none
  | .memoryFill x => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ => some (.plain [a.valType, .i32, a.valType] [])
    | none => none
  | .memoryCopy x₁ x₂ => match C.mems[x₁.toNat]?, C.mems[x₂.toNat]? with
    | some ⟨a₁, _⟩, some ⟨a₂, _⟩ =>
      some (.plain [a₁.valType, a₂.valType, (AddrType.min a₁ a₂).valType] [])
    | _, _ => none
  | .memoryInit x y => match C.mems[x.toNat]?, C.datas[y.toNat]? with
    | some ⟨a, _⟩, some () => some (.plain [a.valType, .i32, .i32] [])
    | _, _ => none
  | .dataDrop y => match C.datas[y.toNat]? with
    | some () => some (.plain [] [])
    | none => none
  | .intLoad t p x arg => match p, C.mems[x.toNat]? with
    | none, some ⟨a, _⟩ =>
      if MemArgOk arg a t.width then some (.plain [a.valType] [.num (.int t)]) else none
    | some (sz, _), some ⟨a, _⟩ =>
      if sz.width < t.width then
        if MemArgOk arg a sz.width then some (.plain [a.valType] [.num (.int t)]) else none
      else none
    | _, _ => none
  | .floatLoad t x arg => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ => if MemArgOk arg a t.width then some (.plain [a.valType] [.num (.float t)])
      else none
    | none => none
  | .intStore t p x arg => match p, C.mems[x.toNat]? with
    | none, some ⟨a, _⟩ =>
      if MemArgOk arg a t.width then some (.plain [a.valType, .num (.int t)] []) else none
    | some sz, some ⟨a, _⟩ =>
      if sz.width < t.width then
        if MemArgOk arg a sz.width then some (.plain [a.valType, .num (.int t)] []) else none
      else none
    | _, _ => none
  | .floatStore t x arg => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ =>
      if MemArgOk arg a t.width then some (.plain [a.valType, .num (.float t)] []) else none
    | none => none
  | .vecLoad op x arg => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ =>
      if MemArgOk arg a op.accessWidth then some (.plain [a.valType] [.v128]) else none
    | none => none
  | .vecLoadLane sz x arg i => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ =>
      if MemArgOk arg a sz.width then
        if i.val < 128 / sz.width then some (.plain [a.valType, .v128] [.v128]) else none
      else none
    | none => none
  | .vecStore x arg => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ => if MemArgOk arg a 128 then some (.plain [a.valType, .v128] []) else none
    | none => none
  | .vecStoreLane sz x arg i => match C.mems[x.toNat]? with
    | some ⟨a, _⟩ =>
      if MemArgOk arg a sz.width then
        if i.val < 128 / sz.width then some (.plain [a.valType, .v128] []) else none
      else none
    | none => none
  | _ => none

theorem memorySig?_sound {C : Context} {i : Instr} {it : InstrType}
    (h : memorySig? C i = some it) : MemoryInstrOk C i it := by
  cases i <;> simp only [memorySig?] at h <;> (try cases h)
  all_goals
    repeat' (split at h <;> (try cases h))
  all_goals first
    | exact .memorySize (by assumption)
    | exact .memoryGrow (by assumption)
    | exact .memoryFill (by assumption)
    | exact .memoryCopy (by assumption) (by assumption)
    | exact .memoryInit (by assumption) (by assumption)
    | exact .dataDrop (by assumption)
    | exact .intLoad (by assumption) (by assumption)
    | exact .intLoadPack (by assumption) (by assumption) (by assumption)
    | exact .floatLoad (by assumption) (by assumption)
    | exact .intStore (by assumption) (by assumption)
    | exact .intStorePack (by assumption) (by assumption) (by assumption)
    | exact .floatStore (by assumption) (by assumption)
    | exact .vecLoad (by assumption) (by assumption)
    | exact .vecLoadLane (by assumption) (by assumption) (by assumption)
    | exact .vecStore (by assumption) (by assumption)
    | exact .vecStoreLane (by assumption) (by assumption) (by assumption)

/-- The memory-family checker. -/
def memoryCheck? (C : Context) (stk : List CValType) (i : Instr) :
    Option (Nat × List Nat × List CValType) :=
  checkBySig C.toTypeCtx (memorySig? C i) stk

theorem memoryCheck?_sound {C : Context} {stk : List CValType} {i : Instr}
    {n : Nat} {xs : List Nat} {out : List CValType}
    (h : memoryCheck? C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ MemoryInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  obtain ⟨it, hs, hn, hl, hx, hr, hsub⟩ := checkBySig_sound h
  refine ⟨hn, it.params, hl, ?_, hsub⟩
  subst hx hr
  exact memorySig?_sound hs

/-! ## Reference instructions -/

/-- The heap type of a reference operand (`BOT` for the bottom value type). -/
def refOperandHeap? : Option CValType → Option CHeapType
  | some (.refv (.ref _ ht)) => some ht
  | some .botv => some .bot
  | _ => none

/-- The nullability of a reference operand (non-null for the bottom value type). -/
def refOperandNull? : Option CValType → Option Bool
  | some (.refv (.ref n _)) => some n
  | some .botv => some false
  | _ => none

/-- Candidate operand supertypes for `ref.test`/`ref.cast`: the operand's own
reference type, the target, and the (nullable) tops of the four hierarchies. -/
def castCandidates (t : CValType) (r : CRefType) : List CRefType :=
  (match t with
    | .refv r' => [r']
    | _ => []) ++
  [r, .ref true (.abs .any), .ref true (.abs .func), .ref true (.abs .extern),
    .ref true (.abs .exn)]

/-- A common supertype `rt'` of the target `r` and the operand `t`. -/
def castTarget? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (t : CValType)
    (r : CRefType) : Option CRefType :=
  (castCandidates t r).find? fun c =>
    tyOk c && Sub.check C.toTypeCtx r c && Sub.check C.toTypeCtx t (.refv c)

theorem castTarget?_spec {tyOk : {k : TKind} → Ty k → Bool} {C : Context} {t : CValType}
    {r c : CRefType} (h : castTarget? tyOk C t r = some c) :
    tyOk c = true ∧ Sub.check C.toTypeCtx r c = true := by
  have := List.find?_some h
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2⟩

/-- Candidate signature of a reference instruction, given the type on top of
the operand stack (if any). -/
def refSig? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (top : Option CValType) :
    Instr → Option InstrType
  | .refNull ht =>
    if tyOk (C.closeHeap ht) then some (.plain [] [.refT true (C.closeHeap ht)]) else none
  | .refFunc x => match C.funcs[x.toNat]? with
    | some d => if x.toNat ∈ C.refs then some (.plain [] [.refT false (.defHeap d)]) else none
    | none => none
  | .refI31 => some (.plain [.i32] [.refT false (.abs .i31)])
  | .refIsNull => match refOperandHeap? top with
    | some ht => if tyOk ht then some (.plain [.refT true ht] [.i32]) else none
    | none => none
  | .refAsNonNull => match refOperandHeap? top with
    | some ht => if tyOk ht then some (.plain [.refT true ht] [.refT false ht]) else none
    | none => none
  | .refEq => some (.plain [.refT true (.abs .eq), .refT true (.abs .eq)] [.i32])
  | .refTest rt => match top with
    | some t =>
      if tyOk (C.closeRef rt) then
        match castTarget? tyOk C t (C.closeRef rt) with
        | some c => some (.plain [.refv c] [.i32])
        | none => none
      else none
    | none => none
  | .refCast rt => match top with
    | some t =>
      if tyOk (C.closeRef rt) then
        match castTarget? tyOk C t (C.closeRef rt) with
        | some c => some (.plain [.refv c] [.refv (C.closeRef rt)])
        | none => none
      else none
    | none => none
  | .i31Get _ => some (.plain [.refT true (.abs .i31)] [.i32])
  | .structNew x => match C.type? x with
    | some d => match d.expand? with
      | some (.struct fs) =>
        some (.plain (fs.toList.map fieldUnpack) [.refT false (.defHeap d)])
      | _ => none
    | none => none
  | .structNewDefault x => match C.type? x with
    | some d => match d.expand? with
      | some (.struct fs) =>
        if ∀ f ∈ fs.toList, Defaultable (fieldUnpack f) then
          some (.plain [] [.refT false (.defHeap d)])
        else none
      | _ => none
    | none => none
  | .structGet sx x i => match C.type? x with
    | some d => match d.expand? with
      | some (.struct fs) => match fs.toList[i.toNat]? with
        | some (.field _ z) =>
          if sx.isSome = z.isPacked then some (.plain [.refT true (.defHeap d)] [z.unpack])
          else none
        | none => none
      | _ => none
    | none => none
  | .structSet x i => match C.type? x with
    | some d => match d.expand? with
      | some (.struct fs) => match fs.toList[i.toNat]? with
        | some (.field .var z) => some (.plain [.refT true (.defHeap d), z.unpack] [])
        | _ => none
      | _ => none
    | none => none
  | .arrayNew x => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field _ z)) => some (.plain [z.unpack, .i32] [.refT false (.defHeap d)])
      | _ => none
    | none => none
  | .arrayNewDefault x => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field _ z)) =>
        if Defaultable z.unpack then some (.plain [.i32] [.refT false (.defHeap d)]) else none
      | _ => none
    | none => none
  | .arrayNewFixed x n => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field _ z)) =>
        some (.plain (List.replicate n.val z.unpack) [.refT false (.defHeap d)])
      | _ => none
    | none => none
  | .arrayNewElem x y => match C.type? x with
    | some d => match d.expand?, C.elems[y.toNat]? with
      | some (.array (.field _ (.val (.refv rt)))), some rt' =>
        if Sub.check C.toTypeCtx rt' rt then
          some (.plain [.i32, .i32] [.refT false (.defHeap d)])
        else none
      | _, _ => none
    | none => none
  | .arrayNewData x y => match C.type? x with
    | some d => match d.expand?, C.datas[y.toNat]? with
      | some (.array (.field _ z)), some () =>
        if z.unpack.IsNumOrVec then some (.plain [.i32, .i32] [.refT false (.defHeap d)])
        else none
      | _, _ => none
    | none => none
  | .arrayGet sx x => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field _ z)) =>
        if sx.isSome = z.isPacked then some (.plain [.refT true (.defHeap d), .i32] [z.unpack])
        else none
      | _ => none
    | none => none
  | .arraySet x => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field .var z)) =>
        some (.plain [.refT true (.defHeap d), .i32, z.unpack] [])
      | _ => none
    | none => none
  | .arrayLen => some (.plain [.refT true (.abs .array)] [.i32])
  | .arrayFill x => match C.type? x with
    | some d => match d.expand? with
      | some (.array (.field .var z)) =>
        some (.plain [.refT true (.defHeap d), .i32, z.unpack, .i32] [])
      | _ => none
    | none => none
  | .arrayCopy x₁ x₂ => match C.type? x₁, C.type? x₂ with
    | some d₁, some d₂ => match d₁.expand?, d₂.expand? with
      | some (.array (.field .var z₁)), some (.array (.field _ z₂)) =>
        if Sub.check C.toTypeCtx z₂ z₁ then
          some (.plain [.refT true (.defHeap d₁), .i32, .refT true (.defHeap d₂), .i32, .i32] [])
        else none
      | _, _ => none
    | _, _ => none
  | .arrayInitElem x y => match C.type? x with
    | some d => match d.expand?, C.elems[y.toNat]? with
      | some (.array (.field .var z)), some rt =>
        if Sub.check C.toTypeCtx (.val (.refv rt)) z then
          some (.plain [.refT true (.defHeap d), .i32, .i32, .i32] [])
        else none
      | _, _ => none
    | none => none
  | .arrayInitData x y => match C.type? x with
    | some d => match d.expand?, C.datas[y.toNat]? with
      | some (.array (.field .var z)), some () =>
        if z.unpack.IsNumOrVec then
          some (.plain [.refT true (.defHeap d), .i32, .i32, .i32] [])
        else none
      | _, _ => none
    | none => none
  | .externConvertAny => match refOperandNull? top with
    | some n => some (.plain [.refT n (.abs .any)] [.refT n (.abs .extern)])
    | none => none
  | .anyConvertExtern => match refOperandNull? top with
    | some n => some (.plain [.refT n (.abs .extern)] [.refT n (.abs .any)])
    | none => none
  | _ => none

theorem refSig?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {top : Option CValType} {i : Instr} {it : InstrType}
    (h : refSig? tyOk C top i = some it) : RefInstrOk C i it := by
  cases i <;> simp only [refSig?] at h <;> (try cases h)
  all_goals
    repeat' (split at h <;> (try cases h))
  all_goals first
    | exact .refNull (htyOk (by assumption))
    | exact .refFunc (by assumption) (by assumption)
    | exact .refI31
    | exact .refIsNull (htyOk (by assumption))
    | exact .refAsNonNull (htyOk (by assumption))
    | exact .refEq
    | exact .refTest (htyOk (by assumption)) (htyOk (castTarget?_spec (by assumption)).1)
        (Sub.check_sound (castTarget?_spec (by assumption)).2)
    | exact .refCast (htyOk (by assumption)) (htyOk (castTarget?_spec (by assumption)).1)
        (Sub.check_sound (castTarget?_spec (by assumption)).2)
    | exact .i31Get _
    | exact .structNew (by assumption) (Expand.iff.mpr (by assumption))
    | exact .structNewDefault (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
    | exact .structGet (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (by assumption)
    | exact .structSet (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
    | exact .arrayNew (by assumption) (Expand.iff.mpr (by assumption))
    | exact .arrayNewDefault (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
    | exact .arrayNewFixed (by assumption) (Expand.iff.mpr (by assumption))
    | exact .arrayNewElem (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (Sub.check_sound (by assumption))
    | exact .arrayNewData (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (by assumption)
    | exact .arrayGet (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
    | exact .arraySet (by assumption) (Expand.iff.mpr (by assumption))
    | exact .arrayLen
    | exact .arrayFill (by assumption) (Expand.iff.mpr (by assumption))
    | exact .arrayCopy (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (Expand.iff.mpr (by assumption)) (Sub.check_sound (by assumption))
    | exact .arrayInitElem (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (Sub.check_sound (by assumption))
    | exact .arrayInitData (by assumption) (Expand.iff.mpr (by assumption)) (by assumption)
        (by assumption)
    | exact .externConvertAny _
    | exact .anyConvertExtern _

/-- The reference-family checker. -/
def refCheck? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (stk : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  checkBySig C.toTypeCtx (refSig? tyOk C stk.getLast? i) stk

theorem refCheck?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {stk : List CValType} {i : Instr} {n : Nat} {xs : List Nat} {out : List CValType}
    (h : refCheck? tyOk C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ RefInstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  obtain ⟨it, hs, hn, hl, hx, hr, hsub⟩ := checkBySig_sound h
  refine ⟨hn, it.params, hl, ?_, hsub⟩
  subst hx hr
  exact refSig?_sound htyOk hs

/-! ## Dispatch -/

/-- Checker for the table, memory and reference families. -/
def atomicB? (tyOk : {k : TKind} → Ty k → Bool) (C : Context) (stk : List CValType)
    (i : Instr) : Option (Nat × List Nat × List CValType) :=
  match tableCheck? C stk i with
  | some r => some r
  | none => match memoryCheck? C stk i with
    | some r => some r
    | none => refCheck? tyOk C stk i

theorem atomicB?_sound {tyOk : {k : TKind} → Ty k → Bool} {C : Context}
    (htyOk : ∀ {k} {t : Ty k}, tyOk t = true → TyOk C.toTypeCtx t)
    {stk : List CValType} {i : Instr} {n : Nat} {xs : List Nat} {out : List CValType}
    (h : atomicB? tyOk C stk i = some (n, xs, out)) :
    n ≤ stk.length ∧ ∃ t₁, t₁.length = n ∧ InstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁ := by
  unfold atomicB? at h
  split at h
  · rename_i ht
    cases h
    obtain ⟨hn, t₁, hl, hi, hs⟩ := tableCheck?_sound ht
    exact ⟨hn, t₁, hl, .table hi, hs⟩
  · split at h
    · rename_i hm
      cases h
      obtain ⟨hn, t₁, hl, hi, hs⟩ := memoryCheck?_sound hm
      exact ⟨hn, t₁, hl, .memory hi, hs⟩
    · obtain ⟨hn, t₁, hl, hi, hs⟩ := refCheck?_sound htyOk h
      exact ⟨hn, t₁, hl, .reference hi, hs⟩

end Silmaril.Wasm.Validation
