module

public import Silmaril.Wasm.Validation.Instructions.Properties
public import Silmaril.Wasm.Validation.Subtyping.Check

@[expose] public section

/-! # A computable checker for instruction sequences (`Instrs_ok`, `Expr_ok`)

`checkSeq` checks an instruction sequence against a concrete (bottom-first)
operand stack. It is generic over two oracles, so that it does not depend on the
checkers of the individual instruction families:

* `atom? C S i` checks a non-control instruction `i` against the stack `S`,
  returning the number `n` of operands it consumes, the locals it initialises and
  its results (`AtomSound`);
* `tyOk Δ t` is a sound checker for `TyOk` (`TyOkSound`).

Control instructions (blocks, branches, calls, tail calls, exceptions,
`unreachable`) are handled here directly.

**Stack polymorphism.** After an instruction whose result type is arbitrary
(`unreachable`, `br`, `br_table`, `return`, `return_call*`, `throw`,
`throw_ref`) the rest of the block is checked in *polymorphic* mode: the
concrete stack is padded below, for each instruction `i`, by `arityBound C i`
copies of `BOT` (`.botv`, a subtype of every value type) -- a bound on the operands
`i` can consume, computed from the context and immediates -- and the number `k`
of `BOT`s actually consumed is returned. The polymorphic instruction's result type
is then chosen retroactively as `BOT^k`.

**Implicit `select` on `BOT`s.** `select` (no annotation) whose two value operands
are `BOT` gets the principal result `BOT` (`Instr_ok/select-impl` with `t = BOT`).

**Goal-directed ends.** `checkSeq` takes an optional goal stack. Block bodies and
expressions pass their declared result type: at the end of a polymorphic
sequence the missing bottom of the goal is materialised as `BOT`s (`endPad`), so
e.g. `unreachable` alone checks against any result type. With a goal, the
returned stack is the goal itself.

Soundness: `checkSeq_sound`, `checkInstrs?_sound`, `checkExpr?_sound`,
`checkBody?_sound`. Completeness: `Check/InstrsComplete.lean`.
-/

namespace Silmaril.Wasm.Validation

/-! ## Oracles -/

/-- The type of the atomic-instruction oracle. -/
abbrev AtomOracle := Context → List CValType → Instr → Option (Nat × List Nat × List CValType)

/-- The type of the type-validity oracle. -/
abbrev TyOkOracle := TypeCtx → {k : TKind} → Ty k → Bool

/-- Soundness of the atomic-instruction oracle. -/
def AtomSound (atom? : AtomOracle) : Prop :=
  ∀ C stk i n xs out, atom? C stk i = some (n, xs, out) → n ≤ stk.length ∧
    ∃ t₁ : List CValType, t₁.length = n ∧ InstrOk C i ⟨t₁, xs, out⟩ ∧
      ResultSub C.toTypeCtx (stk.drop (stk.length - n)) t₁

/-- Soundness of the type-validity oracle. -/
def TyOkSound (tyOk : TyOkOracle) : Prop :=
  ∀ (Δ : TypeCtx) (k : TKind) (t : Ty k), tyOk Δ t = true → TyOk Δ t

/-! ## Small checkers -/

/-- `Resulttype_sub` on Lean lists. -/
def resSub (Δ : TypeCtx) (a b : List CValType) : Bool := Sub.check Δ (Ty.ofList a) (Ty.ofList b)

theorem resSub_sound {Δ : TypeCtx} {a b : List CValType} (h : resSub Δ a b = true) :
    ResultSub Δ a b :=
  (ResultSub.iff_sub Δ a b).2 (Sub.check_sound h)

/-- Every listed local exists. -/
def localsOk (C : Context) (xs : List Nat) : Bool := xs.all fun x => (C.locals[x]?).isSome

theorem localsOk_sound {C : Context} {xs : List Nat} (h : localsOk C xs = true) :
    ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt := by
  intro x hx
  have := List.all_eq_true.1 h x hx
  exact Option.isSome_iff_exists.1 this

/-- Every type in a result type is valid (by the oracle). -/
def resOk (tyOk : TyOkOracle) (Δ : TypeCtx) (ts : List CValType) : Bool := ts.all fun t => tyOk Δ t

theorem resOk_sound {tyOk : TyOkOracle} (htyOk : TyOkSound tyOk) {Δ : TypeCtx}
    {ts : List CValType} (h : resOk tyOk Δ ts = true) : ResultOk Δ ts :=
  fun t ht => htyOk Δ _ t (List.all_eq_true.1 h t ht)

/-- Split off the last element. -/
def splitLast {α : Type} (l : List α) : Option (List α × α) :=
  match l.reverse with
  | [] => none
  | a :: r => some (r.reverse, a)

theorem splitLast_sound {α : Type} {l : List α} {ts : List α} {a : α}
    (h : splitLast l = some (ts, a)) : l = ts ++ [a] := by
  unfold splitLast at h
  split at h
  · cases h
  · rename_i a' r hr
    cases h
    have := congrArg List.reverse hr
    simpa using this

-- Namespaced to avoid clashing with `blockType?`/`tagParams?` in `Check/TyOk.lean`.
namespace CheckInstrs

/-- `Blocktype_ok` as a function. -/
def blockType? (tyOk : TyOkOracle) (C : Context) : BlockType → Option (List CValType × List CValType)
  | .empty => some ([], [])
  | .value t => if tyOk C.toTypeCtx (C.closeVal t) then some ([], [C.closeVal t]) else none
  | .typeIdx x =>
    match C.type? x with
    | some d =>
      match d.expand? with
      | some (.func ps rs) => some (ps.toList, rs.toList)
      | _ => none
    | none => none

theorem blockType?_sound {tyOk : TyOkOracle} (htyOk : TyOkSound tyOk) {C : Context}
    {bt : BlockType} {t₁ t₂ : List CValType} (h : blockType? tyOk C bt = some (t₁, t₂)) :
    BlockTypeOk C bt t₁ t₂ := by
  cases bt with
  | empty => cases h; exact .empty
  | value t =>
    simp only [blockType?] at h
    split at h
    · cases h; exact .value (htyOk _ _ _ (by assumption))
    · cases h
  | typeIdx x =>
    simp only [blockType?] at h
    split at h
    · rename_i d hd
      split at h
      · rename_i ps rs he
        cases h
        exact .typeIdx hd (Expand.iff.2 he)
      · cases h
    · cases h

/-- The tag type of a tag index: its (result-free) function parameters. -/
def tagParams? (C : Context) (x : TagIdx) : Option (List CValType) :=
  match C.tags[x.toNat]? with
  | some d =>
    match d.expand? with
    | some (.func ts .nil) => some ts.toList
    | _ => none
  | none => none

theorem tagParams?_sound {C : Context} {x : TagIdx} {ts : List CValType}
    (h : tagParams? C x = some ts) :
    ∃ d ts', C.tags[x.toNat]? = some d ∧ Expand d (.func ts' .nil) ∧ ts'.toList = ts := by
  unfold tagParams? at h
  split at h
  · rename_i d hd
    split at h
    · rename_i ts' he
      cases h
      exact ⟨d, ts', hd, Expand.iff.2 he, rfl⟩
    · cases h
  · cases h

end CheckInstrs

open CheckInstrs

/-- The function type of a defined type, as Lean lists. -/
def funcOfDef? (d : DefType) : Option (Ty (.list .val) × Ty (.list .val)) :=
  match d.expand? with
  | some (.func ps rs) => some (ps, rs)
  | _ => none

theorem funcOfDef?_sound {d : DefType} {ps rs : Ty (.list .val)}
    (h : funcOfDef? d = some (ps, rs)) : Expand d (.func ps rs) := by
  unfold funcOfDef? at h
  split at h
  · cases h; exact Expand.iff.2 (by assumption)
  · cases h

/-- `Catch_ok` as a function. -/
def catchOk? (C : Context) : Catch → Bool
  | .catch_ x l =>
    match tagParams? C x, C.labels[l.toNat]? with
    | some ts, some lt => resSub C.toTypeCtx ts lt
    | _, _ => false
  | .catchRef x l =>
    match tagParams? C x, C.labels[l.toNat]? with
    | some ts, some lt => resSub C.toTypeCtx (ts ++ [.refT false (.abs .exn)]) lt
    | _, _ => false
  | .catchAll l =>
    match C.labels[l.toNat]? with
    | some lt => resSub C.toTypeCtx [] lt
    | none => false
  | .catchAllRef l =>
    match C.labels[l.toNat]? with
    | some lt => resSub C.toTypeCtx [.refT false (.abs .exn)] lt
    | none => false

theorem catchOk?_sound {C : Context} {c : Catch} (h : catchOk? C c = true) : CatchOk C c := by
  cases c with
  | catch_ x l =>
    simp only [catchOk?] at h
    split at h
    · rename_i ts lt ht hl
      obtain ⟨d, ts', hd, he, rfl⟩ := tagParams?_sound ht
      exact .catch_ hd he hl (resSub_sound h)
    · cases h
  | catchRef x l =>
    simp only [catchOk?] at h
    split at h
    · rename_i ts lt ht hl
      obtain ⟨d, ts', hd, he, rfl⟩ := tagParams?_sound ht
      exact .catchRef hd he hl (resSub_sound h)
    · cases h
  | catchAll l =>
    simp only [catchOk?] at h
    split at h
    · exact .catchAll (by assumption) (resSub_sound h)
    · cases h
  | catchAllRef l =>
    simp only [catchOk?] at h
    split at h
    · exact .catchAllRef (by assumption) (resSub_sound h)
    · cases h

/-! ## Single steps -/

/-- The result of checking one instruction against a stack `S`:

* `normal n xs out`: consumes the top `n` entries, initialises `xs`, pushes `out`;
* `poly t₁`: consumes (a subtype of) `t₁` and has an arbitrary result type. -/
inductive StepRes where
  | normal (n : Nat) (xs : List Nat) (out : List CValType)
  | poly (t₁ : List CValType)

/-- What a step result promises about instruction `i` at stack `S`. -/
def StepSpec (C : Context) (S : List CValType) (i : Instr) : StepRes → Prop
  | .normal n xs out => n ≤ S.length ∧ ∃ t₁ : List CValType, t₁.length = n ∧
      InstrOk C i ⟨t₁, xs, out⟩ ∧ ResultSub C.toTypeCtx (S.drop (S.length - n)) t₁
  | .poly t₁ => t₁.length ≤ S.length ∧
      ResultSub C.toTypeCtx (S.drop (S.length - t₁.length)) t₁ ∧
      ∀ pre post : List CValType, ResultOk C.toTypeCtx pre → ResultOk C.toTypeCtx post →
        InstrOk C i (.plain (pre ++ t₁) post)

/-- The top `t₁.length` entries of `S` are a subtype of `t₁`. -/
def topSub (Δ : TypeCtx) (S t₁ : List CValType) : Bool :=
  decide (t₁.length ≤ S.length) && resSub Δ (S.drop (S.length - t₁.length)) t₁

theorem topSub_sound {Δ : TypeCtx} {S t₁ : List CValType} (h : topSub Δ S t₁ = true) :
    t₁.length ≤ S.length ∧ ResultSub Δ (S.drop (S.length - t₁.length)) t₁ := by
  simp only [topSub, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, resSub_sound h.2⟩

/-- A normal step with parameters `t₁`. -/
def stepA (Δ : TypeCtx) (S t₁ : List CValType) (xs : List Nat) (out : List CValType) :
    Option StepRes :=
  if topSub Δ S t₁ then some (.normal t₁.length xs out) else none

/-- A polymorphic step with parameters `t₁`. -/
def stepB (Δ : TypeCtx) (S t₁ : List CValType) : Option StepRes :=
  if topSub Δ S t₁ then some (.poly t₁) else none

theorem stepA_sound {C : Context} {S t₁ : List CValType} {xs : List Nat} {out : List CValType}
    {i : Instr} {r : StepRes} (hi : InstrOk C i ⟨t₁, xs, out⟩)
    (h : stepA C.toTypeCtx S t₁ xs out = some r) : StepSpec C S i r := by
  unfold stepA at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := topSub_sound (by assumption)
    exact ⟨h1, t₁, rfl, hi, h2⟩
  · cases h

theorem stepB_sound {C : Context} {S t₁ : List CValType} {i : Instr} {r : StepRes}
    (hi : ∀ pre post : List CValType, ResultOk C.toTypeCtx pre → ResultOk C.toTypeCtx post →
        InstrOk C i (.plain (pre ++ t₁) post))
    (h : stepB C.toTypeCtx S t₁ = some r) : StepSpec C S i r := by
  unfold stepB at h
  split at h
  · cases h
    obtain ⟨h1, h2⟩ := topSub_sound (by assumption)
    exact ⟨h1, h2, hi⟩
  · cases h

/-- The heap type of the top of the stack, when it is a reference (`BOT` for `BOT`). -/
def topHeap (S : List CValType) : Option CHeapType :=
  match S.getLast? with
  | some (.refv (.ref _ ht)) => some ht
  | some .botv => some .bot
  | _ => none

/-- The operand count a defined type imposes: its function parameters or struct
fields. -/
def defArity (d : DefType) : Nat :=
  match d.expand? with
  | some (.func ps _) => ps.toList.length
  | some (.struct fs) => fs.toList.length
  | _ => 0

/-- The length of a label type (`0` if absent). -/
def labelArity (C : Context) (l : LabelIdx) : Nat := ((C.labels[l.toNat]?).map List.length).getD 0

/-- `defArity` of a type index (`0` if absent). -/
def typeArity (C : Context) (x : TypeIdx) : Nat := ((C.type? x).map defArity).getD 0

/-- `defArity` of a function index (`0` if absent). -/
def funcArity (C : Context) (x : FuncIdx) : Nat := ((C.funcs[x.toNat]?).map defArity).getD 0

/-- `defArity` of a tag index (`0` if absent). -/
def tagArity (C : Context) (x : TagIdx) : Nat := ((C.tags[x.toNat]?).map defArity).getD 0

/-- `defArity` of a block type's parameters. -/
def btArity (C : Context) : BlockType → Nat
  | .typeIdx x => typeArity C x
  | _ => 0

/-- The context- and immediate-dependent part of `arityBound`. -/
def extraArity (C : Context) : Instr → Nat
  | .block bt _ => btArity C bt
  | .loop bt _ => btArity C bt
  | .if_ bt _ _ => btArity C bt
  | .tryTable bt _ _ => btArity C bt
  | .br l => labelArity C l
  | .brIf l => labelArity C l
  | .brTable _ l => labelArity C l
  | .brOnNull l => labelArity C l
  | .brOnNonNull l => labelArity C l
  | .brOnCast l _ _ => labelArity C l
  | .brOnCastFail l _ _ => labelArity C l
  | .call x => funcArity C x
  | .returnCall x => funcArity C x
  | .callRef x => typeArity C x
  | .returnCallRef x => typeArity C x
  | .callIndirect _ y => typeArity C y
  | .returnCallIndirect _ y => typeArity C y
  | .return_ => (C.return_.map List.length).getD 0
  | .throw x => tagArity C x
  | .structNew x => typeArity C x
  | .arrayNewFixed _ n => n.val
  | _ => 0

/-- An upper bound on the number of operands instruction `i` consumes (beyond the
arbitrary prefix of a stack-polymorphic instruction), computed from the context
and the immediates. Used as the dead-code padding depth. -/
def arityBound (C : Context) (i : Instr) : Nat := 8 + extraArity C i

section Oracles

variable (atom? : AtomOracle) (tyOk : TyOkOracle)

/-- Non-recursive instructions: control transfers handled here, everything else
by the oracle. -/
def directStep (C : Context) (S : List CValType) (i : Instr) : Option StepRes :=
  match i with
  | .unreachable => stepB C.toTypeCtx S []
  | .br l =>
    match C.labels[l.toNat]? with
    | some ts => stepB C.toTypeCtx S ts
    | none => none
  | .brIf l =>
    match C.labels[l.toNat]? with
    | some ts => stepA C.toTypeCtx S (ts ++ [.i32]) [] ts
    | none => none
  | .brTable ls l' =>
    match C.labels[l'.toNat]? with
    | some lt' =>
      let m := lt'.length
      if m + 1 ≤ S.length then
        let ts := (S.drop (S.length - (m + 1))).take m
        if resOk tyOk C.toTypeCtx ts &&
            (l' :: ls).all (fun l => match C.labels[l.toNat]? with
              | some lt => resSub C.toTypeCtx ts lt
              | none => false) then
          stepB C.toTypeCtx S (ts ++ [.i32])
        else none
      else none
    | none => none
  | .brOnNull l =>
    match C.labels[l.toNat]?, topHeap S with
    | some ts, some ht =>
      if tyOk C.toTypeCtx ht then
        stepA C.toTypeCtx S (ts ++ [.refT true ht]) [] (ts ++ [.refT false ht])
      else none
    | _, _ => none
  | .brOnNonNull l =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv (.ref _ ht)) => stepA C.toTypeCtx S (ts ++ [.refT true ht]) [] ts
      | _ => none
    | none => none
  | .brOnCast l rt₁ rt₂ =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv rt) =>
        if tyOk C.toTypeCtx (C.closeRef rt₁) && tyOk C.toTypeCtx (C.closeRef rt₂) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) rt then
          stepA C.toTypeCtx S (ts ++ [.refv (C.closeRef rt₁)]) []
            (ts ++ [.refv (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂))])
        else none
      | _ => none
    | none => none
  | .brOnCastFail l rt₁ rt₂ =>
    match C.labels[l.toNat]? with
    | some lt =>
      match splitLast lt with
      | some (ts, .refv rt) =>
        if tyOk C.toTypeCtx (C.closeRef rt₁) && tyOk C.toTypeCtx (C.closeRef rt₂) &&
            Sub.check C.toTypeCtx (C.closeRef rt₂) (C.closeRef rt₁) &&
            Sub.check C.toTypeCtx (Ty.diffrt (C.closeRef rt₁) (C.closeRef rt₂)) rt then
          stepA C.toTypeCtx S (ts ++ [.refv (C.closeRef rt₁)]) []
            (ts ++ [.refv (C.closeRef rt₂)])
        else none
      | _ => none
    | none => none
  | .call x =>
    match C.funcs[x.toNat]? with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) => stepA C.toTypeCtx S ps.toList [] rs.toList
      | none => none
    | none => none
  | .callRef x =>
    match C.type? x with
    | some d =>
      match funcOfDef? d with
      | some (ps, rs) =>
        stepA C.toTypeCtx S (ps.toList ++ [.refT true (.defHeap d)]) [] rs.toList
      | none => none
    | none => none
  | .callIndirect x y =>
    match C.tables[x.toNat]?, C.type? y with
    | some tt, some d =>
      if Sub.check C.toTypeCtx tt.element Ty.funcref then
        match funcOfDef? d with
        | some (ps, rs) =>
          stepA C.toTypeCtx S (ps.toList ++ [tt.address.valType]) [] rs.toList
        | none => none
      else none
    | _, _ => none
  | .return_ =>
    match C.return_ with
    | some ts => stepB C.toTypeCtx S ts
    | none => none
  | .returnCall x =>
    match C.funcs[x.toNat]?, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then stepB C.toTypeCtx S ps.toList else none
      | none => none
    | _, _ => none
  | .returnCallRef x =>
    match C.type? x, C.return_ with
    | some d, some rs' =>
      match funcOfDef? d with
      | some (ps, rs) =>
        if resSub C.toTypeCtx rs.toList rs' then
          stepB C.toTypeCtx S (ps.toList ++ [.refT true (.defHeap d)])
        else none
      | none => none
    | _, _ => none
  | .returnCallIndirect x y =>
    match C.tables[x.toNat]?, C.type? y, C.return_ with
    | some tt, some d, some rs' =>
      if Sub.check C.toTypeCtx tt.element Ty.funcref then
        match funcOfDef? d with
        | some (ps, rs) =>
          if resSub C.toTypeCtx rs.toList rs' then
            stepB C.toTypeCtx S (ps.toList ++ [tt.address.valType])
          else none
        | none => none
      else none
    | _, _, _ => none
  | .throw x =>
    match tagParams? C x with
    | some ts => stepB C.toTypeCtx S ts
    | none => none
  | .throwRef => stepB C.toTypeCtx S [.refT true (.abs .exn)]
  | i =>
    match atom? C S i with
    | some (n, xs, out) => some (.normal n xs out)
    | none => none

/-- The padded stack: `pad` copies of `BOT` below `s`. -/
def padStack (pad : Nat) (s : List CValType) : List CValType :=
  List.replicate pad .botv ++ s

/-- The number of `BOT`s padded below the stack when checking `i` (only in
polymorphic mode): enough for every operand `i` can consume (`arityBound`). -/
def padFor (C : Context) (poly : Bool) (i : Instr) : Nat := if poly then arityBound C i else 0

/-- The number of `BOT`s needed to reach the goal stack `g` at the end of a
sequence (only in polymorphic mode). -/
def endPad (poly : Bool) (s g : List CValType) : Nat := if poly then g.length - s.length else 0

mutual

/-- Check one instruction against the (padded) stack `S`. -/
def checkInstr (C : Context) (S : List CValType) : Instr → Option StepRes
  | .block bt body =>
    match blockType? tyOk C bt with
    | some (t₁, t₂) =>
      if resOk tyOk C.toTypeCtx t₁ && resOk tyOk C.toTypeCtx t₂ then
        match checkSeq (C.withLabel t₂) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOk C xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .loop bt body =>
    match blockType? tyOk C bt with
    | some (t₁, t₂) =>
      if resOk tyOk C.toTypeCtx t₁ && resOk tyOk C.toTypeCtx t₂ then
        match checkSeq (C.withLabel t₁) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOk C xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .if_ bt b₁ b₂ =>
    match blockType? tyOk C bt with
    | some (t₁, t₂) =>
      if resOk tyOk C.toTypeCtx t₁ && resOk tyOk C.toTypeCtx t₂ then
        match checkSeq (C.withLabel t₂) t₁ false (some t₂) b₁,
            checkSeq (C.withLabel t₂) t₁ false (some t₂) b₂ with
        | some (_, xs₁, _), some (_, xs₂, _) =>
          if localsOk C xs₁ && localsOk C xs₂ then
            stepA C.toTypeCtx S (t₁ ++ [.i32]) [] t₂
          else none
        | _, _ => none
      else none
    | none => none
  | .tryTable bt cs body =>
    match blockType? tyOk C bt with
    | some (t₁, t₂) =>
      if resOk tyOk C.toTypeCtx t₁ && resOk tyOk C.toTypeCtx t₂ && cs.all (catchOk? C) then
        match checkSeq (C.withLabel t₂) t₁ false (some t₂) body with
        | some (_, xsb, _) =>
          if localsOk C xsb then stepA C.toTypeCtx S t₁ [] t₂ else none
        | none => none
      else none
    | none => none
  | .select none =>
    -- Implicit `select` on two `BOT` operands (dead code): the principal result is `BOT`.
    match stepA C.toTypeCtx S [.botv, .botv, .i32] [] [.botv] with
    | some r => some r
    | none => directStep atom? tyOk C S (.select none)
  | i => directStep atom? tyOk C S i

/-- Check a sequence against the concrete stack `s` (in polymorphic mode when
`poly`), ending at the stack `goal` when one is given. Returns the final stack
(`goal` itself when given), the initialised locals and the number of `BOT`s
consumed below `s`. -/
def checkSeq (C : Context) (s : List CValType) (poly : Bool) (goal : Option (List CValType)) :
    List Instr → Option (List CValType × List Nat × Nat)
  | [] =>
    match goal with
    | none => some (s, [], 0)
    | some g =>
      if resSub C.toTypeCtx (List.replicate (endPad poly s g) .botv ++ s) g
          && resOk tyOk C.toTypeCtx g then
        some (g, [], endPad poly s g)
      else none
  | i :: is =>
    match checkInstr C (padStack (padFor C poly i) s) i with
    | some (.normal n xs out) =>
      if localsOk C xs && resOk tyOk C.toTypeCtx out then
        match checkSeq (C.initLocals xs) (s.take (s.length - n) ++ out) poly goal is with
        | some (out', xs', k') => some (out', xs ++ xs', k' + (n - s.length))
        | none => none
      else none
    | some (.poly t₁) =>
      match checkSeq C [] true goal is with
      | some (out', xs', _) => some (out', xs', t₁.length - s.length)
      | none => none
    | none => none

end

/-- Check an instruction sequence from stack `stk`: the final stack and the
initialised locals. -/
def checkInstrs? (C : Context) (stk : List CValType) (is : List Instr) :
    Option (List CValType × List Nat) :=
  match checkSeq atom? tyOk C stk false none is with
  | some (out, xs, _) => some (out, xs)
  | none => none

/-- Check a block body `is : t₁ → t₂` (for function bodies and blocks). -/
def checkBody? (C : Context) (t₁ t₂ : List CValType) (is : List Instr) : Bool :=
  resOk tyOk C.toTypeCtx t₁ && resOk tyOk C.toTypeCtx t₂ &&
    match checkSeq atom? tyOk C t₁ false (some t₂) is with
    | some (_, xs, _) => localsOk C xs
    | none => false

/-- Check `Expr_ok C e ts`. -/
def checkExpr? (C : Context) (e : Expr) (ts : List CValType) : Bool :=
  resOk tyOk C.toTypeCtx ts &&
    match checkSeq atom? tyOk C [] false (some ts) e with
    | some _ => true
    | none => false

end Oracles

/-! ## Soundness -/

section Sound

variable {atom? : AtomOracle} {tyOk : TyOkOracle}

theorem instrTypeOk_of {C : Context} {t₁ t₂ : List CValType} {xs : List Nat}
    (h₁ : ResultOk C.toTypeCtx t₁) (h₂ : ResultOk C.toTypeCtx t₂)
    (hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) : InstrTypeOk C ⟨t₁, xs, t₂⟩ :=
  ⟨h₁, h₂, hx⟩

theorem plainOk {C : Context} {t₁ t₂ : List CValType}
    (h₁ : ResultOk C.toTypeCtx t₁) (h₂ : ResultOk C.toTypeCtx t₂) :
    InstrTypeOk C (.plain t₁ t₂) :=
  ⟨h₁, h₂, fun _ h => by cases h⟩

/-- Weaken the results of a sequence typing. -/
theorem InstrsOk.sub_results {C : Context} {is : List Instr} {t₁ out t₂ : List CValType}
    {xs : List Nat} (h : InstrsOk C is ⟨t₁, xs, out⟩) (hs : ResultSub C.toTypeCtx out t₂)
    (h₁ : ResultOk C.toTypeCtx t₁) (h₂ : ResultOk C.toTypeCtx t₂)
    (hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) : InstrsOk C is ⟨t₁, xs, t₂⟩ :=
  .sub h ⟨ResultSub.refl _ _, hs, fun _ h hn => absurd h hn⟩ ⟨h₁, h₂, hx⟩

/-- Strengthen the parameters of a sequence typing. -/
theorem InstrsOk.sub_params {C : Context} {is : List Instr} {T t₁ out : List CValType}
    {xs : List Nat} (h : InstrsOk C is ⟨t₁, xs, out⟩) (hs : ResultSub C.toTypeCtx T t₁)
    (hT : ResultOk C.toTypeCtx T) (ho : ResultOk C.toTypeCtx out)
    (hx : ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt) : InstrsOk C is ⟨T, xs, out⟩ :=
  .sub h ⟨hs, ResultSub.refl _ _, fun _ h hn => absurd h hn⟩ ⟨hT, ho, hx⟩

theorem resultOk_replicate (Δ : TypeCtx) (k : Nat) : ResultOk Δ (List.replicate k .botv) := by
  intro t ht
  rw [List.eq_of_mem_replicate ht]
  exact .botv

theorem resultOk_i32 (Δ : TypeCtx) : ResultOk Δ [Ty.i32] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  exact .num _

theorem ResultOk.drop' {Δ : TypeCtx} {S : List CValType} (h : ResultOk Δ S) (m : Nat) :
    ResultOk Δ (S.drop m) := fun t ht => h t (List.mem_of_mem_drop ht)

theorem ResultOk.take' {Δ : TypeCtx} {S : List CValType} (h : ResultOk Δ S) (m : Nat) :
    ResultOk Δ (S.take m) := fun t ht => h t (List.mem_of_mem_take ht)

theorem resultOk_padStack {Δ : TypeCtx} {s : List CValType} (h : ResultOk Δ s) (pad : Nat) :
    ResultOk Δ (padStack pad s) :=
  ResultOk.append (resultOk_replicate _ _) h

theorem drop_pad (pad : Nat) (s : List CValType) (n : Nat) (hn : n ≤ pad + s.length) :
    (List.replicate pad Ty.botv ++ s).drop ((List.replicate pad Ty.botv ++ s).length - n) =
      List.replicate (n - s.length) Ty.botv ++ s.drop (s.length - n) := by
  rw [List.drop_append, List.drop_replicate]
  simp only [List.length_append, List.length_replicate]
  congr 2 <;> omega

theorem stack_eq (s : List CValType) (n k : Nat) :
    List.replicate k Ty.botv ++ (s.take (s.length - n) ++
        (List.replicate (n - s.length) Ty.botv ++ s.drop (s.length - n))) =
      List.replicate (k + (n - s.length)) Ty.botv ++ s := by
  by_cases hn : n ≤ s.length
  · have : n - s.length = 0 := by omega
    rw [this, List.replicate_zero, List.nil_append, Nat.add_zero, List.take_append_drop]
  · have : s.length - n = 0 := by omega
    rw [this, List.take_zero, List.drop_zero, List.nil_append, List.replicate_add,
      List.append_assoc]

theorem padStack_length (pad : Nat) (s : List CValType) :
    (padStack pad s).length = pad + s.length := by
  simp [padStack]


theorem directStep_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) {C : Context}
    {S : List CValType} {i : Instr} {r : StepRes}
    (h : directStep atom? tyOk C S i = some r) : StepSpec C S i r := by
  unfold directStep at h
  split at h
  · -- unreachable
    exact stepB_sound (fun pre post hp hq => by
      rw [List.append_nil]; exact .parametric (.unreachable (plainOk hp hq))) h
  · -- br
    split at h
    · rename_i ts hl
      exact stepB_sound (fun pre post hp hq => .br hl (plainOk hp hq)) h
    · cases h
  · -- br_if
    split at h
    · rename_i ts hl
      exact stepA_sound (.brIf hl) h
    · cases h
  · -- br_table
    rename_i ls l'
    split at h
    · rename_i lt' hl'
      dsimp only at h
      split at h
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true, List.all_eq_true] at hc
          obtain ⟨hts, hall⟩ := hc
          have hlab : ∀ l ∈ l' :: ls, ∃ lt, C.labels[l.toNat]? = some lt ∧
              ResultSub C.toTypeCtx ((S.drop (S.length - (lt'.length + 1))).take lt'.length) lt := by
            intro l hl
            have := hall l hl
            split at this
            · exact ⟨_, by assumption, resSub_sound this⟩
            · cases this
          refine stepB_sound (fun pre post hp hq => ?_) h
          rw [← List.append_assoc]
          exact .brTable (fun l hl => hlab l (List.mem_cons_of_mem _ hl)) (hlab l' (by simp))
            (plainOk (ResultOk.append (ResultOk.append hp (resOk_sound htyOk hts))
              (resultOk_i32 _)) hq)
        · cases h
      · cases h
    · cases h
  · -- br_on_null
    split at h
    · rename_i ts ht hl _
      split at h
      · exact stepA_sound (.brOnNull hl (htyOk _ _ _ (by assumption))) h
      · cases h
    · cases h
  · -- br_on_non_null
    split at h
    · rename_i lt hl
      split at h
      · rename_i ts n ht hs
        rw [splitLast_sound hs] at hl
        exact stepA_sound (.brOnNonNull hl) h
      · cases h
    · cases h
  · -- br_on_cast
    split at h
    · rename_i lt hl
      split at h
      · rename_i ts rt hs
        rw [splitLast_sound hs] at hl
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
          exact stepA_sound (.brOnCast hl (htyOk _ _ _ h1) (htyOk _ _ _ h2)
            (Sub.check_sound h3) (Sub.check_sound h4)) h
        · cases h
      · cases h
    · cases h
  · -- br_on_cast_fail
    split at h
    · rename_i lt hl
      split at h
      · rename_i ts rt hs
        rw [splitLast_sound hs] at hl
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
          exact stepA_sound (.brOnCastFail hl (htyOk _ _ _ h1) (htyOk _ _ _ h2)
            (Sub.check_sound h3) (Sub.check_sound h4)) h
        · cases h
      · cases h
    · cases h
  · -- call
    split at h
    · rename_i d hd
      split at h
      · rename_i ps rs hf
        exact stepA_sound (.call hd (funcOfDef?_sound hf)) h
      · cases h
    · cases h
  · -- call_ref
    split at h
    · rename_i d hd
      split at h
      · rename_i ps rs hf
        exact stepA_sound (.callRef hd (funcOfDef?_sound hf)) h
      · cases h
    · cases h
  · -- call_indirect
    split at h
    · rename_i tt d htt hd
      split at h
      · rename_i hsub
        split at h
        · rename_i ps rs hf
          cases tt
          exact stepA_sound (.callIndirect htt (Sub.check_sound hsub) hd (funcOfDef?_sound hf)) h
        · cases h
      · cases h
    · cases h
  · -- return
    split at h
    · rename_i ts hr
      exact stepB_sound (fun pre post hp hq => .return_ hr (plainOk hp hq)) h
    · cases h
  · -- return_call
    split at h
    · rename_i d rs' hd hr
      split at h
      · rename_i ps rs hf
        split at h
        · rename_i hs
          exact stepB_sound (fun pre post hp hq =>
            .returnCall hd (funcOfDef?_sound hf) hr (resSub_sound hs) (plainOk hp hq)) h
        · cases h
      · cases h
    · cases h
  · -- return_call_ref
    split at h
    · rename_i d rs' hd hr
      split at h
      · rename_i ps rs hf
        split at h
        · rename_i hs
          refine stepB_sound (fun pre post hp hq => ?_) h
          rw [← List.append_assoc]
          exact .returnCallRef hd (funcOfDef?_sound hf) hr (resSub_sound hs) (plainOk hp hq)
        · cases h
      · cases h
    · cases h
  · -- return_call_indirect
    split at h
    · rename_i tt d rs' htt hd hr
      split at h
      · rename_i hsub
        split at h
        · rename_i ps rs hf
          split at h
          · rename_i hs
            cases tt
            refine stepB_sound (fun pre post hp hq => ?_) h
            rw [← List.append_assoc]
            exact .returnCallIndirect htt (Sub.check_sound hsub) hd (funcOfDef?_sound hf) hr
              (resSub_sound hs) (plainOk hp hq)
          · cases h
        · cases h
      · cases h
    · cases h
  · -- throw
    split at h
    · rename_i ts ht
      obtain ⟨d, ts', hd, he, rfl⟩ := tagParams?_sound ht
      exact stepB_sound (fun pre post hp hq => .throw hd he (plainOk hp hq)) h
    · cases h
  · -- throw_ref
    exact stepB_sound (fun pre post hp hq => .throwRef (plainOk hp hq)) h
  · -- atoms
    split at h
    · rename_i n xs out ha
      cases h
      exact hatom _ _ _ _ _ _ ha
    · cases h

/-- A checked block body at its declared result type. -/
theorem body_ok {C : Context} {t₁ t₂ : List CValType} {xs : List Nat} {body : List Instr}
    (hb : InstrsOk C body ⟨List.replicate 0 Ty.botv ++ t₁, xs, t₂⟩) :
    InstrsOk C body ⟨t₁, xs, t₂⟩ := by
  simpa using hb

mutual

theorem checkInstr_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) (i : Instr)
    {C : Context} {S : List CValType} {r : StepRes}
    (h : checkInstr atom? tyOk C S i = some r) : StepSpec C S i r := by
  cases hi : i
  case block bt body =>
    rw [hi] at h
    simp only [checkInstr] at h
    split at h
    · rename_i t₁ t₂ hbt
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have h₁ := resOk_sound htyOk hc.1
        split at h
        · rename_i out xsb k hcs
          split at h
          · obtain ⟨hb, hk, hg⟩ := checkSeq_sound hatom htyOk body hcs h₁
            obtain rfl := hk rfl
            obtain rfl := hg _ rfl
            exact stepA_sound (.block (blockType?_sound htyOk hbt) (body_ok hb)) h
          · cases h
        · cases h
      · cases h
    · cases h
  case loop bt body =>
    rw [hi] at h
    simp only [checkInstr] at h
    split at h
    · rename_i t₁ t₂ hbt
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have h₁ := resOk_sound htyOk hc.1
        split at h
        · rename_i out xsb k hcs
          split at h
          · obtain ⟨hb, hk, hg⟩ := checkSeq_sound hatom htyOk body hcs h₁
            obtain rfl := hk rfl
            obtain rfl := hg _ rfl
            exact stepA_sound (.loop (blockType?_sound htyOk hbt) (body_ok hb)) h
          · cases h
        · cases h
      · cases h
    · cases h
  case if_ bt b₁ b₂ =>
    rw [hi] at h
    simp only [checkInstr] at h
    split at h
    · rename_i t₁ t₂ hbt
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have h₁ := resOk_sound htyOk hc.1
        split at h
        · rename_i out₁ xs₁ k₁ out₂ xs₂ k₂ hcs₁ hcs₂
          split at h
          · obtain ⟨hb₁, hk₁, hg₁⟩ := checkSeq_sound hatom htyOk b₁ hcs₁ h₁
            obtain ⟨hb₂, hk₂, hg₂⟩ := checkSeq_sound hatom htyOk b₂ hcs₂ h₁
            obtain rfl := hk₁ rfl
            obtain rfl := hk₂ rfl
            obtain rfl := hg₁ _ rfl
            obtain rfl := hg₂ _ rfl
            exact stepA_sound (.if_ (blockType?_sound htyOk hbt) (body_ok hb₁) (body_ok hb₂)) h
          · cases h
        · cases h
      · cases h
    · cases h
  case tryTable bt cs body =>
    rw [hi] at h
    simp only [checkInstr] at h
    split at h
    · rename_i t₁ t₂ hbt
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨hc1, _⟩, hcs'⟩ := hc
        have h₁ := resOk_sound htyOk hc1
        have hcatch : ∀ c ∈ cs, CatchOk C c :=
          fun c hc => catchOk?_sound (List.all_eq_true.1 hcs' c hc)
        split at h
        · rename_i out xsb k hcs
          split at h
          · obtain ⟨hb, hk, hg⟩ := checkSeq_sound hatom htyOk body hcs h₁
            obtain rfl := hk rfl
            obtain rfl := hg _ rfl
            exact stepA_sound (.tryTable (blockType?_sound htyOk hbt) (body_ok hb) hcatch) h
          · cases h
        · cases h
      · cases h
    · cases h
  case select ts =>
    subst hi
    cases ts with
    | none =>
      simp only [checkInstr] at h
      split at h
      · rename_i r' hst
        cases h
        exact stepA_sound (.parametric (.selectImpl .botv .botv (t' := .i32) (by decide))) hst
      · exact directStep_sound hatom htyOk h
    | some ts => exact directStep_sound hatom htyOk h
  all_goals (subst hi; exact directStep_sound hatom htyOk h)
termination_by sizeOf i
decreasing_by all_goals (subst_vars; simp <;> omega)

theorem checkSeq_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) (l : List Instr)
    {C : Context} {s : List CValType} {poly : Bool} {goal : Option (List CValType)}
    {out : List CValType} {xs : List Nat}
    {k : Nat} (h : checkSeq atom? tyOk C s poly goal l = some (out, xs, k))
    (hs : ResultOk C.toTypeCtx s) :
    InstrsOk C l ⟨List.replicate k .botv ++ s, xs, out⟩ ∧ (poly = false → k = 0) ∧
      (∀ g, goal = some g → out = g) := by
  match l with
  | [] =>
    cases goal with
    | none =>
      unfold checkSeq at h
      cases h
      exact ⟨by simpa using InstrsOk.id hs, fun _ => rfl, fun _ h => by cases h⟩
    | some g =>
      simp only [checkSeq] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2, h3⟩ := h
        subst h1 h2 h3
        simp only [Bool.and_eq_true] at hc
        refine ⟨?_, fun hp => by simp [hp, endPad], fun _ h => by cases h; rfl⟩
        have hR : ResultOk C.toTypeCtx (List.replicate (endPad poly s g) Ty.botv ++ s) :=
          ResultOk.append (resultOk_replicate _ _) hs
        exact InstrsOk.sub_results (InstrsOk.id hR) (resSub_sound hc.1) hR
          (resOk_sound htyOk hc.2) (fun _ h => by cases h)
      · cases h
  | i :: rest =>
    unfold checkSeq at h
    split at h
    · rename_i n xs₁ out₁ hci
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        obtain ⟨hx, ho⟩ := hc
        have hx' := localsOk_sound hx
        have ho' := resOk_sound htyOk ho
        split at h
        · rename_i out' xs' k' hrec
          cases h
          obtain ⟨hn, t₁, hlen, hi, hsub⟩ := checkInstr_sound hatom htyOk i hci
          have hn' : n ≤ padFor C poly i + s.length := by
            rw [← padStack_length]; exact hn
          have hT : (padStack (padFor C poly i) s).drop ((padStack (padFor C poly i) s).length - n) =
              List.replicate (n - s.length) Ty.botv ++ s.drop (s.length - n) :=
            drop_pad _ s n hn'
          rw [hT] at hsub
          have hTok : ResultOk C.toTypeCtx
              (List.replicate (n - s.length) Ty.botv ++ s.drop (s.length - n)) :=
            ResultOk.append (resultOk_replicate _ _) (hs.drop' _)
          have hs' : ResultOk (C.initLocals xs₁).toTypeCtx (s.take (s.length - n) ++ out₁) := by
            rw [Context.initLocals_toTypeCtx]; exact ResultOk.append (hs.take' _) ho'
          obtain ⟨hrest, hk', hg⟩ := checkSeq_sound hatom htyOk rest hrec hs'
          have h2 := (InstrsOk.instr hi).sub_params hsub hTok ho' hx'
          have h3 := InstrsOk.frame (ts := List.replicate k' Ty.botv ++ s.take (s.length - n)) h2
            (ResultOk.append (resultOk_replicate _ _) (hs.take' _))
          simp only [List.append_assoc] at h3
          have h4 := InstrsOk.seq h3 hx' hrest
          rw [stack_eq] at h4
          refine ⟨by simpa using h4, fun hp => ?_, hg⟩
          subst hp
          have := hk' rfl
          simp [padFor] at hn'
          omega
        · cases h
      · cases h
    · rename_i t₁ hci
      split at h
      · rename_i out' xs' k' hrec
        cases h
        obtain ⟨hn, hsub, hi⟩ := checkInstr_sound hatom htyOk i hci
        have hn' : t₁.length ≤ padFor C poly i + s.length := by
          rw [← padStack_length]; exact hn
        have hT : (padStack (padFor C poly i) s).drop ((padStack (padFor C poly i) s).length - t₁.length) =
            List.replicate (t₁.length - s.length) Ty.botv ++ s.drop (s.length - t₁.length) :=
          drop_pad _ s _ hn'
        rw [hT] at hsub
        have hTok : ResultOk C.toTypeCtx
            (List.replicate (t₁.length - s.length) Ty.botv ++ s.drop (s.length - t₁.length)) :=
          ResultOk.append (resultOk_replicate _ _) (hs.drop' _)
        obtain ⟨hrest, -, hg⟩ := checkSeq_sound hatom htyOk rest hrec (C := C) (s := [])
          (fun _ h => by cases h)
        have hI := hi (s.take (s.length - t₁.length)) (List.replicate k' Ty.botv)
          (hs.take' _) (resultOk_replicate _ _)
        have h2 := (InstrsOk.instr hI).sub_params
          (T := s.take (s.length - t₁.length) ++
            (List.replicate (t₁.length - s.length) Ty.botv ++ s.drop (s.length - t₁.length)))
          (ResultSub.append (ResultSub.refl _ _) hsub)
          (ResultOk.append (hs.take' _) hTok) (resultOk_replicate _ _) (fun _ h => by cases h)
        have h4 := InstrsOk.seq (C := C) (xs₁ := []) h2 (fun _ h => by cases h)
          (by simpa using hrest)
        have he := stack_eq s t₁.length 0
        rw [List.replicate_zero, List.nil_append, Nat.zero_add] at he
        rw [he] at h4
        refine ⟨by simpa using h4, fun hp => ?_, hg⟩
        subst hp
        simp [padFor] at hn'
        omega
      · cases h
    · cases h
termination_by sizeOf l
decreasing_by all_goals (simp_wf <;> omega)

end

/-! ## Entry points -/

/-- **Soundness** of `checkInstrs?`. -/
theorem checkInstrs?_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) {C : Context}
    {stk stk' : List CValType} {l : List Instr} {xs : List Nat}
    (h : checkInstrs? atom? tyOk C stk l = some (stk', xs)) (hs : ResultOk C.toTypeCtx stk) :
    InstrsOk C l ⟨stk, xs, stk'⟩ := by
  unfold checkInstrs? at h
  split at h
  · rename_i out xs' k hc
    cases h
    obtain ⟨hi, hk, -⟩ := checkSeq_sound hatom htyOk l hc hs
    obtain rfl := hk rfl
    simpa using hi
  · cases h

/-- **Soundness** of `checkBody?`: a block body `l : t₁ → t₂`. -/
theorem checkBody?_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) {C : Context}
    {t₁ t₂ : List CValType} {l : List Instr} (h : checkBody? atom? tyOk C t₁ t₂ l = true) :
    ∃ xs, InstrsOk C l ⟨t₁, xs, t₂⟩ ∧ ∀ x ∈ xs, ∃ lt, C.locals[x]? = some lt := by
  unfold checkBody? at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h₁, -⟩, h⟩ := h
  have h₁' := resOk_sound htyOk h₁
  split at h
  · rename_i out xs k hc
    obtain ⟨hb, hk, hg⟩ := checkSeq_sound hatom htyOk l hc h₁'
    obtain rfl := hk rfl
    obtain rfl := hg _ rfl
    exact ⟨xs, body_ok hb, localsOk_sound h⟩
  · cases h

/-- **Soundness** of `checkExpr?`. -/
theorem checkExpr?_sound (hatom : AtomSound atom?) (htyOk : TyOkSound tyOk) {C : Context}
    {e : Expr} {ts : List CValType} (h : checkExpr? atom? tyOk C e ts = true) : ExprOk C e ts := by
  unfold checkExpr? at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h₁, h⟩ := h
  split at h
  · rename_i r hc
    obtain ⟨out, xs, k⟩ := r
    obtain ⟨hb, hk, hg⟩ := checkSeq_sound hatom htyOk e hc (fun _ h => by cases h)
    obtain rfl := hk rfl
    obtain rfl := hg _ rfl
    refine InstrsOk.sub (it := ⟨[], xs, out⟩) (by simpa using hb) ?_ ?_
    · exact ⟨ResultSub.refl _ _, ResultSub.refl _ _, fun _ hm => by cases hm⟩
    · exact ⟨(fun _ hm => by cases hm), resOk_sound htyOk h₁, (fun _ hm => by cases hm)⟩
  · cases h

end Sound

end Silmaril.Wasm.Validation
