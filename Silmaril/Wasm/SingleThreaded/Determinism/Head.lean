module

public import Silmaril.Wasm.SingleThreaded.Determinism.Family

@[expose] public section

/-! # Determinism toolkit: head steps and the decomposition of a step

A *head step* `Head P s f args e c'` is a rule of `Step` other than
`ctxt-instrs`, `trap-instrs`, `throw_ref-instrs` and the host-call rules, applied
to the code `vals args ++ [e]`. Every step of a host-free configuration is
either a head step at the first non-value under a value prefix and a suffix
(`HeadDec`), or the bubbling of a `TRAP` or of a `THROW_REF` out of an
instruction sequence (`Bubble`).

The indices of `Head` are built from variables and constructors only, so that
two head derivations can be compared by `cases`.
-/

namespace Silmaril.Wasm.SingleThreaded.Det

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- The empty host relation. -/
abbrev noHost : HostSemantics H := fun _ _ _ _ => False

inductive Head (P : Profile) : Store H → Frame → List Val → Admin → Config H → Prop where
  | parametric {s : Store H} {f : Frame} {args : List Val} {e : Admin} {is' : List Admin}
      (h : ParametricStep (vals args ++ [e]) is') : Head P s f args e ⟨s, f, is'⟩
  | numeric {s : Store H} {f : Frame} {args : List Val} {e : Admin} {is' : List Admin}
      (h : NumericStep P (vals args ++ [e]) is') : Head P s f args e ⟨s, f, is'⟩
  | vector {s : Store H} {f : Frame} {args : List Val} {e : Admin} {is' : List Admin}
      (h : VectorStep P (vals args ++ [e]) is') : Head P s f args e ⟨s, f, is'⟩
  | «variable» {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c' : Config H}
      (h : VariableStep ⟨s, f, vals args ++ [e]⟩ c') : Head P s f args e c'
  | table {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c' : Config H}
      (h : TableStep P ⟨s, f, vals args ++ [e]⟩ c') : Head P s f args e c'
  | memory {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c' : Config H}
      (h : MemoryStep P ⟨s, f, vals args ++ [e]⟩ c') : Head P s f args e c'
  | reference {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c' : Config H}
      (h : RefStep ⟨s, f, vals args ++ [e]⟩ c') : Head P s f args e c'
  | aggregate {s : Store H} {f : Frame} {args : List Val} {e : Admin} {c' : Config H}
      (h : AggregateStep ⟨s, f, vals args ++ [e]⟩ c') : Head P s f args e c'
  | ctxtLabel {s s' : Store H} {f f' : Frame} {n : Nat} {cont : List Instr} {is is' : List Admin}
      (h : Step P noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Head P s f [] (.label n cont is) ⟨s', f', [.label n cont is']⟩
  | ctxtHandler {s s' : Store H} {f f' : Frame} {n : Nat} {cs : List Catch} {is is' : List Admin}
      (h : Step P noHost ⟨s, f, is⟩ ⟨s', f', is'⟩) :
      Head P s f [] (.handler n cs is) ⟨s', f', [.handler n cs is']⟩
  | ctxtFrame {s s' : Store H} {f fi fi' : Frame} {n : Nat} {is is' : List Admin}
      (h : Step P noHost ⟨s, fi, is⟩ ⟨s', fi', is'⟩) :
      Head P s f [] (.frame n fi is) ⟨s', f, [.frame n fi' is']⟩
  | block {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {args : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : args.length = t₁.length) :
      Head P s f args (.plain (.block bt body))
        ⟨s, f, [.label t₂.length [] (vals args ++ expression body)]⟩
  | loop {s : Store H} {f : Frame} {bt : BlockType} {body : List Instr} {args : List Val}
      {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : args.length = t₁.length) :
      Head P s f args (.plain (.loop bt body))
        ⟨s, f, [.label t₁.length [.loop bt body] (vals args ++ expression body)]⟩
  | ifTrue {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
      (hc : c ≠ 0) :
      Head P s f [.num ⟨.int .i32, c⟩] (.plain (.if_ bt b₁ b₂)) ⟨s, f, [.plain (.block bt b₁)]⟩
  | ifFalse {s : Store H} {f : Frame} {c : BitVec 32} {bt : BlockType} {b₁ b₂ : List Instr}
      (hc : c = 0) :
      Head P s f [.num ⟨.int .i32, c⟩] (.plain (.if_ bt b₁ b₂)) ⟨s, f, [.plain (.block bt b₂)]⟩
  | labelVals {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {body : List Admin}
      {vs : List Val} (hb : body = vals vs) :
      Head P s f [] (.label n cont body) ⟨s, f, vals vs⟩
  | brLabelZero {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {body : List Admin}
      {vs' vs : List Val} {l : LabelIdx} {rest : List Admin}
      (hb : body = vals vs' ++ vals vs ++ [.plain (.br l)] ++ rest) (hl : l.toNat = 0)
      (hn : vs.length = n) :
      Head P s f [] (.label n cont body) ⟨s, f, vals vs ++ expression cont⟩
  | brLabelSucc {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {body : List Admin}
      {vs : List Val} {l : LabelIdx} {rest : List Admin}
      (hb : body = vals vs ++ [.plain (.br l)] ++ rest) (hl : 0 < l.toNat) :
      Head P s f [] (.label n cont body) ⟨s, f, vals vs ++ [.plain (.br (labelPred l))]⟩
  | brHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {body : List Admin}
      {vs : List Val} {l : LabelIdx} {rest : List Admin}
      (hb : body = vals vs ++ [.plain (.br l)] ++ rest) :
      Head P s f [] (.handler n cs body) ⟨s, f, vals vs ++ [.plain (.br l)]⟩
  | brIfTrue {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (hc : c ≠ 0) :
      Head P s f [.num ⟨.int .i32, c⟩] (.plain (.brIf l)) ⟨s, f, [.plain (.br l)]⟩
  | brIfFalse {s : Store H} {f : Frame} {c : BitVec 32} {l : LabelIdx} (hc : c = 0) :
      Head P s f [.num ⟨.int .i32, c⟩] (.plain (.brIf l)) ⟨s, f, []⟩
  | brTableLt {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' l : LabelIdx}
      (hi : ls[i.toNat]? = some l) :
      Head P s f [.num ⟨.int .i32, i⟩] (.plain (.brTable ls l')) ⟨s, f, [.plain (.br l)]⟩
  | brTableGe {s : Store H} {f : Frame} {i : BitVec 32} {ls : List LabelIdx} {l' : LabelIdx}
      (hi : ls.length ≤ i.toNat) :
      Head P s f [.num ⟨.int .i32, i⟩] (.plain (.brTable ls l')) ⟨s, f, [.plain (.br l')]⟩
  | brOnNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
      Head P s f [.ref .null] (.plain (.brOnNull l)) ⟨s, f, [.plain (.br l)]⟩
  | brOnNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      Head P s f [v] (.plain (.brOnNull l)) ⟨s, f, [v.toAdmin]⟩
  | brOnNonNullNull {s : Store H} {f : Frame} {l : LabelIdx} :
      Head P s f [.ref .null] (.plain (.brOnNonNull l)) ⟨s, f, []⟩
  | brOnNonNullAddr {s : Store H} {f : Frame} {v : Val} {l : LabelIdx} (hv : v ≠ .ref .null) :
      Head P s f [v] (.plain (.brOnNonNull l)) ⟨s, f, [v.toAdmin, .plain (.br l)]⟩
  | brOnCastSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      Head P s f [.ref r] (.plain (.brOnCast l rt₁ rt₂)) ⟨s, f, [.ref r, .plain (.br l)]⟩
  | brOnCastFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      Head P s f [.ref r] (.plain (.brOnCast l rt₁ rt₂)) ⟨s, f, [.ref r]⟩
  | brOnCastFailSucceed {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : RefOk s r (f.module.instRef rt₂)) :
      Head P s f [.ref r] (.plain (.brOnCastFail l rt₁ rt₂)) ⟨s, f, [.ref r]⟩
  | brOnCastFailFail {s : Store H} {f : Frame} {r : Ref} {l : LabelIdx} {rt₁ rt₂ : RefType}
      (h : ¬ RefOk s r (f.module.instRef rt₂)) :
      Head P s f [.ref r] (.plain (.brOnCastFail l rt₁ rt₂)) ⟨s, f, [.ref r, .plain (.br l)]⟩
  | call {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      Head P s f [] (.plain (.call x)) ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩
  | callRefNull {s : Store H} {f : Frame} {c : Admin} (hc : c.IsCallRef) :
      Head P s f [.ref .null] c ⟨s, f, [.trap]⟩
  | callRefFunc {s : Store H} {f : Frame} {c : Admin} {args vs : List Val} {a : Nat}
      {fi : FuncInst H} {ps rs : Ty (.list .val)} {code : Func}
      (ha : args = vs ++ [.ref (.func a)])
      (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs))
      (hn : vs.length = ps.length) (hcode : fi.code = .wasm code) :
      Head P s f args c
        ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
          [.label rs.length [] (expression code.body)]]⟩
  | returnCall {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
      (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
      Head P s f [] (.plain (.returnCall x)) ⟨s, f, [.ref (.func a), .returnCallRefType fi.type]⟩
  | returnCallRefLabel {s : Store H} {f : Frame} {k : Nat} {cont : List Instr} {body : List Admin}
      {vs : List Val} {c : Admin} {rest : List Admin} (hb : body = vals vs ++ [c] ++ rest)
      (hc : c.IsReturnCallRef) :
      Head P s f [] (.label k cont body) ⟨s, f, vals vs ++ [c]⟩
  | returnCallRefHandler {s : Store H} {f : Frame} {k : Nat} {cs : List Catch} {body : List Admin}
      {vs : List Val} {c : Admin} {rest : List Admin} (hb : body = vals vs ++ [c] ++ rest)
      (hc : c.IsReturnCallRef) :
      Head P s f [] (.handler k cs body) ⟨s, f, vals vs ++ [c]⟩
  | returnCallRefFrameNull {s : Store H} {f fi : Frame} {k : Nat} {body : List Admin}
      {vs : List Val} {c : Admin} {rest : List Admin}
      (hb : body = vals vs ++ [.ref .null, c] ++ rest) (hc : c.IsReturnCallRef) :
      Head P s f [] (.frame k fi body) ⟨s, f, [.trap]⟩
  | returnCallRefFrameAddr {s : Store H} {f fi : Frame} {k : Nat} {body : List Admin}
      {vs' vs : List Val} {a : Nat} {c : Admin} {rest : List Admin} {fn : FuncInst H}
      {ps rs : Ty (.list .val)}
      (hb : body = vals vs' ++ vals vs ++ [.ref (.func a), c] ++ rest)
      (hc : c.IsReturnCallRef) (hf : s.funcs[a]? = some fn) (he : Expand fn.type (.func ps rs))
      (hn : vs.length = ps.length) :
      Head P s f [] (.frame k fi body) ⟨s, f, vals vs ++ [.ref (.func a), c.retToCallIn fi.module]⟩
  | callIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
      Head P s f [] (.plain (.callIndirect x y))
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩), .plain (.callRef y)]⟩
  | returnCallIndirect {s : Store H} {f : Frame} {x : TableIdx} {y : TypeIdx} :
      Head P s f [] (.plain (.returnCallIndirect x y))
        ⟨s, f, [.plain (.tableGet x), .plain (.refCast ⟨true, .typeIdx y⟩),
          .plain (.returnCallRef y)]⟩
  | frameVals {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin} {vs : List Val}
      (hb : body = vals vs) (hn : vs.length = n) :
      Head P s f [] (.frame n fi body) ⟨s, f, vals vs⟩
  | returnFrame {s : Store H} {f fi : Frame} {n : Nat} {body : List Admin} {vs' vs : List Val}
      {rest : List Admin} (hb : body = vals vs' ++ vals vs ++ [.plain .return_] ++ rest)
      (hn : vs.length = n) :
      Head P s f [] (.frame n fi body) ⟨s, f, vals vs⟩
  | returnLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {body : List Admin}
      {vs : List Val} {rest : List Admin} (hb : body = vals vs ++ [.plain .return_] ++ rest) :
      Head P s f [] (.label n cont body) ⟨s, f, vals vs ++ [.plain .return_]⟩
  | returnHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {body : List Admin}
      {vs : List Val} {rest : List Admin} (hb : body = vals vs ++ [.plain .return_] ++ rest) :
      Head P s f [] (.handler n cs body) ⟨s, f, vals vs ++ [.plain .return_]⟩
  | throw {s : Store H} {f : Frame} {x : TagIdx} {args : List Val} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil))
      (hn : args.length = ts.length) :
      Head P s f args (.plain (.throw x))
        ⟨s.addExn ⟨ta, args⟩, f, [.ref (.exn s.exns.length), .plain .throwRef]⟩
  | throwRefNull {s : Store H} {f : Frame} :
      Head P s f [.ref .null] (.plain .throwRef) ⟨s, f, [.trap]⟩
  | throwRefLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {a : Nat} :
      Head P s f [] (.label n cont [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
  | throwRefFrame {s : Store H} {f fi : Frame} {n : Nat} {a : Nat} :
      Head P s f [] (.frame n fi [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
  | throwRefHandlerEmpty {s : Store H} {f : Frame} {n : Nat} {a : Nat} :
      Head P s f [] (.handler n [] [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.ref (.exn a), .plain .throwRef]⟩
  | throwRefHandlerCatch {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Head P s f [] (.handler n (.catch_ x l :: cs) [.ref (.exn a), .plain .throwRef])
        ⟨s, f, vals e.fields ++ [.plain (.br l)]⟩
  | throwRefHandlerCatchRef {s : Store H} {f : Frame} {n : Nat} {x : TagIdx} {l : LabelIdx}
      {cs : List Catch} {a : Nat} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Head P s f [] (.handler n (.catchRef x l :: cs) [.ref (.exn a), .plain .throwRef])
        ⟨s, f, vals e.fields ++ [.ref (.exn a), .plain (.br l)]⟩
  | throwRefHandlerCatchAll {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx} {cs : List Catch}
      {a : Nat} :
      Head P s f [] (.handler n (.catchAll l :: cs) [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.plain (.br l)]⟩
  | throwRefHandlerCatchAllRef {s : Store H} {f : Frame} {n : Nat} {l : LabelIdx}
      {cs : List Catch} {a : Nat} :
      Head P s f [] (.handler n (.catchAllRef l :: cs) [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.ref (.exn a), .plain (.br l)]⟩
  | throwRefHandlerNext {s : Store H} {f : Frame} {n : Nat} {c : Catch} {cs : List Catch} {a : Nat}
      (h : ¬ CatchMatches s f a c) :
      Head P s f [] (.handler n (c :: cs) [.ref (.exn a), .plain .throwRef])
        ⟨s, f, [.handler n cs [.ref (.exn a), .plain .throwRef]]⟩
  | tryTable {s : Store H} {f : Frame} {bt : BlockType} {cs : List Catch} {body : List Instr}
      {args : List Val} {t₁ t₂ : List CValType} (hbt : f.module.blockType? bt = some (t₁, t₂))
      (hm : args.length = t₁.length) :
      Head P s f args (.plain (.tryTable bt cs body))
        ⟨s, f, [.handler t₂.length cs [.label t₂.length [] (vals args ++ expression body)]]⟩
  | handlerVals {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {body : List Admin}
      {vs : List Val} (hb : body = vals vs) :
      Head P s f [] (.handler n cs body) ⟨s, f, vals vs⟩
  | trapLabel {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} :
      Head P s f [] (.label n cont [.trap]) ⟨s, f, [.trap]⟩
  | trapHandler {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} :
      Head P s f [] (.handler n cs [.trap]) ⟨s, f, [.trap]⟩
  | trapFrame {s : Store H} {f fi : Frame} {n : Nat} :
      Head P s f [] (.frame n fi [.trap]) ⟨s, f, [.trap]⟩

/-! ## The first non-value of a head step -/

/-- Instructions that never reduce at the head of a sequence: they reduce only
through an enclosing label, handler or frame. -/
def Blocked (e : Admin) : Prop :=
  (∃ l, e = .plain (.br l)) ∨ e = .plain .return_ ∨ e.IsReturnCallRef

theorem famOf_of_shape {k : Fam} {args : List Val} {e : Admin}
    (h : FamShape k (vals args ++ [e])) : e.val? = none ∧ famOf e = k := by
  obtain ⟨args', e', heq, he, hk⟩ := h
  have := (append_singleton_inj.mp heq).2
  subst this
  exact ⟨he, hk⟩

theorem not_blocked_of_fam {e : Admin} {k : Fam} (hk : famOf e = k) (hc : k ≠ .control) :
    ¬ Blocked e := by
  rintro (⟨l, rfl⟩ | rfl | h)
  · exact hc (by rw [← hk]; rfl)
  · exact hc (by rw [← hk]; rfl)
  · rcases e with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsReturnCallRef] at h
    · cases i <;> simp at h; exact hc (by rw [← hk]; rfl)
    · exact hc (by rw [← hk]; rfl)

/-- The first non-value of a head step: a non-value, not blocked, not a trap,
and `THROW_REF` only on a null reference. -/
structure HeadGood (args : List Val) (e : Admin) : Prop where
  val_none : e.val? = none
  not_blocked : ¬ Blocked e
  ne_trap : e ≠ .trap
  throwRef : e = .plain .throwRef → args = [.ref .null]

theorem headGood_of_fam {k : Fam} {args : List Val} {e : Admin}
    (h : FamShape k (vals args ++ [e])) (hc : k ≠ .control) : HeadGood args e := by
  obtain ⟨hv, hk⟩ := famOf_of_shape h
  refine ⟨hv, not_blocked_of_fam hk hc, ?_, ?_⟩
  · rintro rfl; exact hc (by rw [← hk]; rfl)
  · rintro rfl; exact absurd (by rw [← hk]; rfl) hc

theorem IsCallRef.val_none {c : Admin} (h : c.IsCallRef) : c.val? = none := by
  rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
  · cases i <;> simp at h; rfl
  · rfl

theorem IsCallRef.not_blocked {c : Admin} (h : c.IsCallRef) : ¬ Blocked c := by
  rintro (⟨l, rfl⟩ | rfl | h')
  · exact h
  · exact h
  · rcases c with (i | _ | _ | _ | _ | _ | _ | _) <;> simp [Admin.IsCallRef] at h
    · cases i <;> simp at h; exact h'
    · exact h'

theorem Head.good {P : Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c' : Config H} (h : Head P s f args e c') : HeadGood args e := by
  cases h with
  | parametric h => exact headGood_of_fam (ParametricStep.shape h) (by decide)
  | numeric h => exact headGood_of_fam (NumericStep.shape h) (by decide)
  | vector h => exact headGood_of_fam (VectorStep.shape h) (by decide)
  | «variable» h => exact headGood_of_fam (VariableStep.shape h) (by decide)
  | table h => exact headGood_of_fam (TableStep.shape h) (by decide)
  | memory h => exact headGood_of_fam (MemoryStep.shape h) (by decide)
  | reference h => exact headGood_of_fam (RefStep.shape h) (by decide)
  | aggregate h => exact headGood_of_fam (AggregateStep.shape h) (by decide)
  | callRefNull hc =>
    refine ⟨IsCallRef.val_none hc, IsCallRef.not_blocked hc, ?_, fun _ => rfl⟩
    rintro rfl; exact hc
  | callRefFunc _ hc =>
    refine ⟨IsCallRef.val_none hc, IsCallRef.not_blocked hc, ?_, ?_⟩
    · rintro rfl; exact hc
    · rintro rfl; exact False.elim hc
  | throwRefNull =>
    exact ⟨rfl, by rintro (⟨l, h⟩ | h | h) <;> (cases h), by simp, fun _ => rfl⟩
  | _ =>
    exact ⟨rfl, by rintro (⟨l, h⟩ | h | h) <;> (cases h), by simp,
      by intro h; cases h⟩

/-! ## Decomposition of a host-free step -/

/-- A head step under a value prefix and a suffix. -/
def HeadDec (P : Profile) (s : Store H) (f : Frame) (code : List Admin) (c' : Config H) : Prop :=
  ∃ vs args e rest c₀, code = vals vs ++ (vals args ++ e :: rest) ∧ Head P s f args e c₀ ∧
    c' = ⟨c₀.store, c₀.frame, vals vs ++ c₀.code ++ rest⟩

/-- The bubbling instructions `TRAP` and `(REF.EXN_ADDR a) THROW_REF`. -/
def IsBubble (X : List Admin) : Prop := X = [.trap] ∨ ∃ a, X = [.ref (.exn a), .plain .throwRef]

/-- A `TRAP` or a `THROW_REF` bubbling out of part of the surrounding sequence. -/
def Bubble (s : Store H) (f : Frame) (code : List Admin) (c' : Config H) : Prop :=
  ∃ p q X u r, code = vals (p ++ q) ++ X ++ (u ++ r) ∧ IsBubble X ∧ (q ≠ [] ∨ u ≠ []) ∧
    c' = ⟨s, f, vals p ++ X ++ r⟩

theorem HeadDec.of_head {P : Profile} {s : Store H} {f : Frame} {args : List Val} {e : Admin}
    {c' : Config H} (h : Head P s f args e c') : HeadDec P s f (vals args ++ [e]) c' :=
  ⟨[], args, e, [], c', by simp, h, by cases c'; simp⟩

theorem Step.decomp {P : Profile} {c c' : Config H} (h : Step P noHost c c') :
    HeadDec P c.store c.frame c.code c' ∨ Bubble c.store c.frame c.code c' := by
  induction h with
  | parametric h =>
    obtain ⟨args, e, rfl, -, -⟩ := ParametricStep.shape h
    exact .inl (HeadDec.of_head (.parametric h))
  | numeric h =>
    obtain ⟨args, e, rfl, -, -⟩ := NumericStep.shape h
    exact .inl (HeadDec.of_head (.numeric h))
  | vector h =>
    obtain ⟨args, e, rfl, -, -⟩ := VectorStep.shape h
    exact .inl (HeadDec.of_head (.vector h))
  | «variable» h =>
    rename_i c c'
    rcases c with ⟨s, f, code⟩
    obtain ⟨args, e, rfl, -, -⟩ := VariableStep.shape h
    exact .inl (HeadDec.of_head (.variable h))
  | table h =>
    rename_i c c'
    rcases c with ⟨s, f, code⟩
    obtain ⟨args, e, rfl, -, -⟩ := TableStep.shape h
    exact .inl (HeadDec.of_head (.table h))
  | memory h =>
    rename_i c c'
    rcases c with ⟨s, f, code⟩
    obtain ⟨args, e, rfl, -, -⟩ := MemoryStep.shape h
    exact .inl (HeadDec.of_head (.memory h))
  | reference h =>
    rename_i c c'
    rcases c with ⟨s, f, code⟩
    obtain ⟨args, e, rfl, -, -⟩ := RefStep.shape h
    exact .inl (HeadDec.of_head (.reference h))
  | aggregate h =>
    rename_i c c'
    rcases c with ⟨s, f, code⟩
    obtain ⟨args, e, rfl, -, -⟩ := AggregateStep.shape h
    exact .inl (HeadDec.of_head (.aggregate h))
  | ctxtInstrs _ hne ih =>
    rename_i s s' f f' vs is is' rest _
    rcases ih with ⟨vs₀, args, e, rest₀, c₀, hcode, hh, hc⟩ | ⟨p, q, X, u, r, hcode, hX, hqu, hc⟩
    · refine .inl ⟨vs ++ vs₀, args, e, rest₀ ++ rest, c₀, ?_, hh, ?_⟩
      · simp only at hcode; subst hcode; simp
      · simp only [Config.mk.injEq] at hc ⊢
        obtain ⟨rfl, rfl, rfl⟩ := hc
        simp
    · refine .inr ⟨vs ++ p, q, X, u, r ++ rest, ?_, hX, hqu, ?_⟩
      · simp only at hcode; subst hcode; simp
      · simp only [Config.mk.injEq] at hc ⊢
        obtain ⟨rfl, rfl, rfl⟩ := hc
        simp
  | ctxtLabel h => exact .inl (HeadDec.of_head (args := []) (.ctxtLabel h))
  | ctxtHandler h => exact .inl (HeadDec.of_head (args := []) (.ctxtHandler h))
  | ctxtFrame h => exact .inl (HeadDec.of_head (args := []) (.ctxtFrame h))
  | block hbt hm => exact .inl (HeadDec.of_head (.block hbt hm))
  | loop hbt hm => exact .inl (HeadDec.of_head (.loop hbt hm))
  | ifTrue hc => exact .inl (HeadDec.of_head (.ifTrue hc))
  | ifFalse => exact .inl (HeadDec.of_head (.ifFalse rfl))
  | labelVals => exact .inl (HeadDec.of_head (args := []) (.labelVals rfl))
  | brLabelZero hl hn => exact .inl (HeadDec.of_head (args := []) (.brLabelZero rfl hl hn))
  | brLabelSucc hl => exact .inl (HeadDec.of_head (args := []) (.brLabelSucc rfl hl))
  | brHandler => exact .inl (HeadDec.of_head (args := []) (.brHandler rfl))
  | brIfTrue hc => exact .inl (HeadDec.of_head (.brIfTrue hc))
  | brIfFalse => exact .inl (HeadDec.of_head (.brIfFalse rfl))
  | brTableLt hi => exact .inl (HeadDec.of_head (.brTableLt hi))
  | brTableGe hi => exact .inl (HeadDec.of_head (.brTableGe hi))
  | brOnNullNull => exact .inl (HeadDec.of_head (.brOnNullNull))
  | brOnNullAddr hv => exact .inl (HeadDec.of_head (.brOnNullAddr hv))
  | brOnNonNullNull => exact .inl (HeadDec.of_head (.brOnNonNullNull))
  | brOnNonNullAddr hv => exact .inl (HeadDec.of_head (.brOnNonNullAddr hv))
  | brOnCastSucceed h => exact .inl (HeadDec.of_head (.brOnCastSucceed h))
  | brOnCastFail h => exact .inl (HeadDec.of_head (.brOnCastFail h))
  | brOnCastFailSucceed h => exact .inl (HeadDec.of_head (.brOnCastFailSucceed h))
  | brOnCastFailFail h => exact .inl (HeadDec.of_head (.brOnCastFailFail h))
  | call hx hf => exact .inl (HeadDec.of_head (.call hx hf))
  | callRefNull hc => exact .inl (HeadDec.of_head (.callRefNull hc))
  | callRefFunc hc hf he hn hcode =>
    rename_i f _ _ _ _ _ _ _
    left
    have := HeadDec.of_head (P := P) (f := f) (.callRefFunc rfl hc hf he hn hcode)
    simp only [vals_append, List.append_assoc] at this
    exact this
  | callRefHost _ _ _ _ _ hhost => exact hhost.elim
  | callRefHostDiv _ _ _ _ _ hhost => exact hhost.elim
  | returnCall hx hf => exact .inl (HeadDec.of_head (.returnCall hx hf))
  | returnCallRefLabel hc => exact .inl (HeadDec.of_head (args := []) (.returnCallRefLabel rfl hc))
  | returnCallRefHandler hc =>
    exact .inl (HeadDec.of_head (args := []) (.returnCallRefHandler rfl hc))
  | returnCallRefFrameNull hc =>
    exact .inl (HeadDec.of_head (args := []) (.returnCallRefFrameNull rfl hc))
  | returnCallRefFrameAddr hc hf he hn =>
    exact .inl (HeadDec.of_head (args := []) (.returnCallRefFrameAddr rfl hc hf he hn))
  | callIndirect => exact .inl (HeadDec.of_head (.callIndirect))
  | returnCallIndirect => exact .inl (HeadDec.of_head (.returnCallIndirect))
  | frameVals hn => exact .inl (HeadDec.of_head (args := []) (.frameVals rfl hn))
  | returnFrame hn => exact .inl (HeadDec.of_head (args := []) (.returnFrame rfl hn))
  | returnLabel => exact .inl (HeadDec.of_head (args := []) (.returnLabel rfl))
  | returnHandler => exact .inl (HeadDec.of_head (args := []) (.returnHandler rfl))
  | throw ht he hn => exact .inl (HeadDec.of_head (.throw ht he hn))
  | throwRefNull => exact .inl (HeadDec.of_head (.throwRefNull))
  | throwRefInstrs hne =>
    rename_i s f vs a rest
    exact .inr ⟨[], vs, _, rest, [], by simp, .inr ⟨a, rfl⟩, hne, by simp⟩
  | throwRefLabel => exact .inl (HeadDec.of_head (args := []) (.throwRefLabel))
  | throwRefFrame => exact .inl (HeadDec.of_head (args := []) (.throwRefFrame))
  | throwRefHandlerEmpty => exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerEmpty))
  | throwRefHandlerCatch he ht =>
    exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerCatch he ht))
  | throwRefHandlerCatchRef he ht =>
    exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerCatchRef he ht))
  | throwRefHandlerCatchAll => exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerCatchAll))
  | throwRefHandlerCatchAllRef =>
    exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerCatchAllRef))
  | throwRefHandlerNext h => exact .inl (HeadDec.of_head (args := []) (.throwRefHandlerNext h))
  | tryTable hbt hm => exact .inl (HeadDec.of_head (.tryTable hbt hm))
  | handlerVals => exact .inl (HeadDec.of_head (args := []) (.handlerVals rfl))
  | trapInstrs hne =>
    rename_i s f vs rest
    exact .inr ⟨[], vs, _, rest, [], by simp, .inl rfl, hne, by simp⟩
  | trapLabel => exact .inl (HeadDec.of_head (args := []) (.trapLabel))
  | trapHandler => exact .inl (HeadDec.of_head (args := []) (.trapHandler))
  | trapFrame => exact .inl (HeadDec.of_head (args := []) (.trapFrame))

end Silmaril.Wasm.SingleThreaded.Det
